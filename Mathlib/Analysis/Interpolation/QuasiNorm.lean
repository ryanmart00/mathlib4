/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Quasi-normed additive groups and quasi-norm equivalence

DRAFT — under review, statement-design stage (Unit 0 of the quasi-Banach generalization of the
interpolation-couple framework; see `PROGRESS-interpolation-theory.md`).

## Main definitions

* `QuasinormedAddCommGroup`: like `NormedAddCommGroup`, but the triangle inequality is only
  required up to a fixed multiplicative constant `quasiTriangleConst` — the literature's
  `‖a+b‖ ≲ ‖a‖+‖b‖` — rather than exactly, and bundles its own topology/uniform structure exactly
  the way `NormedAddCommGroup` does (see the design note below). This is what weak-`Lᵖ` (and
  Lorentz spaces generally) actually satisfy, motivating the whole generalization: every genuine
  `NormedAddCommGroup` is an instance with `quasiTriangleConst = 1`
  (`NormedAddCommGroup.toQuasinormedAddCommGroup`), reusing its own topology verbatim, so the
  classical case is recovered exactly, not just up to equivalence.

Equivalence of quasi-Banach spaces (quasinorms comparable up to constants in both directions) is
not a separate notion: it is an isomorphism in `QuasiBanachCat` (`QuasiBanachCat.lean`), i.e. a
continuous linear equivalence, since continuous linear maps between quasi-normed spaces are
automatically bounded (`le_opQuasiNorm`).

## Notation

Scoped under `QuasinormedAddCommGroup` (open with `open scoped QuasinormedAddCommGroup`):
`f ≲ g` for "`‖f x‖` is bounded by a constant multiple of `‖g x‖`, for *all* `x`" and `f ∼ g` for
the two-sided version — spelled out directly as `∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖` (resp. both
directions) rather than reused from `Asymptotics.IsBigO`/`IsTheta` (even instantiated at the top
filter, which was tried and dropped: it pulls in `Filter`/`Eventually` machinery for no benefit
here, and several of Mathlib's own convenience lemmas around it need `SeminormedAddGroup`, which a
merely-quasi-normed space doesn't have — friction with no payoff since we never actually reuse
`Filter`-indexed asymptotics elsewhere). The tradeoff, deliberately accepted: no free ride on
`IsBigO`/`IsTheta`'s general algebra (`.trans`, `.add`, `.symm`, ...) — any such fact needed later
(e.g. composing two equivalences) gets proved directly against the explicit existential instead.

## Design note: the topology is bundled in, exactly like `NormedAddCommGroup`

This class went through two revisions before landing here — worth recording, since the reasoning
matters more than the current shape:

1. First version: purely algebraic, no topology at all (a leg's topology was separately-supplied
   data everywhere it was needed). Reconsidered per Ryan: there is no reason a quasi-norm can't
   get its own topology the way `NormedAddCommGroup` does (the "no topology" version wrongly
   assumed deriving one needs the Aoki–Rolewicz theorem — it doesn't; see `AddGroupFilterBasis`
   below).
2. Second version: the topology-bearing pieces were split into a *second* class,
   `QuasiBanachAddCommGroup`, built by `extends QuasinormedAddCommGroup E, UniformSpace E`.
   Reconsidered again per Ryan, for two reasons. First, structurally: `NormedAddCommGroup` does
   *not* split this way — it (via `PseudoMetricSpace`) bundles its uniform space as a single
   **plain named field** `toUniformSpace : UniformSpace α := .ofDist ...` with a real default,
   and grants instance status via a separate `attribute [instance] ... .toUniformSpace` line, not
   by `extends UniformSpace`. Actually `extends UniformSpace` was the root cause of the whole
   second version's awkwardness: it flattens `UniformSpace`'s own four raw fields in, turning
   `toUniformSpace` into a *derived projection* that Lean refuses to give a default to ("Field
   `toUniformSpace` has already been declared as a projection for parent `UniformSpace`") — which
   is exactly why that version needed two separate hand-built constructors instead of one
   convenient default. Second, there was never a genuine use for the topology-free class on its
   own — every actual consumer wanted the topology too, so keeping two classes was just
   reproducing the friction (missing `UniformSpace`, missing `FirstCountableTopology`, ...) that
   bundling is supposed to remove, for no compensating benefit. Mirrors `NormedAddCommGroup` in
   exactly the relevant sense: `CompleteSpace` stays a separate bracket hypothesis added downstream
   (there is no separate "Banach" class in Mathlib either), but the topology itself is not
   optional.

This third version: one class, `toUniformSpace`/`toIsTopologicalAddGroup`/`toIsUniformAddGroup`
are plain named fields with real defaults (built from the *quasi*-norm data via
`AddGroupFilterBasis.ofQuasiNorm`, defined first, taking that data as plain explicit arguments —
exactly mirroring `UniformSpace.ofDist dist dist_self dist_comm dist_triangle`, which is *why*
that helper needs to exist as its own top-level definition rather than being folded into the
class body: a field's default can only reference *earlier* fields as plain local terms, and a
class can't refer to an instance of itself while still being defined). Instance status for all
three is granted the same way `PseudoMetricSpace.toUniformSpace`/`.toBornology` get it: one
`attribute [instance_reducible, instance] ...` line right after the class, not via `extends`.
`nhds_zero_hasBasis` (norm-balls are a neighborhood basis of `0`) is a fourth bundled field, with
no Mathlib analogue to mirror — it plays the role `PseudoMetricSpace.uniformity_dist` plays there
(tying the bundled uniform structure back to the norm), needed here because we don't get it for
free from `dist x y := ‖x - y‖` the way a `PseudoMetricSpace` does (our triangle inequality isn't
exact, so we can't literally reuse that route — see `AddGroupFilterBasis.ofQuasiNorm`'s docstring).

**Diamond note for `instProd`**: giving the *product* instance `E × F` its own fresh
`AddGroupFilterBasis`-derived topology (i.e. just taking the field defaults) would build a
*second*, only propositionally-equal `TopologicalSpace (E × F)` alongside the one Mathlib already
assembles generically from `[TopologicalSpace E] [TopologicalSpace F]` — so `instProd` explicitly
overrides all four bundled fields to reuse `E`'s and `F`'s own (`Prod.instUniformSpace`,
`Prod.instIsUniformGroup`, ...), never falling back to the defaults, exactly like the
`NormedAddCommGroup` bridge instance reuses rather than recomputes.
-/

open Set Pointwise in
/-- Build the canonical additive-group filter basis for a quasi-norm from its raw axioms, with
*no* `QuasinormedAddCommGroup` instance required — this is what lets `QuasinormedAddCommGroup`
below default its own bundled topology/uniform space to this construction, the same way
`PseudoMetricSpace.toUniformSpace` defaults to `UniformSpace.ofDist dist dist_self dist_comm
dist_triangle`. The construction itself: norm-balls `{x : ‖x‖ < ε}` satisfy the
entourage-composition axiom a filter basis needs using only the *quasi* (not exact) triangle
inequality — picking `ε' = ε / (2C)` gives `‖x‖ < ε' ∧ ‖y‖ < ε' → ‖x+y‖ ≤ C(‖x‖+‖y‖) < ε`. No
Aoki–Rolewicz theorem needed (that theorem gets an *equivalent linear-homogeneous* norm, far more
than the mere topology needed here). -/
@[instance_reducible]
def AddGroupFilterBasis.ofQuasiNorm {E : Type*} [Norm E] [AddCommGroup E] (C : ℝ) (hC : 1 ≤ C)
    (norm_add_le : ∀ a b : E, ‖a + b‖ ≤ C * (‖a‖ + ‖b‖)) (norm_neg : ∀ a : E, ‖-a‖ = ‖a‖)
    (norm_eq_zero_iff : ∀ a : E, ‖a‖ = 0 ↔ a = 0) : AddGroupFilterBasis E :=
  have hC' : 0 < C := by linarith
  addGroupFilterBasisOfComm {s | ∃ ε > 0, s = {x : E | ‖x‖ < ε}}
    ⟨_, 1, one_pos, rfl⟩
    (by
      rintro _ _ ⟨ε₁, hε₁, rfl⟩ ⟨ε₂, hε₂, rfl⟩
      refine ⟨{x : E | ‖x‖ < min ε₁ ε₂}, ⟨min ε₁ ε₂, lt_min hε₁ hε₂, rfl⟩, fun x hx => ?_⟩
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff] at hx ⊢
      exact ⟨hx.trans_le (min_le_left _ _), hx.trans_le (min_le_right _ _)⟩)
    (by
      rintro _ ⟨ε, hε, rfl⟩
      simpa using (norm_eq_zero_iff 0).mpr rfl ▸ hε)
    (by
      rintro _ ⟨ε, hε, rfl⟩
      refine ⟨{x : E | ‖x‖ < ε / (2 * C)}, ⟨_, by positivity, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      calc ‖x + y‖ ≤ C * (‖x‖ + ‖y‖) := norm_add_le x y
        _ < C * (2 * (ε / (2 * C))) := mul_lt_mul_of_pos_left (by linarith) hC'
        _ = ε := by field_simp)
    (by
      rintro _ ⟨ε, hε, rfl⟩
      refine ⟨{x : E | ‖x‖ < ε}, ⟨ε, hε, rfl⟩, fun x hx => ?_⟩
      rw [Set.mem_preimage, Set.mem_ofPred_eq, norm_neg]
      exact hx)

/-- A *quasi-normed* additive commutative group: like `NormedAddCommGroup`, except the triangle
inequality `‖a+b‖ ≤ ‖a‖+‖b‖` is weakened to `‖a+b‖ ≤ quasiTriangleConst * (‖a‖+‖b‖)` for a fixed
constant `quasiTriangleConst ≥ 1` — and, like `NormedAddCommGroup`, bundles its own topology and
uniform structure (see the module docstring for the design history and why it's shaped this way).
`CompleteSpace` is deliberately *not* part of this class, matching `NormedAddCommGroup`: add it
as a separate bracket hypothesis wherever the "quasi-Banach" case is actually needed. -/
class QuasinormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E where
  /-- The fixed constant in the quasi-triangle inequality (`1` for a genuine norm). -/
  quasiTriangleConst : ℝ
  one_le_quasiTriangleConst : 1 ≤ quasiTriangleConst
  norm_add_le : ∀ a b : E, ‖a + b‖ ≤ quasiTriangleConst * (‖a‖ + ‖b‖)
  norm_neg : ∀ a : E, ‖-a‖ = ‖a‖
  norm_eq_zero_iff : ∀ a : E, ‖a‖ = 0 ↔ a = 0
  toUniformSpace : UniformSpace E :=
    (AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst one_le_quasiTriangleConst norm_add_le
      norm_neg norm_eq_zero_iff).uniformSpace
  toIsTopologicalAddGroup : IsTopologicalAddGroup E := by
    show @IsTopologicalAddGroup E
      (AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst one_le_quasiTriangleConst norm_add_le
        norm_neg norm_eq_zero_iff).uniformSpace.toTopologicalSpace _
    exact (AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst one_le_quasiTriangleConst norm_add_le
      norm_neg norm_eq_zero_iff).isTopologicalAddGroup
  toIsUniformAddGroup : IsUniformAddGroup E := by
    show @IsUniformAddGroup E
      (AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst one_le_quasiTriangleConst norm_add_le
        norm_neg norm_eq_zero_iff).uniformSpace _
    exact (AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst one_le_quasiTriangleConst norm_add_le
      norm_neg norm_eq_zero_iff).isUniformAddGroup
  /-- Norm-balls are a neighborhood basis of `0` — ties the bundled topology back to the norm,
  playing the role `PseudoMetricSpace.uniformity_dist` plays for genuine norms. -/
  nhds_zero_hasBasis : (@nhds E toUniformSpace.toTopologicalSpace 0).HasBasis (0 < ·)
      (fun ε : ℝ => {x : E | ‖x‖ < ε}) := by
    have hB := AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst one_le_quasiTriangleConst
      norm_add_le norm_neg norm_eq_zero_iff
    show (@nhds E hB.uniformSpace.toTopologicalSpace 0).HasBasis (0 < ·)
      fun ε : ℝ => {x : E | ‖x‖ < ε}
    rw [hB.nhds_eq (x₀ := 0), AddGroupFilterBasis.N_zero]
    refine (FilterBasis.hasBasis hB.toFilterBasis).to_hasBasis' ?_ ?_
    · rintro s ⟨ε, hε, rfl⟩
      exact ⟨ε, hε, subset_rfl⟩
    · rintro ε hε
      exact FilterBasis.mem_filter_of_mem _ ⟨ε, hε, rfl⟩

attribute [instance_reducible, instance] QuasinormedAddCommGroup.toUniformSpace
attribute [instance] QuasinormedAddCommGroup.toIsTopologicalAddGroup
  QuasinormedAddCommGroup.toIsUniformAddGroup

namespace QuasinormedAddCommGroup

variable {E : Type*} [QuasinormedAddCommGroup E]

theorem norm_nonneg (a : E) : 0 ≤ ‖a‖ := by
  by_contra h
  rw [not_le] at h
  have h0 : ‖(0 : E)‖ = 0 := (norm_eq_zero_iff 0).mpr rfl
  have htri := norm_add_le a (-a)
  rw [add_neg_cancel, norm_neg, h0] at htri
  nlinarith [one_le_quasiTriangleConst (E := E)]

@[simp] theorem norm_zero : ‖(0 : E)‖ = 0 := (norm_eq_zero_iff 0).mpr rfl

theorem quasiTriangleConst_pos : 0 < quasiTriangleConst (E := E) := by
  linarith [one_le_quasiTriangleConst (E := E)]

/-- Convergence in a quasi-normed group is exactly convergence-to-zero of the norm of the
difference — the direct analogue of the same fact for genuine normed groups, needing only the
bundled `nhds_zero_hasBasis` (not the quasi-triangle inequality itself). -/
theorem tendsto_iff_norm_sub_tendsto_zero {ι : Type*} {l : Filter ι} {u : ι → E} {x : E} :
    Filter.Tendsto u l (nhds x) ↔ Filter.Tendsto (fun n => ‖u n - x‖) l (nhds 0) := by
  rw [← tendsto_sub_nhds_zero_iff, (nhds_zero_hasBasis (E := E)).tendsto_right_iff]
  constructor
  · intro h
    rw [tendsto_order]
    exact ⟨fun b hb => .of_forall fun n => hb.trans_le (norm_nonneg _), fun b hb => h b hb⟩
  · intro h ε hε
    exact (tendsto_order.mp h).2 ε hε

/-- Every quasi-normed group is first countable: the bundled `nhds_zero_hasBasis` gives a
neighborhood basis of `0` indexed by `ε ∈ (0,∞)`, which reindexes to a genuine `ℕ`-indexed basis
via the Archimedean cofinal sequence `1/(n+1)` — exactly the trick `PseudoEMetricSpace` uses for
its own `IsCountablyGenerated (𝓤 α)` instance (`EMetric.instIsCountablyGeneratedUniformity`). No
Aoki–Rolewicz theorem is needed here: that theorem gives something far stronger (an *equivalent
p-homogeneous norm*) than the mere countability of a neighborhood basis this only needs. -/
instance (priority := 100) instFirstCountableTopology : FirstCountableTopology E := by
  have hb : (nhds (0 : E)).HasBasis (fun _ : ℕ => True)
      (fun n => {x : E | ‖x‖ < 1 / (n + 1 : ℝ)}) :=
    (nhds_zero_hasBasis (E := E)).to_hasBasis
      (fun ε hε => (exists_nat_one_div_lt hε).imp fun n hn => ⟨trivial, fun x hx => hx.trans hn⟩)
      (fun n _ => ⟨1 / (n + 1 : ℝ), by positivity, subset_rfl⟩)
  have h1 : (nhds (0 : E)).IsCountablyGenerated := hb.isCountablyGenerated
  have h2 : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

/-- Every genuine `NormedAddCommGroup` is quasi-normed with constant `1`, reusing its *own*
underlying `Norm`, topology, and uniform structure verbatim — no diamond, nothing recomputed via
`AddGroupFilterBasis.ofQuasiNorm`. -/
instance (priority := 100) _root_.NormedAddCommGroup.toQuasinormedAddCommGroup
    {F : Type*} [NormedAddCommGroup F] : QuasinormedAddCommGroup F :=
  { ‹NormedAddCommGroup F› with
    quasiTriangleConst := 1
    one_le_quasiTriangleConst := le_refl 1
    norm_add_le := fun a b => by simpa using _root_.norm_add_le a b
    norm_neg := _root_.norm_neg
    norm_eq_zero_iff := fun a => norm_eq_zero
    toUniformSpace := inferInstance
    toIsTopologicalAddGroup := inferInstance
    toIsUniformAddGroup := inferInstance
    nhds_zero_hasBasis := by
      refine Filter.hasBasis_iff.mpr fun s => ?_
      rw [Metric.mem_nhds_iff]
      refine exists_congr fun ε => and_congr_right fun _ => Iff.of_eq (congrArg (· ⊆ s) ?_)
      ext x
      simp [Metric.mem_ball, dist_zero_right] }

/-- The product of two quasi-normed groups, via the (already-existing, from `Norm`-alone)
`Prod` max norm; the triangle constant is the max of the two factors' constants. The topology and
uniform structure are `E`'s and `F`'s own (via `Prod.instUniformSpace`/`Prod.instIsUniformGroup`),
*not* a fresh one recomputed from the max-quasi-norm — see the module docstring's diamond note. -/
instance instProd {F : Type*} [QuasinormedAddCommGroup F] :
    QuasinormedAddCommGroup (E × F) :=
  { (inferInstance : Norm (E × F)), (inferInstance : AddCommGroup (E × F)) with
    quasiTriangleConst := max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F))
    one_le_quasiTriangleConst := le_max_of_le_left one_le_quasiTriangleConst
    norm_add_le := fun p q => by
      have hp1 : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
      have hp2 : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
      have hq1 : ‖q.1‖ ≤ ‖q‖ := le_max_left _ _
      have hq2 : ‖q.2‖ ≤ ‖q‖ := le_max_right _ _
      have hCmax_nonneg : (0 : ℝ) ≤
          max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) :=
        zero_le_one.trans (le_max_of_le_left one_le_quasiTriangleConst)
      have h1 : ‖p.1 + q.1‖ ≤
          max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) * (‖p‖ + ‖q‖) := by
        calc ‖p.1 + q.1‖ ≤ quasiTriangleConst (E := E) * (‖p.1‖ + ‖q.1‖) := norm_add_le p.1 q.1
          _ ≤ max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) *
                (‖p.1‖ + ‖q.1‖) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (add_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) * (‖p‖ + ‖q‖) :=
              mul_le_mul_of_nonneg_left (add_le_add hp1 hq1) hCmax_nonneg
      have h2 : ‖p.2 + q.2‖ ≤
          max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) * (‖p‖ + ‖q‖) := by
        calc ‖p.2 + q.2‖ ≤ quasiTriangleConst (E := F) * (‖p.2‖ + ‖q.2‖) := norm_add_le p.2 q.2
          _ ≤ max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) *
                (‖p.2‖ + ‖q.2‖) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _)
                (add_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ max (quasiTriangleConst (E := E)) (quasiTriangleConst (E := F)) * (‖p‖ + ‖q‖) :=
              mul_le_mul_of_nonneg_left (add_le_add hp2 hq2) hCmax_nonneg
      rw [Prod.norm_def, Prod.fst_add, Prod.snd_add]
      exact max_le h1 h2
    norm_neg := fun p => by
      rw [Prod.norm_def, Prod.norm_def, Prod.fst_neg, Prod.snd_neg, norm_neg, norm_neg]
    norm_eq_zero_iff := fun p => by
      rw [Prod.norm_def]
      constructor
      · intro h
        have h1 : ‖p.1‖ = 0 :=
          le_antisymm (by rw [← h]; exact le_max_left _ _) (norm_nonneg p.1)
        have h2 : ‖p.2‖ = 0 :=
          le_antisymm (by rw [← h]; exact le_max_right _ _) (norm_nonneg p.2)
        exact Prod.ext ((norm_eq_zero_iff p.1).mp h1) ((norm_eq_zero_iff p.2).mp h2)
      · rintro rfl
        simp
    toUniformSpace := inferInstance
    toIsTopologicalAddGroup := inferInstance
    toIsUniformAddGroup := inferInstance
    nhds_zero_hasBasis := by
      rw [show (0 : E × F) = (0, 0) from rfl, nhds_prod_eq]
      have h := (nhds_zero_hasBasis (E := E)).prod_same_index_mono (nhds_zero_hasBasis (E := F))
        (fun _ _ _ _ hij _ hx => hx.trans_le hij) (fun _ _ _ _ hij _ hx => hx.trans_le hij)
      have hset : ∀ ε : ℝ, {x : E | ‖x‖ < ε} ×ˢ {y : F | ‖y‖ < ε} = {p : E × F | ‖p‖ < ε} := by
        intro ε
        ext p
        simp [Set.mem_prod, Prod.norm_def, max_lt_iff]
      simpa only [hset] using h }

-- `f ≲ g` : `‖f x‖` is bounded by a constant multiple of `‖g x‖`, for *all* `x`.
set_option quotPrecheck false in
scoped notation:50 f " ≲ " g => ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * ‖g x‖

-- `f ∼ g` : the two-sided version of `≲` — `‖f x‖` and `‖g x‖` are each bounded by a constant
-- multiple of the other, for *all* `x`. Deliberately *not* the same relation as Mathlib's own
-- bracketed `f ~[l] g` notation for `Asymptotics.IsEquivalent`
-- (`Analysis/Asymptotics/AsymptoticEquivalent.lean`) — that one means genuine asymptotic equality
-- (`f - g = o(g)`), strictly stronger than "same order of magnitude". No token-level clash (that
-- notation always carries the `[l]`), but worth flagging the difference in meaning explicitly
-- since the glyph is shared.
set_option quotPrecheck false in
scoped notation:50 f " ∼ " g =>
  (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * ‖g x‖) ∧ (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C * ‖f x‖)

/-- A bounded additive map between quasi-normed groups is continuous. -/
theorem continuous_of_bound {F : Type*} [QuasinormedAddCommGroup F] (f : E →+ F) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : Continuous f := by
  refine continuous_of_tendsto_nhds_zero f ?_
  rw [(nhds_zero_hasBasis (E := E)).tendsto_iff (nhds_zero_hasBasis (E := F))]
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  refine ⟨ε / (|C| + 1), div_pos hε hC, fun x (hx : ‖x‖ < ε / (|C| + 1)) => ?_⟩
  show ‖f x‖ < ε
  calc ‖f x‖ ≤ C * ‖x‖ := h x
    _ ≤ (|C| + 1) * ‖x‖ := by nlinarith [le_abs_self C, norm_nonneg x]
    _ < (|C| + 1) * (ε / (|C| + 1)) := by gcongr
    _ = ε := by field_simp

end QuasinormedAddCommGroup

/-- A `QuasinormedAddCommGroup` that is also a module over `𝕜`, compatibly with the quasi-norm:
`‖c • x‖ ≤ ‖c‖ * ‖x‖` — exactly the axiom `NormedSpace` uses (`NormedSpace.norm_smul_le`), from
which equality follows as a theorem (`norm_smul` below), the same way `NormedSpace` derives it:
apply the bound to both `c` and (for `c ≠ 0`) `c⁻¹ • (c • x)`.

Mirrors `NormedSpace`, not `NormedAddCommGroup`, deliberately: `QuasinormedAddCommGroup` itself
has no scalar field, exactly like `NormedAddCommGroup`. This axiom is what actually lets scalar
multiplication be continuous (`QuasiNormedSpace.continuousSMul` below) — without it, `‖c • x‖`
has no relationship at all to `‖c‖`/`‖x‖`, and there would be no way to derive continuity of `•`
from the quasi-norm. Threading `[Module 𝕜 A] [ContinuousSMul 𝕜 A]` as two independent, unrelated
hypotheses (as earlier versions of this project did) forces `ContinuousSMul` to be re-derived
through generic, ambient-topology-dependent routes (e.g. `SMulMemClass.continuousSMul` for a
submodule) every time a new quasi-normed type is built, which then has to coincide with this
class's own *bundled* topology — a real diamond, caught when it silently failed for a submodule
of an interpolation couple's legs. Deriving `ContinuousSMul` directly from `norm_smul_le` plus
`nhds_zero_hasBasis` (both already tied to *this* class's own bundled topology) sidesteps that
entirely, the same way `NormedSpace.toIsBoundedSMul`/`IsBoundedSMul.continuousSMul` sidestep it
for genuine normed spaces (there, via `dist` instead of norm-balls, since a metric is available). -/
class QuasiNormedSpace (𝕜 E : Type*) [NormedField 𝕜] [QuasinormedAddCommGroup E] extends
    Module 𝕜 E where
  norm_smul_le : ∀ (c : 𝕜) (x : E), ‖c • x‖ ≤ ‖c‖ * ‖x‖

namespace QuasiNormedSpace

variable {𝕜 E : Type*} [NormedField 𝕜] [QuasinormedAddCommGroup E] [QuasiNormedSpace 𝕜 E]

/-- The quasi-norm homogeneity is actually exact, exactly as for `NormedSpace`: the reverse
inequality follows by applying `norm_smul_le` to `c⁻¹ • (c • x)` and using that `𝕜` is a field
(so `c ≠ 0` is invertible). -/
theorem norm_smul (c : 𝕜) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine le_antisymm (norm_smul_le c x) ?_
    calc ‖c‖ * ‖x‖ = ‖c‖ * ‖c⁻¹ • c • x‖ := by rw [inv_smul_smul₀ hc]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • x‖) := by gcongr; exact norm_smul_le c⁻¹ (c • x)
      _ = ‖c • x‖ := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (mt norm_eq_zero.1 hc), one_mul]

/-- Scalar multiplication is continuous, derived directly from `norm_smul_le` and the bundled
`nhds_zero_hasBasis` — no metric/`dist` needed (unlike `IsBoundedSMul.continuousSMul`, which
this otherwise mirrors): continuity at an arbitrary `(c₀, x₀)` reduces, via the identity
`c • x - c₀ • x₀ = c₀ • (x - x₀) + (c - c₀) • x₀ + (c - c₀) • (x - x₀)`, to a direct ε-δ bound
using the quasi-triangle inequality (applied twice, for the three-term sum) and `norm_smul_le`
(applied to each term). -/
theorem continuousAt_smul (c₀ : 𝕜) (x₀ : E) :
    ContinuousAt (fun p : 𝕜 × E => p.1 • p.2) (c₀, x₀) := by
  rw [ContinuousAt, nhds_prod_eq]
  have hb1 : (nhds c₀).HasBasis (0 < ·) (fun δ : ℝ => Metric.ball c₀ δ) := Metric.nhds_basis_ball
  have hb2 : (nhds x₀).HasBasis (0 < ·) (fun δ : ℝ => {x : E | ‖x - x₀‖ < δ}) := by
    have h1 := (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).map (x₀ + ·)
    rw [map_add_left_nhds_zero x₀] at h1
    have himg : ∀ δ : ℝ, (x₀ + ·) '' {y : E | ‖y‖ < δ} = {x : E | ‖x - x₀‖ < δ} := by
      intro δ; ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hx; exact ⟨x - x₀, by simpa using hx, by abel_nf⟩
    simpa only [himg] using h1
  have htarget : (nhds (c₀ • x₀)).HasBasis (0 < ·) (fun ε : ℝ => {z : E | ‖z - c₀ • x₀‖ < ε}) := by
    have h1 := (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).map (c₀ • x₀ + ·)
    rw [map_add_left_nhds_zero (c₀ • x₀)] at h1
    have himg : ∀ ε : ℝ, (c₀ • x₀ + ·) '' {y : E | ‖y‖ < ε} = {z : E | ‖z - c₀ • x₀‖ < ε} := by
      intro ε; ext z
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hz; exact ⟨z - c₀ • x₀, by simpa using hz, by abel_nf⟩
    simpa only [himg] using h1
  rw [(hb1.prod hb2).tendsto_iff htarget]
  intro ε hε
  have hK1 : 1 ≤ QuasinormedAddCommGroup.quasiTriangleConst (E := E) :=
    QuasinormedAddCommGroup.one_le_quasiTriangleConst (E := E)
  set K := QuasinormedAddCommGroup.quasiTriangleConst (E := E) with hKdef
  have hKpos : 0 < K := by linarith
  have hc0 : 0 ≤ ‖c₀‖ := norm_nonneg c₀
  have hx0 : 0 ≤ ‖x₀‖ := QuasinormedAddCommGroup.norm_nonneg x₀
  set M : ℝ := K ^ 2 * (‖c₀‖ + ‖x₀‖) + K + 1 with hMdef
  have hMpos : 0 < M := by
    have : 0 ≤ K ^ 2 * (‖c₀‖ + ‖x₀‖) := mul_nonneg (sq_nonneg K) (add_nonneg hc0 hx0)
    rw [hMdef]; linarith
  have hε2M : 0 < ε / (2 * M) := div_pos hε (by linarith)
  refine ⟨(min 1 (ε / (2 * M)), min 1 (ε / (2 * M))),
    ⟨lt_min one_pos hε2M, lt_min one_pos hε2M⟩, ?_⟩
  rintro ⟨c, x⟩ ⟨hc, hx⟩
  simp only [Metric.mem_ball, dist_eq_norm] at hc
  simp only [Set.mem_ofPred_eq] at hx
  change ‖c • x - c₀ • x₀‖ < ε
  set δ := min 1 (ε / (2 * M)) with hδdef
  set dc := c - c₀ with hdc
  set dx := x - x₀ with hdx
  have hcx : c • x - c₀ • x₀ = c₀ • dx + dc • x₀ + dc • dx := by
    simp only [hdc, hdx, smul_sub, sub_smul]
    abel_nf
  rw [hcx]
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * M) := min_le_right _ _
  have hδpos : 0 < δ := lt_min one_pos hε2M
  have hdcpos : 0 ≤ ‖dc‖ := QuasinormedAddCommGroup.norm_nonneg _
  have hdxpos : 0 ≤ ‖dx‖ := QuasinormedAddCommGroup.norm_nonneg _
  have hltdc : ‖dc‖ < δ := hc
  have hltdx : ‖dx‖ < δ := hx
  have tb1 : ‖c₀ • dx‖ ≤ ‖c₀‖ * δ :=
    (norm_smul_le c₀ dx).trans (mul_le_mul_of_nonneg_left hltdx.le hc0)
  have tb2 : ‖dc • x₀‖ ≤ δ * ‖x₀‖ :=
    (norm_smul_le dc x₀).trans (mul_le_mul_of_nonneg_right hltdc.le hx0)
  have tb3 : ‖dc • dx‖ ≤ δ := by
    have hb : ‖dc • dx‖ ≤ δ * δ :=
      (norm_smul_le dc dx).trans (mul_le_mul hltdc.le hltdx.le hdxpos (by linarith))
    calc ‖dc • dx‖ ≤ δ * δ := hb
      _ ≤ δ * 1 := by gcongr
      _ = δ := mul_one δ
  have htri : ‖c₀ • dx + dc • x₀ + dc • dx‖ ≤
      K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) := by
    calc ‖c₀ • dx + dc • x₀ + dc • dx‖
        ≤ K * (‖c₀ • dx + dc • x₀‖ + ‖dc • dx‖) := QuasinormedAddCommGroup.norm_add_le _ _
      _ ≤ K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) := by
          gcongr
          exact QuasinormedAddCommGroup.norm_add_le _ _
  have hfinal : K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) ≤ δ * M := by
    have step1 : ‖c₀ • dx‖ + ‖dc • x₀‖ ≤ ‖c₀‖ * δ + δ * ‖x₀‖ := by linarith
    have step2 : K * (‖c₀ • dx‖ + ‖dc • x₀‖) ≤ K * (‖c₀‖ * δ + δ * ‖x₀‖) :=
      mul_le_mul_of_nonneg_left step1 hKpos.le
    have step3 : K * (‖c₀‖ * δ + δ * ‖x₀‖) + ‖dc • dx‖ ≤ K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ := by
      linarith
    have step4 : K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) ≤
        K * (K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ) := by
      have : K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖ ≤ K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ := by
        linarith
      exact mul_le_mul_of_nonneg_left this hKpos.le
    have step5 : K * (K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ) = δ * (M - 1) := by rw [hMdef]; ring
    rw [step5] at step4
    have step6 : δ * (M - 1) ≤ δ * M := by nlinarith
    linarith
  have hδM : δ * M ≤ ε / 2 := by
    calc δ * M ≤ (ε / (2 * M)) * M := mul_le_mul_of_nonneg_right hδ2 hMpos.le
      _ = ε / 2 := by field_simp
  linarith

instance (priority := 100) continuousSMul : ContinuousSMul 𝕜 E where
  continuous_smul := continuous_iff_continuousAt.mpr fun p => continuousAt_smul p.1 p.2

/-- Every `NormedSpace` is a `QuasiNormedSpace` (over the corresponding `NormedAddCommGroup`
bridge instance), with the *same* `norm_smul_le` bound and `Module` structure reused verbatim. -/
instance (priority := 100) _root_.NormedSpace.toQuasiNormedSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] : QuasiNormedSpace 𝕜 F :=
  { ‹NormedSpace 𝕜 F› with norm_smul_le := NormedSpace.norm_smul_le }

/-- The product of two `QuasiNormedSpace`s, via the (already-existing) `Prod` module structure
and max quasi-norm. -/
instance instProd {F : Type*} [QuasinormedAddCommGroup F] [QuasiNormedSpace 𝕜 F] :
    QuasiNormedSpace 𝕜 (E × F) where
  norm_smul_le c p := by
    rw [Prod.norm_def, Prod.norm_def]
    simp only [Prod.smul_fst, Prod.smul_snd]
    rw [norm_smul c p.1, norm_smul c p.2]
    exact (mul_max_of_nonneg _ _ (norm_nonneg c)).ge

end QuasiNormedSpace

namespace QuasinormedAddCommGroup

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [QuasinormedAddCommGroup E] [QuasiNormedSpace 𝕜 E]
  [QuasinormedAddCommGroup F] [QuasiNormedSpace 𝕜 F]

/-- Rescale `x` by a power of `c` (any element of norm `> 1`) to land in the "shell"
`[ε/‖c‖, ε)`, tracking the exact scalar used — the zpow-indexed form `rescale_to_shell` is stated
against. Ports `Seminorm.rescale_to_shell_zpow` (`Analysis/Normed/Module/Seminorm/Basic.lean`)
verbatim: that lemma's proof only ever uses the *exact* homogeneity `p (c • x) = ‖c‖ * p x`, never
the triangle inequality, so it transfers unchanged to our quasi-norm via
`QuasiNormedSpace.norm_smul` (also exact, proved from the `≤` axiom). -/
theorem rescale_to_shell_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ}
    (εpos : 0 < ε) {x : E} (hx : ‖x‖ ≠ 0) : ∃ n : ℤ, c ^ n ≠ 0 ∧
    ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧ (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) := by
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (QuasinormedAddCommGroup.norm_nonneg x) (Ne.symm hx)
  have xεpos : 0 < ‖x‖ / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  · show ‖(c ^ (-(n + 1))) • x‖ < ε
    rw [QuasiNormedSpace.norm_smul, zpow_neg, norm_inv, ← div_eq_inv_mul, div_lt_iff₀ cnpos,
      mul_comm, norm_zpow]
    exact (div_lt_iff₀ εpos).1 hn.2
  · show ε / ‖c‖ ≤ ‖(c ^ (-(n + 1))) • x‖
    rw [zpow_neg, div_le_iff₀ cpos, QuasiNormedSpace.norm_smul, norm_inv, norm_zpow,
      zpow_add₀ (ne_of_gt cpos), zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt cpos), one_mul, ← div_eq_inv_mul, le_div_iff₀ (zpow_pos cpos _),
      mul_comm]
    exact (le_div_iff₀ εpos).1 hn.1
  · show ‖(c ^ (-(n + 1)))‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖
    have hre : ε⁻¹ * ‖c‖ * ‖x‖ = ε⁻¹ * ‖x‖ * ‖c‖ := by ring
    rw [zpow_neg, norm_inv, inv_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos), zpow_one, hre,
      ← div_eq_inv_mul]
    gcongr
    exact hn.1

theorem rescale_to_shell {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : ‖x‖ ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  let ⟨_, hn⟩ := rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

/-- A continuous `𝕜`-linear map between quasi-normed spaces is operator-bounded — the fact that
makes `opQuasiNorm` below a genuine bound rather than a possibly-vacuous infimum. Ports
`SemilinearMapClass.bound_of_continuous`'s shell argument: continuity at `0` gives a ball on which
`f` is bounded by `1`, then `rescale_to_shell` moves an arbitrary `x` into that ball and rescales
the bound back. -/
theorem exists_forall_norm_map_le_mul_norm (f : E →L[𝕜] F) :
    ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ := by
  have hf0 : Filter.Tendsto f (nhds 0) (nhds 0) := map_zero f ▸ f.continuous.tendsto 0
  obtain ⟨ε, εpos, hε⟩ := (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).mem_iff.mp
    (hf0 ((QuasinormedAddCommGroup.nhds_zero_hasBasis (E := F)).mem_iff.mpr
      ⟨1, one_pos, subset_rfl⟩))
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcpos : 0 < ‖c‖ := by positivity
  refine ⟨‖c‖ / ε, by positivity, fun x => ?_⟩
  by_cases hx : ‖x‖ = 0
  · have hx0 : x = 0 := (QuasinormedAddCommGroup.norm_eq_zero_iff x).mp hx
    simp [hx0]
  · obtain ⟨d, hd, hdx1, -, hdinv⟩ := rescale_to_shell hc εpos hx
    have hfd : ‖f (d • x)‖ < 1 := hε hdx1
    rw [map_smul, QuasiNormedSpace.norm_smul] at hfd
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
    have hlt : ‖f x‖ < ‖d‖⁻¹ := by
      rw [← one_div, lt_div_iff₀ hdpos]
      rwa [mul_comm] at hfd
    have hthis := hlt.le.trans hdinv
    have heq : ε⁻¹ * ‖c‖ * ‖x‖ = ‖c‖ / ε * ‖x‖ := by ring
    rwa [heq] at hthis

/-- The operator quasi-norm of a continuous linear map between quasi-normed spaces —
`sInf {C ≥ 0 | ∀ x, ‖f x‖ ≤ C * ‖x‖}`, the natural substitute for Mathlib's own operator norm
(`ContinuousLinearMap.opNorm`), which needs genuine `SeminormedAddCommGroup` on both ends and so
isn't available once a leg is only `QuasinormedAddCommGroup`. -/
noncomputable def opQuasiNorm (f : E →L[𝕜] F) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖}

theorem opQuasiNorm_nonempty (f : E →L[𝕜] F) :
    {C : ℝ | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖}.Nonempty :=
  let ⟨C, hC, hCf⟩ := exists_forall_norm_map_le_mul_norm f; ⟨C, hC.le, hCf⟩

theorem opQuasiNorm_nonneg (f : E →L[𝕜] F) : 0 ≤ opQuasiNorm f :=
  le_csInf (opQuasiNorm_nonempty f) (fun _ hC => hC.1)

/-- The defining property of `opQuasiNorm`: it is an actual upper bound, not just an infimum of
candidate bounds. Proved via the standard ε-approximation of an infimum
(`Real.lt_sInf_add_pos`), using `ε / (‖x‖ + 1)` (rather than `ε / ‖x‖`) as the slack so the same
argument covers `x = 0` without a separate case split on `‖x‖`. -/
theorem le_opQuasiNorm (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ opQuasiNorm f * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hxpos : (0 : ℝ) < ‖x‖ + 1 := by
    have := QuasinormedAddCommGroup.norm_nonneg x; linarith
  obtain ⟨C, hCmem, hClt⟩ := Real.lt_sInf_add_pos (opQuasiNorm_nonempty f) (div_pos hε hxpos)
  have hbound : ‖f x‖ ≤ C * ‖x‖ := hCmem.2 x
  have hCx : C * ‖x‖ < (opQuasiNorm f + ε / (‖x‖ + 1)) * ‖x‖ ∨ ‖x‖ = 0 := by
    rcases eq_or_lt_of_le (QuasinormedAddCommGroup.norm_nonneg x) with h | h
    · right; exact h.symm
    · left; exact mul_lt_mul_of_pos_right hClt h
  rcases hCx with hCx | hx0
  · have hεx : (opQuasiNorm f + ε / (‖x‖ + 1)) * ‖x‖ ≤ opQuasiNorm f * ‖x‖ + ε := by
      have : ε / (‖x‖ + 1) * ‖x‖ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
        nlinarith [QuasinormedAddCommGroup.norm_nonneg x]
      nlinarith
    linarith [hbound, hCx]
  · rw [hx0] at hbound ⊢
    simp only [mul_zero] at hbound ⊢
    linarith

end QuasinormedAddCommGroup
