/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Quasi-normed additive groups

## Main definitions

* `QuasinormedAddCommGroup`: like `NormedAddCommGroup`, but the triangle inequality is only
  required up to a fixed multiplicative constant `quasiTriangleConst` — the literature's
  `‖a+b‖ ≲ ‖a‖+‖b‖` — rather than exactly, and bundles its own topology/uniform structure exactly
  the way `NormedAddCommGroup` does (see the design note below). This is what weak-`Lᵖ` (and
  Lorentz spaces generally) actually satisfy, motivating the whole generalization: every genuine
  `NormedAddCommGroup` is an instance with `quasiTriangleConst = 1`
  (`NormedAddCommGroup.toQuasinormedAddCommGroup`), reusing its own topology verbatim, so the
  classical case is recovered exactly, not just up to equivalence.

The module structure (`QuasiNormedSpace`) is in `Mathlib/Analysis/Normed/Quasi/NormedSpace.lean`
and the operator quasi-norm in `Mathlib/Analysis/Normed/Quasi/Operator.lean`. Equivalence of
quasi-Banach spaces (quasinorms comparable up to constants in both directions) is not a separate
notion: it is an isomorphism in `QuasiBanachCat`
(`Mathlib/Analysis/Normed/Quasi/QuasiBanachCat.lean`), i.e. a continuous linear equivalence, since
continuous linear maps between quasi-normed spaces are automatically bounded
(`QuasinormedAddCommGroup.le_opQuasiNorm`).

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
  change ‖f x‖ < ε
  calc ‖f x‖ ≤ C * ‖x‖ := h x
    _ ≤ (|C| + 1) * ‖x‖ := by nlinarith [le_abs_self C, norm_nonneg x]
    _ < (|C| + 1) * (ε / (|C| + 1)) := by gcongr
    _ = ε := by field_simp

end QuasinormedAddCommGroup
