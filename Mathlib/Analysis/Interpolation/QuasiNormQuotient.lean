/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.QuasiNorm
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Quotients of quasi-normed groups

DRAFT — under review, statement-design stage (Unit 1 of the quasi-Banach generalization of the
interpolation-couple framework; see `PROGRESS-interpolation-theory.md`).

Generalizes `Mathlib/Analysis/Normed/Group/Quotient.lean`'s quotient-norm/completeness
construction from genuine norms to `QuasinormedAddCommGroup`. Two differences from Mathlib's own
file, both consequences of the quasi-triangle inequality only being exact up to a constant:

* **Completeness** comes from the *purely topological* fact `QuotientAddGroup.completeSpace_right`
  (unprimed — see `quotientNorm_completeSpace`'s own docstring for why the primed version doesn't
  work here) — the quotient of a complete first-countable topological group by *any* subgroup is
  complete (Bourbaki, *General Topology* IX.3.1 Prop. 4; no closedness needed, matching what
  `Couple.lean` already relies on for `A₀+A₁`) — rather than anything norm-specific. Genuinely new
  hypothesis versus the genuinely-normed case: `[FirstCountableTopology E]` — free for a
  `NormedAddCommGroup` (metrizable), but a real additional assumption in general. Mild in practice
  (every space we actually plan to feed this — `Lᵖ`, Lorentz spaces — is metrizable).
* **Norm-separation of the quotient** (`‖x‖ = 0 → x = 0`) needs the subgroup quotiented by to be
  "closed" in *some* sense. Mathlib gets this for free from topological closedness, because its
  norm generates its topology — and now that `QuasinormedAddCommGroup` bundles its own topology
  too (`QuasiNorm.lean`), so do we: `AddSubgroup.isNormClosed_of_isClosed` bridges ordinary
  topological closedness (which is all `Couple.lean` ever proves, via `T2Space` + continuity) to
  the purely algebraic `AddSubgroup.IsNormClosed` below, using the norm/topology compatibility
  `QuasinormedAddCommGroup.nhds_zero_hasBasis` already bundles.

No attempt at a `QuasiSeminormedAddCommGroup` intermediate stage (Mathlib's file builds an
unconditional seminorm first, then upgrades to a genuine norm given closedness) — skipped
deliberately since every consumer in this project already establishes closedness before
quotienting, so there is no use for the seminorm-only case yet.
-/

open scoped Topology

namespace AddSubgroup

variable {E : Type*} [QuasinormedAddCommGroup E]

/-- A subgroup is *norm-closed*: it contains every norm-limit of its own points. The purely
algebraic characterization of closedness, phrased directly in terms of the norm rather than the
(now bundled, but still worth stating this way for the proof below) topology. -/
def IsNormClosed (N : AddSubgroup E) : Prop :=
  ∀ x : E, (∀ ε : ℝ, 0 < ε → ∃ n ∈ N, ‖x - n‖ < ε) → x ∈ N

end AddSubgroup

namespace QuasinormedAddCommGroup

variable {E : Type*} [QuasinormedAddCommGroup E]

/-- Topological closedness bridges to `IsNormClosed`, using the norm/topology compatibility
`nhds_zero_hasBasis` that `QuasinormedAddCommGroup` already bundles — this is what lets
`Couple.lean`'s purely topological closedness argument (`T2Space` + continuity) feed the
norm-quotient machinery below. -/
theorem _root_.AddSubgroup.isNormClosed_of_isClosed (N : AddSubgroup E)
    (hN : IsClosed (N : Set E)) : N.IsNormClosed := by
  intro x hx
  have hbasis : (𝓝 x).HasBasis (0 < ·) fun ε : ℝ => {z : E | ‖z - x‖ < ε} := by
    have h1 := (nhds_zero_hasBasis (E := E)).map (x + ·)
    rw [map_add_left_nhds_zero x] at h1
    have himg : ∀ ε : ℝ, (x + ·) '' {y : E | ‖y‖ < ε} = {z : E | ‖z - x‖ < ε} := by
      intro ε
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hz
        exact ⟨z - x, by simpa using hz, by abel_nf⟩
    simpa only [himg] using h1
  rw [← SetLike.mem_coe, ← hN.closure_eq, mem_closure_iff_nhds_basis hbasis]
  intro ε hε
  obtain ⟨n, hn, hn'⟩ := hx ε hε
  refine ⟨n, hn, ?_⟩
  change ‖n - x‖ < ε
  rw [← neg_sub x n, norm_neg]
  exact hn'

open QuotientAddGroup

variable {E : Type*} [QuasinormedAddCommGroup E] (N : AddSubgroup E)

theorem quotientNorm_set_nonempty (x : E ⧸ N) : {y : E | (y : E ⧸ N) = x}.Nonempty :=
  QuotientAddGroup.mk_surjective x

theorem quotientNorm_set_boundedBelow (x : E ⧸ N) :
    BddBelow ((‖·‖) '' {y : E | (y : E ⧸ N) = x}) :=
  ⟨0, by rintro r ⟨y, -, rfl⟩; exact norm_nonneg y⟩

/-- The quotient quasi-norm: the infimum of `‖y‖` over representatives `y` of the coset `x`. -/
noncomputable def quotientNorm (x : E ⧸ N) : ℝ :=
  sInf ((‖·‖) '' {y : E | (y : E ⧸ N) = x})

theorem quotientNorm_nonneg (x : E ⧸ N) : 0 ≤ quotientNorm N x :=
  le_csInf ((quotientNorm_set_nonempty N x).image _) (by rintro r ⟨y, -, rfl⟩; exact norm_nonneg y)

theorem quotientNorm_mk_le (x : E) : quotientNorm N (x : E ⧸ N) ≤ ‖x‖ :=
  csInf_le (quotientNorm_set_boundedBelow N _) ⟨x, rfl, rfl⟩

theorem exists_norm_lt_quotientNorm_add {x : E ⧸ N} {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, (y : E ⧸ N) = x ∧ ‖y‖ < quotientNorm N x + ε := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hle : quotientNorm N x + ε ≤ quotientNorm N x :=
    le_csInf ((quotientNorm_set_nonempty N x).image _) (by rintro r ⟨y, hy, rfl⟩; exact h y hy)
  linarith

theorem quotientNorm_add_le (a b : E ⧸ N) :
    quotientNorm N (a + b) ≤
      quasiTriangleConst (E := E) * (quotientNorm N a + quotientNorm N b) := by
  have hCpos : (0 : ℝ) < quasiTriangleConst (E := E) := quasiTriangleConst_pos
  have hC : (0 : ℝ) < 2 * quasiTriangleConst (E := E) := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hx'⟩ := exists_norm_lt_quotientNorm_add N (x := a) (div_pos hε hC)
  obtain ⟨y, hy, hy'⟩ := exists_norm_lt_quotientNorm_add N (x := b) (div_pos hε hC)
  have hxy : ((x + y : E) : E ⧸ N) = a + b := by rw [← hx, ← hy]; rfl
  have hsum : ‖x‖ + ‖y‖ ≤
      quotientNorm N a + quotientNorm N b + 2 * (ε / (2 * quasiTriangleConst (E := E))) := by
    linarith
  calc quotientNorm N (a + b) ≤ ‖x + y‖ := hxy ▸ quotientNorm_mk_le N (x + y)
    _ ≤ quasiTriangleConst (E := E) * (‖x‖ + ‖y‖) := norm_add_le x y
    _ ≤ quasiTriangleConst (E := E) *
          (quotientNorm N a + quotientNorm N b + 2 * (ε / (2 * quasiTriangleConst (E := E)))) :=
        mul_le_mul_of_nonneg_left hsum hCpos.le
    _ = quasiTriangleConst (E := E) * (quotientNorm N a + quotientNorm N b) + ε := by
        field_simp

theorem quotientNorm_neg (a : E ⧸ N) : quotientNorm N (-a) = quotientNorm N a := by
  unfold quotientNorm
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-y, ?_, norm_neg y⟩
    have : ((-y : E) : E ⧸ N) = -(y : E ⧸ N) := by simp
    rw [this, hy, neg_neg]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-y, ?_, norm_neg y⟩
    have : ((-y : E) : E ⧸ N) = -(y : E ⧸ N) := by simp
    rw [this, hy]

theorem quotientNorm_mk_eq_zero_iff (hN : N.IsNormClosed) (x : E) :
    quotientNorm N (x : E ⧸ N) = 0 ↔ x ∈ N := by
  constructor
  · intro h
    refine hN x fun ε hε => ?_
    obtain ⟨y, hy, hy'⟩ := exists_norm_lt_quotientNorm_add N (x := (x : E ⧸ N)) hε
    rw [h, zero_add] at hy'
    have hyx : y - x ∈ N := QuotientAddGroup.eq_iff_sub_mem.mp hy
    exact ⟨x - y, by simpa using N.neg_mem hyx, by rwa [sub_sub_cancel]⟩
  · intro hx
    refine le_antisymm ?_ (quotientNorm_nonneg N _)
    have hx0 : (x : E ⧸ N) = ((0 : E) : E ⧸ N) :=
      QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hx)
    rw [hx0]
    simpa using quotientNorm_mk_le N (0 : E)

theorem quotientNorm_eq_zero_iff (hN : N.IsNormClosed) (a : E ⧸ N) :
    quotientNorm N a = 0 ↔ a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hmem : x ∈ N ↔ (QuotientAddGroup.mk' N) x = 0 := by
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
  rw [quotientNorm_mk_eq_zero_iff N hN x, hmem, QuotientAddGroup.mk'_apply]

/-- Given a norm-closed subgroup `N`, the quotient `E ⧸ N` is quasi-normed, with the *same*
triangle constant as `E`. The topology/uniform structure fields are given *explicitly* (via the
quotient norm's own `AddGroupFilterBasis`) rather than left to the class's defaults: relying on
the defaults here — i.e. omitting these four fields and letting `QuasinormedAddCommGroup`'s own
default expressions kick in — was tried first and silently mis-elaborated (`quasiTriangleConst`
inside the default resolved to the bare, unapplied field *projection* rather than this
`E ⧸ N` instance's own value, apparently because this definition sits inside
`namespace QuasinormedAddCommGroup`, the same namespace the class itself lives in). Supplying
them explicitly sidesteps that entirely and is guaranteed correct. -/
@[instance_reducible]
noncomputable def quotientQuasinormedAddCommGroup (hN : N.IsNormClosed) :
    QuasinormedAddCommGroup (E ⧸ N) :=
  letI : Norm (E ⧸ N) := ⟨quotientNorm N⟩
  let hB := AddGroupFilterBasis.ofQuasiNorm (E := E ⧸ N) (quasiTriangleConst (E := E))
    (one_le_quasiTriangleConst (E := E)) (quotientNorm_add_le N) (quotientNorm_neg N)
    (quotientNorm_eq_zero_iff N hN)
  { norm := quotientNorm N
    quasiTriangleConst := quasiTriangleConst (E := E)
    one_le_quasiTriangleConst := one_le_quasiTriangleConst (E := E)
    norm_add_le := quotientNorm_add_le N
    norm_neg := quotientNorm_neg N
    norm_eq_zero_iff := quotientNorm_eq_zero_iff N hN
    toUniformSpace := hB.uniformSpace
    toIsTopologicalAddGroup := hB.isTopologicalAddGroup
    toIsUniformAddGroup := hB.isUniformAddGroup
    nhds_zero_hasBasis := by
      change (@nhds (E ⧸ N) hB.uniformSpace.toTopologicalSpace 0).HasBasis (0 < ·)
        fun ε : ℝ => {x : E ⧸ N | quotientNorm N x < ε}
      rw [hB.nhds_eq (x₀ := 0), AddGroupFilterBasis.N_zero]
      refine (FilterBasis.hasBasis hB.toFilterBasis).to_hasBasis' ?_ ?_
      · rintro s ⟨ε, hε, rfl⟩
        exact ⟨ε, hε, subset_rfl⟩
      · rintro ε hε
        exact FilterBasis.mem_filter_of_mem _ ⟨ε, hε, rfl⟩ }

/-- Completeness of the quotient, from the purely topological (unprimed)
`QuotientAddGroup.completeSpace_right` (Bourbaki, *General Topology* IX.3.1 Prop. 4) — no
closedness of `N` needed for *this* half (unlike `quotientQuasinormedAddCommGroup`, which does
need `IsNormClosed` for norm-separation). Deliberately the *unprimed* variant, which takes
`E`'s *ambient* `UniformSpace`/`IsUniformAddGroup` instances as given rather than requiring them
`@`-pinned to `IsTopologicalAddGroup.rightUniformSpace` — the primed version was tried first and
turned out to be the wrong choice: for `E = A₀ × A₁` (`Couple.lean`), the natural ambient uniform
space is `Prod`'s own (built from each factor's, via `Prod.instIsUniformGroup`), which is only
*propositionally*, not *definitionally*, equal to `rightUniformSpace (A₀ × A₁)` — the primed
lemma's `@`-pinned hypothesis then simply never matches what's actually available. Any type with
an `IsUniformAddGroup`-tagged ambient uniform space works here directly, `Couple.lean`'s `A₀×A₁`
included; a genuinely `NormedAddCommGroup` leg doesn't need this lemma at all — it already has
`Submodule.Quotient.completeSpace` from Mathlib directly. -/
theorem quotientNorm_completeSpace [UniformSpace E] [IsUniformAddGroup E]
    [FirstCountableTopology E] [CompleteSpace E] :
    @CompleteSpace (E ⧸ N) (IsTopologicalAddGroup.rightUniformSpace (E ⧸ N)) :=
  QuotientAddGroup.completeSpace_right E N

end QuasinormedAddCommGroup
