/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Couple
import Mathlib.Analysis.Interpolation.InterpolationCat
import Mathlib.Analysis.Convex.Function

/-!
# The K-functional

DRAFT — under review.

Triebel §1.3.1: for an interpolation couple `{A₀,A₁}`, `t > 0`, and `a ∈ A₀+A₁`,
`K(t,a) = inf_{a=a₀+a₁} (‖a₀‖ + t‖a₁‖)`. This is the starting point of the K-method (real
interpolation): the spaces `(A₀,A₁)_{θ,q}` (§1.3.2) are defined by prescribing the behavior of
`K(t,a)` as `t → 0` and `t → ∞`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*} [NormedAddCommGroup A₀] [NormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [NormedAddCommGroup A₁] [NormedSpace 𝕜 A₁] [CompleteSpace A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

/-- The K-functional: `K(t,a) = inf_{a = a₀+a₁} (‖a₀‖ + t‖a₁‖)`. -/
noncomputable def InterpolationCouple.KFunctional (t : ℝ) (a : InterpolationCouple.sum ι₀ ι₁) :
    ℝ :=
  sInf {r : ℝ | ∃ a₀ : A₀, ∃ a₁ : A₁,
    (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum ι₀ ι₁) = a ∧ ‖a₀‖ + t * ‖a₁‖ = r}

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_set_nonempty (t : ℝ) (a : InterpolationCouple.sum ι₀ ι₁) :
    {r : ℝ | ∃ a₀ : A₀, ∃ a₁ : A₁,
      (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum ι₀ ι₁) = a ∧
        ‖a₀‖ + t * ‖a₁‖ = r}.Nonempty := by
  obtain ⟨⟨a₀, a₁⟩, ha⟩ := Submodule.Quotient.mk_surjective _ a
  exact ⟨‖a₀‖ + t * ‖a₁‖, a₀, a₁, ha, rfl⟩

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_set_boundedBelow (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    BddBelow {r : ℝ | ∃ a₀ : A₀, ∃ a₁ : A₁,
      (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum ι₀ ι₁) = a ∧
        ‖a₀‖ + t * ‖a₁‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨a₀, a₁, -, rfl⟩
  positivity

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_nonneg (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    0 ≤ InterpolationCouple.KFunctional ι₀ ι₁ t a :=
  le_csInf (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a) (by
    rintro r ⟨a₀, a₁, -, rfl⟩
    positivity)

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K(t,a)` is monotone increasing in `t`, for `t ≥ 0`. -/
theorem InterpolationCouple.kFunctional_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    InterpolationCouple.KFunctional ι₀ ι₁ s a ≤ InterpolationCouple.KFunctional ι₀ ι₁ t a := by
  apply le_csInf (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a)
  rintro r ⟨a₀, a₁, ha, rfl⟩
  have hr' : ‖a₀‖ + s * ‖a₁‖ ∈ {r : ℝ | ∃ a₀' : A₀, ∃ a₁' : A₁,
      (Submodule.Quotient.mk (a₀', a₁') : InterpolationCouple.sum ι₀ ι₁) = a ∧
        ‖a₀'‖ + s * ‖a₁'‖ = r} := ⟨a₀, a₁, ha, rfl⟩
  calc InterpolationCouple.KFunctional ι₀ ι₁ s a
      ≤ ‖a₀‖ + s * ‖a₁‖ :=
        csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ s hs a) hr'
    _ ≤ ‖a₀‖ + t * ‖a₁‖ := by nlinarith [norm_nonneg a₁]

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K(t,a) ≥ min(1,t) ‖a‖`, relating `K` back to the couple's own sum-space norm. -/
theorem InterpolationCouple.min_mul_norm_le_kFunctional (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    min 1 t * ‖a‖ ≤ InterpolationCouple.KFunctional ι₀ ι₁ t a := by
  apply le_csInf (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a)
  rintro r ⟨a₀, a₁, ha, rfl⟩
  have h1 : ‖a‖ ≤ max ‖a₀‖ ‖a₁‖ := by
    rw [← ha]
    exact (Submodule.Quotient.norm_mk_le (InterpolationCouple.plus ι₀ ι₁).ker
      (a₀, a₁)).trans_eq (Prod.norm_def _)
  have h2 : min 1 t * max ‖a₀‖ ‖a₁‖ ≤ ‖a₀‖ + t * ‖a₁‖ := by
    rcases le_total ‖a₀‖ ‖a₁‖ with h | h
    · rw [max_eq_right h]
      nlinarith [min_le_right (1 : ℝ) t, norm_nonneg a₀]
    · rw [max_eq_left h]
      nlinarith [min_le_left (1 : ℝ) t, norm_nonneg a₁]
  calc min 1 t * ‖a‖ ≤ min 1 t * max ‖a₀‖ ‖a₁‖ :=
        mul_le_mul_of_nonneg_left h1 (le_min zero_le_one ht)
    _ ≤ ‖a₀‖ + t * ‖a₁‖ := h2

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K(t,a) ≤ 2 max(1,t) ‖a‖` — the extra factor `2` (compared to Triebel's literal
`max(1,t)‖a‖`) comes from our `sum`'s norm being the *max*-based quotient norm, not Triebel's
literal `inf ‖a₀‖+‖a₁‖` sum-norm; the two are equivalent but not equal (documented in
`Couple.lean`). -/
theorem InterpolationCouple.kFunctional_le_two_mul_max_mul_norm (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    InterpolationCouple.KFunctional ι₀ ι₁ t a ≤ 2 * max 1 t * ‖a‖ := by
  have hmax : (0 : ℝ) < 2 * max 1 t := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hxlt⟩ := Submodule.Quotient.norm_mk_lt a (div_pos hε hmax)
  have hb : InterpolationCouple.KFunctional ι₀ ι₁ t a ≤ ‖x.1‖ + t * ‖x.2‖ :=
    csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht a)
      ⟨x.1, x.2, by simpa using hx, rfl⟩
  have hc : ‖x.1‖ + t * ‖x.2‖ ≤ 2 * max 1 t * ‖x‖ := by
    rw [Prod.norm_def]
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [le_max_right (1 : ℝ) t, le_max_left (1 : ℝ) t, norm_nonneg x.1, norm_nonneg x.2]
    · rw [max_eq_left h]
      nlinarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t, norm_nonneg x.1, norm_nonneg x.2]
  calc InterpolationCouple.KFunctional ι₀ ι₁ t a
      ≤ ‖x.1‖ + t * ‖x.2‖ := hb
    _ ≤ 2 * max 1 t * ‖x‖ := hc
    _ ≤ 2 * max 1 t * (‖a‖ + ε / (2 * max 1 t)) := by
        apply mul_le_mul_of_nonneg_left hxlt.le (by positivity)
    _ = 2 * max 1 t * ‖a‖ + ε := by field_simp

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- Triebel's Lemma (§1.3.1): `K(t,a)` is continuous in `t` (for `t ≥ 0`). STATEMENT ONLY —
proof deferred. -/
theorem InterpolationCouple.kFunctional_continuousOn (a : InterpolationCouple.sum ι₀ ι₁) :
    ContinuousOn (fun t => InterpolationCouple.KFunctional ι₀ ι₁ t a) (Set.Ici 0) := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- Triebel's Lemma (§1.3.1): `K(t,a)` is concave in `t` (for `t ≥ 0`). STATEMENT ONLY — proof
deferred (not needed for the `(A₀,A₁)_{θ,q}` Banach/type-θ theorem specifically; needed later
for reiteration / K-L-method equivalence). -/
theorem InterpolationCouple.kFunctional_concaveOn (a : InterpolationCouple.sum ι₀ ι₁) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t => InterpolationCouple.KFunctional ι₀ ι₁ t a) := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The key transformation/naturality property used to show `(A₀,A₁)_{θ,q}` is an exact
interpolation functor of type `θ` (Triebel §1.3.3 proof, step 4): a morphism `T : C ⟶ D` scales
the K-functional by its operator norms on each leg. STATEMENT ONLY — proof deferred.

CAVEAT: the `‖T.f₀‖ = 0` edge case (division by zero in the second argument) hasn't been
reviewed yet; revisit when actually proving this. -/
theorem InterpolationCat.Hom.kFunctional_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (t : ℝ) (ht : 0 ≤ t) (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
      ‖T.f₀‖ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * ‖T.f₁‖ / ‖T.f₀‖) a := by
  sorry
