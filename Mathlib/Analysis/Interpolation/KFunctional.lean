/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Couple

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
