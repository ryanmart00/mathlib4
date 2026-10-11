/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.Equivalence

/-!
# Spaces of class `𝒦(θ)`, `𝒥(θ)` and `𝒞(θ)`

Bergh–Löfström Definition 3.5.1 (Triebel §1.10.1): a space `X` between `A₀ ∩ A₁` and `A₀ + A₁`
is of class `𝒦(θ; Ā)` if `K(t, a; Ā) ≤ C t^θ ‖a‖_X` for `a ∈ X`, and of class `𝒥(θ; Ā)` if
`‖a‖_X ≤ C t^{-θ} J(t, a; Ā)` for `a ∈ A₀ ∩ A₁`; of class `𝒞(θ; Ā)` if both. These are the
hypotheses of the reiteration theorem (`RealInterpolation/Reiteration.lean`).

As everywhere in this framework, `X` is located by a continuous linear embedding `κ : X →L[𝕜] 𝒜`
into the ambient space of the couple, and membership in `A₀ + A₁` / `A₀ ∩ A₁` is read through the
injective `sumToAmbient`. So the class conditions also assert `X ⊂ A₀ + A₁` (for `𝒦(θ)`) and
`A₀ ∩ A₁ ⊂ X` (for `𝒥(θ)`).

## Main definitions
* `InterpolationCouple.IsOfClassK θ κ`, `InterpolationCouple.IsOfClassJ θ κ`.

## Main statements
* `isOfClassK_zero_ι₀`, `isOfClassJ_zero_ι₀`, `isOfClassK_one_ι₁`, `isOfClassJ_one_ι₁`: `A₀` is of
  class `𝒞(0; Ā)` and `A₁` of class `𝒞(1; Ā)`.
* `RealInterpolationSpace.isOfClassK`, `RealInterpolationSpace.isOfClassJ`: for `0 < θ < 1`,
  `(A₀, A₁)_{θ,q}` is of class `𝒞(θ; Ā)` (B–L, after Definition 3.5.1, from Theorems 3.1.2 and
  3.2.2 / 3.11.2).
-/

open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
variable {X : Type*} [QuasinormedAddCommGroup X] [QuasiNormedSpace 𝕜 X]

namespace InterpolationCouple

/-- `X` (embedded in the ambient space by `κ`) is of class `𝒦(θ; Ā)` (B–L Definition 3.5.1 (a)):
every `x ∈ X` lies in `A₀ + A₁`, and `K(t, x; Ā) ≤ C t^θ ‖x‖_X` for all `t > 0`. -/
def IsOfClassK (θ : ℝ) (κ : X →L[𝕜] 𝒜) : Prop :=
  ∃ C : ℝ, ∀ x : X, ∃ b : sum ι₀ ι₁, sumToAmbient ι₀ ι₁ b = κ x ∧
    ∀ t : ℝ, 0 < t → KFunctional ι₀ ι₁ t b ≤ C * t ^ θ * ‖x‖

/-- `X` (embedded in the ambient space by `κ`) is of class `𝒥(θ; Ā)` (B–L Definition 3.5.1 (b)):
every `b ∈ A₀ ∩ A₁` lies in `X`, and `‖b‖_X ≤ C t^{-θ} J(t, b; Ā)` for all `t > 0`. -/
def IsOfClassJ (θ : ℝ) (κ : X →L[𝕜] 𝒜) : Prop :=
  ∃ C : ℝ, ∀ b : meet ι₀ ι₁, ∃ x : X, κ x = sumToAmbient ι₀ ι₁ (meetToSum ι₀ ι₁ b) ∧
    ∀ t : ℝ, 0 < t → ‖x‖ ≤ C * t ^ (-θ) * JFunctional ι₀ ι₁ t b

omit [T2Space 𝒜] in
/-- `K(t, b) ≤ ‖a₀‖ + t ‖a₁‖` for any decomposition `b = [(a₀, a₁)]`. -/
private theorem kFunctional_mk_le {t : ℝ} (ht : 0 ≤ t) (a₀ : A₀) (a₁ : A₁) :
    KFunctional ι₀ ι₁ t (Submodule.Quotient.mk (a₀, a₁)) ≤ ‖a₀‖ + t * ‖a₁‖ :=
  csInf_le (kFunctional_set_boundedBelow ι₀ ι₁ t ht _) ⟨a₀, a₁, rfl, rfl⟩

/-- `A₀` is of class `𝒦(0; Ā)` (B–L, after Definition 3.5.1: `K(t, a) ≤ ‖a‖_{A₀}`). -/
theorem isOfClassK_zero_ι₀ : IsOfClassK ι₀ ι₁ 0 ι₀ := by
  refine ⟨1, fun x => ⟨inl₀ ι₀ ι₁ x, sumToAmbient_inl₀ ι₀ ι₁ x, fun t ht => ?_⟩⟩
  rw [Real.rpow_zero, one_mul, one_mul, inl₀_eq_mk]
  simpa using kFunctional_mk_le ι₀ ι₁ ht.le x 0

/-- `A₀` is of class `𝒥(0; Ā)` (`‖b‖_{A₀} ≤ J(t, b)`). -/
theorem isOfClassJ_zero_ι₀ : IsOfClassJ ι₀ ι₁ 0 ι₀ := by
  refine ⟨1, fun b => ⟨(b : A₀ × A₁).1, ?_, fun t ht => ?_⟩⟩
  · obtain ⟨⟨a₀, a₁⟩, hb⟩ := b
    rw [meetToSum_apply, sumToAmbient_inl₀]
  · rw [neg_zero, Real.rpow_zero, one_mul, one_mul]
    exact le_max_left _ _

/-- `A₁` is of class `𝒦(1; Ā)` (`K(t, a) ≤ t ‖a‖_{A₁}`). -/
theorem isOfClassK_one_ι₁ : IsOfClassK ι₀ ι₁ 1 ι₁ := by
  refine ⟨1, fun x => ⟨inl₁ ι₀ ι₁ x, sumToAmbient_inl₁ ι₀ ι₁ x, fun t ht => ?_⟩⟩
  rw [Real.rpow_one, one_mul, inl₁_eq_mk]
  simpa using kFunctional_mk_le ι₀ ι₁ ht.le 0 x

/-- `A₁` is of class `𝒥(1; Ā)` (`‖b‖_{A₁} ≤ t⁻¹ J(t, b)`). -/
theorem isOfClassJ_one_ι₁ : IsOfClassJ ι₀ ι₁ 1 ι₁ :=
  sorry

namespace RealInterpolationSpace

variable [CompleteSpace A₀] [CompleteSpace A₁]
variable (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]

/-- `(A₀, A₁)_{θ,q}` is of class `𝒦(θ; Ā)`: `K(t, a) ≤ C t^θ ‖a‖_{θ,q}` (B–L Theorem 3.1.2 (6) /
3.11.2 (3); here `ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le`). -/
theorem isOfClassK :
    IsOfClassK ι₀ ι₁ θ ((sumToAmbient ι₀ ι₁).comp (RealInterpolationSpace.toSum ι₀ ι₁ θ q)) :=
  sorry

/-- `(A₀, A₁)_{θ,q}` is of class `𝒥(θ; Ā)`: `‖b‖_{θ,q} ≤ C t^{-θ} J(t, b)` for `b ∈ A₀ ∩ A₁`
(B–L Theorem 3.2.2 (6) / 3.11.2 (4); for the K-quasinorm this follows from
`K(s, b) ≤ min(1, s/t) J(t, b)` and the scaling identity, as for Theorem 3.1.2 (6)). -/
theorem isOfClassJ :
    IsOfClassJ ι₀ ι₁ θ ((sumToAmbient ι₀ ι₁).comp (RealInterpolationSpace.toSum ι₀ ι₁ θ q)) :=
  sorry

end RealInterpolationSpace

end InterpolationCouple
