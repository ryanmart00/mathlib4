/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.Classes
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JInterpolationFunctor

/-!
# The reiteration theorem

Bergh–Löfström Theorem 3.5.3 (quasi-normed form: Theorem 3.11.5; Triebel §1.10.2): let
`Ā = (A₀, A₁)` and `X̄ = (X₀, X₁)` be couples (in the same ambient space) with `Xᵢ` complete and
of class `𝒞(θᵢ; Ā)`, `0 ≤ θᵢ ≤ 1`, `θ₀ ≠ θ₁`. For `0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`,
`X̄_{η,q} = Ā_{θ,q}` with equivalent quasinorms. In particular
`(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})_{η,q} = Ā_{θ,q}`.

The proof follows B–L.
* `X̄_{η,q} ⊂ Ā_{θ,q}` uses only the `𝒦(θᵢ)` conditions: `K(t, a; Ā) ≤ C t^{θ₀} K(t^{θ₁-θ₀}, a; X̄)`
  and the change of variables `s = t^{θ₁-θ₀}`.
* `Ā_{θ,q} ⊂ X̄_{η,q}` uses only the `𝒥(θᵢ)` conditions: represent `a = ∑ᵥ uᵥ` by the discrete
  J-method for `Ā` (equivalence theorem), estimate `K(2^{μ(θ₁-θ₀)}, a; X̄)` by Aoki–Rolewicz for
  the quasi-norm `K(t, ·; X̄)`, and conclude by the discrete K-method for `X̄` and Young's
  inequality, as in the proof of the equivalence theorem.

Both halves are first stated for the K-method backend, comparing elements of the two sum spaces
with the same image in the ambient space; the bundled form is an isomorphism of quasi-Banach spaces
compatible with the maps to the ambient space.

## Main definitions
* `InterpolationCat.ofEmbeddings A κ₀ κ₁`: the couple `(X₀, X₁)` embedded in the ambient space of
  `A`.
* `InterpolationCat.realInterpolationCouple A θ₀ q₀ θ₁ q₁`: the couple `(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})`.

## Main statements
* `InterpolationCouple.exists_realInterpolationENorm_le_of_isOfClassK`,
  `InterpolationCouple.exists_realInterpolationENorm_le_of_isOfClassJ`: the two inclusions.
* `InterpolationCat.nonempty_iso_realInterpolationFunctor_reiteration`: the reiteration theorem.
* `InterpolationCat.nonempty_iso_realInterpolationFunctor_realInterpolationCouple`:
  `(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})_{η,q} = Ā_{θ,q}`.
-/

universe v u

open CategoryTheory
open scoped ENNReal

namespace InterpolationCouple

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
variable {X₀ X₁ : Type*}
  [QuasinormedAddCommGroup X₀] [QuasiNormedSpace 𝕜 X₀]
  [QuasinormedAddCommGroup X₁] [QuasiNormedSpace 𝕜 X₁]
variable (κ₀ : X₀ →L[𝕜] 𝒜) (κ₁ : X₁ →L[𝕜] 𝒜)

/-- Reiteration, `X̄_{η,q} ⊂ Ā_{θ,q}` (B–L Theorem 3.5.3, first half; 3.11.5): if `Xᵢ` is of class
`𝒦(θᵢ; Ā)` with `θ₀ ≠ θ₁`, and `θ = (1 - η) θ₀ + η θ₁`, then every `a ∈ X₀ + X₁` lies in `A₀ + A₁`
(as the element `b` with the same image in the ambient space) with
`‖b‖_{Ā,θ,q} ≤ C ‖a‖_{X̄,η,q}`. -/
theorem exists_realInterpolationENorm_le_of_isOfClassK {θ₀ θ₁ η θ : ℝ} (hne : θ₀ ≠ θ₁)
    (hθ : θ = (1 - η) * θ₀ + η * θ₁) {q : ℝ≥0∞} (hq : 0 < q)
    (hK₀ : IsOfClassK ι₀ ι₁ θ₀ κ₀) (hK₁ : IsOfClassK ι₀ ι₁ θ₁ κ₁) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum κ₀ κ₁, ∃ b : sum ι₀ ι₁,
      sumToAmbient ι₀ ι₁ b = sumToAmbient κ₀ κ₁ a ∧
        realInterpolationENorm ι₀ ι₁ θ q b ≤ C * realInterpolationENorm κ₀ κ₁ η q a :=
  sorry

/-- Reiteration, `Ā_{θ,q} ⊂ X̄_{η,q}` (B–L Theorem 3.5.3, second half; 3.11.5): if `Xᵢ` is complete
and of class `𝒥(θᵢ; Ā)` with `θᵢ ∈ [0, 1]`, `θ₀ ≠ θ₁`, `0 < η < 1`, and `θ = (1 - η) θ₀ + η θ₁`,
then every `b ∈ A₀ + A₁` of finite `(θ,q)`-quasinorm lies in `X₀ + X₁` (as the element `a` with the
same image in the ambient space) with `‖a‖_{X̄,η,q} ≤ C ‖b‖_{Ā,θ,q}`. -/
theorem exists_realInterpolationENorm_le_of_isOfClassJ [CompleteSpace A₀] [CompleteSpace A₁]
    [CompleteSpace X₀] [CompleteSpace X₁] {θ₀ θ₁ η θ : ℝ} (hθ₀ : θ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hθ₁ : θ₁ ∈ Set.Icc (0 : ℝ) 1) (hne : θ₀ ≠ θ₁) (hη0 : 0 < η) (hη1 : η < 1)
    (hθ : θ = (1 - η) * θ₀ + η * θ₁) {q : ℝ≥0∞} (hq : 0 < q)
    (hJ₀ : IsOfClassJ ι₀ ι₁ θ₀ κ₀) (hJ₁ : IsOfClassJ ι₀ ι₁ θ₁ κ₁) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ b : sum ι₀ ι₁, realInterpolationENorm ι₀ ι₁ θ q b ≠ ⊤ →
      ∃ a : sum κ₀ κ₁, sumToAmbient κ₀ κ₁ a = sumToAmbient ι₀ ι₁ b ∧
        realInterpolationENorm κ₀ κ₁ η q a ≤ C * realInterpolationENorm ι₀ ι₁ θ q b :=
  sorry

end InterpolationCouple

namespace InterpolationCat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The couple `(X₀, X₁)` with embeddings `κᵢ` into the ambient space of the couple `A`. -/
abbrev ofEmbeddings (A : InterpolationCat.{v, u} 𝕜) {X₀ X₁ : Type v}
    [QuasinormedAddCommGroup X₀] [QuasiNormedSpace 𝕜 X₀] [CompleteSpace X₀]
    [QuasinormedAddCommGroup X₁] [QuasiNormedSpace 𝕜 X₁] [CompleteSpace X₁]
    (κ₀ : X₀ →L[𝕜] A.𝒜) (κ₁ : X₁ →L[𝕜] A.𝒜) (h₀ : Function.Injective κ₀)
    (h₁ : Function.Injective κ₁) : InterpolationCat.{v, u} 𝕜 where
  𝒜 := A.𝒜
  A₀ := X₀
  A₁ := X₁
  ι₀ := κ₀
  ι₁ := κ₁
  injective₀ := h₀
  injective₁ := h₁

/-- **The reiteration theorem** (B–L Theorem 3.5.3; quasi-normed form 3.11.5; Triebel §1.10.2): if
`X₀, X₁` (complete, embedded in the ambient space of `A`) are of class `𝒞(θ₀; Ā)` and
`𝒞(θ₁; Ā)` with `θᵢ ∈ [0, 1]`, `θ₀ ≠ θ₁`, then for `0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`,
`X̄_{η,q} ≅ Ā_{θ,q}`, compatibly with the maps to the ambient space. -/
theorem nonempty_iso_realInterpolationFunctor_reiteration (A : InterpolationCat.{v, u} 𝕜)
    {X₀ X₁ : Type v}
    [QuasinormedAddCommGroup X₀] [QuasiNormedSpace 𝕜 X₀] [CompleteSpace X₀]
    [QuasinormedAddCommGroup X₁] [QuasiNormedSpace 𝕜 X₁] [CompleteSpace X₁]
    (κ₀ : X₀ →L[𝕜] A.𝒜) (κ₁ : X₁ →L[𝕜] A.𝒜) (h₀ : Function.Injective κ₀)
    (h₁ : Function.Injective κ₁) {θ₀ θ₁ : ℝ} (hθ₀ : θ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hθ₁ : θ₁ ∈ Set.Icc (0 : ℝ) 1) (hne : θ₀ ≠ θ₁)
    (hX₀ : InterpolationCouple.IsOfClassK A.ι₀ A.ι₁ θ₀ κ₀ ∧
      InterpolationCouple.IsOfClassJ A.ι₀ A.ι₁ θ₀ κ₀)
    (hX₁ : InterpolationCouple.IsOfClassK A.ι₀ A.ι₁ θ₁ κ₁ ∧
      InterpolationCouple.IsOfClassJ A.ι₀ A.ι₁ θ₁ κ₁)
    (η : ℝ) [Fact (0 < η)] [Fact (η < 1)] (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 1)]
    (hθ : θ = (1 - η) * θ₀ + η * θ₁) (q : ℝ≥0∞) [Fact (0 < q)] :
    ∃ e : (realInterpolationFunctor 𝕜 η q).obj (A.ofEmbeddings κ₀ κ₁ h₀ h₁) ≅
        (realInterpolationFunctor 𝕜 θ q).obj A,
      ∀ x, InterpolationCouple.sumToAmbient A.ι₀ A.ι₁
          ((realInterpolationFunctor 𝕜 θ q).toSum A (e.hom.hom x)) =
        InterpolationCouple.sumToAmbient κ₀ κ₁
          ((realInterpolationFunctor 𝕜 η q).toSum (A.ofEmbeddings κ₀ κ₁ h₀ h₁) x) :=
  sorry

variable (θ₀ : ℝ) (q₀ : ℝ≥0∞) [Fact (0 < θ₀)] [Fact (θ₀ < 1)] [Fact (0 < q₀)]
variable (θ₁ : ℝ) (q₁ : ℝ≥0∞) [Fact (0 < θ₁)] [Fact (θ₁ < 1)] [Fact (0 < q₁)]

/-- The couple `(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})` of real interpolation spaces of `A`, embedded in the
ambient space of `A` through `A₀ + A₁`. -/
noncomputable abbrev realInterpolationCouple (A : InterpolationCat.{v, u} 𝕜) :
    InterpolationCat.{v, u} 𝕜 :=
  A.ofEmbeddings
    ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).comp ((realInterpolationFunctor 𝕜 θ₀ q₀).toSum A))
    ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).comp ((realInterpolationFunctor 𝕜 θ₁ q₁).toSum A))
    (fun _ _ h => (realInterpolationFunctor 𝕜 θ₀ q₀).toSum_injective A
      (InterpolationCouple.sumToAmbient_injective _ _ h))
    (fun _ _ h => (realInterpolationFunctor 𝕜 θ₁ q₁).toSum_injective A
      (InterpolationCouple.sumToAmbient_injective _ _ h))

/-- Reiteration for real interpolation spaces (B–L Theorem 3.5.3 / 3.11.5, "in particular"):
for `0 < θ₀ ≠ θ₁ < 1`, `0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`,
`(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})_{η,q} ≅ Ā_{θ,q}`, compatibly with the maps to the ambient space. -/
theorem nonempty_iso_realInterpolationFunctor_realInterpolationCouple
    (A : InterpolationCat.{v, u} 𝕜) (hne : θ₀ ≠ θ₁) (η : ℝ) [Fact (0 < η)] [Fact (η < 1)]
    (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 1)] (hθ : θ = (1 - η) * θ₀ + η * θ₁)
    (q : ℝ≥0∞) [Fact (0 < q)] :
    ∃ e : (realInterpolationFunctor 𝕜 η q).obj (A.realInterpolationCouple θ₀ q₀ θ₁ q₁) ≅
        (realInterpolationFunctor 𝕜 θ q).obj A,
      ∀ x, InterpolationCouple.sumToAmbient A.ι₀ A.ι₁
          ((realInterpolationFunctor 𝕜 θ q).toSum A (e.hom.hom x)) =
        InterpolationCouple.sumToAmbient (A.realInterpolationCouple θ₀ q₀ θ₁ q₁).ι₀
          (A.realInterpolationCouple θ₀ q₀ θ₁ q₁).ι₁
          ((realInterpolationFunctor 𝕜 η q).toSum (A.realInterpolationCouple θ₀ q₀ θ₁ q₁) x) :=
  sorry

end InterpolationCat
