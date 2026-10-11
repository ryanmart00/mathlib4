/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.InterpolationFunctorEquiv
import Mathlib.Analysis.Interpolation.RealInterpolation.Basic
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.Equivalence

/-!
# The discrete J-method as an interpolation functor

By the equivalence theorem (`JMethod/Equivalence.lean`) the J-space `(A₀, A₁)_{θ,q;J}` is the
same submodule of `A₀ + A₁` as the K-space `(A₀, A₁)_{θ,q}`, with an equivalent quasinorm. So the
identity of `A₀ + A₁` induces an isomorphism of quasi-normed spaces between them; completeness
transfers to the J-space, and the J-method assembles into an interpolation functor
`jInterpolationFunctor 𝕜 θ q`, equivalent (as an object of `Over Sum`) to the canonical real
interpolation functor.

## Main definitions
* `InterpolationCouple.JInterpolationSpace.equivRealInterpolationSpace`: `J_{θ,q} ≃L K_{θ,q}`.
* `jInterpolationFunctor 𝕜 θ q : InterpolationFunctor 𝕜`.
* `realInterpolationFunctorEquivJ`: the canonical real interpolation functor is (equivalent to)
  the discrete J-method.

## Main statements
* `InterpolationCouple.JInterpolationSpace.instCompleteSpace`.
-/

universe v u

open CategoryTheory InterpolationCouple
open scoped ENNReal

namespace InterpolationCouple.JInterpolationSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁] [CompleteSpace A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
variable (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]

/-- `x ≤ C y` in `ℝ≥0∞`, with `C ≠ ⊤` and `y ≠ ⊤`, transfers to `toReal`. -/
private theorem toReal_le_toReal_mul {x y C : ℝ≥0∞} (hC : C ≠ ⊤) (hy : y ≠ ⊤) (h : x ≤ C * y) :
    x.toReal ≤ C.toReal * y.toReal := by
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC hy) h

/-- The J- and K-spaces are isomorphic quasi-normed spaces via the identity of `A₀ + A₁`
(`jInterpolationSubmodule_eq_realInterpolationSubmodule` plus the two quasinorm comparisons). -/
noncomputable def equivRealInterpolationSpace :
    JInterpolationSpace ι₀ ι₁ θ q ≃L[𝕜] RealInterpolationSpace ι₀ ι₁ θ q :=
  have hθ0 : 0 < θ := Fact.out
  have hθ1 : θ < 1 := Fact.out
  have hq : 0 < q := Fact.out
  let e : JInterpolationSpace ι₀ ι₁ θ q ≃ₗ[𝕜] RealInterpolationSpace ι₀ ι₁ θ q :=
    LinearEquiv.ofEq _ _ (jInterpolationSubmodule_eq_realInterpolationSubmodule ι₀ ι₁ hθ0 hθ1 hq)
  { e with
    continuous_toFun := by
      obtain ⟨C, hC, h⟩ :=
        exists_realInterpolationENorm_le_mul_jInterpolationENorm ι₀ ι₁ hθ0 hθ1 hq
      refine QuasinormedAddCommGroup.continuous_of_bound e.toLinearMap.toAddMonoidHom C.toReal
        fun x => ?_
      rw [norm_def, RealInterpolationSpace.norm_def]
      exact toReal_le_toReal_mul hC x.2.ne (h _)
    continuous_invFun := by
      obtain ⟨C, hC, h⟩ :=
        exists_jInterpolationENorm_le_mul_realInterpolationENorm ι₀ ι₁ hθ0 hθ1 hq
      refine QuasinormedAddCommGroup.continuous_of_bound e.symm.toLinearMap.toAddMonoidHom
        C.toReal fun x => ?_
      rw [norm_def, RealInterpolationSpace.norm_def]
      exact toReal_le_toReal_mul hC x.2.ne (h _) }

/-- `equivRealInterpolationSpace` is the identity on the underlying elements of `A₀ + A₁`. -/
theorem toSum_comp_equivRealInterpolationSpace :
    (RealInterpolationSpace.toSum ι₀ ι₁ θ q).comp
        (equivRealInterpolationSpace ι₀ ι₁ θ q : JInterpolationSpace ι₀ ι₁ θ q →L[𝕜] _) =
      JInterpolationSpace.toSum ι₀ ι₁ θ q :=
  rfl

/-- The J-space is complete, transferred from the K-space along `equivRealInterpolationSpace`. -/
instance instCompleteSpace : CompleteSpace (JInterpolationSpace ι₀ ι₁ θ q) :=
  (completeSpace_congr (e := (equivRealInterpolationSpace ι₀ ι₁ θ q).toLinearEquiv.toEquiv)
    (equivRealInterpolationSpace ι₀ ι₁ θ q).isUniformEmbedding).mpr inferInstance

end InterpolationCouple.JInterpolationSpace

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

/-- The discrete J-method `(A₀, A₁) ↦ (A₀, A₁)_{θ,q;J}` as an interpolation functor, for
`0 < θ < 1`, `0 < q ≤ ∞`. -/
noncomputable def jInterpolationFunctor (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)]
    [Fact (0 < q)] : InterpolationFunctor.{v, u} 𝕜 where
  obj C := QuasiBanachCat.of 𝕜 (JInterpolationSpace C.ι₀ C.ι₁ θ q)
  map T := QuasiBanachCat.ofHom (T.jInterpolationMap θ q)
  map_id C := ConcreteCategory.ext (InterpolationCat.Hom.jInterpolationMap_id θ q C)
  map_comp φ ψ := ConcreteCategory.ext (InterpolationCat.Hom.jInterpolationMap_comp θ q φ ψ)
  toSum C := JInterpolationSpace.toSum C.ι₀ C.ι₁ θ q
  toSum_injective C := JInterpolationSpace.toSum_injective C.ι₀ C.ι₁
  fromMeet C := JInterpolationSpace.fromMeet C.ι₀ C.ι₁ θ q
  toSum_fromMeet C := JInterpolationSpace.toSum_comp_fromMeet C.ι₀ C.ι₁
  map_toSum T := T.toSum_comp_jInterpolationMap θ q

variable {𝕜} (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]

/-- The canonical real interpolation functor is equivalent to the discrete J-method (the
equivalence theorem, B–L Theorem 3.11.3), built with `InterpolationFunctor.Equiv.mk'` from
`equivRealInterpolationSpace` through `realInterpolationFunctorEquivK`. -/
noncomputable def realInterpolationFunctorEquivJ :
    (realInterpolationFunctor 𝕜 θ q : InterpolationFunctor.{v, u} 𝕜).Equiv
      (jInterpolationFunctor 𝕜 θ q) :=
  InterpolationFunctor.Equiv.mk'
    (fun C => (realInterpolationFunctorEquivK θ q).iso C ≪≫
      QuasiBanachCat.ofIso (X := (kInterpolationFunctor 𝕜 θ q).obj C)
        (Y := (jInterpolationFunctor 𝕜 θ q).obj C)
        (JInterpolationSpace.equivRealInterpolationSpace C.ι₀ C.ι₁ θ q).symm)
    (fun C => by
      rw [← InterpolationFunctor.Equiv.toSum_comp_hom (realInterpolationFunctorEquivK θ q) C]
      rfl)
