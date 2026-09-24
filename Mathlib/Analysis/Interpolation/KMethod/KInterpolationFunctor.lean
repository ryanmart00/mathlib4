/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.InterpolationFunctor
import Mathlib.Analysis.Interpolation.KMethod.RealInterpolationSpace

/-!
# The K-method as an interpolation functor

DRAFT — statement-review stage.

For `0 < θ < 1` and `0 < q ≤ ∞`, the real interpolation spaces `(A₀, A₁)_{θ,q}` of
`KMethod/RealInterpolationSpace.lean` assemble into an interpolation functor
`kInterpolationFunctor 𝕜 θ q : InterpolationFunctor 𝕜` (Triebel §1.3.3), i.e. a functor
`InterpolationCat 𝕜 ⥤ QuasiBanachCat 𝕜` together with the sandwich
`A₀ ∩ A₁ ↪ F(A₀, A₁) ↪ A₀ + A₁`, compatible with morphisms. It is exact of type `θ`
(`InterpolationCat.Hom.norm_realInterpolationMap_le`).

This is the implementation of the canonical real interpolation functor
`realInterpolationFunctor` (`Analysis/Interpolation/RealInterpolation.lean`), which should be used
downstream instead; the two are related by `realInterpolationFunctorEquivK`. The unbundled form of
the K-method (given two embeddings) is `InterpolationCouple.RealInterpolationSpace`.
-/

universe v u

open CategoryTheory InterpolationCouple
open scoped ENNReal

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

/-- The K-method `(A₀, A₁) ↦ (A₀, A₁)_{θ,q}` as an interpolation functor, for `0 < θ < 1`,
`0 < q ≤ ∞`. -/
noncomputable def kInterpolationFunctor (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)]
    [Fact (0 < q)] : InterpolationFunctor.{v, u} 𝕜 where
  obj C := QuasiBanachCat.of 𝕜 (RealInterpolationSpace C.ι₀ C.ι₁ θ q)
  map T := QuasiBanachCat.ofHom (T.realInterpolationMap θ q)
  map_id C := ConcreteCategory.ext (InterpolationCat.Hom.realInterpolationMap_id θ q C)
  map_comp φ ψ := by
    sorry
  toSum C := RealInterpolationSpace.toSum C.ι₀ C.ι₁ θ q
  toSum_injective C := RealInterpolationSpace.toSum_injective C.ι₀ C.ι₁
  fromMeet C := RealInterpolationSpace.fromMeet C.ι₀ C.ι₁ θ q
  toSum_fromMeet C := RealInterpolationSpace.toSum_comp_fromMeet C.ι₀ C.ι₁
  map_toSum T := T.toSum_comp_realInterpolationMap θ q

variable {𝕜} (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]

theorem kInterpolationFunctor_obj (C : InterpolationCat.{v, u} 𝕜) :
    ((kInterpolationFunctor 𝕜 θ q).obj C : Type v) = RealInterpolationSpace C.ι₀ C.ι₁ θ q :=
  rfl

theorem kInterpolationFunctor_map {C D : InterpolationCat.{v, u} 𝕜} (T : C ⟶ D) :
    ((kInterpolationFunctor 𝕜 θ q).map T).hom = T.realInterpolationMap θ q :=
  rfl
