/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.InterpolationFunctorEquiv
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.KInterpolationFunctor

/-!
# Real interpolation

The real interpolation functor `(A₀, A₁) ↦ (A₀, A₁)_{θ,q}`, for `0 < θ < 1`, `0 < q ≤ ∞`
(Triebel §1.3), as an interpolation functor `InterpolationCat 𝕜 ⥤ QuasiBanachCat 𝕜`.

`realInterpolationFunctor` is the canonical real interpolation functor, and it does not commit to
any particular construction: it is irreducible, and its only link to a construction is an
equivalence of interpolation functors (`InterpolationFunctor.Equiv`, an isomorphism over the sum
functor), which identifies the spaces as the same subspace of `A₀ + A₁` with equivalent
quasinorms. It is implemented by the K-method
(`KMethod/`), so `realInterpolationFunctorEquivK` is trivial. Any other construction (e.g. the
J-method) gets its own equivalence theorem, in parallel.

## Main definitions
* `realInterpolationFunctor 𝕜 θ q`: the canonical real interpolation functor.
* `realInterpolationFunctorEquivK`: its equivalence with the K-method.

## Main statements
* `norm_realInterpolationFunctor_map_le`: the real interpolation functor is exact of type `θ`.
-/

universe v u

open CategoryTheory
open scoped ENNReal

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

/-- The real interpolation functor `(A₀, A₁) ↦ (A₀, A₁)_{θ,q}`, for `0 < θ < 1`, `0 < q ≤ ∞`.
Irreducible: use `realInterpolationFunctorEquivK` (or an equivalence with another construction) to
compute with it. -/
noncomputable irreducible_def realInterpolationFunctor (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)]
    [Fact (θ < 1)] [Fact (0 < q)] : InterpolationFunctor.{v, u} 𝕜 :=
  kInterpolationFunctor 𝕜 θ q

variable {𝕜} (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]

/-- The real interpolation functor is (implemented by) the K-method. -/
noncomputable def realInterpolationFunctorEquivK :
    (realInterpolationFunctor 𝕜 θ q : InterpolationFunctor.{v, u} 𝕜).Equiv
      (kInterpolationFunctor 𝕜 θ q) :=
  InterpolationFunctor.Equiv.ofEq (realInterpolationFunctor_def 𝕜 θ q)

/-- The real interpolation functor is exact of type `θ` (Triebel §1.3.3). -/
theorem norm_realInterpolationFunctor_map_le {C D : InterpolationCat.{v, u} 𝕜} (T : C ⟶ D)
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : (realInterpolationFunctor 𝕜 θ q).obj C) :
    ‖((realInterpolationFunctor 𝕜 θ q).map T).hom a‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖a‖ := by
  have key : ∀ (F : InterpolationFunctor.{v, u} 𝕜), F = kInterpolationFunctor 𝕜 θ q →
      ∀ a : F.obj C, ‖(F.map T).hom a‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖a‖ := by
    rintro F rfl a
    exact T.norm_realInterpolationMap_le θ q hM₀ hM₁ h₀ h₁ a
  exact key _ (realInterpolationFunctor_def 𝕜 θ q) a
