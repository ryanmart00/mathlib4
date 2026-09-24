/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.TrivialFunctors
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Equivalence of interpolation functors

The inclusions `F.toSum C : F(C) →L[𝕜] A₀ + A₁` of an interpolation functor form a natural
transformation `F ⟶ Sum` to the sum functor (`sumInterpolationFunctor`); its naturality is exactly
the `map_toSum` axiom. So an interpolation functor is naturally an object of the over category
`Over Sum` in the functor category `InterpolationCat 𝕜 ⥤ QuasiBanachCat 𝕜`, and two interpolation
functors are *equivalent* when they are isomorphic there: a natural isomorphism, componentwise an
isomorphism in `QuasiBanachCat` (an equivalence of quasi-Banach spaces), commuting with the
inclusions into the sum (so `F(C)` and `G(C)` are the same subspace of `A₀ + A₁`).

This is how different constructions of the same interpolation functor are identified; e.g.
`realInterpolationFunctorEquivK`.

## Main definitions
* `InterpolationFunctor.toSumNatTrans F : F.toFunctor ⟶ Sum`.
* `InterpolationFunctor.toOver F : Over Sum`.
* `InterpolationFunctor.Equiv F G := F.toOver ≅ G.toOver`.
* `InterpolationFunctor.Equiv.mk'`: build an equivalence from componentwise isomorphisms
  compatible with `toSum` (naturality is then automatic, since `toSum` is injective).
-/

universe v u

open CategoryTheory

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

namespace InterpolationFunctor

/-- The inclusions `F(C) →L[𝕜] A₀ + A₁`, as a natural transformation to the sum functor. -/
noncomputable def toSumNatTrans (F : InterpolationFunctor.{v, u} 𝕜) :
    F.toFunctor ⟶ (sumInterpolationFunctor : InterpolationFunctor.{v, u} 𝕜).toFunctor where
  app C := ConcreteCategory.ofHom (F.toSum C)
  naturality _ _ T := ConcreteCategory.ext (F.map_toSum T)

/-- An interpolation functor, as an object over the sum functor. -/
noncomputable def toOver (F : InterpolationFunctor.{v, u} 𝕜) :
    Over (sumInterpolationFunctor : InterpolationFunctor.{v, u} 𝕜).toFunctor :=
  Over.mk F.toSumNatTrans

/-- An equivalence of interpolation functors: an isomorphism over the sum functor. -/
abbrev Equiv (F G : InterpolationFunctor.{v, u} 𝕜) : Type _ :=
  F.toOver ≅ G.toOver

namespace Equiv

variable {F G : InterpolationFunctor.{v, u} 𝕜}

/-- The component of an equivalence at a couple: an isomorphism of quasi-Banach spaces. -/
noncomputable def iso (e : F.Equiv G) (C : InterpolationCat.{v, u} 𝕜) : F.obj C ≅ G.obj C :=
  ((Over.forget _).mapIso e).app C

theorem toSum_comp_hom (e : F.Equiv G) (C : InterpolationCat.{v, u} 𝕜) :
    (G.toSum C).comp (e.iso C).hom.hom = F.toSum C :=
  congrArg ConcreteCategory.hom (NatTrans.congr_app (Over.w e.hom) C)

theorem toSum_comp_inv (e : F.Equiv G) (C : InterpolationCat.{v, u} 𝕜) :
    (F.toSum C).comp (e.iso C).inv.hom = G.toSum C :=
  congrArg ConcreteCategory.hom (NatTrans.congr_app (Over.w e.inv) C)

/-- Componentwise isomorphisms compatible with the inclusions into the sum are automatically
natural (because `toSum` is injective). -/
theorem naturality_of_toSum_comp (iso : ∀ C, F.obj C ≅ G.obj C)
    (h : ∀ C, (G.toSum C).comp (iso C).hom.hom = F.toSum C) {C D : InterpolationCat.{v, u} 𝕜}
    (T : C ⟶ D) : F.map T ≫ (iso D).hom = (iso C).hom ≫ G.map T := by
  refine ConcreteCategory.ext (ContinuousLinearMap.ext fun x => G.toSum_injective D ?_)
  have e1 := DFunLike.congr_fun (h D) ((F.map T).hom x)
  have e2 := DFunLike.congr_fun (F.map_toSum T) x
  have e3 := DFunLike.congr_fun (G.map_toSum T) ((iso C).hom.hom x)
  have e4 := DFunLike.congr_fun (h C) x
  simp only [ContinuousLinearMap.comp_apply] at e1 e2 e3 e4
  simp only [QuasiBanachCat.hom_comp, ContinuousLinearMap.comp_apply]
  rw [e1, e2, e3, e4]

/-- Build an equivalence from componentwise isomorphisms of quasi-Banach spaces compatible with
the inclusions into the sum. -/
noncomputable def mk' (iso : ∀ C, F.obj C ≅ G.obj C)
    (h : ∀ C, (G.toSum C).comp (iso C).hom.hom = F.toSum C) : F.Equiv G :=
  Over.isoMk (NatIso.ofComponents iso fun T => naturality_of_toSum_comp iso h T)
    (NatTrans.ext (funext fun C => ConcreteCategory.ext (h C)))

/-- Equal interpolation functors are equivalent. -/
noncomputable def ofEq (h : F = G) : F.Equiv G :=
  eqToIso (congrArg toOver h)

end Equiv

end InterpolationFunctor
