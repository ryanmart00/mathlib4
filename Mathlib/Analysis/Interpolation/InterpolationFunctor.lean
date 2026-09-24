/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.QuasiBanachCat
import Mathlib.Analysis.Interpolation.InterpolationCat
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Interpolation functors

DRAFT — under review, no instances constructed yet.

Triebel §1.2.2, Definition 1: an interpolation functor is a (covariant) functor
`F : InterpolationCat 𝕜 ⥤ QuasiBanachCat 𝕜` such that `A₀ ∩ A₁ ⊂ F({A₀,A₁}) ⊂ A₀ + A₁`, and for a
morphism `T`, `F(T)` is the restriction of `T` to `F({A₀,A₁})`. Triebel's own definition lands
in genuine Banach spaces; we land in quasi-Banach spaces instead, since `A₀ ∩ A₁`/`A₀ + A₁`
themselves (`Couple.lean`) are only guaranteed quasi-Banach for quasi-normed legs — every
genuinely-Banach case is still covered, via `NormedAddCommGroup.toQuasinormedAddCommGroup`
(`QuasiNorm.lean`).

We realize the sandwich condition as two continuous linear maps `fromMeet C : C.meet →L[𝕜] F(C)`
and `toSum C : F(C) →L[𝕜] C.sum`, agreeing with the canonical `meet →L[𝕜] sum` map on composition,
with `toSum` required injective (so `F(C)` genuinely embeds in `C.sum`, matching the literal
"⊂" reading). The restriction condition becomes: `F(T)`, pushed through `toSum`, agrees with `T`'s
induced action on the sum spaces (`Hom.sumMap`), pulled back through `toSum`.
-/

universe v u

open CategoryTheory

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

/-- Triebel §1.2.2, Definition 1: an interpolation functor. -/
structure InterpolationFunctor extends InterpolationCat.{v, u} 𝕜 ⥤ QuasiBanachCat.{v} 𝕜 where
  /-- The inclusion of `F(C)` into the sum space `A₀ + A₁`. -/
  toSum (C : InterpolationCat.{v, u} 𝕜) :
    (obj C : Type v) →L[𝕜] InterpolationCouple.sum C.ι₀ C.ι₁
  toSum_injective (C : InterpolationCat.{v, u} 𝕜) : Function.Injective (toSum C)
  /-- The map from the meet `A₀ ∩ A₁` into `F(C)`. -/
  fromMeet (C : InterpolationCat.{v, u} 𝕜) :
    InterpolationCouple.meet C.ι₀ C.ι₁ →L[𝕜] (obj C : Type v)
  /-- `fromMeet` followed by `toSum` recovers the canonical `meet →L[𝕜] sum` map — i.e. `F(C)`
  really does sit between the meet and the sum. -/
  toSum_fromMeet (C : InterpolationCat.{v, u} 𝕜) :
    (toSum C).comp (fromMeet C) = InterpolationCouple.meetToSum C.ι₀ C.ι₁
  /-- `F(T)` is the restriction of `T`'s induced sum-space map to `F(C)`, landing in `F(D)`. -/
  map_toSum {C D : InterpolationCat.{v, u} 𝕜} (T : C ⟶ D) :
    (toSum D).comp (map T).hom = T.sumMap.comp (toSum C)

namespace InterpolationFunctor

variable {𝕜}

/-- An equivalence of interpolation functors: for each couple `C`, an isomorphism
`F(C) ≅ G(C)` in `QuasiBanachCat` (i.e. an equivalence of quasi-Banach spaces), compatible with
the inclusions into `A₀ + A₁` (so `F(C)` and `G(C)` are the same subspace of the sum). Naturality
is automatic (`Equiv.naturality`), since `toSum` is injective. This is how different constructions
of the same interpolation functor (e.g. the K- and J-methods) are identified. -/
structure Equiv (F G : InterpolationFunctor.{v, u} 𝕜) where
  /-- The componentwise isomorphism of quasi-Banach spaces. -/
  iso (C : InterpolationCat.{v, u} 𝕜) : F.obj C ≅ G.obj C
  toSum_comp_hom (C : InterpolationCat.{v, u} 𝕜) :
    (G.toSum C).comp (iso C).hom.hom = F.toSum C

namespace Equiv

variable {F G H : InterpolationFunctor.{v, u} 𝕜}

theorem toSum_comp_inv (e : F.Equiv G) (C : InterpolationCat.{v, u} 𝕜) :
    (F.toSum C).comp (e.iso C).inv.hom = G.toSum C := by
  sorry

/-- The componentwise isomorphisms of an equivalence are natural. -/
theorem naturality (e : F.Equiv G) {C D : InterpolationCat.{v, u} 𝕜} (T : C ⟶ D) :
    F.map T ≫ (e.iso D).hom = (e.iso C).hom ≫ G.map T := by
  sorry

/-- An equivalence of interpolation functors as a natural isomorphism of the underlying
functors. -/
def toNatIso (e : F.Equiv G) : F.toFunctor ≅ G.toFunctor :=
  NatIso.ofComponents e.iso fun T => e.naturality T

/-- The identity equivalence. -/
def refl (F : InterpolationFunctor.{v, u} 𝕜) : F.Equiv F where
  iso C := Iso.refl _
  toSum_comp_hom C := by
    sorry

/-- The inverse equivalence. -/
def symm (e : F.Equiv G) : G.Equiv F where
  iso C := (e.iso C).symm
  toSum_comp_hom C := e.toSum_comp_inv C

/-- The composite equivalence. -/
def trans (e : F.Equiv G) (e' : G.Equiv H) : F.Equiv H where
  iso C := e.iso C ≪≫ e'.iso C
  toSum_comp_hom C := by
    sorry

/-- Equal interpolation functors are equivalent. -/
def ofEq (h : F = G) : F.Equiv G :=
  h ▸ refl F

end Equiv

end InterpolationFunctor
