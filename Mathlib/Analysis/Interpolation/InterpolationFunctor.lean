/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.BanachCat
import Mathlib.Analysis.Interpolation.InterpolationCat
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Interpolation functors

DRAFT — under review, no instances constructed yet.

Triebel §1.2.2, Definition 1: an interpolation functor is a (covariant) functor
`F : InterpolationCat 𝕜 ⥤ BanachCat 𝕜` such that `A₀ ∩ A₁ ⊂ F({A₀,A₁}) ⊂ A₀ + A₁`, and for a
morphism `T`, `F(T)` is the restriction of `T` to `F({A₀,A₁})`.

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
structure InterpolationFunctor extends InterpolationCat.{v, u} 𝕜 ⥤ BanachCat.{v} 𝕜 where
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
