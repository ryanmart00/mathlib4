/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.InterpolationFunctor

/-!
# The trivial interpolation functors `∩` and `+`

DRAFT — under review.

Triebel §1.2.3: `F({A₀,A₁}) = A₀∩A₁` and `F({A₀,A₁}) = A₀+A₁` are themselves interpolation
functors (of type `f(t₀,t₁) = max(t₀,t₁)`, though we don't yet formalize the "type" condition).
This is the first real construction of an `InterpolationFunctor`, and validates the definition:
it either goes through, or exposes a design problem `InterpolationFunctor`'s bare type-check
couldn't catch.
-/

universe v u

open CategoryTheory

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Triebel §1.2.3: `A₀ + A₁` is (trivially) an interpolation functor. -/
noncomputable def sumInterpolationFunctor : InterpolationFunctor.{v, u} 𝕜 where
  obj C := QuasiBanachCat.of 𝕜 (InterpolationCouple.sum C.ι₀ C.ι₁)
  map T := QuasiBanachCat.ofHom T.sumMap
  toSum _ := ContinuousLinearMap.id 𝕜 _
  toSum_injective _ := Function.injective_id
  fromMeet C := InterpolationCouple.meetToSum C.ι₀ C.ι₁
  toSum_fromMeet _ := ContinuousLinearMap.id_comp _
  map_toSum _ := by simp

theorem InterpolationCouple.meetToSum_injective (C : InterpolationCat.{v, u} 𝕜) :
    Function.Injective (InterpolationCouple.meetToSum C.ι₀ C.ι₁) := by
  rintro ⟨⟨a₀, a₁⟩, ha⟩ ⟨⟨b₀, b₁⟩, hb⟩ hab
  rw [InterpolationCouple.mem_meet_iff] at ha hb
  have hab' : InterpolationCouple.inl₀ C.ι₀ C.ι₁ a₀ = InterpolationCouple.inl₀ C.ι₀ C.ι₁ b₀ := hab
  have ha0 : a₀ = b₀ :=
    InterpolationCouple.inl₀_injective C.ι₀ C.ι₁ C.injective₀ hab'
  have ha1 : a₁ = b₁ := C.injective₁ (by rw [← ha, ← hb, ha0])
  simp [ha0, ha1]

/-- Triebel §1.2.3: `A₀ ∩ A₁` is (trivially) an interpolation functor. -/
noncomputable def meetInterpolationFunctor : InterpolationFunctor.{v, u} 𝕜 where
  obj C := QuasiBanachCat.of 𝕜 (InterpolationCouple.meet C.ι₀ C.ι₁)
  map T := QuasiBanachCat.ofHom T.meetMap
  toSum C := InterpolationCouple.meetToSum C.ι₀ C.ι₁
  toSum_injective C := InterpolationCouple.meetToSum_injective C
  fromMeet _ := ContinuousLinearMap.id 𝕜 _
  toSum_fromMeet _ := ContinuousLinearMap.comp_id _
  map_toSum {C D} T := by
    ext ⟨⟨a₀, a₁⟩, ha⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      QuasiBanachCat.hom_ofHom, InterpolationCat.Hom.meetMap_apply,
      InterpolationCouple.meetToSum_apply, InterpolationCouple.meetToSum_apply,
      InterpolationCouple.inl₀_eq_mk, InterpolationCouple.inl₀_eq_mk,
      InterpolationCat.Hom.sumMap_mk, map_zero]
