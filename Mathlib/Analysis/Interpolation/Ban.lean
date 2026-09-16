/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The category of Banach spaces

DRAFT — under review.

`Ban 𝕜` is Triebel's category ℭ₁ (*Interpolation Theory, Function Spaces, Differential
Operators*, §1.2.2): objects are Banach spaces over `𝕜`, morphisms are *all* continuous linear
maps (not just contractions). Modeled closely on `TopModuleCat`
(`Mathlib/Algebra/Category/ModuleCat/Topology/Basic.lean`), which does the same thing for
topological modules generally — here we additionally require a norm and completeness.
-/

universe v u

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

open CategoryTheory ConcreteCategory

/-- The category of Banach spaces over `𝕜` (Triebel's ℭ₁). -/
structure Ban extends ModuleCat.{v} 𝕜 where
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace 𝕜 carrier]
  [completeSpace : CompleteSpace carrier]

namespace Ban

noncomputable instance : CoeSort (Ban.{v} 𝕜) (Type v) := ⟨fun M ↦ M.toModuleCat⟩

attribute [instance] normedAddCommGroup normedSpace completeSpace

/-- Make an object in `Ban 𝕜` from an unbundled Banach space. -/
abbrev of (M : Type v) [NormedAddCommGroup M] [NormedSpace 𝕜 M] [CompleteSpace M] : Ban.{v} 𝕜 :=
  ⟨ModuleCat.of 𝕜 M⟩

lemma coe_of (M : Type v) [NormedAddCommGroup M] [NormedSpace 𝕜 M] [CompleteSpace M] :
    (of 𝕜 M : Type v) = M := rfl

variable {𝕜} in
/-- Homs in `Ban` as one field structures over `ContinuousLinearMap`. -/
structure Hom (X Y : Ban.{v} 𝕜) where
  private ofHom' ::
  /-- The underlying continuous linear map. Use `hom` instead. -/
  hom' : X →L[𝕜] Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (Ban.{v} 𝕜) where
  Hom := Hom
  id M := ⟨ContinuousLinearMap.id 𝕜 M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (Ban.{v} 𝕜) (· →L[𝕜] ·) where
  hom := Hom.hom'
  ofHom := Hom.ofHom'

variable {𝕜} in
/-- Cast a hom in `Ban` into a continuous linear map. -/
abbrev Hom.hom {X Y : Ban 𝕜} (f : X.Hom Y) : X →L[𝕜] Y :=
  ConcreteCategory.hom (C := Ban 𝕜) f

variable {𝕜} in
/-- Construct a hom in `Ban` from a continuous linear map. -/
abbrev ofHom {X Y : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (f : X →L[𝕜] Y) : of 𝕜 X ⟶ of 𝕜 Y :=
  ConcreteCategory.ofHom f

@[simp] lemma hom_ofHom {X Y : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (f : X →L[𝕜] Y) : (ofHom f).hom = f := rfl

@[simp] lemma hom_comp {X Y Z : Ban 𝕜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] lemma hom_id (X : Ban 𝕜) : hom (𝟙 X) = .id _ _ := rfl

end Ban
