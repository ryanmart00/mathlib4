/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Analysis.Interpolation.QuasiNorm

/-!
# The category of quasi-Banach spaces

DRAFT — under review.

`QuasiBanachCat 𝕜` is the quasi-Banach analogue of Triebel's category ℭ₁ (*Interpolation
Theory, Function Spaces, Differential Operators*, §1.2.2): objects are quasi-Banach spaces over
`𝕜` (quasi-normed and complete), morphisms are *all* continuous linear maps (not just
contractions). Supersedes an earlier `BanachCat`, whose objects were required to be genuinely
`NormedAddCommGroup`.

Deliberately just *one* category here, not two: every genuine Banach space is already a
quasi-Banach space, via `NormedAddCommGroup.toQuasinormedAddCommGroup` (`QuasiNorm.lean`, no
diamond, reuses the genuine norm's own topology verbatim) — so `QuasiBanachCat.of` already
accepts a genuinely-normed space directly, and a second, parallel `BanachCat` category would
just duplicate every declaration below for no payoff. Wherever a construction genuinely needs
the *exact* triangle inequality rather than merely a quasi one, that should be expressed as a
fact about the specific space in question (an isomorphism in `QuasiBanachCat` with a genuinely
normed space), not as membership in a different category.

Modeled closely on `TopModuleCat` (`Mathlib/Algebra/Category/ModuleCat/Topology/Basic.lean`),
which does the same thing for topological modules generally — here we additionally require a
quasi-norm and completeness.
-/

universe v u

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

open CategoryTheory ConcreteCategory

/-- The category of quasi-Banach spaces over `𝕜` (the quasi-Banach analogue of Triebel's ℭ₁). -/
structure QuasiBanachCat extends ModuleCat.{v} 𝕜 where
  [quasinormedAddCommGroup : QuasinormedAddCommGroup carrier]
  [continuousSMul : ContinuousSMul 𝕜 carrier]
  [completeSpace : CompleteSpace carrier]

namespace QuasiBanachCat

noncomputable instance : CoeSort (QuasiBanachCat.{v} 𝕜) (Type v) := ⟨fun M ↦ M.toModuleCat⟩

attribute [instance] quasinormedAddCommGroup continuousSMul completeSpace

/-- Make an object in `QuasiBanachCat 𝕜` from an unbundled quasi-Banach space. -/
abbrev of (M : Type v) [QuasinormedAddCommGroup M] [Module 𝕜 M] [ContinuousSMul 𝕜 M]
    [CompleteSpace M] : QuasiBanachCat.{v} 𝕜 :=
  ⟨ModuleCat.of 𝕜 M⟩

lemma coe_of (M : Type v) [QuasinormedAddCommGroup M] [Module 𝕜 M] [ContinuousSMul 𝕜 M]
    [CompleteSpace M] : (of 𝕜 M : Type v) = M := rfl

variable {𝕜} in
/-- Homs in `QuasiBanachCat` as one field structures over `ContinuousLinearMap`. -/
structure Hom (X Y : QuasiBanachCat.{v} 𝕜) where
  private ofHom' ::
  /-- The underlying continuous linear map. Use `hom` instead. -/
  hom' : X →L[𝕜] Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (QuasiBanachCat.{v} 𝕜) where
  Hom := Hom
  id M := ⟨ContinuousLinearMap.id 𝕜 M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (QuasiBanachCat.{v} 𝕜) (· →L[𝕜] ·) where
  hom := Hom.hom'
  ofHom := Hom.ofHom'

variable {𝕜} in
/-- Cast a hom in `QuasiBanachCat` into a continuous linear map. -/
abbrev Hom.hom {X Y : QuasiBanachCat 𝕜} (f : X.Hom Y) : X →L[𝕜] Y :=
  ConcreteCategory.hom (C := QuasiBanachCat 𝕜) f

variable {𝕜} in
/-- Construct a hom in `QuasiBanachCat` from a continuous linear map. -/
abbrev ofHom {X Y : Type v}
    [QuasinormedAddCommGroup X] [Module 𝕜 X] [ContinuousSMul 𝕜 X] [CompleteSpace X]
    [QuasinormedAddCommGroup Y] [Module 𝕜 Y] [ContinuousSMul 𝕜 Y] [CompleteSpace Y]
    (f : X →L[𝕜] Y) : of 𝕜 X ⟶ of 𝕜 Y :=
  ConcreteCategory.ofHom f

@[simp] lemma hom_ofHom {X Y : Type v}
    [QuasinormedAddCommGroup X] [Module 𝕜 X] [ContinuousSMul 𝕜 X] [CompleteSpace X]
    [QuasinormedAddCommGroup Y] [Module 𝕜 Y] [ContinuousSMul 𝕜 Y] [CompleteSpace Y]
    (f : X →L[𝕜] Y) : (ofHom f).hom = f := rfl

@[simp] lemma hom_comp {X Y Z : QuasiBanachCat 𝕜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] lemma hom_id (X : QuasiBanachCat 𝕜) : hom (𝟙 X) = .id _ _ := rfl

/-! ### Isomorphisms

An isomorphism in `QuasiBanachCat` is exactly a continuous linear equivalence, i.e. (since every
continuous linear map between quasi-normed spaces is bounded, `le_opQuasiNorm`) a linear
equivalence whose quasinorm comparison holds up to constants in both directions. This is the
notion of *equivalence of quasi-Banach spaces* used throughout. Mirrors `TopModuleCat.ofIso` /
`Iso.toContinuousLinearEquiv`. -/

variable {𝕜}

/-- Construct an iso in `QuasiBanachCat` from a continuous linear equiv. -/
def ofIso {X Y : QuasiBanachCat 𝕜} (e : X ≃L[𝕜] Y) : X ≅ Y where
  hom := ConcreteCategory.ofHom e.toContinuousLinearMap
  inv := ConcreteCategory.ofHom e.symm.toContinuousLinearMap
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/-- Cast an iso in `QuasiBanachCat` into a continuous linear equiv. -/
def continuousLinearEquivOfIso {X Y : QuasiBanachCat 𝕜} (e : X ≅ Y) : X ≃L[𝕜] Y where
  __ := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by
    sorry
  right_inv x := by
    sorry

@[simp]
theorem ofIso_hom {X Y : QuasiBanachCat 𝕜} (e : X ≃L[𝕜] Y) :
    (ofIso e).hom.hom = e.toContinuousLinearMap := by
  sorry

@[simp]
theorem continuousLinearEquivOfIso_apply {X Y : QuasiBanachCat 𝕜} (e : X ≅ Y) (x : X) :
    continuousLinearEquivOfIso e x = e.hom x := by
  sorry

end QuasiBanachCat
