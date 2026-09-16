/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Couple
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of interpolation couples

DRAFT — under review.

`InterpolationCat 𝕜` bundles a Triebel interpolation couple (§1.2.1: two Banach spaces
`A₀, A₁`, continuously embedded in a common Hausdorff TVS `𝒜`) as a single object; the
`Category` instance on it is Triebel's category ℭ₂ (§1.2.2) of such couples.

Triebel defines a morphism `{A₀,A₁} ⟶ {B₀,B₁}` as a linear operator `T : A₀+A₁ → B₀+B₁` whose
restriction to each `Aⱼ` is a continuous map into `Bⱼ`. We package this *equivalently* but more
usably as a pair of continuous linear maps `f₀ : A₀ →L[𝕜] B₀`, `f₁ : A₁ →L[𝕜] B₁`, together with
a compatibility condition ensuring they agree on the meet (`C.ι₀ a₀ = C.ι₁ a₁ →
D.ι₀ (f₀ a₀) = D.ι₁ (f₁ a₁)`). This determines a well-defined linear map on the sum spaces via
the quotient's universal property, without needing that map as separate primitive data.
-/

universe v u

open CategoryTheory

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]

/-- An interpolation couple (Triebel §1.2.1): two Banach spaces `A₀, A₁` over `𝕜`, both linearly
and continuously embedded (via `ι₀, ι₁`) in a common Hausdorff topological vector space `𝒜`. -/
structure InterpolationCat where
  /-- The ambient Hausdorff topological vector space. -/
  𝒜 : Type v
  [addCommGroup𝒜 : AddCommGroup 𝒜]
  [module𝒜 : Module 𝕜 𝒜]
  [topologicalSpace𝒜 : TopologicalSpace 𝒜]
  [isTopologicalAddGroup𝒜 : IsTopologicalAddGroup 𝒜]
  [continuousSMul𝒜 : ContinuousSMul 𝕜 𝒜]
  [t2Space𝒜 : T2Space 𝒜]
  /-- The first Banach space of the couple. -/
  A₀ : Type v
  [normedAddCommGroup₀ : NormedAddCommGroup A₀]
  [normedSpace₀ : NormedSpace 𝕜 A₀]
  [completeSpace₀ : CompleteSpace A₀]
  /-- The second Banach space of the couple. -/
  A₁ : Type v
  [normedAddCommGroup₁ : NormedAddCommGroup A₁]
  [normedSpace₁ : NormedSpace 𝕜 A₁]
  [completeSpace₁ : CompleteSpace A₁]
  /-- The embedding of `A₀` into the ambient space. -/
  ι₀ : A₀ →L[𝕜] 𝒜
  /-- The embedding of `A₁` into the ambient space. -/
  ι₁ : A₁ →L[𝕜] 𝒜
  injective₀ : Function.Injective ι₀
  injective₁ : Function.Injective ι₁

namespace InterpolationCat

attribute [instance] addCommGroup𝒜 module𝒜 topologicalSpace𝒜 isTopologicalAddGroup𝒜
  continuousSMul𝒜 t2Space𝒜 normedAddCommGroup₀ normedSpace₀ completeSpace₀
  normedAddCommGroup₁ normedSpace₁ completeSpace₁

variable {𝕜}

/-- A morphism of interpolation couples: a pair of continuous linear maps on the legs, compatible
in the sense that they agree wherever the legs' embeddings agree (i.e. on the meet). Equivalent
to, but more directly usable than, Triebel's "linear map on the sum space, continuous on each
restriction". -/
structure Hom (C D : InterpolationCat.{v, u} 𝕜) where
  /-- The induced map on the first leg. -/
  f₀ : C.A₀ →L[𝕜] D.A₀
  /-- The induced map on the second leg. -/
  f₁ : C.A₁ →L[𝕜] D.A₁
  compatible : ∀ a₀ a₁, C.ι₀ a₀ = C.ι₁ a₁ → D.ι₀ (f₀ a₀) = D.ι₁ (f₁ a₁)

@[ext]
theorem Hom.ext {C D : InterpolationCat.{v, u} 𝕜} {φ ψ : Hom C D}
    (h₀ : φ.f₀ = ψ.f₀) (h₁ : φ.f₁ = ψ.f₁) : φ = ψ := by
  cases φ; cases ψ; simp_all

instance : Category (InterpolationCat.{v, u} 𝕜) where
  Hom := Hom
  id C := ⟨ContinuousLinearMap.id 𝕜 C.A₀, ContinuousLinearMap.id 𝕜 C.A₁, fun _ _ h ↦ h⟩
  comp φ ψ := ⟨ψ.f₀.comp φ.f₀, ψ.f₁.comp φ.f₁,
    fun a₀ a₁ h ↦ ψ.compatible _ _ (φ.compatible a₀ a₁ h)⟩

@[simp] lemma id_f₀ (C : InterpolationCat.{v, u} 𝕜) : (𝟙 C : Hom C C).f₀ = .id 𝕜 C.A₀ := rfl
@[simp] lemma id_f₁ (C : InterpolationCat.{v, u} 𝕜) : (𝟙 C : Hom C C).f₁ = .id 𝕜 C.A₁ := rfl

@[simp] lemma comp_f₀ {C D E : InterpolationCat.{v, u} 𝕜} (φ : C ⟶ D) (ψ : D ⟶ E) :
    (φ ≫ ψ).f₀ = ψ.f₀.comp φ.f₀ := rfl
@[simp] lemma comp_f₁ {C D E : InterpolationCat.{v, u} 𝕜} (φ : C ⟶ D) (ψ : D ⟶ E) :
    (φ ≫ ψ).f₁ = ψ.f₁.comp φ.f₁ := rfl

/-- The map a `Hom` induces on the sum spaces: `(f₀, f₁)` applied on `A₀ × A₁`, descended to the
quotient `A₀ + A₁` via the quotient's universal property — well-defined precisely because
`compatible` (meet-based) is equivalent, via the substitution `a₁ ↦ -a₁`, to the plus-kernel
condition the quotient is actually built from. This recovers Triebel's own notion of morphism:
"a linear map on the sum space, continuous on each restriction". -/
noncomputable def Hom.sumMap {C D : InterpolationCat.{v, u} 𝕜} (T : Hom C D) :
    InterpolationCouple.sum C.ι₀ C.ι₁ →L[𝕜] InterpolationCouple.sum D.ι₀ D.ι₁ :=
  (InterpolationCouple.plus C.ι₀ C.ι₁).ker.liftQL
    ((InterpolationCouple.plus D.ι₀ D.ι₁).ker.mkQL.comp (T.f₀.prodMap T.f₁)) <| by
  rintro ⟨a₀, a₁⟩ ha
  rw [InterpolationCouple.mem_ker_plus_iff] at ha
  rw [LinearMap.mem_ker]
  change (InterpolationCouple.plus D.ι₀ D.ι₁).ker.mkQ (T.f₀ a₀, T.f₁ a₁) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, InterpolationCouple.mem_ker_plus_iff]
  have := T.compatible a₀ (-a₁) (by simpa using ha)
  simpa using this

end InterpolationCat
