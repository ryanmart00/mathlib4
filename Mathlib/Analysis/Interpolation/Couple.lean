/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Interpolation couples

DRAFT — under review, no proof attempted beyond the completeness of `A₀ ⊓ A₁` and `A₀ + A₁`.

Following Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, §1.2.1:
two Banach spaces `A₀, A₁`, both linearly and continuously embedded in a common Hausdorff
topological vector space `𝒜`, form an *interpolation couple*. `A₀ ⊓ A₁` and `A₀ + A₁` are then
Banach spaces in their own right.

Realized here as: `A₀ ⊓ A₁` (the "meet") is the kernel of `diff (a₀,a₁) = ι₀ a₀ - ι₁ a₁` on
`A₀ × A₁` — the pullback/equalizer, matching Triebel's `A₀ ∩ A₁` as the set of points reachable
from both legs. `A₀ + A₁` (the "sum") is the quotient of `A₀ × A₁` by the kernel of the *different*
map `plus (a₀,a₁) = ι₀ a₀ + ι₁ a₁` — matching Triebel's `A₀+A₁` as the image of `plus` via the
first isomorphism theorem (`(A₀×A₁)/ker(plus) ≅ image(plus)`). Both kernels are closed (the maps
are continuous into a `T2Space`), so both quotient/submodule constructions are Banach spaces via
existing Mathlib instances, with no from-scratch Cauchy-sequence argument needed.

Both `diff`'s kernel and `plus`'s kernel are needed — they are genuinely different submodules
(related by the sign-flip automorphism `(a₀,a₁) ↦ (a₀,-a₁)` on `A₁`, not literally equal). An
earlier version of this file mistakenly quotiented by the *same* kernel (`diff`'s) for both,
which made the canonical `meet → sum` map identically zero (every element of the kernel you
quotient by is trivially killed by that same quotient) — a real bug, only caught once we tried
to actually construct the interpolation functors `∩`/`+` themselves and needed that map to be
meaningful. The norms obtained this way (`Prod`'s max-norm, restricted resp. quotiented) are
equivalent to, but not literally equal to, Triebel's `max(‖a₀‖,‖a₁‖)` and `inf ‖a₀‖+‖a₁‖` — an
acceptable trade since interpolation theory works up to norm equivalence throughout.
-/

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*} [NormedAddCommGroup A₀] [NormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [NormedAddCommGroup A₁] [NormedSpace 𝕜 A₁] [CompleteSpace A₁]

/-- The continuous linear map `(a₀, a₁) ↦ ι₀ a₀ - ι₁ a₁` on the product. Its kernel realizes
`A₀ ∩ A₁` and its induced quotient realizes `A₀ + A₁`. -/
noncomputable def InterpolationCouple.diff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    (A₀ × A₁) →L[𝕜] 𝒜 :=
  ι₀.comp (ContinuousLinearMap.fst 𝕜 A₀ A₁) - ι₁.comp (ContinuousLinearMap.snd 𝕜 A₀ A₁)

/-- The continuous linear map `(a₀, a₁) ↦ ι₀ a₀ + ι₁ a₁` on the product. Its kernel is what
`A₀ + A₁` is the quotient by (via the first isomorphism theorem, `(A₀×A₁)/ker(plus) ≅
image(plus) = A₀+A₁`). -/
noncomputable def InterpolationCouple.plus (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    (A₀ × A₁) →L[𝕜] 𝒜 :=
  ι₀.comp (ContinuousLinearMap.fst 𝕜 A₀ A₁) + ι₁.comp (ContinuousLinearMap.snd 𝕜 A₀ A₁)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The kernel of `diff` is closed, since `diff` is continuous into a Hausdorff space. -/
theorem InterpolationCouple.isClosed_ker_diff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    IsClosed ((InterpolationCouple.diff ι₀ ι₁).ker : Set (A₀ × A₁)) :=
  isClosed_singleton.preimage (InterpolationCouple.diff ι₀ ι₁).continuous

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The kernel of `plus` is closed, since `plus` is continuous into a Hausdorff space. -/
theorem InterpolationCouple.isClosed_ker_plus (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    IsClosed ((InterpolationCouple.plus ι₀ ι₁).ker : Set (A₀ × A₁)) :=
  isClosed_singleton.preimage (InterpolationCouple.plus ι₀ ι₁).continuous

/-- `A₀ ∩ A₁`, realized as the (closed) kernel submodule of `diff` inside `A₀ × A₁`. -/
noncomputable def InterpolationCouple.meet (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    Submodule 𝕜 (A₀ × A₁) :=
  (InterpolationCouple.diff ι₀ ι₁).ker

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.mem_meet_iff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a₀ : A₀) (a₁ : A₁) :
    (a₀, a₁) ∈ InterpolationCouple.meet ι₀ ι₁ ↔ ι₀ a₀ = ι₁ a₁ := by
  simp [InterpolationCouple.meet, InterpolationCouple.diff, LinearMap.mem_ker, sub_eq_zero]

noncomputable instance InterpolationCouple.meet.completeSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    CompleteSpace (InterpolationCouple.meet ι₀ ι₁) :=
  (InterpolationCouple.isClosed_ker_diff ι₀ ι₁).completeSpace_coe

/-- `A₀ + A₁`, realized as the quotient of `A₀ × A₁` by the (closed) kernel of `plus`. -/
def InterpolationCouple.sum (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) : Type _ :=
  (A₀ × A₁) ⧸ (InterpolationCouple.plus ι₀ ι₁).ker

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.mem_ker_plus_iff
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a₀ : A₀) (a₁ : A₁) :
    (a₀, a₁) ∈ (InterpolationCouple.plus ι₀ ι₁).ker ↔ ι₀ a₀ = -ι₁ a₁ := by
  simp [InterpolationCouple.plus, LinearMap.mem_ker, eq_neg_iff_add_eq_zero]

noncomputable instance InterpolationCouple.sum.normedAddCommGroup
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    NormedAddCommGroup (InterpolationCouple.sum ι₀ ι₁) :=
  Submodule.Quotient.normedAddCommGroup (S := (InterpolationCouple.plus ι₀ ι₁).ker)
    (hS := InterpolationCouple.isClosed_ker_plus ι₀ ι₁)

noncomputable instance InterpolationCouple.sum.completeSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    CompleteSpace (InterpolationCouple.sum ι₀ ι₁) :=
  Submodule.Quotient.completeSpace (InterpolationCouple.plus ι₀ ι₁).ker

noncomputable instance InterpolationCouple.sum.normedSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    NormedSpace 𝕜 (InterpolationCouple.sum ι₀ ι₁) :=
  Submodule.Quotient.normedSpace 𝕜 (S := (InterpolationCouple.plus ι₀ ι₁).ker)

/-- The canonical continuous linear map `A₀ →L[𝕜] A₀ + A₁`, `a₀ ↦ [(a₀, 0)]`. -/
noncomputable def InterpolationCouple.inl₀ (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    A₀ →L[𝕜] InterpolationCouple.sum ι₀ ι₁ :=
  (InterpolationCouple.plus ι₀ ι₁).ker.mkQL.comp (ContinuousLinearMap.inl 𝕜 A₀ A₁)

/-- The canonical continuous linear map `A₁ →L[𝕜] A₀ + A₁`, `a₁ ↦ [(0, a₁)]`. -/
noncomputable def InterpolationCouple.inl₁ (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    A₁ →L[𝕜] InterpolationCouple.sum ι₀ ι₁ :=
  (InterpolationCouple.plus ι₀ ι₁).ker.mkQL.comp (ContinuousLinearMap.inr 𝕜 A₀ A₁)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
@[simp]
theorem InterpolationCouple.inl₀_eq_mk (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₀) :
    InterpolationCouple.inl₀ ι₀ ι₁ a = Submodule.Quotient.mk (a, 0) := rfl

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
@[simp]
theorem InterpolationCouple.inl₁_eq_mk (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₁) :
    InterpolationCouple.inl₁ ι₀ ι₁ a = Submodule.Quotient.mk (0, a) := rfl

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₀_eq_zero_iff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₀) :
    InterpolationCouple.inl₀ ι₀ ι₁ a = 0 ↔ ι₀ a = 0 := by
  change (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (a, 0) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, InterpolationCouple.mem_ker_plus_iff]
  simp

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₁_eq_zero_iff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₁) :
    InterpolationCouple.inl₁ ι₀ ι₁ a = 0 ↔ ι₁ a = 0 := by
  change (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (0, a) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, InterpolationCouple.mem_ker_plus_iff]
  simp

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₀_injective (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    (hι₀ : Function.Injective ι₀) :
    Function.Injective (InterpolationCouple.inl₀ ι₀ ι₁) := by
  intro a b hab
  have h0 : InterpolationCouple.inl₀ ι₀ ι₁ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [InterpolationCouple.inl₀_eq_zero_iff, map_sub] at h0
  exact hι₀ (sub_eq_zero.mp h0)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₁_injective (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    (hι₁ : Function.Injective ι₁) :
    Function.Injective (InterpolationCouple.inl₁ ι₀ ι₁) := by
  intro a b hab
  have h0 : InterpolationCouple.inl₁ ι₀ ι₁ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [InterpolationCouple.inl₁_eq_zero_iff, map_sub] at h0
  exact hι₁ (sub_eq_zero.mp h0)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- For `(a₀,a₁)` in the meet (so `ι₀ a₀ = ι₁ a₁`, a single point of the ambient space reachable
from both legs), its images in the sum space via either leg agree: `[(a₀,0)] = [(0,a₁)]`. This is
what makes `meetToSum` (using only the `A₀` leg) the right, symmetric notion of "the meet, viewed
inside the sum". -/
theorem InterpolationCouple.inl₀_fst_eq_inl₁_snd (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    {a₀ : A₀} {a₁ : A₁} (h : ι₀ a₀ = ι₁ a₁) :
    InterpolationCouple.inl₀ ι₀ ι₁ a₀ = InterpolationCouple.inl₁ ι₀ ι₁ a₁ := by
  change (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (a₀, 0) =
    (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (0, a₁)
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    InterpolationCouple.mem_ker_plus_iff]
  simpa using h

/-- The canonical continuous linear map `A₀ ∩ A₁ →L[𝕜] A₀ + A₁`: `(a₀,a₁) ↦ [(a₀,0)]` (which,
by `inl₀_fst_eq_inl₁_snd`, agrees with `[(0,a₁)]` — the meet, viewed inside the sum). -/
noncomputable def InterpolationCouple.meetToSum (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    InterpolationCouple.meet ι₀ ι₁ →L[𝕜] InterpolationCouple.sum ι₀ ι₁ :=
  (InterpolationCouple.inl₀ ι₀ ι₁).comp
    ((ContinuousLinearMap.fst 𝕜 A₀ A₁).comp (InterpolationCouple.meet ι₀ ι₁).subtypeL)

/-- Scoped notation `ι₀ ∩ ι₁` for `InterpolationCouple.meet` and `ι₀ + ι₁` for
`InterpolationCouple.sum`, matching Triebel's own `A₀ ∩ A₁` / `A₀ + A₁` literally. Scoped (needs
`open scoped InterpolationCouple`) so it doesn't shadow `Set`/`Submodule`'s `∩`/`+` elsewhere.

NOTE for later: this notation currently takes the *embedding maps* `ι₀, ι₁` as arguments, not the
Banach spaces `A₀, A₁` themselves, since nothing yet determines a canonical embedding from a type
alone. Once canonical embeddings exist for concrete spaces (e.g. `Lp` spaces embedding into `𝒟'`
or `𝒮'`), it will likely read better for this notation to apply directly to `A₀, A₁` (with the
embedding found automatically) rather than to `ι₀, ι₁` explicitly — deliberately not acted on
yet, flagged here for when that machinery exists. -/
scoped[InterpolationCouple] notation:70 ι₀ " ∩ " ι₁ => InterpolationCouple.meet ι₀ ι₁

scoped[InterpolationCouple] notation:65 ι₀ " + " ι₁ => InterpolationCouple.sum ι₀ ι₁
