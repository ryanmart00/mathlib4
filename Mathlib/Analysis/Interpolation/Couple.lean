/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Interpolation couples

DRAFT — under review, no proof attempted beyond the completeness of `A₀ ⊓ A₁` and `A₀ + A₁`.

Following Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, §1.2.1:
two Banach spaces `A₀, A₁`, both linearly and continuously embedded in a common Hausdorff
topological vector space `𝒜`, form an *interpolation couple*. `A₀ ⊓ A₁` and `A₀ + A₁` are then
Banach spaces in their own right.

Realized here as: `A₀ ⊓ A₁` is the kernel of `(a₀, a₁) ↦ ι₀ a₀ - ι₁ a₁` on `A₀ × A₁` (a closed
submodule, since the map is continuous into a `T2Space`), and `A₀ + A₁` is the quotient of
`A₀ × A₁` by that same kernel. The norms obtained this way (`Prod`'s max-norm, restricted resp.
quotiented) are equivalent to, but not literally equal to, Triebel's `max(‖a₀‖,‖a₁‖)` and
`inf ‖a₀‖+‖a₁‖` — an acceptable trade since interpolation theory works up to norm equivalence
throughout, and it lets completeness come from existing Mathlib quotient/submodule instances
instead of a from-scratch Cauchy-sequence argument.
-/

open scoped Topology

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (𝒜 : Type*) [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*} [NormedAddCommGroup A₀] [NormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [NormedAddCommGroup A₁] [NormedSpace 𝕜 A₁] [CompleteSpace A₁]

/-- The continuous linear map `(a₀, a₁) ↦ ι₀ a₀ - ι₁ a₁` on the product. Its kernel realizes
`A₀ ⊓ A₁` and its induced quotient realizes `A₀ + A₁`. -/
noncomputable def InterpolationCouple.diff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    (A₀ × A₁) →L[𝕜] 𝒜 :=
  ι₀.comp (ContinuousLinearMap.fst 𝕜 A₀ A₁) - ι₁.comp (ContinuousLinearMap.snd 𝕜 A₀ A₁)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The kernel of `diff` is closed, since `diff` is continuous into a Hausdorff space. -/
theorem InterpolationCouple.isClosed_ker_diff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    IsClosed ((InterpolationCouple.diff 𝕜 𝒜 ι₀ ι₁).ker : Set (A₀ × A₁)) :=
  isClosed_singleton.preimage (InterpolationCouple.diff 𝕜 𝒜 ι₀ ι₁).continuous

/-- `A₀ ⊓ A₁`, realized as the (closed) kernel submodule of `diff` inside `A₀ × A₁`. -/
noncomputable def InterpolationCouple.meet (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    Submodule 𝕜 (A₀ × A₁) :=
  (InterpolationCouple.diff 𝕜 𝒜 ι₀ ι₁).ker

noncomputable instance InterpolationCouple.meet.completeSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    CompleteSpace (InterpolationCouple.meet 𝕜 𝒜 ι₀ ι₁) :=
  (InterpolationCouple.isClosed_ker_diff 𝕜 𝒜 ι₀ ι₁).completeSpace_coe

/-- `A₀ + A₁`, realized as the quotient of `A₀ × A₁` by the (closed) kernel of `diff`. -/
def InterpolationCouple.sum (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) : Type _ :=
  (A₀ × A₁) ⧸ InterpolationCouple.meet 𝕜 𝒜 ι₀ ι₁

noncomputable instance InterpolationCouple.sum.normedAddCommGroup
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    NormedAddCommGroup (InterpolationCouple.sum 𝕜 𝒜 ι₀ ι₁) :=
  Submodule.Quotient.normedAddCommGroup (S := InterpolationCouple.meet 𝕜 𝒜 ι₀ ι₁)
    (hS := InterpolationCouple.isClosed_ker_diff 𝕜 𝒜 ι₀ ι₁)

noncomputable instance InterpolationCouple.sum.completeSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    CompleteSpace (InterpolationCouple.sum 𝕜 𝒜 ι₀ ι₁) :=
  Submodule.Quotient.completeSpace (InterpolationCouple.meet 𝕜 𝒜 ι₀ ι₁)
