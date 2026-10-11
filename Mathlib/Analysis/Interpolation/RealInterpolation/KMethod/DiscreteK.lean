/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.KInterpolation
import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-!
# The discrete K-method

Bergh–Löfström Lemma 3.1.3 (Triebel §1.7, part (a)): the `(θ,q)` K-quasinorm of `a ∈ A₀ + A₁`
is equivalent to the `ℓ^q(ℤ)` quasinorm of the sequence `ν ↦ 2^{-νθ} K(2^ν, a)`. On each dyadic
interval `2^ν ≤ t ≤ 2^{ν+1}` one has `K(2^ν, a) ≤ K(t, a) ≤ 2 K(2^ν, a)`, and
`∫_{2^ν}^{2^{ν+1}} dt/t = log 2`, whence the constants `2^{-θ} (log 2)^{1/q}` and `2 (log 2)^{1/q}` (read as `1` when
`q = ∞`, since then `q⁻¹.toReal = 0`).

The discrete form is what the equivalence theorem `K = J` (`JMethod/Equivalence.lean`) compares
with the discrete J-method.

## Main definitions
* `InterpolationCouple.kSequenceENorm θ q a`: `‖(2^{-νθ} K(2^ν, a))ᵥ‖_{ℓ^q}`.

## Main statements
* `ofReal_mul_kSequenceENorm_le_realInterpolationENorm`,
  `realInterpolationENorm_le_mul_kSequenceENorm`: the two halves of B–L Lemma 3.1.3.
-/

open MeasureTheory
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- The discrete K-method quasinorm: the `ℓ^q(ℤ)` quasinorm of `ν ↦ 2^{-νθ} K(2^ν, a)`
(Bergh–Löfström's `‖(αᵥ)‖_{λ^{θ,q}}` with `αᵥ = K(2^ν, a)`). -/
noncomputable def kSequenceENorm (θ : ℝ) (q : ℝ≥0∞) (a : sum ι₀ ι₁) : ℝ≥0∞ :=
  eLpNorm (fun ν : ℤ => ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a))
    q Measure.count

/-- B–L Lemma 3.1.3, lower half: `2^{-θ} (log 2)^{1/q} ‖(2^{-νθ} K(2^ν, a))‖_{ℓ^q} ≤ ‖a‖_{θ,q}`. -/
theorem ofReal_mul_kSequenceENorm_le_realInterpolationENorm {θ : ℝ} (hθ : 0 ≤ θ) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) :
    ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal *
        kSequenceENorm ι₀ ι₁ θ q a ≤ realInterpolationENorm ι₀ ι₁ θ q a :=
  sorry

/-- B–L Lemma 3.1.3, upper half: `‖a‖_{θ,q} ≤ 2 (log 2)^{1/q} ‖(2^{-νθ} K(2^ν, a))‖_{ℓ^q}`. -/
theorem realInterpolationENorm_le_mul_kSequenceENorm {θ : ℝ} (hθ : 0 ≤ θ) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q a ≤
      2 * ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal * kSequenceENorm ι₀ ι₁ θ q a :=
  sorry

end InterpolationCouple
