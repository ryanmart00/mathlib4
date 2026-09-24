/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Hardy's inequality

DRAFT — statement only.

Hardy's inequality on `(0, ∞)` with the Haar measure `dt/t`, in `ℝ≥0∞`-valued form: for
`λ > 0` and `s ≥ 1`,
`∫₀^∞ (t^{-λ} ∫₀ᵗ g)^s dt/t ≤ λ^{-s} ∫₀^∞ (t^{1-λ} g(t))^s dt/t`.

This is the analytic input of the K-method computations for Lorentz spaces (Triebel §1.18.6,
Theorem 1, and Bergh–Löfström §3.4).

## Main results
* `lintegral_hardy`
-/

open MeasureTheory Set
open scoped ENNReal

/-- **Hardy's inequality**: `∫₀^∞ (t^{-λ} ∫₀ᵗ g)^s dt/t ≤ λ^{-s} ∫₀^∞ (t^{1-λ} g(t))^s dt/t`
for measurable `g ≥ 0`, `λ > 0` and `s ≥ 1`. -/
theorem lintegral_hardy {g : ℝ → ℝ≥0∞} (hg : Measurable g) {l s : ℝ} (hl : 0 < l)
    (hs : 1 ≤ s) :
    ∫⁻ t in Ioi 0, (ENNReal.ofReal t ^ (-l) * ∫⁻ u in Ioc 0 t, g u) ^ s * ENNReal.ofReal t⁻¹ ≤
      ENNReal.ofReal l⁻¹ ^ s *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t ^ (1 - l) * g t) ^ s * ENNReal.ofReal t⁻¹ := by
  sorry
