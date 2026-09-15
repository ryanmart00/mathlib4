/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Basic.NNReal.Defs
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The Riesz-Thorin interpolation theorem

STATEMENT DRAFT — under review, no proof attempted yet.

Scoped for now to scalar-valued (`ℂ`-valued) targets. The general Banach-space-valued target
case needs a Hahn-Banach norming-functional construction that is deferred to a follow-up.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Riesz-Thorin interpolation theorem**, on simple functions, scalar-valued target.

If a `ℂ`-linear map `T` from `Ω₁`-valued `E`-simple functions to `Ω₂`-a.e.-equal `ℂ`-valued
functions is bounded `p₀ → q₀` with constant `C₀` and bounded `p₁ → q₁` with constant `C₁`,
then it is bounded `pθ → qθ` with constant `C₀ ^ (1 - θ) * C₁ ^ θ`, where the interpolated
exponents satisfy `pθ⁻¹ = (1 - θ) • p₀⁻¹ + θ • p₁⁻¹` (and similarly for `qθ`). -/
theorem MeasureTheory.rieszThorin_simpleFunc
    {p₀ p₁ q₀ q₁ pθ qθ : ℝ≥0∞}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpθ : pθ⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hqθ : qθ⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (T : SimpleFunc Ω₁ E →ₗ[ℂ] (Ω₂ →ₘ[μ₂] ℂ))
    {C₀ C₁ : ℝ≥0}
    (hT₀ : ∀ f : SimpleFunc Ω₁ E, eLpNorm (T f) q₀ μ₂ ≤ C₀ * eLpNorm f p₀ μ₁)
    (hT₁ : ∀ f : SimpleFunc Ω₁ E, eLpNorm (T f) q₁ μ₂ ≤ C₁ * eLpNorm f p₁ μ₁) :
    ∀ f : SimpleFunc Ω₁ E,
      eLpNorm (T f) qθ μ₂ ≤ (C₀ : ℝ≥0∞) ^ (1 - θ) * (C₁ : ℝ≥0∞) ^ θ * eLpNorm f pθ μ₁ := by
  sorry
