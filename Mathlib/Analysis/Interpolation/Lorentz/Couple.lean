/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.InterpolationCat
import Mathlib.MeasureTheory.Function.LorentzSpace.ToL0

/-!
# The interpolation couple of two Lorentz spaces

For `0 < q₀, q₁`, the Lorentz spaces `L_{p₀,q₀}(μ)` and `L_{p₁,q₁}(μ)` form an interpolation couple
(Triebel §1.2.1), with ambient space `L⁰(μ)` (`MeasureTheory.L0`, convergence in measure on
finite-measure sets) and the inclusions `LorentzSpace.toL0` as embeddings.

The hypotheses are exactly those needed by the pieces:
* `[CompleteSpace E]`, for `CompleteSpace (LorentzSpace E p q μ)`;
* `[Fact (0 < qᵢ)]`, for the quasinorm (at `q = 0` the Lorentz "quasinorm" is constantly `1`);
* `[SigmaFinite μ]`, for `T2Space (L0 α E μ)`.

## Main definitions
* `InterpolationCat.lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁`: the couple `(L_{p₀,q₀}, L_{p₁,q₁})` over
  `L⁰(μ)`.
-/

open MeasureTheory
open scoped ENNReal

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace InterpolationCat

/-- The interpolation couple `(L_{p₀,q₀}(μ), L_{p₁,q₁}(μ))`, embedded in `L⁰(μ)`. -/
noncomputable def lorentzCouple (p₀ q₀ p₁ q₁ : ℝ≥0∞) [Fact (0 < q₀)] [Fact (0 < q₁)] :
    InterpolationCat 𝕜 where
  𝒜 := L0 α E μ
  A₀ := LorentzSpace E p₀ q₀ μ
  A₁ := LorentzSpace E p₁ q₁ μ
  ι₀ := LorentzSpace.toL0 μ E 𝕜 p₀ q₀
  ι₁ := LorentzSpace.toL0 μ E 𝕜 p₁ q₁
  injective₀ := LorentzSpace.toL0ₗ_injective μ p₀ q₀
  injective₁ := LorentzSpace.toL0ₗ_injective μ p₁ q₁

variable (p₀ q₀ p₁ q₁ : ℝ≥0∞) [Fact (0 < q₀)] [Fact (0 < q₁)]

theorem lorentzCouple_𝒜 : (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).𝒜 = L0 α E μ := rfl

theorem lorentzCouple_A₀ : (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).A₀ = LorentzSpace E p₀ q₀ μ := rfl

theorem lorentzCouple_A₁ : (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).A₁ = LorentzSpace E p₁ q₁ μ := rfl

@[simp]
theorem lorentzCouple_ι₀ :
    (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).ι₀ = LorentzSpace.toL0 μ E 𝕜 p₀ q₀ := rfl

@[simp]
theorem lorentzCouple_ι₁ :
    (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).ι₁ = LorentzSpace.toL0 μ E 𝕜 p₁ q₁ := rfl

/-- The canonical map `L_{p₀,q₀} + L_{p₁,q₁} →L[𝕜] L⁰(μ)`: `InterpolationCouple.sumToAmbient`,
typed with codomain `L0 α E μ` (rather than the defeq `(lorentzCouple …).𝒜`), so that its values
coerce to functions `α → E`. -/
noncomputable def lorentzSumToL0 :
    InterpolationCouple.sum (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).ι₀
      (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).ι₁ →L[𝕜] L0 α E μ :=
  InterpolationCouple.sumToAmbient _ _

theorem lorentzSumToL0_eq :
    lorentzSumToL0 𝕜 μ E p₀ q₀ p₁ q₁ =
      InterpolationCouple.sumToAmbient (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).ι₀
        (lorentzCouple 𝕜 μ E p₀ q₀ p₁ q₁).ι₁ := rfl

theorem lorentzSumToL0_mk (a₀ : LorentzSpace E p₀ q₀ μ) (a₁ : LorentzSpace E p₁ q₁ μ) :
    lorentzSumToL0 𝕜 μ E p₀ q₀ p₁ q₁ (Submodule.Quotient.mk (a₀, a₁)) =
      LorentzSpace.toL0 μ E 𝕜 p₀ q₀ a₀ + LorentzSpace.toL0 μ E 𝕜 p₁ q₁ a₁ :=
  rfl

end InterpolationCat
