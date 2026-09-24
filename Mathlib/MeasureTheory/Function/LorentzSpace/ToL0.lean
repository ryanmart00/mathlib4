/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.AEEqFun.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LorentzSpace.Complete

/-!
# The continuous embedding `L_{p,q} ↪ L⁰`

DRAFT — statement-review stage.

Every Lorentz space `LorentzSpace E p q μ` (with `0 < q`) embeds continuously into `L0 α E μ`,
the space of a.e.-classes with the topology of convergence in measure on finite-measure sets. This
provides the maps `ι₀`, `ι₁` of an `InterpolationCouple` (`Analysis/Interpolation/Couple.lean`)
for any pair of Lorentz spaces over the same `μ`, with `L0 α E μ` as the ambient space.

Continuity is the weak-type (Chebyshev) tail bound: a small `lorentzNorm f` forces a small
`distributionFunction μ f σ` (`distributionFunction_le_of_lorentzNorm_top_lt` /
`distributionFunction_le_of_lorentzNorm_finite_lt`), hence a small Ky Fan distance to `0` on
every finite-measure set. No `σ`-finiteness is needed.

## Main definitions
* `LorentzSpace.toL0ₗ`: the inclusion, as a linear map (every `p, q`).
* `LorentzSpace.toL0`: the inclusion, as a continuous linear map (`0 < q`).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
variable (p q : ℝ≥0∞)

namespace LorentzSpace

variable (𝕜 E) in
/-- The inclusion `LorentzSpace E p q μ → L0 α E μ`, as a linear map. -/
noncomputable def toL0ₗ : LorentzSpace E p q μ →ₗ[𝕜] L0 α E μ where
  toFun f := L0.toL0 μ 𝕜 (f : α →ₘ[μ] E)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem toL0ₗ_apply (f : LorentzSpace E p q μ) :
    toL0ₗ μ E 𝕜 p q f = L0.toL0 μ 𝕜 (f : α →ₘ[μ] E) :=
  rfl

theorem toL0ₗ_injective : Function.Injective (toL0ₗ μ E 𝕜 p q) := by
  sorry

/-- The inclusion `L_{p,q} ↪ L⁰` is continuous, for every `p` and every `q > 0`. -/
theorem continuous_toL0ₗ [Fact (0 < q)] : Continuous (toL0ₗ μ E 𝕜 p q) := by
  sorry

variable (𝕜 E) in
/-- The inclusion `LorentzSpace E p q μ → L0 α E μ`, as a continuous linear map. -/
noncomputable def toL0 [Fact (0 < q)] : LorentzSpace E p q μ →L[𝕜] L0 α E μ :=
  ⟨toL0ₗ μ E 𝕜 p q, continuous_toL0ₗ μ p q⟩

end LorentzSpace
