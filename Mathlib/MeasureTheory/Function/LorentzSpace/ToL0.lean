/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.AEEqFun.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LorentzSpace.Complete

/-!
# The continuous embedding `L_{p,q} ↪ L⁰`

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

## Main statements
* `LorentzSpace.eventually_distributionFunction_le`: near `0` in `L_{p,q}`, `ϱ(f, σ) ≤ δ`.
* `LorentzSpace.continuous_toL0ₗ`: the inclusion is continuous.
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

theorem toL0ₗ_injective : Function.Injective (toL0ₗ μ E 𝕜 p q) :=
  fun _ _ h => Subtype.ext h

/-- Weak-type control near `0`: for fixed levels `σ, δ > 0`, every `f` close enough to `0` in
`L_{p,q}` has `ϱ(f, σ) ≤ δ`. -/
theorem eventually_distributionFunction_le [Fact (0 < q)] {σ δ : ℝ≥0∞} (hσ : 0 < σ)
    (hδ : 0 < δ) :
    ∀ᶠ f : LorentzSpace E p q μ in 𝓝 0, distributionFunction μ f σ ≤ δ := by
  have hq0 : q ≠ 0 := (Fact.out : 0 < q).ne'
  have hσ1 : min σ 1 ≠ ⊤ := ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne
  have hδ1 : min δ 1 ≠ ⊤ := ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne
  set σ' : ℝ := (min σ 1).toReal
  have hσ' : 0 < σ' := ENNReal.toReal_pos (lt_min hσ one_pos).ne' hσ1
  have hσle : ENNReal.ofReal σ' ≤ σ := by
    rw [ENNReal.ofReal_toReal hσ1]
    exact min_le_left _ _
  set s : ℝ := (min δ 1).toReal / 2
  have hs : 0 < s := half_pos (ENNReal.toReal_pos (lt_min hδ one_pos).ne' hδ1)
  have h2s : ENNReal.ofReal (2 * s) ≤ δ := by
    rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_toReal hδ1]
    exact min_le_left _ _
  obtain ⟨ε, hε, hkey⟩ : ∃ ε > 0, ∀ f : α → E, lorentzNorm μ p q f < ENNReal.ofReal ε →
      distributionFunction μ f (ENNReal.ofReal σ') ≤ ENNReal.ofReal (2 * s) := by
    by_cases hqt : q = ⊤
    · subst hqt
      exact ⟨(2 * s) ^ p⁻¹.toReal * σ', by positivity, fun f hf =>
        distributionFunction_le_of_lorentzNorm_top_lt_real p f σ' (2 * s) (by positivity) hf⟩
    · have hlog : 0 < Real.log 2 ^ q⁻¹.toReal := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
      exact ⟨s ^ p⁻¹.toReal * σ' * Real.log 2 ^ q⁻¹.toReal, by positivity, fun f hf =>
        distributionFunction_le_of_lorentzNorm_finite_lt_real p q hq0 hqt f σ' s hσ'.le hs hf⟩
  filter_upwards [QuasinormedAddCommGroup.nhds_zero_hasBasis.mem_of_mem hε] with f hf
  have hlt : lorentzNorm μ p q f < ENNReal.ofReal ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt f.2.ne).mpr hf
  exact (distributionFunction_antitone f hσle).trans ((hkey f hlt).trans h2s)

/-- The inclusion `L_{p,q} ↪ L⁰` is continuous, for every `p` and every `q > 0`. -/
theorem continuous_toL0ₗ [Fact (0 < q)] : Continuous (toL0ₗ μ E 𝕜 p q) := by
  refine continuous_of_tendsto_nhds_zero (toL0ₗ μ E 𝕜 p q) ?_
  rw [L0.tendsto_iff_tendstoInMeasure]
  intro s _ _ ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  filter_upwards [eventually_distributionFunction_le μ p q (ENNReal.half_pos hε.ne') hδ]
    with f hf
  refine (Measure.restrict_apply_le _ _).trans ((measure_mono_ae ?_).trans hf)
  filter_upwards [AEEqFun.coeFn_zero (μ := μ) (β := E)] with x hx
  intro (hmem : ε ≤ edist ((f : α →ₘ[μ] E) x) ((0 : α →ₘ[μ] E) x))
  rw [hx, Pi.zero_apply, edist_zero_right] at hmem
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top enorm_ne_top hmem
  exact (ENNReal.half_lt_self hε.ne' hεt).trans_le hmem

variable (𝕜 E) in
/-- The inclusion `LorentzSpace E p q μ → L0 α E μ`, as a continuous linear map. -/
noncomputable def toL0 [Fact (0 < q)] : LorentzSpace E p q μ →L[𝕜] L0 α E μ :=
  ⟨toL0ₗ μ E 𝕜 p q, continuous_toL0ₗ μ p q⟩

end LorentzSpace
