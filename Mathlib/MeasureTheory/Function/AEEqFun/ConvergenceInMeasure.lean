/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# The topology of convergence in measure on `α →ₘ[μ] E`

Built to serve as the common ambient topological vector space `𝒜` an `InterpolationCouple`
(`Analysis/Interpolation/Couple.lean`) needs, for a couple of Lorentz (or plain `Lᵖ`) spaces —
neither `α →ₘ[μ] E` (`MeasureTheory.AEEqFun`) nor any variant of it currently carries *any*
topology in Mathlib for general `E`/`μ` (confirmed by a dedicated research pass, 2026-09-20):
each `Lp E p μ`'s own topology comes directly from its own `eLpNorm`, with no shared ambient space
different `p`'s sit inside. This file builds that ambient space from scratch, as genuinely
general-purpose Mathlib content (not couple- or Lorentz-specific), following `TendstoInMeasure`'s
existing convergence-in-measure relation (`ConvergenceInMeasure.lean`) rather than duplicating it.

## Design (per Ryan, 2026-09-20)

The classical "topology of convergence in (local) measure" only has a single clean Ky Fan metric
`d(f,g) = ∫ min(1, edist(f,g)) dμ` when `μ` is *finite*. Since the actual motivating case
(Marcinkiewicz interpolation on `ℝⁿ` with Lebesgue measure) is `SigmaFinite` but genuinely
infinite, that single-metric approach doesn't work as is; instead, following the standard fix for
`σ`-finite spaces, this uses a *countable family* of truncated-`edist` integrals
(`dPart`) over `μ`'s existing exhausting sequence `MeasureTheory.spanningSets μ`
(`[SigmaFinite μ]`, each piece finite measure), each truncated at `1` and
combined into one metric (`measureEdist`) via a `2⁻ⁿ`-weighted sum (the standard Fréchet-metric
construction). The truncation `min 1 (dPart μ n f g)` is essential: `dPart μ n f g` is only bounded
by `μ (spanningSets μ n)`, which may grow arbitrarily fast, and without it a small constant
function could be at distance `⊤` from `0` (so scalar multiplication would not even be continuous).
With it, `measureEdist f g ≤ 2`, and `measureEdist f g` is small iff every `dPart μ n f g` is small,
i.e. iff `f` is close to `g` in measure on every finite-measure piece of `α` — a condition
independent of the particular choice of `spanningSets μ`.

The pointwise `min 1 (edist (f x) (g x))` truncation (rather than the raw `edist`) is what makes
`dPart μ n f g → 0` mean *convergence in measure* on that piece specifically, rather than the
strictly stronger (and wrong, for this purpose) `Lᵖ`-type convergence: `dPart μ n f g` small says
"the *measure* of the set where `f`, `g` differ by more than `ε`, weighted, is small" via the
same truncation trick `TendstoInMeasure` is defined around (`ε ≤ edist (f i x) (g x)`), not "the
*integral* of `‖f-g‖` is small".

## Main definitions
* `AEEqFun.dPart μ n f g`: the truncated-`edist` integral over the `n`-th spanning set — one
  piece of the countable family the full distance is built from.
* `AEEqFun.measureEdist μ f g`: the `2⁻ⁿ`-weighted combination of `min 1 dPart` over all `n`, the
  candidate `edist` for an `EMetricSpace (α →ₘ[μ] E)` instance (not yet built — see the plan in
  `PROGRESS-interpolation-theory.md`).
-/

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable {E : Type*} [NormedAddCommGroup E]

/-- The `n`-th piece of the convergence-in-measure extended distance: the truncated `edist`,
integrated over the `n`-th set of `μ`'s exhausting sequence `MeasureTheory.spanningSets`. -/
noncomputable def AEEqFun.dPart (n : ℕ) (f g : α →ₘ[μ] E) : ℝ≥0∞ :=
  ∫⁻ x in spanningSets μ n, min 1 (edist (f x) (g x)) ∂μ

/-- The convergence-in-measure distance on `α →ₘ[μ] E`: a `2⁻ⁿ`-weighted combination of the
pieces `dPart`, each truncated at `1`, over `μ`'s exhausting sequence, so that `measureEdist f g`
is small iff `f`, `g` are close in measure on every finite-measure piece of `α`. See the module
docstring for why this (rather than a single Ky Fan metric) is needed for genuinely infinite
`σ`-finite `μ`, and why the truncation at `1` is needed. -/
noncomputable def AEEqFun.measureEdist (f g : α →ₘ[μ] E) : ℝ≥0∞ :=
  ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * min 1 (AEEqFun.dPart μ n f g)

/-! ## Toward `EMetricSpace (α →ₘ[μ] E)`

`dPart_self`/`dPart_comm`/`dPart_triangle` are
pointwise truncated-`edist` facts lifted through the integral; `measureEdist_self`/`_comm`/
`_triangle` lift those again through the weighted sum, giving exactly `PseudoEMetricSpace`'s three
defining fields (`Topology/EMetricSpace/Defs.lean`, whose default `toUniformSpace`/
`uniformity_edist` fields need no separate construction here, unlike the `AddGroupFilterBasis`
route `LorentzSpace/Basic.lean` needed). `eq_of_measureEdist_eq_zero` is the remaining
`EMetricSpace` field on top of that. `measureEdist_add_add` (translation invariance) is what will
let the resulting topology's `+` be shown continuous. -/

/-- Truncation at `1` preserves the triangle inequality. -/
theorem ENNReal.min_one_le_add_of_le {a b c : ℝ≥0∞} (h : a ≤ b + c) :
    min 1 a ≤ min 1 b + min 1 c := by
  refine (min_le_min le_rfl h).trans ?_
  by_cases hb : (1 : ℝ≥0∞) ≤ b
  · rw [min_eq_left hb]; exact (min_le_left _ _).trans le_self_add
  by_cases hc : (1 : ℝ≥0∞) ≤ c
  · rw [min_eq_left hc]; exact (min_le_left _ _).trans le_add_self
  rw [min_eq_right (not_le.mp hb).le, min_eq_right (not_le.mp hc).le]
  exact min_le_right _ _

theorem AEEqFun.dPart_self (n : ℕ) (f : α →ₘ[μ] E) : AEEqFun.dPart μ n f f = 0 := by
  unfold AEEqFun.dPart
  simp [edist_self]

theorem AEEqFun.dPart_comm (n : ℕ) (f g : α →ₘ[μ] E) :
    AEEqFun.dPart μ n f g = AEEqFun.dPart μ n g f := by
  unfold AEEqFun.dPart
  simp_rw [edist_comm (f _)]

theorem AEEqFun.dPart_triangle (n : ℕ) (f g h : α →ₘ[μ] E) :
    AEEqFun.dPart μ n f h ≤ AEEqFun.dPart μ n f g + AEEqFun.dPart μ n g h := by
  unfold AEEqFun.dPart
  have hedist : AEStronglyMeasurable (fun x => edist (f x) (g x)) μ :=
    continuous_edist.comp_aestronglyMeasurable₂ f.aestronglyMeasurable g.aestronglyMeasurable
  have hfg : AEMeasurable (fun x => min 1 (edist (f x) (g x))) μ :=
    aemeasurable_const.min hedist.aemeasurable
  rw [← lintegral_add_left' hfg.restrict]
  apply setLIntegral_mono' (measurableSet_spanningSets μ n)
  intro x _
  exact ENNReal.min_one_le_add_of_le (edist_triangle _ _ _)

theorem AEEqFun.measureEdist_self (f : α →ₘ[μ] E) : AEEqFun.measureEdist μ f f = 0 := by
  unfold AEEqFun.measureEdist
  simp [AEEqFun.dPart_self]

theorem AEEqFun.measureEdist_comm (f g : α →ₘ[μ] E) :
    AEEqFun.measureEdist μ f g = AEEqFun.measureEdist μ g f := by
  unfold AEEqFun.measureEdist
  simp_rw [AEEqFun.dPart_comm μ _ f g]

theorem AEEqFun.measureEdist_triangle (f g h : α →ₘ[μ] E) :
    AEEqFun.measureEdist μ f h ≤ AEEqFun.measureEdist μ f g + AEEqFun.measureEdist μ g h := by
  unfold AEEqFun.measureEdist
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← mul_add]
  gcongr
  exact ENNReal.min_one_le_add_of_le (AEEqFun.dPart_triangle μ n f g h)

/-- The crux fact for `EMetricSpace.eq_of_edist_eq_zero`: `dPart μ n f g = 0` for every `n` in
`μ`'s exhausting sequence forces `f =ᵐ[μ] g` on all of `α` (via `iUnion_spanningSets`), hence
`f = g` as elements of `α →ₘ[μ] E`. -/
theorem AEEqFun.eq_of_measureEdist_eq_zero {f g : α →ₘ[μ] E}
    (h : AEEqFun.measureEdist μ f g = 0) : f = g := by
  unfold AEEqFun.measureEdist at h
  rw [ENNReal.tsum_eq_zero] at h
  have hedist : AEStronglyMeasurable (fun x => edist (f x) (g x)) μ :=
    continuous_edist.comp_aestronglyMeasurable₂ f.aestronglyMeasurable g.aestronglyMeasurable
  have hfgmeas : AEMeasurable (fun x => min 1 (edist (f x) (g x))) μ :=
    aemeasurable_const.min hedist.aemeasurable
  have hae : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ spanningSets μ n → f x = g x := by
    intro n
    have hdpart : AEEqFun.dPart μ n f g = 0 := by
      rcases mul_eq_zero.mp (h n) with h1 | h1
      · exact absurd h1 (pow_ne_zero n (by simp))
      · rcases le_total 1 (AEEqFun.dPart μ n f g) with hd | hd
        · exact absurd (min_eq_left hd ▸ h1) one_ne_zero
        · exact min_eq_right hd ▸ h1
    rw [AEEqFun.dPart, setLIntegral_eq_zero_iff' (measurableSet_spanningSets μ n)
      hfgmeas.restrict] at hdpart
    filter_upwards [hdpart] with x hx hxs
    rcases le_total (edist (f x) (g x)) 1 with hle | hle
    · rw [min_eq_right hle] at hx
      exact edist_eq_zero.mp (hx hxs)
    · rw [min_eq_left hle] at hx
      exact absurd (hx hxs) one_ne_zero
  have hglobal : f =ᵐ[μ] g := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (iUnion_spanningSets μ ▸ mem_univ x)
    exact hx n hn
  exact AEEqFun.ext hglobal

/-- Translation invariance of `measureEdist`, needed for `+` to be continuous on the resulting
topology. -/
theorem AEEqFun.measureEdist_add_add (f g h : α →ₘ[μ] E) :
    AEEqFun.measureEdist μ (f + h) (g + h) = AEEqFun.measureEdist μ f g := by
  unfold AEEqFun.measureEdist
  refine tsum_congr fun n => ?_
  congr 2
  unfold AEEqFun.dPart
  refine setLIntegral_congr_fun_ae (measurableSet_spanningSets μ n) ?_
  filter_upwards [AEEqFun.coeFn_add f h, AEEqFun.coeFn_add g h] with x hxf hxg _
  show min 1 (edist ((f + h) x) ((g + h) x)) = min 1 (edist (f x) (g x))
  rw [hxf, hxg]
  simp only [Pi.add_apply]
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub,
    show f x + h x - (g x + h x) = f x - g x by abel]
