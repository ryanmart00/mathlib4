/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# The topology of convergence in measure on `α →ₘ[μ] E`

DRAFT — definitions only, no proofs attempted yet (statement-review stage).

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
(`[SigmaFinite μ]`, each piece finite measure), combined into one extended metric
(`measureEdist`) via a `2⁻ⁿ`-weighted sum. `measureEdist f g` is allowed to be genuinely `⊤`
(this is an `EMetricSpace`, not a `MetricSpace`) — only its behaviour *near* `0` needs to match
`TendstoInMeasure`, which is all the weighted-sum construction is built to guarantee: `measureEdist
f g` is small iff every `dPart μ n f g` (`n` ranging over the exhausting sequence) is small, i.e.
iff `f` is close to `g` in measure over every finite-measure piece of `α`.

The pointwise `min 1 (edist (f x) (g x))` truncation (rather than the raw `edist`) is what makes
`dPart μ n f g → 0` mean *convergence in measure* on that piece specifically, rather than the
strictly stronger (and wrong, for this purpose) `Lᵖ`-type convergence: `dPart μ n f g` small says
"the *measure* of the set where `f`, `g` differ by more than `ε`, weighted, is small" via the
same truncation trick `TendstoInMeasure` is defined around (`ε ≤ edist (f i x) (g x)`), not "the
*integral* of `‖f-g‖` is small".

## Main definitions
* `AEEqFun.dPart μ n f g`: the truncated-`edist` integral over the `n`-th spanning set — one
  piece of the countable family the full distance is built from.
* `AEEqFun.measureEdist μ f g`: the `2⁻ⁿ`-weighted combination of `dPart` over all `n`, the
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

/-- The convergence-in-measure extended distance on `α →ₘ[μ] E`: a `2⁻ⁿ`-weighted combination of
`dPart` over `μ`'s exhausting sequence, so that `measureEdist f g` is small iff `f`, `g` are close
in measure on every finite-measure piece of `α`. See the module docstring for why this
(rather than a single Ky Fan metric) is needed for genuinely infinite `σ`-finite `μ`, and why
allowing `measureEdist f g = ⊤` for far-apart `f`, `g` is fine (this is meant to become an
`EMetricSpace`, not a `MetricSpace`). -/
noncomputable def AEEqFun.measureEdist (f g : α →ₘ[μ] E) : ℝ≥0∞ :=
  ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * AEEqFun.dPart μ n f g

/-! ## Toward `EMetricSpace (α →ₘ[μ] E)`

The plan (signed off, no proofs attempted yet): `dPart_self`/`dPart_comm`/`dPart_triangle` are
pointwise truncated-`edist` facts lifted through the integral; `measureEdist_self`/`_comm`/
`_triangle` lift those again through the weighted sum, giving exactly `PseudoEMetricSpace`'s three
defining fields (`Topology/EMetricSpace/Defs.lean`, whose default `toUniformSpace`/
`uniformity_edist` fields need no separate construction here, unlike the `AddGroupFilterBasis`
route `LorentzSpace/Basic.lean` needed). `eq_of_measureEdist_eq_zero` is the remaining
`EMetricSpace` field on top of that. `measureEdist_add_add` (translation invariance) is what will
let the resulting topology's `+` be shown continuous. -/

theorem AEEqFun.dPart_self (n : ℕ) (f : α →ₘ[μ] E) : AEEqFun.dPart μ n f f = 0 := by
  sorry

theorem AEEqFun.dPart_comm (n : ℕ) (f g : α →ₘ[μ] E) :
    AEEqFun.dPart μ n f g = AEEqFun.dPart μ n g f := by
  sorry

theorem AEEqFun.dPart_triangle (n : ℕ) (f g h : α →ₘ[μ] E) :
    AEEqFun.dPart μ n f h ≤ AEEqFun.dPart μ n f g + AEEqFun.dPart μ n g h := by
  sorry

theorem AEEqFun.measureEdist_self (f : α →ₘ[μ] E) : AEEqFun.measureEdist μ f f = 0 := by
  sorry

theorem AEEqFun.measureEdist_comm (f g : α →ₘ[μ] E) :
    AEEqFun.measureEdist μ f g = AEEqFun.measureEdist μ g f := by
  sorry

theorem AEEqFun.measureEdist_triangle (f g h : α →ₘ[μ] E) :
    AEEqFun.measureEdist μ f h ≤ AEEqFun.measureEdist μ f g + AEEqFun.measureEdist μ g h := by
  sorry

/-- The crux fact for `EMetricSpace.eq_of_edist_eq_zero`: `dPart μ n f g = 0` for every `n` in
`μ`'s exhausting sequence forces `f =ᵐ[μ] g` on all of `α` (via `iUnion_spanningSets`), hence
`f = g` as elements of `α →ₘ[μ] E`. -/
theorem AEEqFun.eq_of_measureEdist_eq_zero {f g : α →ₘ[μ] E}
    (h : AEEqFun.measureEdist μ f g = 0) : f = g := by
  sorry

/-- Translation invariance of `measureEdist`, needed for `+` to be continuous on the resulting
topology. -/
theorem AEEqFun.measureEdist_add_add (f g h : α →ₘ[μ] E) :
    AEEqFun.measureEdist μ (f + h) (g + h) = AEEqFun.measureEdist μ f g := by
  sorry
