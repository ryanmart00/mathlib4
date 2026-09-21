/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.Basic

/-!
# `L_{p,p} = Lᵖ`

Triebel, *Interpolation Theory, Function Spaces, Differential Operators* §1.18.6, Lemma: the
diagonal Lorentz space `L_{p,p}(μ)` is literally the ordinary `Lᵖ(μ)` space, both at the level of
the raw quasinorm formulas (`lorentzNorm_diag`) and of the bundled types (`LorentzSpace.eq_Lp`).

`lorentzNorm_diag` moved here from `Analysis/Interpolation/LpLorentz.lean` (2026-09-20, statement
review): it is general-purpose Lorentz-space content with no dependence on the interpolation-couple
machinery, matching why `distributionFunction`/`decreasingRearrangement`/`lorentzNorm` themselves
already live in this directory rather than there. Its statement also picked up a genuine fix at
that review: the original draft was universally quantified over every `p : ℝ≥0∞` including `p = 0`,
where it is **false** — at `q = 0` (hence on the diagonal, `p = 0` too), `lorentzNorm` is the
*constant* function `1` (see `LorentzSpace/Basic.lean`'s `instQuasinormedAddCommGroup` docstring,
which is exactly why that instance requires `[Fact (0 < q)]`), while `eLpNorm f 0 μ = 0` always by
Mathlib's own convention. Fixed by adding `0 < p`; the rest of the range `0 < p ≤ ∞` is the genuine
classical statement (at `p = ⊤` an `essSup` identity, at finite `0 < p < ⊤` the classical
rearrangement-preserves-integral/equimeasurability fact `∫₀^∞ f*(t)^p dt = ∫_α ‖f‖^p dμ`).

`LorentzSpace.eq_Lp` is new: since `lorentzNorm_diag` gives *literal* equality of the defining
`ℝ≥0∞`-valued quasinorms (not just an equivalence up to constants), the two bundled types —
both literally `AddSubgroup (α →ₘ[μ] E)` cut out by their respective quasinorm being finite — have
identical carriers, hence are literally equal as `AddSubgroup`s (per Ryan, 2026-09-20: this
settles the "literal equality vs. `QuasiNormEquiv`" open question flagged in
`LorentzSpace/Basic.lean`'s module docstring, in favor of literal equality).

## Main results
* `lorentzNorm_diag`: `‖f‖_{L_{p,p}} = ‖f‖_{Lᵖ}` for `0 < p ≤ ∞`, as raw `ℝ≥0∞` quasinorms.
* `LorentzSpace.eq_Lp`: `LorentzSpace E p p μ = Lp E p μ` for `0 < p ≤ ∞`, as bundled types.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable {E : Type*} [NormedAddCommGroup E]

/-- Triebel §1.18.6, Lemma: `L_{p,p} = Lᵖ`, as raw quasinorms. Needs `0 < p` — see the module
docstring for why the diagonal at `p = 0` is a genuine counterexample, not just an omitted
convenience hypothesis. -/
theorem lorentzNorm_diag {p : ℝ≥0∞} (hp : 0 < p) (f : α → E) :
    lorentzNorm μ p p f = eLpNorm f p μ := by
  sorry

/-- Triebel §1.18.6, Lemma, bundled-type form: the Lorentz space `L_{p,p}(μ)` is literally the
same `AddSubgroup` of `α →ₘ[μ] E` as the ordinary `Lᵖ(μ)`, since the underlying quasinorms agree
exactly (`lorentzNorm_diag`) rather than merely up to equivalence. -/
theorem LorentzSpace.eq_Lp {p : ℝ≥0∞} (hp : 0 < p) :
    LorentzSpace E p p μ = Lp E p μ := by
  sorry
