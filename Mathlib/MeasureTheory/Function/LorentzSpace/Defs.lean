/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lorentz spaces: the defining formulas

The Lorentz `L_{p,q}(μ)` (quasi-)norm, Triebel *Interpolation Theory, Function Spaces,
Differential Operators* §1.18.6, built from the decreasing rearrangement of a function.
Split into its own file, mirroring `MeasureTheory.Function.LpSeminorm.Defs` relative to
`LpSeminorm/TriangleInequality.lean` and `LpSpace/Basic.lean`: the raw formulas here have no
dependency on the bundled `LorentzLp` type (`LorentzSpace/Basic.lean`) or on the quasi-triangle
inequality (`LorentzSpace/TriangleInequality.lean`), and both of those depend on this file, so
this has to be the bottom of that chain to avoid a cycle.

## Main definitions
* `distributionFunction`, `decreasingRearrangement` (Triebel §1.18.6).
* `lorentzNorm p q μ f` — the Lorentz `L_{p,q}` (quasi-)norm.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]

/-- The distribution function `ϱ(f,σ) = μ{x : σ < ‖f x‖}`, Triebel §1.18.6. -/
noncomputable def distributionFunction (f : α → E) (σ : ℝ≥0∞) : ℝ≥0∞ :=
  μ {x | σ < ‖f x‖ₑ}

/-- The decreasing rearrangement `f*(t) = inf{σ : ϱ(f,σ) ≤ t}`, Triebel §1.18.6. -/
noncomputable def decreasingRearrangement (f : α → E) (t : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {σ : ℝ≥0∞ | distributionFunction μ f σ ≤ t}

/-- The Lorentz (quasi-)norm `‖f‖_{L_{p,q}}`, Triebel §1.18.6:
`(∫₀^∞ (t^{1/p} f*(t))^q dt/t)^{1/q}` for `q < ∞`, `sup_t t^{1/p} f*(t)` for `q = ∞`. -/
noncomputable def lorentzNorm (p q : ℝ≥0∞) (f : α → E) : ℝ≥0∞ :=
  if q = ⊤ then
    ⨆ t : ℝ≥0, ENNReal.ofNNReal t ^ p⁻¹.toReal *
      decreasingRearrangement μ f (ENNReal.ofNNReal t)
  else
    (∫⁻ t in Ioi (0 : ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal *
        decreasingRearrangement μ f (ENNReal.ofReal t)) ^ q.toReal * ENNReal.ofReal t⁻¹)
      ^ q⁻¹.toReal
