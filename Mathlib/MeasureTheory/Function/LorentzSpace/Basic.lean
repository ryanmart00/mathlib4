/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Interpolation.QuasiNorm

/-!
# Lorentz spaces

DRAFT — statement-design stage, pending review-gate sign-off (see `PROGRESS-interpolation-theory.md`
in the repository root's `lean/` directory, Unit 6). Not yet part of the classical
`Analysis/Interpolation/LpLorentz.lean` file: this file gives the Lorentz spaces `L_{p,q}(μ)` a real
**bundled type**, mirroring `MeasureTheory.Lp` (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
as closely as possible, one file at a time (`Basic.lean` here corresponds to `LpSpace/Basic.lean`;
a `Complete.lean` proving `CompleteSpace` is expected to follow, mirroring `LpSpace/Complete.lean`).

Per Ryan (2026-09-20): unlike `Lp`, which is genuinely normed for `1 ≤ p`, `LorentzLp` is given
only a `QuasinormedAddCommGroup` instance here, for **all** `p, q` — the literal `f*`-based Lorentz
quasinorm is not a genuine norm even for `p > 1` (Hunt's maximal-function `f**` trick is needed for
that, and is *not* attempted here). This is exactly the case the quasi-Banach generalization
(`Analysis/Interpolation/QuasiNorm.lean` etc.) was built to accommodate. The fact that `L_{p,p}`
recovers the genuine `Lᵖ` norm (up to a `QuasiNormEquiv`, or perhaps literal equality — open
question, not yet settled) is deferred to a later theorem, once this bundled type exists.

## Main definitions
* `distributionFunction`, `decreasingRearrangement` (Triebel §1.18.6) — moved here verbatim from
  `Analysis/Interpolation/LpLorentz.lean`, unchanged.
* `lorentzNorm p q μ f` — the Lorentz `L_{p,q}` (quasi-)norm, Triebel's formula — moved here
  verbatim as well.
* `LorentzLp E p q μ` — the bundled Lorentz space: elements of `α →ₘ[μ] E`
  (`MeasureTheory.AEEqFun`) with `lorentzNorm p q μ f < ∞`, as an `AddSubgroup`, exactly mirroring
  `MeasureTheory.Lp`'s own definition.

## Main results (all `sorry` — Definitions/Statement phase only, no proof attempted yet)
* `LorentzLp.instQuasinormedAddCommGroup` — the `QuasinormedAddCommGroup (LorentzLp E p q μ)`
  instance. Its constant and all three defining inequalities are `sorry`; nailing these down needs
  a Hardy–Littlewood-type rearrangement inequality (`(f+g)* (t) ≤ f*(t/2) + g*(t/2)`, or similar)
  that has not been researched/derived yet.

## Implementation notes

`LorentzLp` is *not yet* wired through `Module`/`ContinuousSMul`/`CompleteSpace` — those are the
natural next additions (mirroring `Lp`'s own later sections in the same file, and its separate
`Complete.lean`), deferred until this skeleton itself is signed off.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
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

variable (p q : ℝ≥0∞)

/-- The Lorentz space `L_{p,q}(μ)`: elements of `α →ₘ[μ] E` such that `lorentzNorm p q μ f < ∞`.
Mirrors `MeasureTheory.Lp` exactly (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`), with
`lorentzNorm` in place of `eLpNorm`. Membership-closure proofs deferred (`sorry`) pending
statement sign-off, per this project's workflow. -/
noncomputable def LorentzLp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lorentzNorm μ p q f < ∞ }
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

namespace LorentzLp

/-- Coercion straight to functions `α → E`, bypassing the intermediate `α →ₘ[μ] E` — mirrors
`MeasureTheory.Lp.instCoeFun` exactly (needed so `lorentzNorm μ p q f` elaborates for
`f : LorentzLp E p q μ` below). -/
noncomputable instance instCoeFun : CoeFun (LorentzLp E p q μ) (fun _ => α → E) :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

/-- The Lorentz quasinorm on `LorentzLp E p q μ`, via `ENNReal.toReal (lorentzNorm ...)` —
mirrors `MeasureTheory.Lp.instNorm` exactly. -/
noncomputable instance instNorm : Norm (LorentzLp E p q μ) where
  norm f := (lorentzNorm μ p q f).toReal

/-- **Pending**: the `QuasinormedAddCommGroup` instance on `LorentzLp E p q μ`. Per Ryan's
2026-09-20 decision, this is a genuine *quasi*-norm (not upgraded to a real norm here, even for
`p > 1` — that would need Hunt's `f**` maximal-function construction, out of scope). Every field is
`sorry`, including the bundled topology ones: the quasi-triangle constant itself is not yet
known/derived, so none of the topology defaults (which are literally built *from* it via
`AddGroupFilterBasis.ofQuasiNorm`) can even be computed yet, hence all fields are given explicitly
rather than relying on the class's default mechanism. -/
noncomputable instance instQuasinormedAddCommGroup :
    QuasinormedAddCommGroup (LorentzLp E p q μ) where
  quasiTriangleConst := sorry
  one_le_quasiTriangleConst := sorry
  norm_add_le := sorry
  norm_neg := sorry
  norm_eq_zero_iff := sorry
  toUniformSpace := sorry
  toIsTopologicalAddGroup := sorry
  toIsUniformAddGroup := sorry
  nhds_zero_hasBasis := sorry

end LorentzLp
