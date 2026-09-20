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

-- None of the lemmas in this block need `[SigmaFinite μ]` (only the classical identification
-- theorems in `Analysis/Interpolation/LpLorentz.lean` do), so it is `omit`ted from each — needed
-- so they apply inside `LorentzLp`'s own definition below, whose signature (mirroring
-- `MeasureTheory.Lp`'s) doesn't carry that instance either.
omit [SigmaFinite μ] in
/-- `distributionFunction` only depends on `f` through its a.e.-equivalence class: altering `f` on
a `μ`-null set doesn't change the measure of any of its super-level sets. Needed so `lorentzNorm`
descends to `α →ₘ[μ] E` (`MeasureTheory.AEEqFun`), exactly as `eLpNorm_congr_ae` does for `eLpNorm`
in `MeasureTheory.Lp`. -/
theorem distributionFunction_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) (σ : ℝ≥0∞) :
    distributionFunction μ f σ = distributionFunction μ g σ := by
  unfold distributionFunction
  apply measure_congr
  filter_upwards [hfg] with x hx
  simp [hx]

omit [SigmaFinite μ] in
theorem decreasingRearrangement_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) (t : ℝ≥0∞) :
    decreasingRearrangement μ f t = decreasingRearrangement μ g t := by
  unfold decreasingRearrangement
  congr 1
  ext σ
  simp only [Set.mem_ofPred_eq, distributionFunction_congr_ae μ hfg]

omit [SigmaFinite μ] in
theorem lorentzNorm_congr_ae (p q : ℝ≥0∞) {f g : α → E} (hfg : f =ᵐ[μ] g) :
    lorentzNorm μ p q f = lorentzNorm μ p q g := by
  unfold lorentzNorm
  simp_rw [decreasingRearrangement_congr_ae μ hfg]

omit [SigmaFinite μ] in
theorem distributionFunction_zero (σ : ℝ≥0∞) : distributionFunction μ (0 : α → E) σ = 0 := by
  unfold distributionFunction
  have : {x : α | σ < ‖(0 : α → E) x‖ₑ} = ∅ := by ext x; simp
  rw [this, measure_empty]

omit [SigmaFinite μ] in
theorem decreasingRearrangement_zero (t : ℝ≥0∞) :
    decreasingRearrangement μ (0 : α → E) t = 0 := by
  unfold decreasingRearrangement
  simp [distributionFunction_zero]

omit [SigmaFinite μ] in
/-- `lorentzNorm` of the zero function is at most `1` (in fact `0` unless `p = q = 0`, an
otherwise-unused degenerate case — `≤ 1` is all that's needed for `LorentzLp.zero_mem'`, and is
uniformly true, so no case restriction on `p, q` is imposed here). -/
theorem lorentzNorm_zero_le_one (p q : ℝ≥0∞) : lorentzNorm μ p q (0 : α → E) ≤ 1 := by
  unfold lorentzNorm
  split
  · simp [decreasingRearrangement_zero]
  · rename_i hqtop
    rcases eq_or_ne q 0 with hq0 | hq0
    · simp [hq0]
    · have hqtoReal : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
      simp [decreasingRearrangement_zero, ENNReal.zero_rpow_of_pos hqtoReal,
        ENNReal.zero_rpow_of_pos (inv_pos.mpr hqtoReal)]

omit [SigmaFinite μ] in
theorem distributionFunction_neg (f : α → E) (σ : ℝ≥0∞) :
    distributionFunction μ (-f) σ = distributionFunction μ f σ := by
  unfold distributionFunction
  congr 1
  ext x
  simp

omit [SigmaFinite μ] in
theorem decreasingRearrangement_neg (f : α → E) (t : ℝ≥0∞) :
    decreasingRearrangement μ (-f) t = decreasingRearrangement μ f t := by
  unfold decreasingRearrangement
  simp_rw [distributionFunction_neg]

omit [SigmaFinite μ] in
theorem lorentzNorm_neg (p q : ℝ≥0∞) (f : α → E) :
    lorentzNorm μ p q (-f) = lorentzNorm μ p q f := by
  unfold lorentzNorm
  simp_rw [decreasingRearrangement_neg]

variable (p q : ℝ≥0∞)

/-- The Lorentz space `L_{p,q}(μ)`: elements of `α →ₘ[μ] E` such that `lorentzNorm p q μ f < ∞`.
Mirrors `MeasureTheory.Lp` exactly (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`), with
`lorentzNorm` in place of `eLpNorm`. `add_mem'` is the one real remaining gap: it needs a
Hardy-Littlewood-type quasi-triangle inequality for `lorentzNorm` that hasn't been derived yet
(tracked together with `LorentzLp.instQuasinormedAddCommGroup.norm_add_le` below). -/
noncomputable def LorentzLp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lorentzNorm μ p q f < ∞ }
  zero_mem' := by
    rw [Set.mem_ofPred_eq, lorentzNorm_congr_ae μ p q AEEqFun.coeFn_zero]
    exact (lorentzNorm_zero_le_one μ p q).trans_lt ENNReal.one_lt_top
  add_mem' := sorry
  neg_mem' {f} hf := by
    rw [Set.mem_ofPred_eq] at hf ⊢
    rwa [lorentzNorm_congr_ae μ p q (AEEqFun.coeFn_neg f), lorentzNorm_neg]

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
