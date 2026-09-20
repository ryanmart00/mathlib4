/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.TriangleInequality
import Mathlib.Analysis.Interpolation.QuasiNorm

/-!
# Lorentz spaces: the bundled type

Mirrors `MeasureTheory.Lp` (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`) as closely as
possible: `LorentzLp E p q μ`, the Lorentz space `L_{p,q}(μ)` as an `AddSubgroup (α →ₘ[μ] E)`, cut
out by `lorentzNorm p q μ f < ∞` in place of `eLpNorm f p μ < ∞`. A `Complete.lean` proving
`CompleteSpace` is expected to follow, mirroring `LpSpace/Complete.lean`.

Per Ryan (2026-09-20): unlike `Lp`, which is genuinely normed for `1 ≤ p`, `LorentzLp` is given
only a `QuasinormedAddCommGroup` instance here, for **all** `p, q` — the literal `f*`-based Lorentz
quasinorm is not a genuine norm even for `p > 1` (Hunt's maximal-function `f**` trick is needed for
that, and is *not* attempted here). This is exactly the case the quasi-Banach generalization
(`Analysis/Interpolation/QuasiNorm.lean` etc.) was built to accommodate. The fact that `L_{p,p}`
recovers the genuine `Lᵖ` norm (up to a `QuasiNormEquiv`, or perhaps literal equality — open
question, not yet settled) is deferred to a later theorem, once this bundled type exists.

## Main definitions
* `LorentzLp E p q μ` — the bundled Lorentz space, mirroring `MeasureTheory.Lp`'s own definition.
* `LorentzLp.instQuasinormedAddCommGroup` — its `QuasinormedAddCommGroup` instance, using
  `TriangleInequality.lean`'s `lorentzNorm_add_le` for the quasi-triangle inequality. Its
  `norm_eq_zero_iff` field (and, blocked on that alone, the four bundled topology fields) is the
  one remaining gap: it needs `lorentzNorm p q μ f = 0 → f =ᵐ[μ] 0`, a genuine limiting argument
  not yet proved.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]
variable (p q : ℝ≥0∞)

/-- The Lorentz space `L_{p,q}(μ)`: elements of `α →ₘ[μ] E` such that `lorentzNorm p q μ f < ∞`.
Mirrors `MeasureTheory.Lp` exactly (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`), with
`lorentzNorm` in place of `eLpNorm`. -/
noncomputable def LorentzLp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lorentzNorm μ p q f < ∞ }
  zero_mem' := by
    rw [Set.mem_ofPred_eq, lorentzNorm_congr_ae p q AEEqFun.coeFn_zero]
    exact (lorentzNorm_zero_le_one p q).trans_lt ENNReal.one_lt_top
  add_mem' {f g} hf hg := by
    rw [Set.mem_ofPred_eq] at hf hg ⊢
    rw [lorentzNorm_congr_ae p q (AEEqFun.coeFn_add f g)]
    refine lt_of_le_of_lt (lorentzNorm_add_le p q f g) ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num))
      (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)
  neg_mem' {f} hf := by
    rw [Set.mem_ofPred_eq] at hf ⊢
    rwa [lorentzNorm_congr_ae p q (AEEqFun.coeFn_neg f), lorentzNorm_neg]

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

/-- **Pending**: `norm_eq_zero_iff` (and, blocked on it alone, the four bundled topology fields —
see the module docstring) are the only remaining gaps in this instance. Every other field now has
a real proof, via `TriangleInequality.lean`'s `lorentzNorm_add_le`/`lorentzNorm_neg`. -/
noncomputable instance instQuasinormedAddCommGroup :
    QuasinormedAddCommGroup (LorentzLp E p q μ) where
  quasiTriangleConst := (2:ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal)
  one_le_quasiTriangleConst := by
    calc (1:ℝ) = (2:ℝ) ^ (0:ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2:ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          positivity
  norm_add_le f g := by
    change (lorentzNorm μ p q (⇑(f + g))).toReal ≤
      (2:ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) * ((lorentzNorm μ p q f).toReal +
        (lorentzNorm μ p q g).toReal)
    have hcoe : ((f + g : LorentzLp E p q μ) : α →ₘ[μ] E) =
        (f : α →ₘ[μ] E) + (g : α →ₘ[μ] E) := rfl
    rw [show (⇑(f + g) : α → E) = ((f + g : LorentzLp E p q μ) : α →ₘ[μ] E) from rfl, hcoe,
      lorentzNorm_congr_ae p q (AEEqFun.coeFn_add (f : α →ₘ[μ] E) g)]
    have hfin : lorentzNorm μ p q (f : α → E) + lorentzNorm μ p q (g : α → E) ≠ ⊤ :=
      (ENNReal.add_lt_top.mpr ⟨f.2, g.2⟩).ne
    have hrpow : (2:ℝ≥0∞) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)).ne
    have key : lorentzNorm μ p q ((f : α → E) + (g : α → E)) ≤
        (2:ℝ≥0∞) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) *
          (lorentzNorm μ p q (f : α → E) + lorentzNorm μ p q (g : α → E)) :=
      lorentzNorm_add_le p q (f : α → E) (g : α → E)
    have hrhsfin : (2:ℝ≥0∞) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) *
        (lorentzNorm μ p q (f : α → E) + lorentzNorm μ p q (g : α → E)) ≠ ⊤ :=
      ENNReal.mul_ne_top hrpow hfin
    have hlhsfin : lorentzNorm μ p q ((f : α → E) + (g : α → E)) ≠ ⊤ :=
      (key.trans_lt (lt_top_iff_ne_top.mpr hrhsfin)).ne
    rw [← ENNReal.toReal_le_toReal hlhsfin hrhsfin] at key
    rw [ENNReal.toReal_mul, ENNReal.toReal_add f.2.ne g.2.ne, ← ENNReal.toReal_rpow] at key
    rwa [show (2:ℝ≥0∞).toReal = (2:ℝ) from rfl] at key
  norm_neg f := by
    change (lorentzNorm μ p q (⇑(-f))).toReal = (lorentzNorm μ p q (⇑f)).toReal
    have hcoe : ((-f : LorentzLp E p q μ) : α →ₘ[μ] E) = -(f : α →ₘ[μ] E) := rfl
    rw [show (⇑(-f) : α → E) = ((-f : LorentzLp E p q μ) : α →ₘ[μ] E) from rfl, hcoe,
      lorentzNorm_congr_ae p q (AEEqFun.coeFn_neg (f : α →ₘ[μ] E)), lorentzNorm_neg]
  norm_eq_zero_iff := sorry
  toUniformSpace := sorry
  toIsTopologicalAddGroup := sorry
  toIsUniformAddGroup := sorry
  nhds_zero_hasBasis := sorry

end LorentzLp
