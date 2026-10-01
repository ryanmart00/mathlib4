/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Quasi.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The Aoki–Rolewicz theorem

DRAFT — statements only.

Let `E` be a quasi-normed group with quasi-triangle constant `C ≥ 1`, i.e.
`‖x + y‖ ≤ C (‖x‖ + ‖y‖)`. Put `ρ = 1 / (1 + log₂ C) ∈ (0, 1]`, so that `C = 2^{1/ρ - 1}`
(`aokiRolewiczExponent`). The **Aoki–Rolewicz theorem** says that `E` carries an equivalent
`ρ`-norm: a function `N` with `N(x + y)^ρ ≤ N(x)^ρ + N(y)^ρ` and `N ≤ ‖·‖ ≤ 4^{1/ρ} N`. We take
`N(x) = inf (∑ ‖xᵢ‖^ρ)^{1/ρ}` over finite decompositions `x = ∑ xᵢ` (`aokiRolewiczNorm`).

The analytic content is the finite-sum bound `‖∑ xᵢ‖ ≤ 4^{1/ρ} (∑ ‖xᵢ‖^ρ)^{1/ρ}`
(`norm_sum_le_rpow`, Kalton–Peck–Roberts, *An F-space sampler*, Theorem 1.3). The `ρ`-norm
properties follow from it formally. As a consequence, the same bound holds for `‖∑' xᵢ‖` whenever
`∑ ‖xᵢ‖^ρ < ∞` (`norm_tsum_le_rpow`), and in a complete quasi-normed group such a family is
summable (`summable_of_summable_norm_rpow`). A quasi-norm need not be continuous, so
the bound on `‖∑' xᵢ‖` goes through the `ρ`-norm, whose `ρ`-th power is subadditive.

This is what makes the discrete J-method of real interpolation work for quasi-Banach couples
(Bergh–Löfström, *Interpolation Spaces*, Lemma 3.10.1 and §3.11).

## Main definitions
* `QuasinormedAddCommGroup.aokiRolewiczExponent E`: `ρ = 1 / (1 + log₂ C)`.
* `QuasinormedAddCommGroup.aokiRolewiczNorm`: the equivalent `ρ`-norm.

## Main results
* `QuasinormedAddCommGroup.norm_sum_le_rpow`: the finite-sum bound.
* `QuasinormedAddCommGroup.aokiRolewiczNorm_add_rpow_le`, `aokiRolewiczNorm_le_norm`,
  `norm_le_aokiRolewiczNorm`: the `ρ`-norm and its equivalence with `‖·‖`.
* `QuasinormedAddCommGroup.summable_of_summable_norm_rpow`, `norm_tsum_le_rpow`: series.
-/

namespace QuasinormedAddCommGroup

variable (E : Type*) [QuasinormedAddCommGroup E]

/-- The Aoki–Rolewicz exponent `ρ = 1 / (1 + log₂ C)` of a quasi-normed group with
quasi-triangle constant `C`. It satisfies `0 < ρ ≤ 1` and `C = 2^{1/ρ - 1}`. -/
noncomputable def aokiRolewiczExponent : ℝ :=
  (1 + Real.logb 2 (quasiTriangleConst (E := E)))⁻¹

theorem one_le_inv_aokiRolewiczExponent : 1 ≤ (aokiRolewiczExponent E)⁻¹ := by
  rw [aokiRolewiczExponent, inv_inv, le_add_iff_nonneg_right]
  exact Real.logb_nonneg one_lt_two one_le_quasiTriangleConst

theorem aokiRolewiczExponent_pos : 0 < aokiRolewiczExponent E :=
  inv_pos.mp (one_pos.trans_le (one_le_inv_aokiRolewiczExponent E))

theorem aokiRolewiczExponent_le_one : aokiRolewiczExponent E ≤ 1 := by
  simpa using inv_le_one_of_one_le₀ (one_le_inv_aokiRolewiczExponent E)

theorem quasiTriangleConst_eq_two_rpow :
    quasiTriangleConst (E := E) = (2 : ℝ) ^ ((aokiRolewiczExponent E)⁻¹ - 1) := by
  rw [aokiRolewiczExponent, inv_inv, add_sub_cancel_left,
    Real.rpow_logb two_pos (by norm_num) quasiTriangleConst_pos]

variable {E}

/-- **Aoki–Rolewicz**, finite-sum form: `‖∑ xᵢ‖ ≤ 4^{1/ρ} (∑ ‖xᵢ‖^ρ)^{1/ρ}`. -/
theorem norm_sum_le_rpow {ι : Type*} (s : Finset ι) (x : ι → E) :
    ‖∑ i ∈ s, x i‖ ≤ (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ *
      (∑ i ∈ s, ‖x i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ := by
  sorry

/-- The Aoki–Rolewicz `ρ`-norm: `N(x) = inf (∑ ‖yᵢ‖^ρ)^{1/ρ}` over finite decompositions
`x = ∑ yᵢ`. -/
noncomputable def aokiRolewiczNorm (x : E) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (y : Fin n → E), ∑ i, y i = x ∧
    (∑ i, ‖y i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ = r}

theorem aokiRolewiczNorm_nonneg (x : E) : 0 ≤ aokiRolewiczNorm x := by
  sorry

theorem aokiRolewiczNorm_le_norm (x : E) : aokiRolewiczNorm x ≤ ‖x‖ := by
  sorry

theorem norm_le_aokiRolewiczNorm (x : E) :
    ‖x‖ ≤ (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ * aokiRolewiczNorm x := by
  sorry

/-- The `ρ`-triangle inequality `N(x + y)^ρ ≤ N(x)^ρ + N(y)^ρ`. -/
theorem aokiRolewiczNorm_add_rpow_le (x y : E) :
    aokiRolewiczNorm (x + y) ^ aokiRolewiczExponent E ≤
      aokiRolewiczNorm x ^ aokiRolewiczExponent E +
        aokiRolewiczNorm y ^ aokiRolewiczExponent E := by
  sorry

theorem aokiRolewiczNorm_neg (x : E) : aokiRolewiczNorm (-x) = aokiRolewiczNorm x := by
  sorry

/-- In a complete quasi-normed group, `∑ ‖xᵢ‖^ρ < ∞` implies that `∑ xᵢ` converges. -/
theorem summable_of_summable_norm_rpow [CompleteSpace E] {ι : Type*} {x : ι → E}
    (h : Summable fun i => ‖x i‖ ^ aokiRolewiczExponent E) : Summable x := by
  sorry

/-- The Aoki–Rolewicz bound for infinite sums: `‖∑' xᵢ‖ ≤ 4^{1/ρ} (∑' ‖xᵢ‖^ρ)^{1/ρ}`. Note that we
do not assume that `∑' i, x i` is summable, and it might not be the case if `E` is not complete. -/
theorem norm_tsum_le_rpow {ι : Type*} {x : ι → E}
    (h : Summable fun i => ‖x i‖ ^ aokiRolewiczExponent E) :
    ‖∑' i, x i‖ ≤ (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ *
      (∑' i, ‖x i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ := by
  sorry

end QuasinormedAddCommGroup
