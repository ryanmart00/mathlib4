/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Quasi.NormedSpace
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The operator quasi-norm

Every continuous linear map between quasi-normed spaces is bounded
(`exists_forall_norm_map_le_mul_norm`), so it has an operator quasi-norm `‖f‖ₒₚ`, the
least `C ≥ 0` with `‖f x‖ ≤ C ‖x‖`. Mathlib's `ContinuousLinearMap.opNorm` needs seminormed groups
on both ends, so it is not available here.

## Main definitions
* `QuasinormedAddCommGroup.opQuasiNorm`, with scoped notation `‖f‖ₒₚ`.

## Main results
* `QuasinormedAddCommGroup.rescale_to_shell`: rescaling into a norm shell.
* `QuasinormedAddCommGroup.exists_forall_norm_map_le_mul_norm`: continuous linear maps are
  bounded.
* `QuasinormedAddCommGroup.le_opQuasiNorm`: `‖f x‖ ≤ ‖f‖ₒₚ * ‖x‖`.

## Notation
* `‖f‖ₒₚ` (scoped in `QuasinormedAddCommGroup`): the operator quasi-norm `opQuasiNorm f` (a
  notation rather than a `Norm` instance, to avoid a diamond; see `opQuasiNorm`).
-/

namespace QuasinormedAddCommGroup

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [QuasinormedAddCommGroup E] [QuasiNormedSpace 𝕜 E]
  [QuasinormedAddCommGroup F] [QuasiNormedSpace 𝕜 F]

/-- Rescale `x` by a power of `c` (any element of norm `> 1`) to land in the "shell"
`[ε/‖c‖, ε)`, tracking the exact scalar used — the zpow-indexed form `rescale_to_shell` is stated
against. Ports `Seminorm.rescale_to_shell_zpow` (`Analysis/Normed/Module/Seminorm/Basic.lean`)
verbatim: that lemma's proof only ever uses the *exact* homogeneity `p (c • x) = ‖c‖ * p x`, never
the triangle inequality, so it transfers unchanged to our quasi-norm via
`QuasiNormedSpace.norm_smul` (also exact, proved from the `≤` axiom). -/
theorem rescale_to_shell_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ}
    (εpos : 0 < ε) {x : E} (hx : ‖x‖ ≠ 0) : ∃ n : ℤ, c ^ n ≠ 0 ∧
    ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧ (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) := by
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (QuasinormedAddCommGroup.norm_nonneg x) (Ne.symm hx)
  have xεpos : 0 < ‖x‖ / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  · show ‖(c ^ (-(n + 1))) • x‖ < ε
    rw [QuasiNormedSpace.norm_smul, zpow_neg, norm_inv, ← div_eq_inv_mul, div_lt_iff₀ cnpos,
      mul_comm, norm_zpow]
    exact (div_lt_iff₀ εpos).1 hn.2
  · show ε / ‖c‖ ≤ ‖(c ^ (-(n + 1))) • x‖
    rw [zpow_neg, div_le_iff₀ cpos, QuasiNormedSpace.norm_smul, norm_inv, norm_zpow,
      zpow_add₀ (ne_of_gt cpos), zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt cpos), one_mul, ← div_eq_inv_mul, le_div_iff₀ (zpow_pos cpos _),
      mul_comm]
    exact (le_div_iff₀ εpos).1 hn.1
  · show ‖(c ^ (-(n + 1)))‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖
    have hre : ε⁻¹ * ‖c‖ * ‖x‖ = ε⁻¹ * ‖x‖ * ‖c‖ := by ring
    rw [zpow_neg, norm_inv, inv_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos), zpow_one, hre,
      ← div_eq_inv_mul]
    gcongr
    exact hn.1

theorem rescale_to_shell {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : ‖x‖ ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  let ⟨_, hn⟩ := rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

/-- A continuous `𝕜`-linear map between quasi-normed spaces is operator-bounded — the fact that
makes `opQuasiNorm` below a genuine bound rather than a possibly-vacuous infimum. Ports
`SemilinearMapClass.bound_of_continuous`'s shell argument: continuity at `0` gives a ball on which
`f` is bounded by `1`, then `rescale_to_shell` moves an arbitrary `x` into that ball and rescales
the bound back. -/
theorem exists_forall_norm_map_le_mul_norm (f : E →L[𝕜] F) :
    ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ := by
  have hf0 : Filter.Tendsto f (nhds 0) (nhds 0) := map_zero f ▸ f.continuous.tendsto 0
  obtain ⟨ε, εpos, hε⟩ := (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).mem_iff.mp
    (hf0 ((QuasinormedAddCommGroup.nhds_zero_hasBasis (E := F)).mem_iff.mpr
      ⟨1, one_pos, subset_rfl⟩))
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcpos : 0 < ‖c‖ := by positivity
  refine ⟨‖c‖ / ε, by positivity, fun x => ?_⟩
  by_cases hx : ‖x‖ = 0
  · have hx0 : x = 0 := (QuasinormedAddCommGroup.norm_eq_zero_iff x).mp hx
    simp [hx0]
  · obtain ⟨d, hd, hdx1, -, hdinv⟩ := rescale_to_shell hc εpos hx
    have hfd : ‖f (d • x)‖ < 1 := hε hdx1
    rw [map_smul, QuasiNormedSpace.norm_smul] at hfd
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
    have hlt : ‖f x‖ < ‖d‖⁻¹ := by
      rw [← one_div, lt_div_iff₀ hdpos]
      rwa [mul_comm] at hfd
    have hthis := hlt.le.trans hdinv
    have heq : ε⁻¹ * ‖c‖ * ‖x‖ = ‖c‖ / ε * ‖x‖ := by ring
    rwa [heq] at hthis

/-- The operator quasi-norm of a continuous linear map between quasi-normed spaces —
`sInf {C ≥ 0 | ∀ x, ‖f x‖ ≤ C * ‖x‖}`, the natural substitute for Mathlib's own operator norm
(`ContinuousLinearMap.opNorm`), which needs genuine `SeminormedAddCommGroup` on both ends and so
isn't available once a leg is only `QuasinormedAddCommGroup`.

Written `‖f‖ₒₚ` (scoped notation). It is deliberately a plain function with a notation, not a
`Norm (E →L[𝕜] F)` instance: for genuinely normed `E, F` (quasi-normed through the bridge
instances) such an instance would be a diamond with Mathlib's `ContinuousLinearMap.hasOpNorm`.
The two have the same formula, but agree only after unfolding `opQuasiNorm`/`opNorm`, not at
instance-reducible transparency. -/
noncomputable def opQuasiNorm (f : E →L[𝕜] F) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖}

@[inherit_doc] scoped notation "‖" f "‖ₒₚ" => opQuasiNorm f

theorem opQuasiNorm_nonempty (f : E →L[𝕜] F) :
    {C : ℝ | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖}.Nonempty :=
  let ⟨C, hC, hCf⟩ := exists_forall_norm_map_le_mul_norm f; ⟨C, hC.le, hCf⟩

theorem opQuasiNorm_nonneg (f : E →L[𝕜] F) : 0 ≤ ‖f‖ₒₚ :=
  le_csInf (opQuasiNorm_nonempty f) (fun _ hC => hC.1)

/-- The defining property of `opQuasiNorm`: it is an actual upper bound, not just an infimum of
candidate bounds. Proved via the standard ε-approximation of an infimum
(`Real.lt_sInf_add_pos`), using `ε / (‖x‖ + 1)` (rather than `ε / ‖x‖`) as the slack so the same
argument covers `x = 0` without a separate case split on `‖x‖`. -/
theorem le_opQuasiNorm (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ₒₚ * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hxpos : (0 : ℝ) < ‖x‖ + 1 := by
    have := QuasinormedAddCommGroup.norm_nonneg x; linarith
  obtain ⟨C, hCmem, hClt⟩ := Real.lt_sInf_add_pos (opQuasiNorm_nonempty f) (div_pos hε hxpos)
  have hbound : ‖f x‖ ≤ C * ‖x‖ := hCmem.2 x
  have hCx : C * ‖x‖ < (‖f‖ₒₚ + ε / (‖x‖ + 1)) * ‖x‖ ∨ ‖x‖ = 0 := by
    rcases eq_or_lt_of_le (QuasinormedAddCommGroup.norm_nonneg x) with h | h
    · right; exact h.symm
    · left; exact mul_lt_mul_of_pos_right hClt h
  rcases hCx with hCx | hx0
  · have hεx : (‖f‖ₒₚ + ε / (‖x‖ + 1)) * ‖x‖ ≤ ‖f‖ₒₚ * ‖x‖ + ε := by
      have : ε / (‖x‖ + 1) * ‖x‖ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
        nlinarith [QuasinormedAddCommGroup.norm_nonneg x]
      nlinarith
    linarith [hbound, hCx]
  · rw [hx0] at hbound ⊢
    simp only [mul_zero] at hbound ⊢
    linarith

end QuasinormedAddCommGroup
