/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.KInterpolation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-!
# The discrete K-method

Bergh–Löfström Lemma 3.1.3 (Triebel §1.7, part (a)): the `(θ,q)` K-quasinorm of `a ∈ A₀ + A₁`
is equivalent to the `ℓ^q(ℤ)` quasinorm of the sequence `ν ↦ 2^{-νθ} K(2^ν, a)`. On each dyadic
interval `2^ν ≤ t ≤ 2^{ν+1}` one has `K(2^ν, a) ≤ K(t, a) ≤ 2 K(2^ν, a)`, and
`∫_{2^ν}^{2^{ν+1}} dt/t = log 2`, whence the constants `2^{-θ} (log 2)^{1/q}` and
`2 (log 2)^{1/q}` (the factor `(log 2)^{1/q}` reads as `1` when `q = ∞`, since then
`q⁻¹.toReal = 0`).

The discrete form is what the equivalence theorem `K = J` (`JMethod/Equivalence.lean`) compares
with the discrete J-method.

## Main definitions
* `InterpolationCouple.kSequenceENorm θ q a`: `‖(2^{-νθ} K(2^ν, a))ᵥ‖_{ℓ^q}`.

## Main statements
* `ofReal_mul_kSequenceENorm_le_realInterpolationENorm`,
  `realInterpolationENorm_le_mul_kSequenceENorm`: the two halves of B–L Lemma 3.1.3.
-/

open MeasureTheory Set
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- The discrete K-method quasinorm: the `ℓ^q(ℤ)` quasinorm of `ν ↦ 2^{-νθ} K(2^ν, a)`
(Bergh–Löfström's `‖(αᵥ)‖_{λ^{θ,q}}` with `αᵥ = K(2^ν, a)`). -/
noncomputable def kSequenceENorm (θ : ℝ) (q : ℝ≥0∞) (a : sum ι₀ ι₁) : ℝ≥0∞ :=
  eLpNorm (fun ν : ℤ => ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a))
    q Measure.count

/-- B–L, proof of Lemma 3.1.3: on `2^ν ≤ t < 2^{ν+1}`,
`2^{-θ} 2^{-νθ} K(2^ν, a) ≤ t^{-θ} K(t, a) ≤ 2 · 2^{-νθ} K(2^ν, a)` (for `θ ≥ 0`). -/
private theorem rpow_neg_mul_kFunctional_bounds_of_mem_Ico {θ : ℝ} (hθ : 0 ≤ θ)
    (a : sum ι₀ ι₁) (ν : ℤ) {t : ℝ} (ht : t ∈ Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1))) :
    (2 : ℝ) ^ (-θ) * (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a) ≤
        t ^ (-θ) * KFunctional ι₀ ι₁ t a ∧
      t ^ (-θ) * KFunctional ι₀ ι₁ t a ≤
        2 * (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a) := by
  have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
  have ht0 : 0 < t := h2ν.trans_le ht.1
  have h2ν1 : (2 : ℝ) ^ (ν + 1) = 2 * 2 ^ ν := by rw [zpow_add_one₀ two_ne_zero, mul_comm]
  have hK0 : 0 ≤ KFunctional ι₀ ι₁ (2 ^ ν) a := kFunctional_nonneg ι₀ ι₁ _ h2ν.le a
  -- B–L: by Lemma 3.1.1, `K(2^ν, a) ≤ K(t, a) ≤ 2 K(2^ν, a)` for `2^ν ≤ t ≤ 2^{ν+1}`.
  have hKmono : KFunctional ι₀ ι₁ (2 ^ ν) a ≤ KFunctional ι₀ ι₁ t a :=
    kFunctional_mono ι₀ ι₁ h2ν.le ht.1 a
  have hK2 : KFunctional ι₀ ι₁ t a ≤ 2 * KFunctional ι₀ ι₁ (2 ^ ν) a := by
    have h := min_one_div_mul_kFunctional_le ι₀ ι₁ ht0 h2ν.le a
    have hmin : 1 / 2 ≤ min 1 (2 ^ ν / t) := by
      refine le_min (by norm_num) ?_
      rw [le_div_iff₀ ht0]
      linarith [ht.2, h2ν1]
    nlinarith [kFunctional_nonneg ι₀ ι₁ t ht0.le a]
  constructor
  · -- `t^{-θ} ≥ (2^{ν+1})^{-θ} = 2^{-θ} (2^ν)^{-θ}`
    have hpow : (2 : ℝ) ^ (-θ) * ((2 : ℝ) ^ ν) ^ (-θ) ≤ t ^ (-θ) := by
      rw [← Real.mul_rpow zero_le_two h2ν.le, ← h2ν1]
      exact Real.rpow_le_rpow_of_nonpos ht0 ht.2.le (neg_nonpos.mpr hθ)
    calc (2 : ℝ) ^ (-θ) * (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a)
        = (2 : ℝ) ^ (-θ) * ((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a := by ring
      _ ≤ t ^ (-θ) * KFunctional ι₀ ι₁ t a :=
          mul_le_mul hpow hKmono hK0 (Real.rpow_nonneg ht0.le _)
  · -- `t^{-θ} ≤ (2^ν)^{-θ}`
    have hpow : t ^ (-θ) ≤ ((2 : ℝ) ^ ν) ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos h2ν ht.1 (neg_nonpos.mpr hθ)
    calc t ^ (-θ) * KFunctional ι₀ ι₁ t a
        ≤ ((2 : ℝ) ^ ν) ^ (-θ) * (2 * KFunctional ι₀ ι₁ (2 ^ ν) a) :=
          mul_le_mul hpow hK2 (kFunctional_nonneg ι₀ ι₁ t ht0.le a) (Real.rpow_nonneg h2ν.le _)
      _ = _ := by ring

/-- `∫_{2^ν}^{2^{ν+1}} dt/t = log 2`. -/
private theorem lintegral_Ico_zpow_inv (ν : ℤ) :
    ∫⁻ t in Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1)), ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (Real.log 2) := by
  have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
  have hle : (2 : ℝ) ^ ν ≤ 2 ^ (ν + 1) := zpow_le_zpow_right₀ one_le_two (by omega)
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Icc ((2 : ℝ) ^ ν) (2 ^ (ν + 1))) :=
    (continuousOn_inv₀.mono fun t ht => (h2ν.trans_le ht.1).ne').integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ico_subset_Icc_self)
      (ae_restrict_of_forall_mem measurableSet_Ico fun t ht =>
        inv_nonneg.mpr (h2ν.le.trans ht.1)),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    integral_inv_of_pos h2ν (zpow_pos two_pos _), zpow_add_one₀ two_ne_zero,
    mul_div_cancel_left₀ _ h2ν.ne']

/-- `(0, ∞)` is the union of the dyadic intervals `[2^ν, 2^{ν+1})`. -/
private theorem iUnion_Ico_zpow_two :
    ⋃ ν : ℤ, Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1)) = Ioi 0 := by
  ext t
  simp only [mem_iUnion, mem_Ioi]
  exact ⟨fun ⟨ν, hν⟩ => (zpow_pos two_pos ν).trans_le hν.1,
    fun ht => exists_mem_Ico_zpow ht one_lt_two⟩

/-- B–L: `∫₀^∞ = ∑ᵥ ∫_{2^ν}^{2^{ν+1}}` (the dyadic intervals are disjoint). -/
private theorem lintegral_Ioi_eq_tsum (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), F t =
      ∑' ν : ℤ, ∫⁻ t in Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1)), F t := by
  refine (congrArg (fun s => ∫⁻ t in s, F t) iUnion_Ico_zpow_two).symm.trans
    (lintegral_iUnion (fun _ => measurableSet_Ico) (fun m n hmn => ?_) F)
  refine Set.disjoint_left.mpr fun t h1 h2 => hmn ?_
  have hm := (zpow_lt_zpow_iff_right₀ one_lt_two).mp (h1.1.trans_lt h2.2)
  have hn := (zpow_lt_zpow_iff_right₀ one_lt_two).mp (h2.1.trans_lt h1.2)
  omega

/-- B–L Lemma 3.1.3, lower half: `2^{-θ} (log 2)^{1/q} ‖(2^{-νθ} K(2^ν, a))‖_{ℓ^q} ≤ ‖a‖_{θ,q}`. -/
theorem ofReal_mul_kSequenceENorm_le_realInterpolationENorm {θ : ℝ} (hθ : 0 ≤ θ) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) :
    ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal *
        kSequenceENorm ι₀ ι₁ θ q a ≤ realInterpolationENorm ι₀ ι₁ θ q a := by
  set α : ℤ → ℝ≥0∞ := fun ν =>
    ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a)
  unfold kSequenceENorm realInterpolationENorm
  split_ifs with htop
  · -- `q = ∞`: compare each `αᵥ` with the supremand at `t = 2^ν`
    subst htop
    rw [eLpNorm_exponent_top Measurable.of_discrete.aestronglyMeasurable, eLpNormEssSup,
      essSup_count_eq_ciSup (OrderTop.bddAbove _)]
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, mul_one, enorm_eq_self]
    rw [ENNReal.mul_iSup]
    refine iSup_le fun ν => le_iSup_of_le ⟨2 ^ ν, mem_Ioi.mpr (zpow_pos two_pos ν)⟩ ?_
    calc ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * α ν ≤ 1 * α ν := by
          gcongr
          exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos one_le_two
            (neg_nonpos.mpr hθ))
      _ = _ := one_mul _
  · -- `q < ∞`: B–L, `‖a‖^q = ∑ᵥ ∫_{2^ν}^{2^{ν+1}} (t^{-θ} K(t, a))^q dt/t`, and each piece is
    -- at least `(2^{-θ} 2^{-νθ} αᵥ)^q log 2`
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    set c := ENNReal.ofReal ((2 : ℝ) ^ (-θ))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq.ne' htop
      Measurable.of_discrete.aestronglyMeasurable, lintegral_count]
    simp only [enorm_eq_self]
    rw [← ENNReal.rpow_le_rpow_iff hr]
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, ENNReal.toReal_inv,
      one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]
    rw [lintegral_Ioi_eq_tsum, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ν => ?_
    calc c ^ q.toReal * ENNReal.ofReal (Real.log 2) * α ν ^ q.toReal
        = ∫⁻ t in Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1)),
            (c * α ν) ^ q.toReal * ENNReal.ofReal t⁻¹ := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)),
            lintegral_Ico_zpow_inv, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
          ring
      _ ≤ _ := by
          refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
          gcongr
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _)]
          exact ENNReal.ofReal_le_ofReal
            (rpow_neg_mul_kFunctional_bounds_of_mem_Ico ι₀ ι₁ hθ a ν ht).1

/-- B–L Lemma 3.1.3, upper half: `‖a‖_{θ,q} ≤ 2 (log 2)^{1/q} ‖(2^{-νθ} K(2^ν, a))‖_{ℓ^q}`. -/
theorem realInterpolationENorm_le_mul_kSequenceENorm {θ : ℝ} (hθ : 0 ≤ θ) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q a ≤
      2 * ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal * kSequenceENorm ι₀ ι₁ θ q a := by
  set α : ℤ → ℝ≥0∞ := fun ν =>
    ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a)
  have h2α (ν : ℤ) {t : ℝ} (ht : t ∈ Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1))) :
      ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) ≤ 2 * α ν := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
    exact ENNReal.ofReal_le_ofReal (rpow_neg_mul_kFunctional_bounds_of_mem_Ico ι₀ ι₁ hθ a ν ht).2
  unfold kSequenceENorm realInterpolationENorm
  split_ifs with htop
  · -- `q = ∞`: each `t` lies in some dyadic interval `[2^ν, 2^{ν+1})`
    subst htop
    rw [eLpNorm_exponent_top Measurable.of_discrete.aestronglyMeasurable, eLpNormEssSup,
      essSup_count_eq_ciSup (OrderTop.bddAbove _)]
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, mul_one, enorm_eq_self]
    refine iSup_le fun t => ?_
    obtain ⟨ν, hν⟩ := exists_mem_Ico_zpow (mem_Ioi.mp t.2) one_lt_two
    exact (h2α ν hν).trans (mul_le_mul_right (le_iSup α ν) 2)
  · -- `q < ∞`: B–L, each piece `∫_{2^ν}^{2^{ν+1}} (t^{-θ} K(t, a))^q dt/t` is at most
    -- `(2 · 2^{-νθ} αᵥ)^q log 2`
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq.ne' htop
      Measurable.of_discrete.aestronglyMeasurable, lintegral_count]
    simp only [enorm_eq_self]
    rw [← ENNReal.rpow_le_rpow_iff hr]
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, ENNReal.toReal_inv,
      one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]
    rw [lintegral_Ioi_eq_tsum, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ν => ?_
    calc ∫⁻ t in Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1)),
          ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) ^ q.toReal * ENNReal.ofReal t⁻¹
        ≤ ∫⁻ t in Ico ((2 : ℝ) ^ ν) (2 ^ (ν + 1)),
            (2 * α ν) ^ q.toReal * ENNReal.ofReal t⁻¹ := by
          refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
          gcongr
          exact h2α ν ht
      _ = 2 ^ q.toReal * ENNReal.ofReal (Real.log 2) * α ν ^ q.toReal := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le
              (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)),
            lintegral_Ico_zpow_inv, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
          ring

end InterpolationCouple
