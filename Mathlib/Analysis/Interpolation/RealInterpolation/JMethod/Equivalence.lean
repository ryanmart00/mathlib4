/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.FundamentalLemma
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JInterpolationSpace
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.DiscreteK
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.RealInterpolationSpace

/-!
# The equivalence theorem `K = J`

Bergh–Löfström Theorem 3.11.3 (Theorem 3.3.1 for normed couples): for `0 < θ < 1` and
`0 < q ≤ ∞`, the discrete J-method and the K-method give the same subspace of `A₀ + A₁`, with
equivalent quasinorms.

* `K ⊂ J` (B–L's "converse inequality"): the fundamental lemma
  `exists_jFunctional_le_kFunctional` represents `a` by `uᵥ` with `J(2^ν, uᵥ) ≤ γ K(2^ν, a)`; the
  discrete K-method (`KMethod/DiscreteK.lean`) then bounds `‖a‖_J` by `‖a‖_K`. The fundamental
  lemma only gives symmetric partial sums; for `a` of finite K-quasinorm the terms decay
  geometrically, so (Aoki–Rolewicz, completeness of `A₀ + A₁`) the series converges
  unconditionally, as the J-method's representations require
  (`exists_hasSum_jFunctional_le_kFunctional`).
* `J ⊂ K`: for `a = ∑ᵥ uᵥ`, the Aoki–Rolewicz inequality for the quasi-norm `K(t, ·)` and
  `K(t, uᵥ) ≤ min(1, t 2^{-ν}) J(2^ν, uᵥ)` give
  `K(2^μ, a) ≲ (∑ᵥ (min(1, 2^ν) J(2^{μ-ν}, u_{μ-ν}))^ρ)^{1/ρ}`, and Minkowski's inequality in
  `ℓ^{q/ρ}` (with `ρ < q`) finishes the proof.

## Main statements
* `exists_hasSum_jFunctional_le_kFunctional`: J-representations from the fundamental lemma.
* `exists_jInterpolationENorm_le_mul_realInterpolationENorm`: `‖a‖_J ≤ C ‖a‖_K`.
* `exists_realInterpolationENorm_le_mul_jInterpolationENorm`: `‖a‖_K ≤ C ‖a‖_J`.
* `jInterpolationSubmodule_eq_realInterpolationSubmodule`: the two spaces coincide.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- For `a` of finite `(θ,q)` K-quasinorm, the representation of the fundamental lemma converges
unconditionally: there is `u : ℤ → A₀ ∩ A₁` with `a = ∑ᵥ uᵥ` (`HasSum` in `A₀ + A₁`) and
`J(2^ν, uᵥ) ≤ 3 (1 + ε) C K(2^ν, a)`. -/
theorem exists_hasSum_jFunctional_le_kFunctional [CompleteSpace A₀] [CompleteSpace A₁]
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) {a : sum ι₀ ι₁}
    (ha : realInterpolationENorm ι₀ ι₁ θ q a ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℤ → meet ι₀ ι₁, HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a ∧
      ∀ ν : ℤ, JFunctional ι₀ ι₁ (2 ^ ν) (u ν) ≤
        3 * (1 + ε) * max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
          (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) *
          KFunctional ι₀ ι₁ (2 ^ ν) a := by
  -- B–L (proof of Theorem 3.3.1): `K(t,a) ≤ M t^θ`, so the fundamental lemma applies
  obtain ⟨M, hM⟩ := exists_kFunctional_le_mul_rpow ι₀ ι₁ θ hq ha
  have hM0 : 0 ≤ M := by
    simpa using (kFunctional_nonneg ι₀ ι₁ 1 zero_le_one a).trans (hM 1 one_pos)
  obtain ⟨u, hsym, hJ⟩ := exists_jFunctional_le_kFunctional ι₀ ι₁
    (tendsto_kFunctional_nhdsGT_zero ι₀ ι₁ hθ0 hq ha)
    (tendsto_kFunctional_div_atTop ι₀ ι₁ hθ1 hq ha) hε
  refine ⟨u, ?_, hJ⟩
  set γ := 3 * (1 + ε) * max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hγ : 0 ≤ γ := mul_nonneg (by linarith)
    (QuasinormedAddCommGroup.quasiTriangleConst_pos.le.trans (le_max_left _ _))
  -- geometric decay: `‖uᵥ‖ ≤ min(1, 2^{-ν}) J(2^ν, uᵥ) ≤ γ M min(2^{νθ}, 2^{ν(θ-1)})`
  set δ := min θ (1 - θ)
  have hδ : 0 < δ := lt_min hθ0 (by linarith)
  have hterm (ν : ℤ) : ‖meetToSum ι₀ ι₁ (u ν)‖ ≤ ((2 : ℝ) ^ (-δ)) ^ ν.natAbs * (γ * M) := by
    have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
    have hk := min_mul_norm_le_kFunctional ι₀ ι₁ 1 zero_le_one (meetToSum ι₀ ι₁ (u ν))
    have hkj := kFunctional_meetToSum_le_jFunctional ι₀ ι₁ h2ν zero_le_one (u ν)
    rw [min_self, one_mul] at hk
    have hmin : 0 ≤ min 1 ((2 : ℝ) ^ ν)⁻¹ := le_min zero_le_one (inv_nonneg.mpr h2ν.le)
    calc ‖meetToSum ι₀ ι₁ (u ν)‖
        ≤ min 1 (1 / (2 : ℝ) ^ ν) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν) := hk.trans hkj
      _ ≤ min 1 ((2 : ℝ) ^ ν)⁻¹ * (γ * (M * ((2 : ℝ) ^ ν) ^ θ)) := by
          rw [one_div]
          exact mul_le_mul_of_nonneg_left ((hJ ν).trans
            (mul_le_mul_of_nonneg_left (hM _ h2ν) hγ)) hmin
      _ = (min 1 ((2 : ℝ) ^ ν)⁻¹ * ((2 : ℝ) ^ ν) ^ θ) * (γ * M) := by ring
      _ ≤ ((2 : ℝ) ^ (-δ)) ^ ν.natAbs * (γ * M) :=
          mul_le_mul_of_nonneg_right (min_one_inv_mul_rpow_le (min_le_left _ _)
            (min_le_right _ _) ν) (mul_nonneg hγ hM0)
  -- Aoki–Rolewicz in the complete space `A₀ + A₁`: the series converges unconditionally
  set ρ := QuasinormedAddCommGroup.aokiRolewiczExponent (sum ι₀ ι₁)
  have hρ : 0 < ρ := QuasinormedAddCommGroup.aokiRolewiczExponent_pos _
  set r := ((2 : ℝ) ^ (-δ)) ^ ρ
  have hr1 : r < 1 := Real.rpow_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)) hρ
  have hsumm : Summable fun ν => ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ := by
    refine Summable.of_nonneg_of_le
      (fun _ => Real.rpow_nonneg (QuasinormedAddCommGroup.norm_nonneg _) _) (fun ν => ?_)
      ((summable_pow_natAbs (by positivity) hr1).mul_right ((γ * M) ^ ρ))
    calc ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ ≤ (((2 : ℝ) ^ (-δ)) ^ ν.natAbs * (γ * M)) ^ ρ :=
          Real.rpow_le_rpow (QuasinormedAddCommGroup.norm_nonneg _) (hterm ν) hρ.le
      _ = r ^ ν.natAbs * (γ * M) ^ ρ := by
          rw [Real.mul_rpow (by positivity) (mul_nonneg hγ hM0),
            ← Real.rpow_pow_comm (x := (2 : ℝ) ^ (-δ)) (by positivity)]
  have hS := (QuasinormedAddCommGroup.summable_of_summable_norm_rpow hsumm).hasSum
  -- the unconditional sum is also the limit of the symmetric partial sums, hence equals `a`
  have hIcc : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) atTop atTop :=
    tendsto_atTop_finset_of_monotone (fun m n hmn => Finset.Icc_subset_Icc (by omega) (by omega))
      (fun ν => ⟨ν.natAbs, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩)
  rwa [tendsto_nhds_unique hsym (hS.comp hIcc)]

/-- `K ⊂ J` (B–L Theorem 3.11.3, via the fundamental lemma as in the proof of Theorem 3.3.1):
`‖a‖_{θ,q;J} ≤ 6 C 2^θ (log 2)^{-1/q} ‖a‖_{θ,q;K}`, with `C = max C₀ C₁` the larger
quasi-triangle constant. The fundamental lemma with `ε = 1` gives `J(2^ν, uᵥ) ≤ 6 C K(2^ν, a)`, and
`2^θ (log 2)^{-1/q}` is the inverse of the lower constant of the discrete K-method
(`ofReal_mul_kSequenceENorm_le_realInterpolationENorm`). -/
theorem jInterpolationENorm_le_mul_realInterpolationENorm [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q)
    (a : sum ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q a ≤
      ENNReal.ofReal (6 * max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
          (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) * 2 ^ θ) *
        (ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal)⁻¹ * realInterpolationENorm ι₀ ι₁ θ q a := by
  set C := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hCpos : 0 < C :=
    QuasinormedAddCommGroup.quasiTriangleConst_pos.trans_le (le_max_left _ _)
  have hC : 0 ≤ C := hCpos.le
  set L := ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal
  have hL0 : L ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two))
    ENNReal.ofReal_ne_top).ne'
  have hLtop : L ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  rcases eq_or_ne (realInterpolationENorm ι₀ ι₁ θ q a) ⊤ with ha | ha
  · -- nothing to prove if `‖a‖_K = ∞`
    rw [ha, ENNReal.mul_top (mul_ne_zero (ENNReal.ofReal_pos.mpr
        (mul_pos (mul_pos (by norm_num) hCpos) (Real.rpow_pos_of_pos two_pos θ))).ne'
      (ENNReal.inv_ne_zero.mpr hLtop))]
    exact le_top
  -- B–L: the fundamental lemma (with `ε = 1`) gives `a = ∑ uᵥ` with `J(2^ν, uᵥ) ≤ 6 C K(2^ν, a)`
  obtain ⟨u, hu, hJ⟩ := exists_hasSum_jFunctional_le_kFunctional ι₀ ι₁ hθ0 hθ1 hq ha one_pos
  -- thus `‖(2^{-νθ} J(2^ν, uᵥ))‖_{ℓ^q} ≤ 6 C ‖(2^{-νθ} K(2^ν, a))‖_{ℓ^q}`
  have hseq : jSequenceENorm ι₀ ι₁ θ q u ≤
      ENNReal.ofReal (6 * C) * kSequenceENorm ι₀ ι₁ θ q a := by
    set h : ℤ → ℝ := fun ν => ((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) a
    have hh (ν : ℤ) : 0 ≤ h ν := mul_nonneg (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _)
      (kFunctional_nonneg ι₀ ι₁ _ (zpow_nonneg zero_le_two _) a)
    have hk : kSequenceENorm ι₀ ι₁ θ q a = eLpNorm h q Measure.count :=
      eLpNorm_congr_enorm_ae Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aestronglyMeasurable (Eventually.of_forall fun ν => by
          rw [enorm_eq_self, Real.enorm_of_nonneg (hh ν)])
    calc jSequenceENorm ι₀ ι₁ θ q u ≤ eLpNorm ((6 * C) • h) q Measure.count := by
          refine eLpNorm_mono_enorm Measurable.of_discrete.aestronglyMeasurable fun ν => ?_
          rw [enorm_eq_self, Pi.smul_apply, smul_eq_mul,
            Real.enorm_of_nonneg (mul_nonneg (by positivity) (hh ν))]
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 := hJ ν
          rw [show (3 : ℝ) * (1 + 1 : ℝ) = 6 by norm_num] at h3
          calc ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)
              ≤ ((2 : ℝ) ^ ν) ^ (-θ) * (6 * C * KFunctional ι₀ ι₁ (2 ^ ν) a) :=
                mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _)
            _ = 6 * C * h ν := by ring
      _ = ENNReal.ofReal (6 * C) * kSequenceENorm ι₀ ι₁ θ q a := by
          rw [eLpNorm_const_smul, hk, Real.enorm_of_nonneg (by positivity)]
  -- and by B–L Lemma 3.1.3, `‖(2^{-νθ} K(2^ν, a))‖_{ℓ^q} ≤ 2^θ (log 2)^{-1/q} ‖a‖_K`
  have hdisc := ofReal_mul_kSequenceENorm_le_realInterpolationENorm ι₀ ι₁ hθ0.le hq a
  have h2θ : ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * ENNReal.ofReal ((2 : ℝ) ^ θ) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos, neg_add_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  have hk : kSequenceENorm ι₀ ι₁ θ q a ≤
      ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ * realInterpolationENorm ι₀ ι₁ θ q a := by
    calc kSequenceENorm ι₀ ι₁ θ q a
        = ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ *
            (ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * L * kSequenceENorm ι₀ ι₁ θ q a) := by
          rw [show ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ *
              (ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * L * kSequenceENorm ι₀ ι₁ θ q a) =
              (ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * ENNReal.ofReal ((2 : ℝ) ^ θ)) * (L⁻¹ * L) *
                kSequenceENorm ι₀ ι₁ θ q a by ring,
            h2θ, ENNReal.inv_mul_cancel hL0 hLtop, one_mul, one_mul]
      _ ≤ _ := by gcongr
  calc jInterpolationENorm ι₀ ι₁ θ q a ≤ jSequenceENorm ι₀ ι₁ θ q u :=
        jInterpolationENorm_le ι₀ ι₁ θ q u hu
    _ ≤ ENNReal.ofReal (6 * C) * kSequenceENorm ι₀ ι₁ θ q a := hseq
    _ ≤ ENNReal.ofReal (6 * C) *
          (ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ * realInterpolationENorm ι₀ ι₁ θ q a) := by
        gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 6 * C)]; ring

/-- `K ⊂ J` with an unspecified constant: `‖a‖_{θ,q;J} ≤ C ‖a‖_{θ,q;K}`. -/
theorem exists_jInterpolationENorm_le_mul_realInterpolationENorm [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum ι₀ ι₁,
      jInterpolationENorm ι₀ ι₁ θ q a ≤ C * realInterpolationENorm ι₀ ι₁ θ q a :=
  ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)) ENNReal.ofReal_ne_top).ne'),
    jInterpolationENorm_le_mul_realInterpolationENorm ι₀ ι₁ hθ0 hθ1 hq⟩

/-- `J ⊂ K` (B–L Theorem 3.11.3, first half): `‖a‖_{θ,q;K} ≤ C ‖a‖_{θ,q;J}`. -/
theorem exists_realInterpolationENorm_le_mul_jInterpolationENorm {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum ι₀ ι₁,
      realInterpolationENorm ι₀ ι₁ θ q a ≤ C * jInterpolationENorm ι₀ ι₁ θ q a :=
  sorry

/-- The equivalence theorem (B–L Theorem 3.11.3): `J_{θ,q}(A) = K_{θ,q}(A)` as subspaces of
`A₀ + A₁`. -/
theorem jInterpolationSubmodule_eq_realInterpolationSubmodule [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    jInterpolationSubmodule ι₀ ι₁ θ q = realInterpolationSubmodule ι₀ ι₁ θ q :=
  sorry

end InterpolationCouple
