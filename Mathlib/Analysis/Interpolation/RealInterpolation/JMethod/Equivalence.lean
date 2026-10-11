/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.FundamentalLemma
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JInterpolationSpace
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.DiscreteK
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.RealInterpolationSpace
import Mathlib.Analysis.MeanInequalities

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

/-! ### Auxiliary inequalities for `ℝ≥0∞`-valued series -/

/-- Hölder's inequality for `ℝ≥0∞`-valued series. -/
private theorem tsum_mul_le_of_holderConjugate {ι : Type*} (f g : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => (ENNReal.inner_le_Lp_mul_Lq s f g hpq).trans ?_
  have hp : 0 ≤ 1 / p := one_div_nonneg.mpr hpq.nonneg
  have hq : 0 ≤ 1 / q := one_div_nonneg.mpr hpq.symm.nonneg
  exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) hp)
    (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) hq)

/-- Weighted power-mean (Jensen) inequality for series: for `p > 1`,
`(∑ φᵢ Wᵢ)^p ≤ (∑ φᵢ)^{p-1} ∑ φᵢ Wᵢ^p`. -/
private theorem tsum_mul_rpow_le {ι : Type*} (φ W : ι → ℝ≥0∞) {p : ℝ} (hp : 1 < p) :
    (∑' i, φ i * W i) ^ p ≤ (∑' i, φ i) ^ (p - 1) * ∑' i, φ i * W i ^ p := by
  set q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hsum : (1 / q + 1 / p : ℝ) = 1 := by
    rw [one_div, one_div, add_comm]
    exact hpq.inv_add_inv_eq_one
  -- `φ W = φ^{1/q} (φ^{1/p} W)`, then Hölder with exponents `q, p`
  have hsplit (i : ι) : φ i * W i = φ i ^ (1 / q) * (φ i ^ (1 / p) * W i) := by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
      ENNReal.rpow_one]
  have hH := tsum_mul_le_of_holderConjugate (fun i => φ i ^ (1 / q))
    (fun i => φ i ^ (1 / p) * W i) hpq.symm
  simp only [← hsplit] at hH
  have hf (i : ι) : (φ i ^ (1 / q)) ^ q = φ i := by
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have hg (i : ι) : (φ i ^ (1 / p) * W i) ^ p = φ i * W i ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  simp only [hf, hg] at hH
  calc (∑' i, φ i * W i) ^ p
      ≤ ((∑' i, φ i) ^ (1 / q) * (∑' i, φ i * W i ^ p) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hH hp0.le
    _ = (∑' i, φ i) ^ (p - 1) * ∑' i, φ i * W i ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
        congr 2
        have : q⁻¹ = 1 - p⁻¹ := by rw [← hsum]; simp [one_div]
        rw [this]
        field_simp

/-- Young's inequality `ℓ¹ * ℓ^p ⊂ ℓ^p` on `ℤ` for `ℝ≥0∞`-valued sequences (`p ≥ 1`):
`∑_μ (∑_k φ_k W_{μ-k})^p ≤ (∑ φ)^p ∑ W^p`. This is the "Minkowski's inequality" step of B–L's
proof of Theorem 3.11.3. -/
private theorem tsum_conv_rpow_le (φ W : ℤ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    ∑' μ, (∑' k, φ k * W (μ - k)) ^ p ≤ (∑' k, φ k) ^ p * ∑' μ, W μ ^ p := by
  -- `∑_μ ∑_k φ_k V_{μ-k} = (∑ φ)(∑ V)`, by Fubini and translation invariance
  have hswap (V : ℤ → ℝ≥0∞) : ∑' μ, ∑' k, φ k * V (μ - k) = (∑' k, φ k) * ∑' μ, V μ := by
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [ENNReal.tsum_mul_left]
    exact congrArg (φ k * ·) ((Equiv.subRight k).tsum_eq V)
  rcases hp.eq_or_lt with rfl | hp1
  · simp only [ENNReal.rpow_one]
    exact (hswap W).le
  calc ∑' μ, (∑' k, φ k * W (μ - k)) ^ p
      ≤ ∑' μ, (∑' k, φ k) ^ (p - 1) * ∑' k, φ k * W (μ - k) ^ p :=
        ENNReal.tsum_le_tsum fun μ => tsum_mul_rpow_le φ (fun k => W (μ - k)) hp1
    _ = (∑' k, φ k) ^ p * ∑' μ, W μ ^ p := by
        rw [ENNReal.tsum_mul_left, hswap (fun μ => W μ ^ p), ← mul_assoc]
        congr 1
        conv_rhs => rw [show p = (p - 1 + 1 : ℝ) by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]

/-- B–L, proof of Theorem 3.11.3: for `t > 0` and `a = ∑ᵥ uᵥ` in `A₀ + A₁`,
`K(t, a) ≤ C_k 4^{1/ρ} (∑ᵥ K(t, uᵥ)^ρ)^{1/ρ}`, where `C_k = max C₀ C₁` and `ρ` is the
Aoki–Rolewicz exponent of any constant `C' ≥ C_k` (`K(t, ·)` is a `C_k`-quasi-norm, B–L
Lemma 3.11.1, so B–L Lemma 3.10.2 applies to it). -/
private theorem ofReal_kFunctional_le_tsum_rpow {C' : ℝ}
    (hC' : max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
      (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) ≤ C') {t : ℝ} (ht : 0 < t)
    {a : sum ι₀ ι₁} {u : ℤ → meet ι₀ ι₁} (hu : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a) :
    ENNReal.ofReal (KFunctional ι₀ ι₁ t a) ≤
      ENNReal.ofReal (max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
        (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) *
          4 ^ (AokiRolewicz.exponent C')⁻¹) *
        (∑' ν, ENNReal.ofReal (KFunctional ι₀ ι₁ t (meetToSum ι₀ ι₁ (u ν))) ^
          AokiRolewicz.exponent C') ^ (AokiRolewicz.exponent C')⁻¹ := by
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hCk1 : 1 ≤ Ck :=
    QuasinormedAddCommGroup.one_le_quasiTriangleConst.trans (le_max_left _ _)
  have hC'1 : 1 ≤ C' := hCk1.trans hC'
  set ρ := AokiRolewicz.exponent C'
  have hρ : 0 < ρ := AokiRolewicz.exponent_pos hC'1
  set B : ℝ := 4 ^ ρ⁻¹
  have hB : 0 ≤ B := by positivity
  set x : ℤ → sum ι₀ ι₁ := fun ν => meetToSum ι₀ ι₁ (u ν)
  set T := (∑' ν, ENNReal.ofReal (KFunctional ι₀ ι₁ t (x ν)) ^ ρ) ^ ρ⁻¹
  -- `K(t, ·)` is a `C'`-quasi-norm on `A₀ + A₁` (B–L Lemma 3.11.1)
  have hK0 (b : sum ι₀ ι₁) : 0 ≤ KFunctional ι₀ ι₁ t b := kFunctional_nonneg ι₀ ι₁ t ht.le b
  have hKz (b : sum ι₀ ι₁) : KFunctional ι₀ ι₁ t b = 0 ↔ b = 0 := by
    refine ⟨fun h => (QuasinormedAddCommGroup.norm_eq_zero_iff b).mp (le_antisymm ?_
      (QuasinormedAddCommGroup.norm_nonneg b)), fun h => h ▸ kFunctional_zero ι₀ ι₁ t ht.le⟩
    have h1 := min_mul_norm_le_kFunctional ι₀ ι₁ t ht.le b
    rw [h] at h1
    nlinarith [lt_min one_pos ht, QuasinormedAddCommGroup.norm_nonneg b]
  have hKadd (b c : sum ι₀ ι₁) :
      KFunctional ι₀ ι₁ t (b + c) ≤ C' * (KFunctional ι₀ ι₁ t b + KFunctional ι₀ ι₁ t c) :=
    (kFunctional_add_le ι₀ ι₁ t ht.le b c).trans
      (mul_le_mul_of_nonneg_right hC' (add_nonneg (hK0 b) (hK0 c)))
  -- B–L Lemma 3.10.2 for the partial sums
  have hfin (F : Finset ℤ) :
      ENNReal.ofReal (KFunctional ι₀ ι₁ t (∑ ν ∈ F, x ν)) ≤ ENNReal.ofReal B * T := by
    have h := AokiRolewicz.apply_sum_le_rpow (fun b => KFunctional ι₀ ι₁ t b) hC'1 hK0 hKz
      hKadd F x
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    rw [ENNReal.ofReal_mul hB, ← ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun ν _ => Real.rpow_nonneg (hK0 _) _) (inv_pos.mpr hρ).le,
      ENNReal.ofReal_sum_of_nonneg fun ν _ => Real.rpow_nonneg (hK0 _) _]
    refine mul_le_mul_right (ENNReal.rpow_le_rpow ?_ (inv_pos.mpr hρ).le) _
    calc ∑ ν ∈ F, ENNReal.ofReal (KFunctional ι₀ ι₁ t (x ν) ^ ρ)
        = ∑ ν ∈ F, ENNReal.ofReal (KFunctional ι₀ ι₁ t (x ν)) ^ ρ :=
          Finset.sum_congr rfl fun ν _ => (ENNReal.ofReal_rpow_of_nonneg (hK0 _) hρ.le).symm
      _ ≤ _ := ENNReal.sum_le_tsum F
  -- and pass to the limit: `K(t, a) ≤ C_k (K(t, ∑_F uᵥ) + K(t, a - ∑_F uᵥ))`, the last term
  -- being at most `2 max(1, t) ‖a - ∑_F uᵥ‖ → 0`
  have hbound (F : Finset ℤ) : ENNReal.ofReal (KFunctional ι₀ ι₁ t a) ≤
      ENNReal.ofReal Ck * (ENNReal.ofReal B * T) +
        ENNReal.ofReal Ck * ENNReal.ofReal (2 * max 1 t * ‖a - ∑ ν ∈ F, x ν‖) := by
    have h := kFunctional_add_le ι₀ ι₁ t ht.le (∑ ν ∈ F, x ν) (a - ∑ ν ∈ F, x ν)
    rw [add_sub_cancel] at h
    have h2 := kFunctional_le_two_mul_max_mul_norm ι₀ ι₁ t ht.le (a - ∑ ν ∈ F, x ν)
    rw [← mul_add]
    calc ENNReal.ofReal (KFunctional ι₀ ι₁ t a)
        ≤ ENNReal.ofReal (Ck * (KFunctional ι₀ ι₁ t (∑ ν ∈ F, x ν) +
            2 * max 1 t * ‖a - ∑ ν ∈ F, x ν‖)) := by
          refine ENNReal.ofReal_le_ofReal (h.trans ?_)
          gcongr
      _ = ENNReal.ofReal Ck * (ENNReal.ofReal (KFunctional ι₀ ι₁ t (∑ ν ∈ F, x ν)) +
            ENNReal.ofReal (2 * max 1 t * ‖a - ∑ ν ∈ F, x ν‖)) := by
          rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_add (hK0 _)
            (mul_nonneg (by positivity) (QuasinormedAddCommGroup.norm_nonneg _))]
      _ ≤ _ := by gcongr; exact hfin F
  have hlim : Tendsto (fun F : Finset ℤ => ENNReal.ofReal Ck * (ENNReal.ofReal B * T) +
      ENNReal.ofReal Ck * ENNReal.ofReal (2 * max 1 t * ‖a - ∑ ν ∈ F, x ν‖)) atTop
      (𝓝 (ENNReal.ofReal Ck * (ENNReal.ofReal B * T) +
        ENNReal.ofReal Ck * ENNReal.ofReal 0)) := by
    refine tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ?_) (Or.inr ENNReal.ofReal_ne_top))
    have h := QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero.mp hu
    simpa [← QuasinormedAddCommGroup.norm_neg (_ - a), neg_sub] using h.const_mul (2 * max 1 t)
  have := ge_of_tendsto' hlim hbound
  rwa [ENNReal.ofReal_zero, mul_zero, add_zero, ← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    at this

/-- `J ⊂ K` (B–L Theorem 3.11.3, first half): `‖a‖_{θ,q;K} ≤ C ‖a‖_{θ,q;J}`. -/
theorem exists_realInterpolationENorm_le_mul_jInterpolationENorm {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum ι₀ ι₁,
      realInterpolationENorm ι₀ ι₁ θ q a ≤ C * jInterpolationENorm ι₀ ι₁ θ q a := by
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hCk1 : 1 ≤ Ck :=
    QuasinormedAddCommGroup.one_le_quasiTriangleConst.trans (le_max_left _ _)
  -- B–L: "choosing `c` large and `ρ` so that `(2c)^ρ = 2`, we have `p = q/ρ > 1`"
  set C' := max Ck (2 ^ q⁻¹.toReal)
  have hC'1 : 1 ≤ C' := hCk1.trans (le_max_left _ _)
  set ρ := AokiRolewicz.exponent C'
  have hρ : 0 < ρ := AokiRolewicz.exponent_pos hC'1
  have hρq (htop : q ≠ ⊤) : ρ ≤ q.toReal := by
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    have hlog : q.toReal⁻¹ ≤ Real.logb 2 C' := by
      calc q.toReal⁻¹ = Real.logb 2 ((2 : ℝ) ^ q⁻¹.toReal) := by
            rw [Real.logb_rpow two_pos (by norm_num), ENNReal.toReal_inv]
        _ ≤ Real.logb 2 C' :=
            Real.logb_le_logb_of_le one_lt_two (by positivity) (le_max_right _ _)
    calc ρ = (1 + Real.logb 2 C')⁻¹ := rfl
      _ ≤ (q.toReal⁻¹)⁻¹ := inv_anti₀ (by positivity) (by linarith)
      _ = q.toReal := inv_inv _
  -- the kernel `φ(k) = 2^{-kθ} min(1, 2^k)` and `Φ = φ^ρ`, summable since `0 < θ < 1`
  set φ : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-θ) * min 1 ((2 : ℝ) ^ k))
  set Φ : ℤ → ℝ≥0∞ := fun k => φ k ^ ρ
  set δ := min θ (1 - θ)
  have hδ : 0 < δ := lt_min hθ0 (by linarith)
  set r := ((2 : ℝ) ^ (-δ)) ^ ρ
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)) hρ
  have hΦle (k : ℤ) : Φ k ≤ ENNReal.ofReal (r ^ k.natAbs) := by
    have h := min_one_inv_mul_rpow_le (min_le_left θ (1 - θ)) (min_le_right θ (1 - θ)) (-k)
    have hk : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
    rw [zpow_neg, inv_inv, Int.natAbs_neg, Real.inv_rpow hk.le, ← Real.rpow_neg hk.le,
      mul_comm] at h
    calc Φ k ≤ ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ k.natAbs) ^ ρ :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) hρ.le
      _ = ENNReal.ofReal (r ^ k.natAbs) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hρ.le,
            ← Real.rpow_pow_comm (x := (2 : ℝ) ^ (-δ)) (by positivity)]
  have hΦtop : ∑' k, Φ k ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hΦle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => pow_nonneg hr0 _)
      (summable_pow_natAbs hr0 hr1)]
    exact ENNReal.ofReal_ne_top
  have hΦ0 : ∑' k, Φ k ≠ 0 := by
    have h : Φ 0 = 1 := by simp [Φ, φ]
    exact (zero_lt_one.trans_le (h ▸ ENNReal.le_tsum 0)).ne'
  set D := ENNReal.ofReal (Ck * 4 ^ ρ⁻¹)
  set M := D * (∑' k, Φ k) ^ ρ⁻¹
  -- B–L: `‖(2^{-μθ} K(2^μ, a))‖_{λ^{θ,q}} ≤ M ‖(2^{-νθ} J(2^ν, uᵥ))‖_{λ^{θ,q}}`
  have hcore (a : sum ι₀ ι₁) (u : ℤ → meet ι₀ ι₁)
      (hu : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a) :
      kSequenceENorm ι₀ ι₁ θ q a ≤ M * jSequenceENorm ι₀ ι₁ θ q u := by
    set W : ℤ → ℝ≥0∞ := fun ν =>
      ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν))
    set y : ℤ → ℝ≥0∞ := fun μ =>
      ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ μ) a)
    -- B–L: `K(2^μ, a) ≤ C (∑ᵥ (min(1, 2^{μ-ν}) J(2^ν, uᵥ))^ρ)^{1/ρ}`, i.e. after weighting,
    -- `2^{-μθ} K(2^μ, a) ≤ D (∑ᵥ (φ(μ - ν) Wᵥ)^ρ)^{1/ρ}`
    have hy (μ : ℤ) : y μ ≤ D * (∑' ν, Φ (μ - ν) * W ν ^ ρ) ^ ρ⁻¹ := by
      have h2μ : (0 : ℝ) < 2 ^ μ := zpow_pos two_pos μ
      have hc : 0 ≤ ((2 : ℝ) ^ μ) ^ (-θ) := Real.rpow_nonneg h2μ.le _
      have h1 := ofReal_kFunctional_le_tsum_rpow ι₀ ι₁ (C' := C') (le_max_left Ck _) h2μ hu
      -- `2^{-μθ} K(2^μ, uᵥ) ≤ φ(μ - ν) 2^{-νθ} J(2^ν, uᵥ)` (B–L Lemma 3.2.1)
      have hterm (ν : ℤ) : ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (-θ)) *
          ENNReal.ofReal (KFunctional ι₀ ι₁ (2 ^ μ) (meetToSum ι₀ ι₁ (u ν))) ≤
            φ (μ - ν) * W ν := by
        have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
        have hkj := kFunctional_meetToSum_le_jFunctional ι₀ ι₁ h2ν h2μ.le (u ν)
        have hsplit : ((2 : ℝ) ^ μ) ^ (-θ) =
            ((2 : ℝ) ^ (μ - ν)) ^ (-θ) * ((2 : ℝ) ^ ν) ^ (-θ) := by
          rw [← Real.mul_rpow (zpow_pos two_pos _).le h2ν.le, zpow_sub₀ two_ne_zero,
            div_mul_cancel₀ _ h2ν.ne']
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ((2 : ℝ) ^ μ) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ μ) (meetToSum ι₀ ι₁ (u ν))
            ≤ ((2 : ℝ) ^ μ) ^ (-θ) *
                (min 1 (2 ^ μ / 2 ^ ν) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)) :=
              mul_le_mul_of_nonneg_left hkj hc
          _ = ((2 : ℝ) ^ (μ - ν)) ^ (-θ) * min 1 ((2 : ℝ) ^ (μ - ν)) *
                (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)) := by
              rw [hsplit, zpow_sub₀ two_ne_zero]
              ring
      calc y μ = ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (-θ)) *
            ENNReal.ofReal (KFunctional ι₀ ι₁ (2 ^ μ) a) := ENNReal.ofReal_mul hc
        _ ≤ ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (-θ)) * (D * (∑' ν,
              ENNReal.ofReal (KFunctional ι₀ ι₁ (2 ^ μ) (meetToSum ι₀ ι₁ (u ν))) ^ ρ) ^ ρ⁻¹) :=
            mul_le_mul_right h1 _
        _ = D * (∑' ν, (ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (-θ)) *
              ENNReal.ofReal (KFunctional ι₀ ι₁ (2 ^ μ) (meetToSum ι₀ ι₁ (u ν)))) ^ ρ) ^
                ρ⁻¹ := by
            simp only [ENNReal.mul_rpow_of_nonneg _ _ hρ.le]
            rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (inv_pos.mpr hρ).le,
              ← ENNReal.rpow_mul, mul_inv_cancel₀ hρ.ne', ENNReal.rpow_one]
            ring
        _ ≤ D * (∑' ν, Φ (μ - ν) * W ν ^ ρ) ^ ρ⁻¹ := by
            refine mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun ν => ?_)
              (inv_pos.mpr hρ).le) _
            rw [← ENNReal.mul_rpow_of_nonneg _ _ hρ.le]
            exact ENNReal.rpow_le_rpow (hterm ν) hρ.le
    -- `∑ᵥ Φ(μ - ν) Vᵥ = ∑ₖ Φₖ V_{μ-k}` (reindexing)
    have hreindex (V : ℤ → ℝ≥0∞) (μ : ℤ) :
        ∑' ν, Φ (μ - ν) * V ν = ∑' k, Φ k * V (μ - k) := by
      refine ((Equiv.subLeft μ).tsum_eq (fun ν => Φ (μ - ν) * V ν)).symm.trans ?_
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
    unfold kSequenceENorm jSequenceENorm
    by_cases htop : q = ⊤
    · -- `q = ∞`: `2^{-μθ} K(2^μ, a) ≤ D (∑ Φ)^{1/ρ} sup W`
      subst htop
      rw [eLpNorm_exponent_top Measurable.of_discrete.aestronglyMeasurable, eLpNormEssSup,
        essSup_count_eq_ciSup (OrderTop.bddAbove _),
        eLpNorm_exponent_top Measurable.of_discrete.aestronglyMeasurable, eLpNormEssSup,
        essSup_count_eq_ciSup (OrderTop.bddAbove _)]
      simp only [enorm_eq_self]
      refine iSup_le fun μ => (hy μ).trans ?_
      set S := ⨆ ν, W ν
      calc D * (∑' ν, Φ (μ - ν) * W ν ^ ρ) ^ ρ⁻¹
          ≤ D * (∑' ν, Φ (μ - ν) * S ^ ρ) ^ ρ⁻¹ := by
            refine mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun ν => ?_)
              (inv_pos.mpr hρ).le) _
            exact mul_le_mul_right (ENNReal.rpow_le_rpow (le_iSup W ν) hρ.le) _
        _ = M * S := by
            have hshift : ∑' ν, Φ (μ - ν) = ∑' k, Φ k := by
              simpa using hreindex (fun _ => 1) μ
            rw [ENNReal.tsum_mul_right, hshift,
              ENNReal.mul_rpow_of_nonneg _ _ (inv_pos.mpr hρ).le, ← ENNReal.rpow_mul,
              mul_inv_cancel₀ hρ.ne', ENNReal.rpow_one, ← mul_assoc]
    · -- `q < ∞`: Young's inequality in `ℓ^{q/ρ}` (B–L: "Minkowski's inequality")
      have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
      have hp : 1 ≤ q.toReal / ρ := (one_le_div hρ).mpr (hρq htop)
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq.ne' htop
          Measurable.of_discrete.aestronglyMeasurable, lintegral_count,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hq.ne' htop
          Measurable.of_discrete.aestronglyMeasurable, lintegral_count]
      simp only [enorm_eq_self]
      rw [← ENNReal.rpow_le_rpow_iff hr]
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]
      calc ∑' μ, y μ ^ q.toReal
          ≤ ∑' μ, (D * (∑' k, Φ k * W (μ - k) ^ ρ) ^ ρ⁻¹) ^ q.toReal := by
            refine ENNReal.tsum_le_tsum fun μ => ENNReal.rpow_le_rpow ?_ hr.le
            rw [← hreindex (fun ν => W ν ^ ρ) μ]
            exact hy μ
        _ = D ^ q.toReal * ∑' μ, (∑' k, Φ k * W (μ - k) ^ ρ) ^ (q.toReal / ρ) := by
            simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul]
            rw [ENNReal.tsum_mul_left, inv_mul_eq_div]
        _ ≤ D ^ q.toReal *
              ((∑' k, Φ k) ^ (q.toReal / ρ) * ∑' μ, (W μ ^ ρ) ^ (q.toReal / ρ)) :=
            mul_le_mul_right (tsum_conv_rpow_le Φ (fun ν => W ν ^ ρ) hp) _
        _ = (D * (∑' k, Φ k) ^ ρ⁻¹) ^ q.toReal * ∑' μ, W μ ^ q.toReal := by
            simp only [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
            rw [mul_div_cancel₀ _ hρ.ne', inv_mul_eq_div, mul_assoc]
  -- B–L: by Lemma 3.1.3, `‖a‖_K ≤ 2 (log 2)^{1/q} ‖(2^{-μθ} K(2^μ, a))‖_{λ^{θ,q}}`
  set L := ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal
  have hLtop : L ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hL0 : L ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two))
    ENNReal.ofReal_ne_top).ne'
  have hD0 : D ≠ 0 := (ENNReal.ofReal_pos.mpr (mul_pos (by linarith) (by positivity))).ne'
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (inv_pos.mpr hρ).le hΦtop)
  have hM0 : M ≠ 0 :=
    mul_ne_zero hD0 (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hΦ0) hΦtop).ne'
  have hC0 : 2 * L * M ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hL0) hM0
  have hCtop : 2 * L * M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hLtop) hMtop
  refine ⟨2 * L * M, hCtop, fun a => ?_⟩
  rw [jInterpolationENorm, ENNReal.mul_iInf_of_ne hC0 hCtop]
  refine le_iInf fun u => ?_
  rw [ENNReal.mul_iInf_of_ne hC0 hCtop]
  refine le_iInf fun hu => ?_
  calc realInterpolationENorm ι₀ ι₁ θ q a ≤ 2 * L * kSequenceENorm ι₀ ι₁ θ q a :=
        realInterpolationENorm_le_mul_kSequenceENorm ι₀ ι₁ hθ0.le hq a
    _ ≤ 2 * L * (M * jSequenceENorm ι₀ ι₁ θ q u) := mul_le_mul_right (hcore a u hu) _
    _ = 2 * L * M * jSequenceENorm ι₀ ι₁ θ q u := (mul_assoc _ _ _).symm

/-- The equivalence theorem (B–L Theorem 3.11.3): `J_{θ,q}(A) = K_{θ,q}(A)` as subspaces of
`A₀ + A₁`. -/
theorem jInterpolationSubmodule_eq_realInterpolationSubmodule [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    jInterpolationSubmodule ι₀ ι₁ θ q = realInterpolationSubmodule ι₀ ι₁ θ q := by
  obtain ⟨CJ, hCJ, hJ⟩ := exists_jInterpolationENorm_le_mul_realInterpolationENorm ι₀ ι₁ hθ0 hθ1 hq
  obtain ⟨CK, hCK, hK⟩ := exists_realInterpolationENorm_le_mul_jInterpolationENorm ι₀ ι₁ hθ0 hθ1 hq
  ext a
  change jInterpolationENorm ι₀ ι₁ θ q a < ⊤ ↔ realInterpolationENorm ι₀ ι₁ θ q a < ⊤
  exact ⟨fun h => (hK a).trans_lt (ENNReal.mul_lt_top hCK.lt_top h),
    fun h => (hJ a).trans_lt (ENNReal.mul_lt_top hCJ.lt_top h)⟩

end InterpolationCouple
