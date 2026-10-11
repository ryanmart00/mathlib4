/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.KInterpolation
import Mathlib.Analysis.Normed.Quasi.Completeness

/-!
# The real interpolation space `(A₀, A₁)_{θ,q}` as a quasi-Banach space

The unbundled form of the K-method: given two quasi-Banach spaces `A₀`, `A₁` with embeddings
`ι₀ : A₀ →L[𝕜] 𝒜`, `ι₁ : A₁ →L[𝕜] 𝒜` into a common Hausdorff TVS, the real interpolation space
`(A₀, A₁)_{θ,q}` (Triebel §1.3.2) is the submodule of `A₀ + A₁` of elements of finite
`(θ,q)`-quasinorm `realInterpolationENorm`. For `0 < θ < 1` and `0 < q ≤ ∞` it is a quasi-Banach
space sandwiched between the meet and the sum, `A₀ ∩ A₁ ↪ (A₀, A₁)_{θ,q} ↪ A₀ + A₁`, and every
morphism of couples induces a bounded map between the interpolation spaces (with the "exact of
type `θ`" bound `M₀^{1-θ} M₁^θ`).

The bundled form, the K-method as an `InterpolationFunctor`, is in
`KMethod/KInterpolationFunctor.lean`.

## Main definitions
* `InterpolationCouple.realInterpolationConst θ q`: the `(θ,q)`-quasinorm of `t ↦ min 1 t`, the
  constant in both halves of the sandwich.
* `InterpolationCouple.RealInterpolationSpace ι₀ ι₁ θ q : Submodule 𝕜 (sum ι₀ ι₁)`.
* `InterpolationCouple.RealInterpolationSpace.toSum`, `.fromMeet`: the sandwich maps.
* `InterpolationCat.Hom.realInterpolationMap`: the map induced by a morphism of couples.

## Main statements
* `RealInterpolationSpace.instQuasinormedAddCommGroup`, `instQuasiNormedSpace`,
  `instCompleteSpace`.
* `InterpolationCat.Hom.norm_realInterpolationMap_le`: exactness of type `θ`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology QuasinormedAddCommGroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-! ### Properties of the `(θ,q)`-quasinorm -/

/-- The `(θ,q)`-quasinorm of `t ↦ min 1 t`, i.e. `realInterpolationENorm` with `K(t, a)` replaced
by `min 1 t`. Since `min(1,t) ‖a‖ ≤ K(t,a)` on the sum and `K(t,a) ≤ min(1,t) ‖a‖` on the meet,
it is the constant in both halves of the sandwich `A₀ ∩ A₁ ↪ (A₀,A₁)_{θ,q} ↪ A₀ + A₁`. -/
noncomputable def realInterpolationConst (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  if q = ⊤ then
    ⨆ t : Ioi (0 : ℝ), ENNReal.ofReal ((t : ℝ) ^ (-θ) * min 1 (t : ℝ))
  else
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹)
      ^ q⁻¹.toReal

theorem realInterpolationConst_pos (θ : ℝ) (q : ℝ≥0∞) : 0 < realInterpolationConst θ q := by
  unfold realInterpolationConst
  split_ifs with htop
  · refine lt_of_lt_of_le ?_ (le_iSup _ (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)))
    simp
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 htop
  refine ENNReal.rpow_pos_of_nonneg ?_ ENNReal.toReal_nonneg
  have hmeas : Measurable fun t : ℝ =>
      ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹ := by
    fun_prop
  rw [setLIntegral_pos_iff hmeas]
  refine lt_of_lt_of_le (by simp) (measure_mono (s := Ioi (0 : ℝ)) fun t (ht : 0 < t) => ⟨?_, ht⟩)
  have h1 : 0 < t ^ (-θ) * min 1 t := mul_pos (Real.rpow_pos_of_pos ht _) (lt_min one_pos ht)
  exact mul_ne_zero (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr h1) ENNReal.ofReal_ne_top).ne'
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr ht)).ne'

theorem realInterpolationConst_lt_top {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) :
    realInterpolationConst θ q < ⊤ := by
  have hpow : ∀ t : ℝ, 0 < t → t ^ (-θ) * t = t ^ (1 - θ) := fun t ht => by
    rw [show (1 : ℝ) - θ = -θ + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  unfold realInterpolationConst
  split_ifs with htop
  · refine lt_of_le_of_lt (iSup_le fun t => ?_) ENNReal.one_lt_top
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have ht : (0 : ℝ) < t := t.2
    rcases le_total (t : ℝ) 1 with h | h
    · rw [min_eq_right h, hpow t ht]
      exact Real.rpow_le_one ht.le h (by linarith)
    · rw [min_eq_left h, mul_one]
      exact Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 htop
  suffices hfin : ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹ < ⊤ from
    ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hfin.ne
  have hle1 : ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (t ^ ((1 - θ) * q.toReal - 1)) := by
    rintro t ⟨ht0, ht1⟩
    have h := rpow_pow_dtOverT_eq (p := 1 - θ) ht0 zero_le_one hr.le
    rw [Real.one_rpow, ENNReal.ofReal_one, one_mul, mul_one] at h
    rw [min_eq_right ht1, hpow t ht0, h]
  have hle2 : ∀ t ∈ Ioi (1 : ℝ),
      ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (t ^ (-θ * q.toReal - 1)) := by
    intro t ht1
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have h := rpow_pow_dtOverT_eq (p := -θ) ht0 zero_le_one hr.le
    rw [Real.one_rpow, ENNReal.ofReal_one, one_mul, mul_one] at h
    rw [min_eq_left (le_of_lt ht1), mul_one, h]
  have hint1 : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((1 - θ) * q.toReal - 1)) < ⊤ := by
    apply IntegrableOn.setLIntegral_lt_top
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by nlinarith))
  have hint2 : ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-θ * q.toReal - 1)) < ⊤ :=
    (integrableOn_Ioi_rpow_of_lt (by nlinarith) one_pos).setLIntegral_lt_top
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
    rw [Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [hsplit]
  exact lt_of_le_of_lt (lintegral_union_le _ _ _) (ENNReal.add_lt_top.2
    ⟨lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc hle1) hint1,
      lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hle2) hint2⟩)

theorem realInterpolationENorm_zero (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) :
    realInterpolationENorm ι₀ ι₁ θ q 0 = 0 := by
  unfold realInterpolationENorm
  split_ifs with htop
  · refine ENNReal.iSup_eq_zero.mpr fun t => ?_
    rw [kFunctional_zero ι₀ ι₁ _ (le_of_lt t.2), mul_zero, ENNReal.ofReal_zero]
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun t ht => by
      simp only [kFunctional_zero ι₀ ι₁ t (le_of_lt ht), mul_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hr, zero_mul]]
    simp [hr]

theorem realInterpolationENorm_smul (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) (c : 𝕜)
    (a : sum ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q (c • a) = ‖c‖ₑ * realInterpolationENorm ι₀ ι₁ θ q a := by
  have hpt : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (c • a)) =
      ‖c‖ₑ * ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) := by
    intro t ht
    rw [kFunctional_smul ι₀ ι₁ t ht.le, mul_left_comm, ENNReal.ofReal_mul (norm_nonneg c),
      ofReal_norm]
  unfold realInterpolationENorm
  split_ifs with htop
  · rw [ENNReal.mul_iSup]
    exact iSup_congr fun t => hpt t t.2
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun t => ‖c‖ₑ ^ q.toReal *
        (ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) ^ q.toReal * ENNReal.ofReal t⁻¹))
        fun t ht => by
          simp only
          rw [hpt t ht, ENNReal.mul_rpow_of_nonneg _ _ hr.le, mul_assoc],
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le enorm_ne_top),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ENNReal.toReal_inv,
      mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]

/-- The "`⊂ A₀ + A₁`" half of the sandwich, quantitatively: `c_{θ,q} ‖a‖_{A₀+A₁} ≤ ‖a‖_{θ,q}`. -/
theorem ofReal_norm_mul_realInterpolationConst_le (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q)
    (a : sum ι₀ ι₁) :
    ENNReal.ofReal ‖a‖ * realInterpolationConst θ q ≤ realInterpolationENorm ι₀ ι₁ θ q a := by
  have hpt : ∀ t : ℝ, 0 < t → ENNReal.ofReal ‖a‖ * ENNReal.ofReal (t ^ (-θ) * min 1 t) ≤
      ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) := by
    intro t ht
    rw [← ENNReal.ofReal_mul (QuasinormedAddCommGroup.norm_nonneg a)]
    apply ENNReal.ofReal_le_ofReal
    have hK := min_mul_norm_le_kFunctional ι₀ ι₁ t ht.le a
    have h0 : 0 ≤ t ^ (-θ) := Real.rpow_nonneg ht.le _
    nlinarith
  unfold realInterpolationENorm realInterpolationConst
  split_ifs with htop
  · rw [ENNReal.mul_iSup]
    exact iSup_mono fun t => hpt t t.2
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    have hr' : 0 ≤ q⁻¹.toReal := ENNReal.toReal_nonneg
    calc ENNReal.ofReal ‖a‖ * (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal
        = (ENNReal.ofReal ‖a‖ ^ q.toReal * ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹)
              ^ q⁻¹.toReal := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr', ← ENNReal.rpow_mul, ENNReal.toReal_inv,
            mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]
      _ ≤ (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) ^ q.toReal *
            ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal := by
          refine ENNReal.rpow_le_rpow ?_ hr'
          rw [← lintegral_const_mul' _ _
            (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)]
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hr.le]
          gcongr
          exact hpt t ht

theorem realInterpolationENorm_eq_zero_iff (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) (a : sum ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ realInterpolationENorm_zero ι₀ ι₁ θ hq⟩
  have hle := ofReal_norm_mul_realInterpolationConst_le ι₀ ι₁ θ hq a
  rw [h, nonpos_iff_eq_zero, mul_eq_zero] at hle
  rcases hle with h0 | h0
  · rw [ENNReal.ofReal_eq_zero] at h0
    exact (QuasinormedAddCommGroup.norm_eq_zero_iff a).mp
      (le_antisymm h0 (QuasinormedAddCommGroup.norm_nonneg a))
  · exact absurd h0 (realInterpolationConst_pos θ q).ne'

/-- A Fatou-type lower semicontinuity bound: if `y m → z` in `A₀ + A₁` and eventually
`‖y m‖_{θ,q} ≤ R`, then `‖z‖_{θ,q} ≤ Ck · R`, with `Ck` the quasi-triangle constant of the
K-functional (`kFunctional_add_le`). -/
theorem realInterpolationENorm_le_of_tendsto (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q)
    {y : ℕ → sum ι₀ ι₁} {z : sum ι₀ ι₁} (hy : Tendsto y atTop (𝓝 z)) {R : ℝ≥0∞}
    (hR : ∀ᶠ m in atTop, realInterpolationENorm ι₀ ι₁ θ q (y m) ≤ R) :
    realInterpolationENorm ι₀ ι₁ θ q z ≤
      ENNReal.ofReal (max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
        (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))) * R := by
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) with hCk
  have hCk0 : 0 ≤ Ck :=
    zero_le_one.trans (le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst)
  have hnorm : Tendsto (fun m => ‖z - y m‖) atTop (𝓝 0) := by
    refine (QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero.mp hy).congr fun m => ?_
    rw [← neg_sub z (y m), QuasinormedAddCommGroup.norm_neg]
  -- The pointwise (in `t`) Fatou bound for the K-functional.
  have hpt : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ≤
      ENNReal.ofReal Ck *
        liminf (fun m => ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) atTop := by
    intro t ht
    have htθ : 0 ≤ t ^ (-θ) := Real.rpow_nonneg ht.le _
    set e : ℕ → ℝ≥0∞ := fun m =>
      ENNReal.ofReal (Ck * (t ^ (-θ) * (2 * max 1 t * ‖z - y m‖))) with he_def
    have he : Tendsto e atTop (𝓝 0) := by
      have h := tendsto_const_nhds (x := Ck) |>.mul (tendsto_const_nhds (x := t ^ (-θ)) |>.mul
        (tendsto_const_nhds (x := 2 * max 1 t) |>.mul hnorm))
      simpa using ENNReal.tendsto_ofReal h
    have hbound : ∀ m, ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ≤
        ENNReal.ofReal Ck * ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m)) + e m := by
      intro m
      have hK := kFunctional_add_le ι₀ ι₁ t ht.le (y m) (z - y m)
      rw [add_sub_cancel] at hK
      have hK2 := kFunctional_le_two_mul_max_mul_norm ι₀ ι₁ t ht.le (z - y m)
      have hK0 := kFunctional_nonneg ι₀ ι₁ t ht.le (y m)
      have hn := QuasinormedAddCommGroup.norm_nonneg (z - y m)
      rw [he_def, ← ENNReal.ofReal_mul hCk0,
        ← ENNReal.ofReal_add (mul_nonneg hCk0 (mul_nonneg htθ hK0))
          (mul_nonneg hCk0 (mul_nonneg htθ (by positivity)))]
      apply ENNReal.ofReal_le_ofReal
      calc t ^ (-θ) * KFunctional ι₀ ι₁ t z
          ≤ t ^ (-θ) * (Ck * (KFunctional ι₀ ι₁ t (y m) + KFunctional ι₀ ι₁ t (z - y m))) :=
            mul_le_mul_of_nonneg_left hK htθ
        _ = Ck * (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m)) +
              Ck * (t ^ (-θ) * KFunctional ι₀ ι₁ t (z - y m)) := by ring
        _ ≤ Ck * (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m)) +
              Ck * (t ^ (-θ) * (2 * max 1 t * ‖z - y m‖)) := by gcongr
    calc ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z)
        ≤ liminf (fun m => ENNReal.ofReal Ck *
            ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m)) + e m) atTop :=
          le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbound)
      _ = liminf (fun m => ENNReal.ofReal Ck *
            ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) atTop :=
          ENNReal.liminf_add_of_right_tendsto_zero he _
      _ = ENNReal.ofReal Ck *
            liminf (fun m => ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) atTop :=
          ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
  by_cases htop : q = ⊤
  · subst htop
    simp only [realInterpolationENorm, ite_true] at hR ⊢
    calc ⨆ t : Ioi (0 : ℝ), ENNReal.ofReal ((t : ℝ) ^ (-θ) * KFunctional ι₀ ι₁ t z)
        ≤ ⨆ t : Ioi (0 : ℝ), ENNReal.ofReal Ck *
            liminf (fun m => ENNReal.ofReal ((t : ℝ) ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) atTop :=
          iSup_mono fun t => hpt t t.2
      _ ≤ ENNReal.ofReal Ck * liminf (fun m => ⨆ t : Ioi (0 : ℝ),
            ENNReal.ofReal ((t : ℝ) ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) atTop := by
          refine iSup_le fun t => ?_
          gcongr
          exact liminf_le_liminf (Eventually.of_forall fun m => le_iSup (fun t : Ioi (0 : ℝ) =>
            ENNReal.ofReal ((t : ℝ) ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) t)
      _ ≤ ENNReal.ofReal Ck * R := by
          gcongr
          exact liminf_le_of_frequently_le' hR.frequently
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
  simp only [realInterpolationENorm, htop, ite_false, ENNReal.toReal_inv] at hR ⊢
  set r := q.toReal with hr_def
  -- Globally measurable integrands, agreeing with the real ones on `Ioi 0`.
  set G : ℕ → ℝ → ℝ≥0∞ := fun m t =>
    ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ (max t 0) (y m)) ^ r * ENNReal.ofReal t⁻¹
    with hG
  have hGmeas : ∀ m, AEMeasurable (G m) (volume.restrict (Ioi 0)) := fun m => by
    have := kFunctional_max_measurable ι₀ ι₁ (y m)
    exact (by fun_prop : Measurable (G m)).aemeasurable
  have hGeq : ∀ m, ∀ t ∈ Ioi (0 : ℝ), G m t =
      ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m)) ^ r * ENNReal.ofReal t⁻¹ :=
    fun m t ht => by simp only [hG, kFunctional_max_eq ι₀ ι₁ (y m) ht]
  have hptz : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ^ r * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal Ck ^ r * liminf (fun m => G m t) atTop := by
    intro t ht
    have h1 := hpt t ht
    calc ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ^ r * ENNReal.ofReal t⁻¹
        ≤ (ENNReal.ofReal Ck * liminf (fun m =>
            ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m))) atTop) ^ r *
              ENNReal.ofReal t⁻¹ := by gcongr
      _ = ENNReal.ofReal Ck ^ r * (liminf (fun m =>
            ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (y m)) ^ r) atTop *
              ENNReal.ofReal t⁻¹) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, mul_assoc]
          congr 2
          exact (ENNReal.monotone_rpow_of_nonneg hr.le).map_liminf_of_continuousAt _
            ENNReal.continuous_rpow_const.continuousAt
      _ = ENNReal.ofReal Ck ^ r * liminf (fun m => G m t) atTop := by
          congr 1
          rw [mul_comm, ← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
          congr 1
          ext m
          rw [hGeq m t ht, mul_comm]
  have hbound : ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ^ r * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal Ck ^ r * R ^ r := by
    calc ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ^ r * ENNReal.ofReal t⁻¹
        ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal Ck ^ r * liminf (fun m => G m t) atTop :=
          setLIntegral_mono' measurableSet_Ioi hptz
      _ = ENNReal.ofReal Ck ^ r * ∫⁻ t in Ioi (0 : ℝ), liminf (fun m => G m t) atTop :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal Ck ^ r * liminf (fun m => ∫⁻ t in Ioi (0 : ℝ), G m t) atTop := by
          gcongr
          exact lintegral_liminf_le' hGmeas
      _ ≤ ENNReal.ofReal Ck ^ r * R ^ r := by
          gcongr
          refine liminf_le_of_frequently_le' (hR.mono fun m hm => ?_).frequently
          rw [setLIntegral_congr_fun measurableSet_Ioi (hGeq m)]
          exact (ENNReal.rpow_inv_rpow hr.ne' _).symm.le.trans (ENNReal.rpow_le_rpow hm hr.le)
  calc (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t z) ^ r * ENNReal.ofReal t⁻¹) ^ r⁻¹
      ≤ (ENNReal.ofReal Ck ^ r * R ^ r) ^ r⁻¹ :=
        ENNReal.rpow_le_rpow hbound (inv_nonneg.mpr hr.le)
    _ = ENNReal.ofReal Ck * R := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le), ENNReal.rpow_rpow_inv hr.ne',
          ENNReal.rpow_rpow_inv hr.ne']

/-- The "`A₀ ∩ A₁ ⊂`" half of the sandwich, quantitatively: `‖a‖_{θ,q} ≤ c_{θ,q} ‖a‖_{A₀∩A₁}`
(strengthens `realInterpolationENorm_meetToSum_lt_top`). -/
theorem realInterpolationENorm_meetToSum_le (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) (b : meet ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b) ≤
      realInterpolationConst θ q * ENNReal.ofReal ‖b‖ := by
  have hpt : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (meetToSum ι₀ ι₁ b)) ≤
        ENNReal.ofReal (t ^ (-θ) * min 1 t) * ENNReal.ofReal ‖b‖ := by
    intro t ht
    have h0 : 0 ≤ t ^ (-θ) := Real.rpow_nonneg ht.le _
    rw [← ENNReal.ofReal_mul (mul_nonneg h0 (le_min zero_le_one ht.le))]
    apply ENNReal.ofReal_le_ofReal
    have hK := kFunctional_meetToSum_le ι₀ ι₁ t ht.le b
    nlinarith
  unfold realInterpolationENorm realInterpolationConst
  split_ifs with htop
  · rw [ENNReal.iSup_mul]
    exact iSup_mono fun t => hpt t t.2
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    have hr' : 0 ≤ q⁻¹.toReal := ENNReal.toReal_nonneg
    calc (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (meetToSum ι₀ ι₁ b)) ^ q.toReal *
              ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal
        ≤ (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ‖b‖ ^ q.toReal *
            (ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹))
              ^ q⁻¹.toReal := by
          refine ENNReal.rpow_le_rpow (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_) hr'
          rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hr.le,
            mul_comm (ENNReal.ofReal ‖b‖)]
          gcongr
          exact hpt t ht
      _ = (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-θ) * min 1 t) ^ q.toReal * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal *
              ENNReal.ofReal ‖b‖ := by
          rw [lintegral_const_mul' _ _
              (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ hr', ← ENNReal.rpow_mul, ENNReal.toReal_inv,
            mul_inv_cancel₀ hr.ne', ENNReal.rpow_one, mul_comm]

omit [T2Space 𝒜] in
/-- Pointwise control of the K-functional by the `(θ,q)`-quasinorm (Bergh–Löfström Theorem 3.1.2,
formula (6)): `c_{θ,q} t^{-θ} K(t,a) ≤ ‖a‖_{θ,q}` for all `t > 0`, where
`c_{θ,q} = realInterpolationConst θ q` is the `(θ,q)`-quasinorm of `t ↦ min 1 t` (B–L's
`1/γ_{θ,q}`). At `t = 1` this is essentially `ofReal_norm_mul_realInterpolationConst_le`, since
`‖a‖ ≤ K(1,a)`. -/
theorem ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le (θ : ℝ) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) * realInterpolationConst θ q ≤
      realInterpolationENorm ι₀ ι₁ θ q a := by
  have htθ : 0 ≤ t ^ (-θ) := Real.rpow_nonneg ht.le _
  -- B–L: by Lemma 3.1.1 (1), `min(1, u/t) K(t,a) ≤ K(u,a)`; multiply by `u^{-θ}`.
  have hpt (u : ℝ) (hu : 0 < u) :
      ENNReal.ofReal (KFunctional ι₀ ι₁ t a) * ENNReal.ofReal (u ^ (-θ) * min 1 (u / t)) ≤
        ENNReal.ofReal (u ^ (-θ) * KFunctional ι₀ ι₁ u a) := by
    have hu' : 0 ≤ u ^ (-θ) := Real.rpow_nonneg hu.le _
    rw [← ENNReal.ofReal_mul (kFunctional_nonneg ι₀ ι₁ t ht.le a)]
    apply ENNReal.ofReal_le_ofReal
    calc KFunctional ι₀ ι₁ t a * (u ^ (-θ) * min 1 (u / t))
        = u ^ (-θ) * (min 1 (u / t) * KFunctional ι₀ ι₁ t a) := by ring
      _ ≤ u ^ (-θ) * KFunctional ι₀ ι₁ u a :=
          mul_le_mul_of_nonneg_left (min_one_div_mul_kFunctional_le ι₀ ι₁ ht hu.le a) hu'
  -- B–L (7): `Φ_{θ,q}(min(1, u/t)) = t^{-θ} Φ_{θ,q}(min(1, u))`, pointwise under `u = t v`.
  have hscale (v : ℝ) (hv : 0 < v) :
      (t * v) ^ (-θ) * min 1 (t * v / t) = t ^ (-θ) * (v ^ (-θ) * min 1 v) := by
    rw [Real.mul_rpow ht.le hv.le, mul_div_cancel_left₀ v ht.ne']
    ring
  rw [ENNReal.ofReal_mul htθ]
  unfold realInterpolationENorm realInterpolationConst
  split_ifs with htop
  · -- `q = ∞`
    rw [ENNReal.mul_iSup]
    refine iSup_le fun v => le_iSup_of_le ⟨t * v, mul_pos ht v.2⟩ ?_
    have h := hpt (t * v) (mul_pos ht v.2)
    rw [hscale v v.2, ENNReal.ofReal_mul htθ] at h
    calc ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (KFunctional ι₀ ι₁ t a) *
          ENNReal.ofReal ((v : ℝ) ^ (-θ) * min 1 (v : ℝ))
        = ENNReal.ofReal (KFunctional ι₀ ι₁ t a) * (ENNReal.ofReal (t ^ (-θ)) *
          ENNReal.ofReal ((v : ℝ) ^ (-θ) * min 1 (v : ℝ))) := by ring
      _ ≤ _ := h
  · -- `q < ∞`
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    have hr' : 0 ≤ q⁻¹.toReal := ENNReal.toReal_nonneg
    -- B–L (7) for the integral, by the dilation invariance of `dt/t`
    have hΦ : (∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-θ) * min 1 (u / t)) ^ q.toReal * ENNReal.ofReal u⁻¹) =
        ENNReal.ofReal (t ^ (-θ)) ^ q.toReal * ∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (v ^ (-θ) * min 1 v) ^ q.toReal * ENNReal.ofReal v⁻¹ := by
      rw [← lintegral_Ioi_comp_mul_left_div_self ht
          (F := fun u => ENNReal.ofReal (u ^ (-θ) * min 1 (u / t)) ^ q.toReal) (by fun_prop),
        ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)]
      refine setLIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      rw [hscale v hv, ENNReal.ofReal_mul htθ, ENNReal.mul_rpow_of_nonneg _ _ hr.le, mul_assoc]
    -- B–L: apply `Φ_{θ,q}` to the pointwise inequality.
    calc ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (KFunctional ι₀ ι₁ t a) *
          (∫⁻ v in Ioi (0 : ℝ),
            ENNReal.ofReal (v ^ (-θ) * min 1 v) ^ q.toReal * ENNReal.ofReal v⁻¹) ^ q⁻¹.toReal
        = (ENNReal.ofReal (KFunctional ι₀ ι₁ t a) ^ q.toReal * ∫⁻ u in Ioi (0 : ℝ),
            ENNReal.ofReal (u ^ (-θ) * min 1 (u / t)) ^ q.toReal * ENNReal.ofReal u⁻¹)
              ^ q⁻¹.toReal := by
          rw [hΦ, ENNReal.mul_rpow_of_nonneg _ _ hr', ENNReal.mul_rpow_of_nonneg _ _ hr',
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ENNReal.toReal_inv, mul_inv_cancel₀ hr.ne',
            ENNReal.rpow_one, ENNReal.rpow_one]
          ring
      _ ≤ (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-θ) * KFunctional ι₀ ι₁ u a) ^ q.toReal *
            ENNReal.ofReal u⁻¹) ^ q⁻¹.toReal := by
          refine ENNReal.rpow_le_rpow ?_ hr'
          rw [← lintegral_const_mul' _ _
            (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)]
          refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
          rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hr.le]
          gcongr
          exact hpt u hu

omit [T2Space 𝒜] in
/-- The consequence of `ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le` used in
Bergh–Löfström's proof of Theorem 3.3.1: `K(t,a) ≤ M t^θ` for an element of finite
`(θ,q)`-quasinorm. -/
theorem exists_kFunctional_le_mul_rpow (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q)
    {a : sum ι₀ ι₁} (ha : realInterpolationENorm ι₀ ι₁ θ q a ≠ ⊤) :
    ∃ M : ℝ, ∀ t : ℝ, 0 < t → KFunctional ι₀ ι₁ t a ≤ M * t ^ θ := by
  set c := realInterpolationConst θ q
  have hc0 : c ≠ 0 := (realInterpolationConst_pos θ q).ne'
  have h6 := fun t (ht : 0 < t) =>
    ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le ι₀ ι₁ θ hq a ht
  -- `K(t,a) = t^θ · (t^{-θ} K(t,a))`
  have hsplit (t : ℝ) (ht : 0 < t) :
      KFunctional ι₀ ι₁ t a = t ^ θ * (t ^ (-θ) * KFunctional ι₀ ι₁ t a) := by
    rw [← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
  rcases eq_or_ne c ⊤ with hct | hct
  · -- `c = ∞` (only possible for `θ ∉ (0,1)`): finiteness of `‖a‖_{θ,q}` forces `K(·,a) = 0`
    refine ⟨0, fun t ht => ?_⟩
    have h := h6 t ht
    rw [show realInterpolationConst θ q = ⊤ from hct] at h
    have h0 : ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a) = 0 := by
      by_contra hne
      exact ha (top_le_iff.mp (ENNReal.mul_top hne ▸ h))
    rw [ENNReal.ofReal_eq_zero] at h0
    rw [hsplit t ht, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht.le _) h0
  · refine ⟨(realInterpolationENorm ι₀ ι₁ θ q a / c).toReal, fun t ht => ?_⟩
    have h := (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).mpr (h6 t ht)
    rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_ne_top ha hc0)] at h
    rw [hsplit t ht, mul_comm _ (t ^ θ)]
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ht.le _)

omit [T2Space 𝒜] in
/-- An element of finite `(θ,q)`-quasinorm has `K(t,a) → 0` as `t → 0⁺` (since
`K(t,a) ≲ t^θ ‖a‖_{θ,q}`). One of the two hypotheses of the fundamental lemma
`exists_jFunctional_le_kFunctional`. -/
theorem tendsto_kFunctional_nhdsGT_zero {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞} (hq : 0 < q)
    {a : sum ι₀ ι₁} (ha : realInterpolationENorm ι₀ ι₁ θ q a ≠ ⊤) :
    Tendsto (fun t => KFunctional ι₀ ι₁ t a) (𝓝[>] 0) (𝓝 0) := by
  -- B–L (proof of Theorem 3.3.1): by (6), `K(t,a) ≤ M t^θ → 0` as `t → 0`.
  obtain ⟨M, hM⟩ := exists_kFunctional_le_mul_rpow ι₀ ι₁ θ hq ha
  have hlim : Tendsto (fun t : ℝ => M * t ^ θ) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.const_mul M).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [Real.zero_rpow hθ.ne', mul_zero] at h
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht using
      kFunctional_nonneg ι₀ ι₁ t (le_of_lt ht) a
  · filter_upwards [self_mem_nhdsWithin] with t ht using hM t ht

omit [T2Space 𝒜] in
/-- An element of finite `(θ,q)`-quasinorm has `K(t,a)/t → 0` as `t → ∞` (since
`K(t,a)/t ≲ t^{θ-1} ‖a‖_{θ,q}`). The other hypothesis of the fundamental lemma
`exists_jFunctional_le_kFunctional`. -/
theorem tendsto_kFunctional_div_atTop {θ : ℝ} (hθ1 : θ < 1) {q : ℝ≥0∞}
    (hq : 0 < q) {a : sum ι₀ ι₁} (ha : realInterpolationENorm ι₀ ι₁ θ q a ≠ ⊤) :
    Tendsto (fun t => KFunctional ι₀ ι₁ t a / t) atTop (𝓝 0) := by
  -- B–L (proof of Theorem 3.3.1): by (6), `K(t,a)/t ≤ M t^{θ-1} → 0` as `t → ∞`.
  obtain ⟨M, hM⟩ := exists_kFunctional_le_mul_rpow ι₀ ι₁ θ hq ha
  have hlim : Tendsto (fun t : ℝ => M * t ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul M
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop 0] with t ht using
      div_nonneg (kFunctional_nonneg ι₀ ι₁ t ht.le a) ht.le
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [div_le_iff₀ ht, mul_assoc, ← Real.rpow_add_one ht.ne', neg_sub, sub_add_cancel]
    exact hM t ht

omit [T2Space 𝒜] in
/-- The real interpolation spaces increase with the second parameter (Bergh–Löfström
Theorem 3.4.1 (b)), with explicit constant: for `0 < θ < 1` and `0 < q ≤ r`,
`‖a‖_{θ,r} ≤ c_{θ,q}^{-(1-q/r)} ‖a‖_{θ,q}`, where `c_{θ,q} = realInterpolationConst θ q`. B–L: by
Theorem 3.1.2 (6), `‖a‖_{θ,∞} ≤ c_{θ,q}⁻¹ ‖a‖_{θ,q}`, and
`‖a‖_{θ,r} ≤ ‖a‖_{θ,∞}^{1-q/r} ‖a‖_{θ,q}^{q/r}`. For `r = ∞` the exponent `1 - q.toReal / r.toReal`
is `1`, by the `x / 0 = 0` convention. -/
theorem realInterpolationENorm_le_of_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {q r : ℝ≥0∞} (hq : 0 < q) (hqr : q ≤ r) (a : sum ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ r a ≤
      (realInterpolationConst θ q)⁻¹ ^ (1 - q.toReal / r.toReal) *
        realInterpolationENorm ι₀ ι₁ θ q a := by
  set c := realInterpolationConst θ q
  have hc0 : c ≠ 0 := (realInterpolationConst_pos θ q).ne'
  have hct : c ≠ ⊤ := (realInterpolationConst_lt_top hθ0 hθ1 q).ne
  set φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t a)
  set Ntop := realInterpolationENorm ι₀ ι₁ θ ⊤ a
  set Nq := realInterpolationENorm ι₀ ι₁ θ q a
  have hφNtop (t : ℝ) (ht : 0 < t) : φ t ≤ Ntop := by
    simp only [Ntop, realInterpolationENorm, ite_true]
    exact le_iSup (fun t : Ioi (0 : ℝ) => φ t) ⟨t, ht⟩
  -- B–L Theorem 3.1.2 (6): `‖a‖_{θ,∞} ≤ c_{θ,q}⁻¹ ‖a‖_{θ,q}`
  have h6 : Ntop ≤ c⁻¹ * Nq := by
    simp only [Ntop, realInterpolationENorm, ite_true]
    refine iSup_le fun t => ?_
    rw [← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).mpr
      (ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le ι₀ ι₁ θ hq a t.2)
  rcases eq_or_ne r ⊤ with rfl | hr
  · simpa using h6
  rcases eq_or_ne Nq ⊤ with hNq | hNq
  · rw [hNq, ENNReal.mul_top (ENNReal.rpow_pos (ENNReal.inv_pos.2 hct)
      (ENNReal.inv_ne_top.2 hc0)).ne']
    exact le_top
  have hNtop : Ntop ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hNq) h6
  have hq' : q ≠ ⊤ := ne_top_of_le_ne_top hr hqr
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hq'
  have hqr' : q.toReal ≤ r.toReal := ENNReal.toReal_mono hr hqr
  have hr0 : 0 < r.toReal := hq0.trans_le hqr'
  set s := q.toReal / r.toReal with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : 0 ≤ 1 - s := sub_nonneg.2 (div_le_one_of_le₀ hqr' hr0.le)
  -- B–L: `‖a‖_{θ,r}^r = ∫ φ^{r-q} φ^q dt/t ≤ ‖a‖_{θ,∞}^{r-q} ‖a‖_{θ,q}^q`
  have hint : ∫⁻ t in Ioi (0 : ℝ), φ t ^ r.toReal * ENNReal.ofReal t⁻¹ ≤
      Ntop ^ (r.toReal - q.toReal) * Nq ^ q.toReal := by
    have hNq' : Nq ^ q.toReal = ∫⁻ t in Ioi (0 : ℝ), φ t ^ q.toReal * ENNReal.ofReal t⁻¹ := by
      simp only [Nq, realInterpolationENorm, hq', ite_false]
      rw [← ENNReal.rpow_mul, ENNReal.toReal_inv, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    rw [hNq', ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hqr') hNtop)]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [← mul_assoc]
    gcongr ?_ * _
    calc φ t ^ r.toReal = φ t ^ (r.toReal - q.toReal) * φ t ^ q.toReal := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hqr') hq0.le, sub_add_cancel]
      _ ≤ Ntop ^ (r.toReal - q.toReal) * φ t ^ q.toReal := by
          gcongr
          exact hφNtop t ht
  -- B–L: `‖a‖_{θ,r} ≤ ‖a‖_{θ,∞}^{1-q/r} ‖a‖_{θ,q}^{q/r}`, then (6)
  calc realInterpolationENorm ι₀ ι₁ θ r a
      = (∫⁻ t in Ioi (0 : ℝ), φ t ^ r.toReal * ENNReal.ofReal t⁻¹) ^ r⁻¹.toReal := by
        simp only [realInterpolationENorm, hr, ite_false, φ]
    _ ≤ (Ntop ^ (r.toReal - q.toReal) * Nq ^ q.toReal) ^ r⁻¹.toReal :=
        ENNReal.rpow_le_rpow hint ENNReal.toReal_nonneg
    _ = Ntop ^ (1 - s) * Nq ^ s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, ENNReal.toReal_inv, hs, ← div_eq_mul_inv, ← div_eq_mul_inv,
          sub_div, div_self hr0.ne']
    _ ≤ (c⁻¹ * Nq) ^ (1 - s) * Nq ^ s := by gcongr
    _ = c⁻¹ ^ (1 - s) * Nq := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs1, mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ hs1 hs0, sub_add_cancel, ENNReal.rpow_one]

omit [T2Space 𝒜] in
/-- Existential form of `realInterpolationENorm_le_of_le` (Bergh–Löfström Theorem 3.4.1 (b)). -/
theorem exists_realInterpolationENorm_le_of_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {q r : ℝ≥0∞} (hq : 0 < q) (hqr : q ≤ r) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum ι₀ ι₁,
      realInterpolationENorm ι₀ ι₁ θ r a ≤ C * realInterpolationENorm ι₀ ι₁ θ q a := by
  refine ⟨_, ?_, realInterpolationENorm_le_of_le ι₀ ι₁ hθ0 hθ1 hq hqr⟩
  simp [ENNReal.rpow_eq_top_iff, (realInterpolationConst_pos θ q).ne',
    (realInterpolationConst_lt_top hθ0 hθ1 q).ne]

/-! ### The space -/

/-- The submodule of `A₀ + A₁` of elements of finite `(θ,q)`-quasinorm. Defined for every `θ, q`
(at `q = 0` the quasinorm is constantly `1` and this is all of `A₀ + A₁`). The quasi-Banach space
`(A₀, A₁)_{θ,q}` is `RealInterpolationSpace`, a type synonym of this submodule. -/
noncomputable def realInterpolationSubmodule (θ : ℝ) (q : ℝ≥0∞) : Submodule 𝕜 (sum ι₀ ι₁) where
  carrier := {a | realInterpolationENorm ι₀ ι₁ θ q a < ⊤}
  zero_mem' := by
    change realInterpolationENorm ι₀ ι₁ θ q 0 < ⊤
    rcases eq_or_ne q 0 with rfl | hq
    · simp [realInterpolationENorm]
    · rw [realInterpolationENorm_zero ι₀ ι₁ θ (pos_iff_ne_zero.mpr hq)]
      exact ENNReal.zero_lt_top
  add_mem' := by
    intro a b (ha : realInterpolationENorm ι₀ ι₁ θ q a < ⊤)
      (hb : realInterpolationENorm ι₀ ι₁ θ q b < ⊤)
    change realInterpolationENorm ι₀ ι₁ θ q (a + b) < ⊤
    rcases eq_or_ne q 0 with rfl | hq
    · simp [realInterpolationENorm]
    obtain ⟨C, -, hC⟩ := exists_realInterpolationENorm_add_le ι₀ ι₁ θ (pos_iff_ne_zero.mpr hq)
    exact (hC a b).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨ha, hb⟩))
  smul_mem' := by
    intro c a (ha : realInterpolationENorm ι₀ ι₁ θ q a < ⊤)
    change realInterpolationENorm ι₀ ι₁ θ q (c • a) < ⊤
    rcases eq_or_ne q 0 with rfl | hq
    · simp [realInterpolationENorm]
    rw [realInterpolationENorm_smul ι₀ ι₁ θ (pos_iff_ne_zero.mpr hq)]
    exact ENNReal.mul_lt_top enorm_lt_top ha

/-- `(A₀, A₁)_{θ,q}` (Triebel §1.3.2): the elements of `A₀ + A₁` of finite `(θ,q)`-quasinorm; a
quasi-Banach space for `0 < θ < 1`, `0 < q`.

This is a type synonym for `realInterpolationSubmodule` rather than the coerced submodule itself:
`A₀ + A₁` carries its own topology, and the coerced submodule would inherit the subtype topology,
a second topology (non-defeq to the quasinorm one) on the same type. -/
def RealInterpolationSpace (θ : ℝ) (q : ℝ≥0∞) : Type _ :=
  realInterpolationSubmodule ι₀ ι₁ θ q

namespace RealInterpolationSpace

variable {θ : ℝ} {q : ℝ≥0∞}

noncomputable instance instAddCommGroup : AddCommGroup (RealInterpolationSpace ι₀ ι₁ θ q) :=
  inferInstanceAs (AddCommGroup (realInterpolationSubmodule ι₀ ι₁ θ q))

noncomputable instance instModule : Module 𝕜 (RealInterpolationSpace ι₀ ι₁ θ q) :=
  inferInstanceAs (Module 𝕜 (realInterpolationSubmodule ι₀ ι₁ θ q))

/-- Elements of `(A₀, A₁)_{θ,q}` coerce to `A₀ + A₁`. -/
instance instCoeOut : CoeOut (RealInterpolationSpace ι₀ ι₁ θ q) (sum ι₀ ι₁) :=
  ⟨fun a => Subtype.val (p := (· ∈ realInterpolationSubmodule ι₀ ι₁ θ q)) a⟩

noncomputable instance instNorm : Norm (RealInterpolationSpace ι₀ ι₁ θ q) where
  norm a := (realInterpolationENorm ι₀ ι₁ θ q a).toReal

theorem norm_def (a : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖a‖ = (realInterpolationENorm ι₀ ι₁ θ q a).toReal :=
  rfl

variable (θ q) in
/-- The quasi-triangle constant of `(A₀, A₁)_{θ,q}`, extracted from
`exists_realInterpolationENorm_add_le`. -/
noncomputable def quasiTriangleConst [Fact (0 < q)] : ℝ :=
  Classical.choose (exists_realInterpolationENorm_add_le ι₀ ι₁ θ (Fact.out : 0 < q))

theorem one_le_quasiTriangleConst [Fact (0 < q)] : 1 ≤ quasiTriangleConst ι₀ ι₁ θ q :=
  (Classical.choose_spec (exists_realInterpolationENorm_add_le ι₀ ι₁ θ (Fact.out : 0 < q))).1

theorem norm_add_le [Fact (0 < q)] (a b : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖a + b‖ ≤ quasiTriangleConst ι₀ ι₁ θ q * (‖a‖ + ‖b‖) := by
  have hC := (Classical.choose_spec
    (exists_realInterpolationENorm_add_le ι₀ ι₁ θ (Fact.out : 0 < q))).2 a b
  have ha : realInterpolationENorm ι₀ ι₁ θ q (a : sum ι₀ ι₁) < ⊤ := a.2
  have hb : realInterpolationENorm ι₀ ι₁ θ q (b : sum ι₀ ι₁) < ⊤ := b.2
  have h1 : 0 ≤ quasiTriangleConst ι₀ ι₁ θ q := zero_le_one.trans (one_le_quasiTriangleConst ι₀ ι₁)
  rw [norm_def, norm_def, norm_def]
  calc (realInterpolationENorm ι₀ ι₁ θ q ((a + b : RealInterpolationSpace ι₀ ι₁ θ q) :
          sum ι₀ ι₁)).toReal
      ≤ (ENNReal.ofReal (quasiTriangleConst ι₀ ι₁ θ q) *
          (realInterpolationENorm ι₀ ι₁ θ q a + realInterpolationENorm ι₀ ι₁ θ q b)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_lt_top.mpr ⟨ha, hb⟩).ne) hC
    _ = quasiTriangleConst ι₀ ι₁ θ q * ((realInterpolationENorm ι₀ ι₁ θ q a).toReal +
          (realInterpolationENorm ι₀ ι₁ θ q b).toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, ENNReal.toReal_add ha.ne hb.ne]

theorem norm_neg (a : RealInterpolationSpace ι₀ ι₁ θ q) : ‖-a‖ = ‖a‖ := by
  rw [norm_def, norm_def]
  congr 1
  change realInterpolationENorm ι₀ ι₁ θ q (-(a : sum ι₀ ι₁)) = _
  rcases eq_or_ne q 0 with rfl | hq
  · simp [realInterpolationENorm]
  rw [← neg_one_smul 𝕜 (a : sum ι₀ ι₁),
    realInterpolationENorm_smul ι₀ ι₁ θ (pos_iff_ne_zero.mpr hq), enorm_neg, enorm_one, one_mul]

theorem norm_eq_zero_iff [Fact (0 < q)] (a : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖a‖ = 0 ↔ a = 0 := by
  have ha : realInterpolationENorm ι₀ ι₁ θ q (a : sum ι₀ ι₁) < ⊤ := a.2
  rw [norm_def, ENNReal.toReal_eq_zero_iff, or_iff_left ha.ne,
    realInterpolationENorm_eq_zero_iff ι₀ ι₁ θ Fact.out]
  exact Submodule.coe_eq_zero (x := (a : realInterpolationSubmodule ι₀ ι₁ θ q))

/-- The quasi-normed group structure on `(A₀, A₁)_{θ,q}`, for `0 < q`. Built exactly as
`LorentzSpace.instQuasinormedAddCommGroup`. -/
noncomputable instance instQuasinormedAddCommGroup [Fact (0 < q)] :
    QuasinormedAddCommGroup (RealInterpolationSpace ι₀ ι₁ θ q) := by
  let hB : AddGroupFilterBasis (RealInterpolationSpace ι₀ ι₁ θ q) :=
    AddGroupFilterBasis.ofQuasiNorm (quasiTriangleConst ι₀ ι₁ θ q)
      (one_le_quasiTriangleConst ι₀ ι₁) (norm_add_le ι₀ ι₁) (norm_neg ι₀ ι₁)
      (norm_eq_zero_iff ι₀ ι₁)
  exact
    { quasiTriangleConst := quasiTriangleConst ι₀ ι₁ θ q
      one_le_quasiTriangleConst := one_le_quasiTriangleConst ι₀ ι₁
      norm_add_le := norm_add_le ι₀ ι₁
      norm_neg := norm_neg ι₀ ι₁
      norm_eq_zero_iff := norm_eq_zero_iff ι₀ ι₁
      toUniformSpace := hB.uniformSpace
      toIsTopologicalAddGroup := hB.isTopologicalAddGroup
      toIsUniformAddGroup := hB.isUniformAddGroup
      nhds_zero_hasBasis := by
        change (@nhds _ hB.uniformSpace.toTopologicalSpace 0).HasBasis (0 < ·)
          fun ε : ℝ => {x : RealInterpolationSpace ι₀ ι₁ θ q | ‖x‖ < ε}
        rw [hB.nhds_eq (x₀ := 0), AddGroupFilterBasis.N_zero]
        refine (FilterBasis.hasBasis hB.toFilterBasis).to_hasBasis' ?_ ?_
        · rintro s ⟨ε, hε, rfl⟩
          exact ⟨ε, hε, subset_rfl⟩
        · rintro ε hε
          exact FilterBasis.mem_filter_of_mem _ ⟨ε, hε, rfl⟩ }

theorem norm_smul [Fact (0 < q)] (c : 𝕜) (a : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖c • a‖ = ‖c‖ * ‖a‖ := by
  rw [norm_def, norm_def]
  change (realInterpolationENorm ι₀ ι₁ θ q (c • (a : sum ι₀ ι₁))).toReal = _
  rw [realInterpolationENorm_smul ι₀ ι₁ θ Fact.out, ENNReal.toReal_mul, toReal_enorm]

noncomputable instance instQuasiNormedSpace [Fact (0 < q)] :
    QuasiNormedSpace 𝕜 (RealInterpolationSpace ι₀ ι₁ θ q) where
  norm_smul_le c a := (norm_smul ι₀ ι₁ c a).le

/-! ### The sandwich maps -/

variable (θ q) in
/-- The inclusion `(A₀, A₁)_{θ,q} ↪ A₀ + A₁`, continuous by
`ofReal_norm_mul_realInterpolationConst_le`. -/
noncomputable def toSum [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    RealInterpolationSpace ι₀ ι₁ θ q →L[𝕜] sum ι₀ ι₁ where
  toLinearMap := (realInterpolationSubmodule ι₀ ι₁ θ q).subtype
  cont := by
    have hcpos : 0 < (realInterpolationConst θ q).toReal :=
      ENNReal.toReal_pos (realInterpolationConst_pos θ q).ne'
        (realInterpolationConst_lt_top (Fact.out : 0 < θ) (Fact.out : θ < 1) q).ne
    refine QuasinormedAddCommGroup.continuous_of_bound (E := RealInterpolationSpace ι₀ ι₁ θ q)
      (F := sum ι₀ ι₁) (realInterpolationSubmodule ι₀ ι₁ θ q).subtype.toAddMonoidHom
      (realInterpolationConst θ q).toReal⁻¹ fun a => ?_
    have ha : realInterpolationENorm ι₀ ι₁ θ q (a : sum ι₀ ι₁) < ⊤ := a.2
    have h := ENNReal.toReal_mono ha.ne
      (ofReal_norm_mul_realInterpolationConst_le ι₀ ι₁ θ (Fact.out : 0 < q) (a : sum ι₀ ι₁))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (QuasinormedAddCommGroup.norm_nonneg _)] at h
    change ‖(a : sum ι₀ ι₁)‖ ≤ _ * (realInterpolationENorm ι₀ ι₁ θ q a).toReal
    rw [inv_mul_eq_div, le_div_iff₀ hcpos]
    exact h

@[simp]
theorem toSum_apply [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]
    (a : RealInterpolationSpace ι₀ ι₁ θ q) : toSum ι₀ ι₁ θ q a = (a : sum ι₀ ι₁) :=
  rfl

theorem toSum_injective [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    Function.Injective (toSum ι₀ ι₁ θ q) :=
  Subtype.val_injective

variable (θ q) in
/-- The inclusion `A₀ ∩ A₁ ↪ (A₀, A₁)_{θ,q}`, continuous by
`realInterpolationENorm_meetToSum_le`. -/
noncomputable def fromMeet [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    meet ι₀ ι₁ →L[𝕜] RealInterpolationSpace ι₀ ι₁ θ q where
  toLinearMap := (meetToSum ι₀ ι₁ : meet ι₀ ι₁ →ₗ[𝕜] sum ι₀ ι₁).codRestrict _ fun b =>
    realInterpolationENorm_meetToSum_lt_top ι₀ ι₁ θ Fact.out Fact.out q Fact.out b
  cont := by
    refine QuasinormedAddCommGroup.continuous_of_bound (E := meet ι₀ ι₁)
      (F := RealInterpolationSpace ι₀ ι₁ θ q)
      (LinearMap.toAddMonoidHom <| (meetToSum ι₀ ι₁ : meet ι₀ ι₁ →ₗ[𝕜] sum ι₀ ι₁).codRestrict
        (realInterpolationSubmodule ι₀ ι₁ θ q) fun b =>
          realInterpolationENorm_meetToSum_lt_top ι₀ ι₁ θ Fact.out Fact.out q Fact.out b)
      (realInterpolationConst θ q).toReal fun b => ?_
    have h := realInterpolationENorm_meetToSum_le ι₀ ι₁ θ (Fact.out : 0 < q) b
    have hct := realInterpolationConst_lt_top (Fact.out : 0 < θ) (Fact.out : θ < 1) q
    change (realInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b)).toReal ≤ _
    calc (realInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b)).toReal
        ≤ (realInterpolationConst θ q * ENNReal.ofReal ‖b‖).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hct.ne ENNReal.ofReal_ne_top) h
      _ = (realInterpolationConst θ q).toReal * ‖b‖ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (QuasinormedAddCommGroup.norm_nonneg b)]

theorem toSum_comp_fromMeet [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    (toSum ι₀ ι₁ θ q).comp (fromMeet ι₀ ι₁ θ q) = meetToSum ι₀ ι₁ :=
  ContinuousLinearMap.ext fun _ => rfl

/-! ### Completeness -/

/-- `(A₀, A₁)_{θ,q}` is complete (Triebel §1.3.2, Theorem 1(a)): a Cauchy sequence is Cauchy in
`A₀ + A₁` (by the sandwich bound), converges there, and the limit is also its limit in
`(A₀, A₁)_{θ,q}` by a Fatou argument on the K-functional. -/
instance instCompleteSpace [CompleteSpace A₀] [CompleteSpace A₁] [Fact (0 < θ)] [Fact (θ < 1)]
    [Fact (0 < q)] :
    CompleteSpace (RealInterpolationSpace ι₀ ι₁ θ q) := by
  refine QuasinormedAddCommGroup.completeSpace_of_cauchy_complete fun f B hB hf => ?_
  have hBt : Tendsto B atTop (𝓝 0) := hB.tendsto_atTop_zero
  have hB0 : ∀ n, 0 ≤ B n := fun n =>
    (QuasinormedAddCommGroup.norm_nonneg _).trans (hf n n n le_rfl le_rfl).le
  -- The image in `A₀ + A₁` is Cauchy, hence converges to some `s`.
  have hfC : CauchySeq f := QuasinormedAddCommGroup.cauchySeq_of_le_tendsto_zero B
    (fun N n m hn hm => (hf N n m hn hm).le) hBt
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete
    ((toSum ι₀ ι₁ θ q).uniformContinuous.comp_cauchySeq hfC)
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) with hCk
  have hCk0 : 0 ≤ Ck :=
    zero_le_one.trans (le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst)
  -- By the Fatou bound, `s - f n` has `(θ,q)`-quasinorm at most `Ck · B n`.
  have hkey : ∀ n, realInterpolationENorm ι₀ ι₁ θ q (s - (f n : sum ι₀ ι₁)) ≤
      ENNReal.ofReal Ck * ENNReal.ofReal (B n) := by
    intro n
    refine realInterpolationENorm_le_of_tendsto ι₀ ι₁ θ Fact.out
      (y := fun m => (f m : sum ι₀ ι₁) - (f n : sum ι₀ ι₁)) (hs.sub_const _) ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    have hfin : realInterpolationENorm ι₀ ι₁ θ q ((f m : sum ι₀ ι₁) - (f n : sum ι₀ ι₁)) < ⊤ :=
      (f m - f n).2
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact ENNReal.ofReal_le_ofReal (hf n m n hm le_rfl).le
  have hmem : s ∈ realInterpolationSubmodule ι₀ ι₁ θ q := by
    rw [← sub_add_cancel s (f 0 : sum ι₀ ι₁)]
    exact (realInterpolationSubmodule ι₀ ι₁ θ q).add_mem
      ((hkey 0).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
      (f 0).2
  let x : RealInterpolationSpace ι₀ ι₁ θ q := ⟨s, hmem⟩
  refine ⟨x, QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  refine squeeze_zero (fun n => QuasinormedAddCommGroup.norm_nonneg _) (fun n => ?_)
    (by simpa using hBt.const_mul Ck)
  rw [show f n - x = -(x - f n) from (neg_sub _ _).symm, norm_neg, norm_def]
  change (realInterpolationENorm ι₀ ι₁ θ q (s - (f n : sum ι₀ ι₁))).toReal ≤ _
  calc (realInterpolationENorm ι₀ ι₁ θ q (s - (f n : sum ι₀ ι₁))).toReal
      ≤ (ENNReal.ofReal Ck * ENNReal.ofReal (B n)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          (hkey n)
    _ = Ck * B n := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCk0,
        ENNReal.toReal_ofReal (hB0 n)]

end RealInterpolationSpace

end InterpolationCouple

/-! ### Functoriality -/

namespace InterpolationCat.Hom

open CategoryTheory InterpolationCouple

variable {C D E : InterpolationCat 𝕜} (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)]
  [Fact (0 < q)]

/-- The linear map underlying `realInterpolationMap`: the restriction of `T.sumMap`. -/
noncomputable def realInterpolationMapₗ (T : C ⟶ D) :
    RealInterpolationSpace C.ι₀ C.ι₁ θ q →ₗ[𝕜] RealInterpolationSpace D.ι₀ D.ι₁ θ q :=
    ((T.sumMap : sum C.ι₀ C.ι₁ →ₗ[𝕜] sum D.ι₀ D.ι₁).comp
      (realInterpolationSubmodule C.ι₀ C.ι₁ θ q).subtype).codRestrict _ (by
        intro a
        change realInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap (a : sum C.ι₀ C.ι₁)) < ⊤
        have ha : realInterpolationENorm C.ι₀ C.ι₁ θ q (a : sum C.ι₀ C.ι₁) < ⊤ := a.2
        have h₀ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₀
        have h₁ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₁
        exact (T.realInterpolationENorm_sumMap_le θ Fact.out Fact.out q Fact.out _ _
          (by linarith) (by linarith) (le_add_of_nonneg_right zero_le_one)
          (le_add_of_nonneg_right zero_le_one) a).trans_lt
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha))

theorem norm_realInterpolationMapₗ_le (T : C ⟶ D) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ‖T.f₀‖ₒₚ ≤ M₀) (h₁ : ‖T.f₁‖ₒₚ ≤ M₁)
    (a : RealInterpolationSpace C.ι₀ C.ι₁ θ q) :
    ‖T.realInterpolationMapₗ θ q a‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖a‖ := by
  have ha : realInterpolationENorm C.ι₀ C.ι₁ θ q (a : sum C.ι₀ C.ι₁) < ⊤ := a.2
  have hb := T.realInterpolationENorm_sumMap_le θ Fact.out Fact.out q Fact.out M₀ M₁ hM₀ hM₁
    h₀ h₁ (a : sum C.ι₀ C.ι₁)
  have hM : 0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ :=
    mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)
  rw [RealInterpolationSpace.norm_def, RealInterpolationSpace.norm_def]
  change (realInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap (a : sum C.ι₀ C.ι₁))).toReal ≤ _
  calc (realInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap (a : sum C.ι₀ C.ι₁))).toReal
      ≤ (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
          realInterpolationENorm C.ι₀ C.ι₁ θ q (a : sum C.ι₀ C.ι₁)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.ne) hb
    _ = M₀ ^ (1 - θ) * M₁ ^ θ * (realInterpolationENorm C.ι₀ C.ι₁ θ q a).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-- The map `(C.A₀, C.A₁)_{θ,q} → (D.A₀, D.A₁)_{θ,q}` induced by a morphism of couples: the
restriction of `T.sumMap`, bounded by `realInterpolationENorm_sumMap_le`. -/
noncomputable def realInterpolationMap (T : C ⟶ D) :
    RealInterpolationSpace C.ι₀ C.ι₁ θ q →L[𝕜] RealInterpolationSpace D.ι₀ D.ι₁ θ q where
  toLinearMap := T.realInterpolationMapₗ θ q
  cont := by
    have h₀ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₀
    have h₁ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₁
    exact QuasinormedAddCommGroup.continuous_of_bound (T.realInterpolationMapₗ θ q).toAddMonoidHom
      _ (T.norm_realInterpolationMapₗ_le θ q (by linarith) (by linarith)
        (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_right zero_le_one))

theorem toSum_comp_realInterpolationMap (T : C ⟶ D) :
    (RealInterpolationSpace.toSum D.ι₀ D.ι₁ θ q).comp (T.realInterpolationMap θ q) =
      T.sumMap.comp (RealInterpolationSpace.toSum C.ι₀ C.ι₁ θ q) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem realInterpolationMap_id (C : InterpolationCat 𝕜) :
    (𝟙 C : C ⟶ C).realInterpolationMap θ q = ContinuousLinearMap.id 𝕜 _ := by
  refine ContinuousLinearMap.ext fun a => Subtype.ext ?_
  change (𝟙 C : C ⟶ C).sumMap (a : sum C.ι₀ C.ι₁) = a
  rw [Hom.sumMap_id]
  rfl

theorem realInterpolationMap_comp (φ : C ⟶ D) (ψ : D ⟶ E) :
    (φ ≫ ψ).realInterpolationMap θ q =
      (ψ.realInterpolationMap θ q).comp (φ.realInterpolationMap θ q) := by
  refine ContinuousLinearMap.ext fun a => Subtype.ext ?_
  change (φ ≫ ψ).sumMap (a : sum C.ι₀ C.ι₁) = ψ.sumMap (φ.sumMap (a : sum C.ι₀ C.ι₁))
  rw [Hom.sumMap_comp]
  rfl

/-- The K-method is exact of type `θ` (Triebel §1.3.3): if `‖T.f₀‖ ≤ M₀` and `‖T.f₁‖ ≤ M₁`, then
the induced map has quasinorm at most `M₀^{1-θ} M₁^θ`. -/
theorem norm_realInterpolationMap_le (T : C ⟶ D) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ‖T.f₀‖ₒₚ ≤ M₀) (h₁ : ‖T.f₁‖ₒₚ ≤ M₁)
    (a : RealInterpolationSpace C.ι₀ C.ι₁ θ q) :
    ‖T.realInterpolationMap θ q a‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖a‖ :=
  T.norm_realInterpolationMapₗ_le θ q hM₀ hM₁ h₀ h₁ a

end InterpolationCat.Hom
