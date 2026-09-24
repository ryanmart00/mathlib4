/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.KMethod.KInterpolation

/-!
# The real interpolation space `(A₀, A₁)_{θ,q}` as a quasi-Banach space

DRAFT — statement-review stage.

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

open MeasureTheory Set
open scoped ENNReal

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

/-! ### The space -/

/-- The submodule of `A₀ + A₁` of elements of finite `(θ,q)`-quasinorm. Defined for every `θ, q`
(at `q = 0` the quasinorm is constantly `1` and this is all of `A₀ + A₁`). The quasi-Banach space
`(A₀, A₁)_{θ,q}` is `RealInterpolationSpace`, a type synonym of this submodule. -/
noncomputable def realInterpolationSubmodule (θ : ℝ) (q : ℝ≥0∞) : Submodule 𝕜 (sum ι₀ ι₁) where
  carrier := {a | realInterpolationENorm ι₀ ι₁ θ q a < ⊤}
  zero_mem' := by
    show realInterpolationENorm ι₀ ι₁ θ q 0 < ⊤
    rcases eq_or_ne q 0 with rfl | hq
    · simp [realInterpolationENorm]
    · rw [realInterpolationENorm_zero ι₀ ι₁ θ (pos_iff_ne_zero.mpr hq)]
      exact ENNReal.zero_lt_top
  add_mem' := by
    intro a b (ha : realInterpolationENorm ι₀ ι₁ θ q a < ⊤)
      (hb : realInterpolationENorm ι₀ ι₁ θ q b < ⊤)
    show realInterpolationENorm ι₀ ι₁ θ q (a + b) < ⊤
    rcases eq_or_ne q 0 with rfl | hq
    · simp [realInterpolationENorm]
    obtain ⟨C, -, hC⟩ := exists_realInterpolationENorm_add_le ι₀ ι₁ θ (pos_iff_ne_zero.mpr hq)
    exact (hC a b).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨ha, hb⟩))
  smul_mem' := by
    intro c a (ha : realInterpolationENorm ι₀ ι₁ θ q a < ⊤)
    show realInterpolationENorm ι₀ ι₁ θ q (c • a) < ⊤
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

/-- `(A₀, A₁)_{θ,q}` is complete (Triebel §1.3.2, Theorem 1(a)): a Cauchy sequence is Cauchy in
`A₀ + A₁` (by the sandwich bound), converges there, and the limit is also its limit in
`(A₀, A₁)_{θ,q}` by a Fatou argument on the K-functional. -/
instance instCompleteSpace [CompleteSpace A₀] [CompleteSpace A₁] [Fact (0 < θ)] [Fact (θ < 1)]
    [Fact (0 < q)] :
    CompleteSpace (RealInterpolationSpace ι₀ ι₁ θ q) := by
  sorry

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
    (toSum ι₀ ι₁ θ q).comp (fromMeet ι₀ ι₁ θ q) = meetToSum ι₀ ι₁ := by
  sorry

end RealInterpolationSpace

end InterpolationCouple

/-! ### Functoriality -/

namespace InterpolationCat.Hom

open CategoryTheory InterpolationCouple

variable {C D E : InterpolationCat 𝕜} (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)]
  [Fact (0 < q)]

/-- The map `(C.A₀, C.A₁)_{θ,q} → (D.A₀, D.A₁)_{θ,q}` induced by a morphism of couples: the
restriction of `T.sumMap`, bounded by `realInterpolationENorm_sumMap_le`. -/
noncomputable def realInterpolationMap (T : C ⟶ D) :
    RealInterpolationSpace C.ι₀ C.ι₁ θ q →L[𝕜] RealInterpolationSpace D.ι₀ D.ι₁ θ q where
  toLinearMap :=
    ((T.sumMap : sum C.ι₀ C.ι₁ →ₗ[𝕜] sum D.ι₀ D.ι₁).comp
      (realInterpolationSubmodule C.ι₀ C.ι₁ θ q).subtype).codRestrict _ (by
        sorry)
  cont := by
    sorry

theorem toSum_comp_realInterpolationMap (T : C ⟶ D) :
    (RealInterpolationSpace.toSum D.ι₀ D.ι₁ θ q).comp (T.realInterpolationMap θ q) =
      T.sumMap.comp (RealInterpolationSpace.toSum C.ι₀ C.ι₁ θ q) := by
  sorry

theorem realInterpolationMap_id (C : InterpolationCat 𝕜) :
    (𝟙 C : C ⟶ C).realInterpolationMap θ q = ContinuousLinearMap.id 𝕜 _ := by
  sorry

theorem realInterpolationMap_comp (φ : C ⟶ D) (ψ : D ⟶ E) :
    (φ ≫ ψ).realInterpolationMap θ q =
      (ψ.realInterpolationMap θ q).comp (φ.realInterpolationMap θ q) := by
  sorry

/-- The K-method is exact of type `θ` (Triebel §1.3.3): if `‖T.f₀‖ ≤ M₀` and `‖T.f₁‖ ≤ M₁`, then
the induced map has quasinorm at most `M₀^{1-θ} M₁^θ`. -/
theorem norm_realInterpolationMap_le (T : C ⟶ D) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : RealInterpolationSpace C.ι₀ C.ι₁ θ q) :
    ‖T.realInterpolationMap θ q a‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖a‖ := by
  sorry

end InterpolationCat.Hom
