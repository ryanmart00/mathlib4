/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JFunctional
import Mathlib.Analysis.Normed.Quasi.AokiRolewicz
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Count

/-!
# Real interpolation spaces via the discrete J-method

The discrete J-method (Bergh–Löfström §3.10–3.11; the continuous version is Triebel §1.6.1).
For an interpolation couple `{A₀, A₁}`, `θ ∈ ℝ` and `0 < q ≤ ∞`, a *representation* of
`a ∈ A₀ + A₁` is a family `u : ℤ → A₀ ∩ A₁` with `a = ∑ᵥ uᵥ` in `A₀ + A₁` (unconditional
summation, `HasSum`). The `(θ,q)` J-quasinorm of `a` is the infimum over representations of the
`ℓ^q(ℤ)` quasinorm of `ν ↦ 2^{-νθ} J(2^ν, uᵥ)`, the latter taken as Mathlib's `eLpNorm` for the
counting measure (so `q = ∞` is the supremum automatically). It is `∞` when `a` has no
representation.

For quasi-Banach couples the series is the right object (an integral `∫ u(t) dt/t` would need a
Banach space); the Aoki–Rolewicz theorem controls `‖∑ᵥ uᵥ‖` in `A₀ + A₁`.

The space itself, as a quasi-normed space with its sandwich and morphism maps, is in
`JMethod/JInterpolationSpace.lean`.

## Main definitions
* `InterpolationCouple.jSequenceENorm θ q u`: `‖(2^{-νθ} J(2^ν, uᵥ))ᵥ‖_{ℓ^q}`.
* `InterpolationCouple.jInterpolationENorm θ q a`: its infimum over representations of `a`.

## Main statements
* `jInterpolationENorm_zero`, `jInterpolationENorm_smul`, `exists_jInterpolationENorm_add_le`.
* `jInterpolationENorm_meetToSum_le`: `‖b‖_J ≤ ‖b‖_{A₀ ∩ A₁}` (one-term representation).
* `exists_ofReal_mul_norm_le_jInterpolationENorm`: `c ‖a‖_{A₀ + A₁} ≤ ‖a‖_J` for `0 < θ < 1`,
  `0 < q` (via the K–J inequality and Aoki–Rolewicz in `A₀ + A₁`).
* `InterpolationCat.Hom.jInterpolationENorm_sumMap_le`: a morphism of couples with leg bounds
  `M₀, M₁` has `‖T a‖_J ≤ 2 M₀^{1-θ} M₁^θ ‖a‖_J`. The factor `2` comes from discretizing the
  rescaling `t ↦ t M₁ / M₀`; the discrete J-method is not exact.
-/

open MeasureTheory
open scoped ENNReal QuasinormedAddCommGroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- The `ℓ^q(ℤ)` quasinorm of `ν ↦ 2^{-νθ} J(2^ν, uᵥ)` for a family `u : ℤ → A₀ ∩ A₁`. -/
noncomputable def jSequenceENorm (θ : ℝ) (q : ℝ≥0∞) (u : ℤ → meet ι₀ ι₁) : ℝ≥0∞ :=
  eLpNorm (fun ν : ℤ => ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)))
    q Measure.count

/-- The discrete J-method `(θ,q)` quasinorm: the infimum of `jSequenceENorm θ q u` over all
representations `a = ∑ᵥ uᵥ` (in `A₀ + A₁`) with `uᵥ ∈ A₀ ∩ A₁`; `∞` if there is none. -/
noncomputable def jInterpolationENorm (θ : ℝ) (q : ℝ≥0∞) (a : sum ι₀ ι₁) : ℝ≥0∞ :=
  ⨅ (u : ℤ → meet ι₀ ι₁) (_ : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a),
    jSequenceENorm ι₀ ι₁ θ q u

omit [T2Space 𝒜] in
/-- `jSequenceENorm` is the `eLpNorm` of the corresponding nonnegative real sequence, so the
real-valued `eLpNorm` API (scaling, quasi-triangle inequality) applies. -/
private theorem jSequenceENorm_eq (θ : ℝ) (q : ℝ≥0∞) (u : ℤ → meet ι₀ ι₁) :
    jSequenceENorm ι₀ ι₁ θ q u =
      eLpNorm (fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν))
        q Measure.count :=
  eLpNorm_congr_enorm_ae Measurable.of_discrete.aestronglyMeasurable
    Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun ν => by
      rw [enorm_eq_self, Real.enorm_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _) (jFunctional_nonneg ι₀ ι₁ _ _))])

/-- Any representation bounds the J-quasinorm. -/
theorem jInterpolationENorm_le (θ : ℝ) (q : ℝ≥0∞) {a : sum ι₀ ι₁} (u : ℤ → meet ι₀ ι₁)
    (hu : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a) :
    jInterpolationENorm ι₀ ι₁ θ q a ≤ jSequenceENorm ι₀ ι₁ θ q u :=
  iInf₂_le u hu

theorem jInterpolationENorm_zero (θ : ℝ) (q : ℝ≥0∞) :
    jInterpolationENorm ι₀ ι₁ θ q 0 = 0 := by
  refine le_antisymm ((jInterpolationENorm_le ι₀ ι₁ θ q (fun _ => 0) ?_).trans_eq ?_) zero_le
  · simp
  · simp [jSequenceENorm, jFunctional_zero]

theorem jInterpolationENorm_smul (θ : ℝ) (q : ℝ≥0∞) (c : 𝕜) (a : sum ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q (c • a) = ‖c‖ₑ * jInterpolationENorm ι₀ ι₁ θ q a := by
  -- scaling a representation scales its sequence norm by `‖c‖ₑ`
  have hseq (c : 𝕜) (u : ℤ → meet ι₀ ι₁) :
      jSequenceENorm ι₀ ι₁ θ q (fun ν => c • u ν) = ‖c‖ₑ * jSequenceENorm ι₀ ι₁ θ q u := by
    rw [jSequenceENorm_eq, jSequenceENorm_eq, ← enorm_norm c, ← eLpNorm_const_smul]
    congr 1
    funext ν
    rw [Pi.smul_apply, jFunctional_smul, smul_eq_mul]
    ring
  have key (c : 𝕜) (a : sum ι₀ ι₁) :
      jInterpolationENorm ι₀ ι₁ θ q (c • a) ≤ ‖c‖ₑ * jInterpolationENorm ι₀ ι₁ θ q a := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp [jInterpolationENorm_zero]
    have h0 : ‖c‖ₑ ≠ 0 := by simpa using hc
    conv_rhs => rw [jInterpolationENorm, ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
    refine le_iInf fun u => ?_
    rw [ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
    refine le_iInf fun hu => ?_
    rw [← hseq]
    exact jInterpolationENorm_le ι₀ ι₁ θ q _ (by simpa only [map_smul] using hu.const_smul c)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [jInterpolationENorm_zero]
  refine le_antisymm (key c a) (ENNReal.mul_le_of_le_div' ?_)
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul] using key c⁻¹ (c • a)

/-- Quasi-triangle inequality for the J-quasinorm, with a real constant `C ≥ 1` (add the two
representations termwise; combine `jFunctional_add_le` with the `ℓ^q` quasi-triangle inequality). -/
theorem exists_jInterpolationENorm_add_le (θ : ℝ) (q : ℝ≥0∞) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : sum ι₀ ι₁,
      jInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        ENNReal.ofReal C * (jInterpolationENorm ι₀ ι₁ θ q a + jInterpolationENorm ι₀ ι₁ θ q b) := by
  set CJ := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hCJ : 0 ≤ CJ :=
    zero_le_one.trans (le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst)
  set L := ENNReal.LpAddConst q
  set C := max 1 (CJ * L.toReal)
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_max_of_lt_left one_pos)).ne'
  refine ⟨C, le_max_left _ _, fun a b => ?_⟩
  -- one pair of representations: add them termwise
  have hpair (u v : ℤ → meet ι₀ ι₁) (hu : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a)
      (hv : HasSum (fun ν => meetToSum ι₀ ι₁ (v ν)) b) :
      jInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        ENNReal.ofReal C * (jSequenceENorm ι₀ ι₁ θ q u + jSequenceENorm ι₀ ι₁ θ q v) := by
    refine (jInterpolationENorm_le ι₀ ι₁ θ q (fun ν => u ν + v ν)
      (by simpa only [map_add] using hu.add hv)).trans ?_
    rw [jSequenceENorm_eq, jSequenceENorm_eq, jSequenceENorm_eq]
    set gu := fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)
    set gv := fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (v ν)
    calc eLpNorm (fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν + v ν))
          q Measure.count
        ≤ eLpNorm (CJ • (gu + gv)) q Measure.count := by
          refine eLpNorm_mono_real Measurable.of_discrete.aestronglyMeasurable fun ν => ?_
          have hw : 0 ≤ ((2 : ℝ) ^ ν) ^ (-θ) := Real.rpow_nonneg (zpow_nonneg zero_le_two _) _
          rw [Real.norm_of_nonneg (mul_nonneg hw (jFunctional_nonneg ι₀ ι₁ _ _))]
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, gu, gv]
          calc ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν + v ν)
              ≤ ((2 : ℝ) ^ ν) ^ (-θ) * (CJ * (JFunctional ι₀ ι₁ (2 ^ ν) (u ν) +
                  JFunctional ι₀ ι₁ (2 ^ ν) (v ν))) :=
                mul_le_mul_of_nonneg_left (jFunctional_add_le ι₀ ι₁ _ _ _) hw
            _ = _ := by ring
      _ = ‖CJ‖ₑ * eLpNorm (gu + gv) q Measure.count := eLpNorm_const_smul _ _ _ _
      _ ≤ ‖CJ‖ₑ * (L * (eLpNorm gu q Measure.count + eLpNorm gv q Measure.count)) := by
          gcongr
          exact eLpNorm_add_le' q
      _ = ENNReal.ofReal (CJ * L.toReal) *
            (eLpNorm gu q Measure.count + eLpNorm gv q Measure.count) := by
          rw [Real.enorm_of_nonneg hCJ, ENNReal.ofReal_mul hCJ,
            ENNReal.ofReal_toReal (ENNReal.LpAddConst_lt_top q).ne, mul_assoc]
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _
  -- take the infimum over both representations
  calc jInterpolationENorm ι₀ ι₁ θ q (a + b)
      ≤ ⨅ (v : ℤ → meet ι₀ ι₁) (_ : HasSum (fun ν => meetToSum ι₀ ι₁ (v ν)) b)
          (u : ℤ → meet ι₀ ι₁) (_ : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a),
            ENNReal.ofReal C * (jSequenceENorm ι₀ ι₁ θ q u + jSequenceENorm ι₀ ι₁ θ q v) :=
        le_iInf₂ fun v hv => le_iInf₂ fun u hu => hpair u v hu hv
    _ = _ := by
        simp only [jInterpolationENorm, ENNReal.iInf_add, ENNReal.add_iInf,
          ENNReal.mul_iInf_of_ne hC0 ENNReal.ofReal_ne_top]

/-- The "`A₀ ∩ A₁ ⊂`" half of the sandwich: the one-term representation `u₀ = b` gives
`‖b‖_J ≤ J(1, b) = ‖b‖`. -/
theorem jInterpolationENorm_meetToSum_le (θ : ℝ) (q : ℝ≥0∞) (b : meet ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b) ≤ ENNReal.ofReal ‖b‖ := by
  set u : ℤ → meet ι₀ ι₁ := Pi.single 0 b with hu_def
  have hu : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) (meetToSum ι₀ ι₁ b) := by
    simpa [hu_def] using hasSum_single (0 : ℤ)
      (f := fun ν => meetToSum ι₀ ι₁ (u ν)) fun ν hν => by simp [hu_def, hν]
  refine (jInterpolationENorm_le ι₀ ι₁ θ q _ hu).trans ?_
  have hg : (fun ν : ℤ => ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) *
      JFunctional ι₀ ι₁ (2 ^ ν) (u ν))) =
        ({0} : Set ℤ).indicator fun _ => ENNReal.ofReal ‖b‖ := by
    funext ν
    by_cases hν : ν = 0
    · subst hν
      simp [hu_def, jFunctional_one]
    · simp [hu_def, hν, jFunctional_zero]
  rw [jSequenceENorm, hg]
  refine (eLpNorm_indicator_const_le _ q (measurableSet_singleton 0).nullMeasurableSet).trans ?_
  simp

/-- Two-sided geometric series over `ℤ`. -/
theorem summable_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun ν : ℤ => r ^ ν.natAbs :=
  Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one h0 h1)
    (by simpa using summable_geometric_of_lt_one h0 h1)

/-- The weight comparison behind the sum bound: with `r = 2^ν`,
`min(1, r⁻¹) r^θ = min(r^θ, r^{θ-1}) ≤ (2^{-δ})^{|ν|}` whenever `δ ≤ θ` and `δ ≤ 1 - θ`. -/
theorem min_one_inv_mul_rpow_le {θ δ : ℝ} (hδθ : δ ≤ θ) (hδ1 : δ ≤ 1 - θ) (ν : ℤ) :
    min 1 ((2 : ℝ) ^ ν)⁻¹ * ((2 : ℝ) ^ ν) ^ θ ≤ ((2 : ℝ) ^ (-δ)) ^ ν.natAbs := by
  have hr : 0 < (2 : ℝ) ^ ν := zpow_pos two_pos ν
  rw [Real.rpow_pow_comm zero_le_two]
  rcases le_or_gt 0 ν with hν | hν
  · have h1 : 1 ≤ (2 : ℝ) ^ ν := one_le_zpow₀ one_le_two hν
    have heq : (2 : ℝ) ^ ν.natAbs = (2 : ℝ) ^ ν := by
      rw [← zpow_natCast, Int.natAbs_of_nonneg hν]
    rw [heq, min_eq_right (inv_le_one_of_one_le₀ h1), ← Real.rpow_neg_one, ← Real.rpow_add hr]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · have h1 : (2 : ℝ) ^ ν ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two hν.le
    have heq : (2 : ℝ) ^ ν.natAbs = ((2 : ℝ) ^ ν)⁻¹ := by
      rw [← zpow_natCast, Int.ofNat_natAbs_of_nonpos hν.le, zpow_neg]
    rw [heq, min_eq_left ((one_le_inv₀ hr).mpr h1), one_mul, Real.inv_rpow hr.le,
      Real.rpow_neg hr.le, inv_inv]
    exact Real.rpow_le_rpow_of_exponent_ge hr h1 hδθ

/-- The "`⊂ A₀ + A₁`" half of the sandwich: `c ‖a‖_{A₀ + A₁} ≤ ‖a‖_J` for some `c > 0`. For a
representation, `‖uᵥ‖_{A₀+A₁} ≤ min(1, 2^{-ν}) J(2^ν, uᵥ) ≤ min(2^{νθ}, 2^{ν(θ-1)}) ‖x‖_{ℓ^q}`
(`x` the weighted sequence), and Aoki–Rolewicz in `A₀ + A₁` sums the geometric weights. -/
theorem exists_ofReal_mul_norm_le_jInterpolationENorm (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : sum ι₀ ι₁,
      ENNReal.ofReal (c * ‖a‖) ≤ jInterpolationENorm ι₀ ι₁ θ q a := by
  set ρ := QuasinormedAddCommGroup.aokiRolewiczExponent (sum ι₀ ι₁)
  have hρ : 0 < ρ := QuasinormedAddCommGroup.aokiRolewiczExponent_pos _
  set δ := min θ (1 - θ)
  have hδ : 0 < δ := lt_min hθ0 (by linarith)
  set r := ((2 : ℝ) ^ (-δ)) ^ ρ
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)) hρ
  have hW := summable_pow_natAbs hr0 hr1
  set W := ∑' ν : ℤ, r ^ ν.natAbs
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => pow_nonneg hr0 _
  set B := (4 : ℝ) ^ ρ⁻¹
  have hB : 0 ≤ B := by positivity
  set M := B * W ^ ρ⁻¹ + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos (mul_nonneg hB (Real.rpow_nonneg hW0 _)) one_pos
  refine ⟨M⁻¹, inv_pos.mpr hM, fun a => le_iInf₂ fun u hu => ?_⟩
  rw [jSequenceENorm_eq]
  set g := fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)
  set s := eLpNorm g q Measure.count
  rcases eq_or_ne s ⊤ with hs | hs
  · rw [hs]
    exact le_top
  set S := s.toReal
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  have hgnn (ν : ℤ) : 0 ≤ g ν :=
    mul_nonneg (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _) (jFunctional_nonneg ι₀ ι₁ _ _)
  -- each weighted term is at most the `ℓ^q` norm
  have hgS (ν : ℤ) : g ν ≤ S := by
    have h := enorm_le_eLpNorm_count g ν hq.ne'
    rw [Real.enorm_of_nonneg (hgnn ν)] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hs).mp h
  -- termwise bound in `A₀ + A₁`, via the K–J inequality at `t = 1`
  have hterm (ν : ℤ) : ‖meetToSum ι₀ ι₁ (u ν)‖ ≤ ((2 : ℝ) ^ (-δ)) ^ ν.natAbs * S := by
    have hk := min_mul_norm_le_kFunctional ι₀ ι₁ 1 zero_le_one (meetToSum ι₀ ι₁ (u ν))
    have hkj := kFunctional_meetToSum_le_jFunctional ι₀ ι₁ (zpow_pos two_pos ν) zero_le_one (u ν)
    rw [min_self, one_mul] at hk
    have hJ : JFunctional ι₀ ι₁ (2 ^ ν) (u ν) = ((2 : ℝ) ^ ν) ^ θ * g ν := by
      simp only [g]
      rw [← mul_assoc, ← Real.rpow_add (zpow_pos two_pos ν), add_neg_cancel, Real.rpow_zero,
        one_mul]
    calc ‖meetToSum ι₀ ι₁ (u ν)‖
        ≤ min 1 (1 / (2 : ℝ) ^ ν) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν) := hk.trans hkj
      _ = min 1 ((2 : ℝ) ^ ν)⁻¹ * ((2 : ℝ) ^ ν) ^ θ * g ν := by rw [hJ, one_div]; ring
      _ ≤ ((2 : ℝ) ^ (-δ)) ^ ν.natAbs * S :=
          mul_le_mul (min_one_inv_mul_rpow_le (min_le_left _ _) (min_le_right _ _) ν) (hgS ν)
            (hgnn ν) (by positivity)
  have hterm' (ν : ℤ) : ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ ≤ r ^ ν.natAbs * S ^ ρ := by
    calc ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ ≤ (((2 : ℝ) ^ (-δ)) ^ ν.natAbs * S) ^ ρ :=
          Real.rpow_le_rpow (QuasinormedAddCommGroup.norm_nonneg _) (hterm ν) hρ.le
      _ = r ^ ν.natAbs * S ^ ρ := by
          rw [Real.mul_rpow (by positivity) hS,
            ← Real.rpow_pow_comm (x := (2 : ℝ) ^ (-δ)) (by positivity)]
  have hsumm : Summable fun ν => ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ :=
    Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (QuasinormedAddCommGroup.norm_nonneg _) _)
      hterm' (hW.mul_right _)
  -- Aoki–Rolewicz in `A₀ + A₁`
  have hA := QuasinormedAddCommGroup.norm_tsum_le_rpow hsumm
  rw [hu.tsum_eq] at hA
  have hsum_le : ∑' ν, ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ ≤ W * S ^ ρ := by
    rw [← tsum_mul_right]
    exact hsumm.tsum_le_tsum hterm' (hW.mul_right _)
  have hpow : (∑' ν, ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ) ^ ρ⁻¹ ≤ W ^ ρ⁻¹ * S := by
    calc (∑' ν, ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ) ^ ρ⁻¹ ≤ (W * S ^ ρ) ^ ρ⁻¹ :=
          Real.rpow_le_rpow (tsum_nonneg fun _ =>
            Real.rpow_nonneg (QuasinormedAddCommGroup.norm_nonneg _) _) hsum_le
            (inv_pos.mpr hρ).le
      _ = W ^ ρ⁻¹ * S := by
          rw [Real.mul_rpow hW0 (Real.rpow_nonneg hS _), Real.rpow_rpow_inv hS hρ.ne']
  have hnorm : ‖a‖ ≤ M * S :=
    calc ‖a‖ ≤ B * (∑' ν, ‖meetToSum ι₀ ι₁ (u ν)‖ ^ ρ) ^ ρ⁻¹ := hA
      _ ≤ B * (W ^ ρ⁻¹ * S) := mul_le_mul_of_nonneg_left hpow hB
      _ ≤ M * S := by
          rw [add_mul, one_mul, mul_assoc]
          linarith
  calc ENNReal.ofReal (M⁻¹ * ‖a‖) ≤ ENNReal.ofReal S :=
        ENNReal.ofReal_le_ofReal (by rw [inv_mul_le_iff₀ hM]; exact hnorm)
    _ = s := ENNReal.ofReal_toReal hs

theorem jInterpolationENorm_eq_zero_iff (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ jInterpolationENorm_zero ι₀ ι₁ θ q⟩
  obtain ⟨c, hc, hle⟩ := exists_ofReal_mul_norm_le_jInterpolationENorm ι₀ ι₁ θ hθ0 hθ1 hq
  have h0 : c * ‖a‖ ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm (h ▸ hle a) zero_le)
  exact (QuasinormedAddCommGroup.norm_eq_zero_iff a).mp (le_antisymm
    (le_of_mul_le_mul_left (by simpa using h0) hc) (QuasinormedAddCommGroup.norm_nonneg a))

end InterpolationCouple

open InterpolationCouple in
/-- A morphism of couples `T` with `‖T.f₀‖ₒₚ ≤ M₀`, `‖T.f₁‖ₒₚ ≤ M₁` satisfies
`‖T a‖_J ≤ 2 M₀^{1-θ} M₁^θ ‖a‖_J` (`θ ≥ 0`). Proof: map a representation by `T.meetMap`, use
`Hom.jFunctional_meetMap_le`, and shift the index by the `k ∈ ℤ` with
`2^k ≤ M₁/M₀ < 2^{k+1}`; the mismatch costs `max(1, (M₁/M₀)/2^k) ≤ 2`. -/
theorem InterpolationCat.Hom.jInterpolationENorm_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ≥0∞)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ‖T.f₀‖ₒₚ ≤ M₀) (h₁ : ‖T.f₁‖ₒₚ ≤ M₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.jInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap a) ≤
      ENNReal.ofReal (2 * (M₀ ^ (1 - θ) * M₁ ^ θ)) *
        InterpolationCouple.jInterpolationENorm C.ι₀ C.ι₁ θ q a := by
  set lam := M₁ / M₀ with hlam_def
  have hlam : 0 < lam := div_pos hM₁ hM₀
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow hlam one_lt_two
  set K := 2 * (M₀ ^ (1 - θ) * M₁ ^ θ)
  have hK : 0 < K := by positivity
  have hK0 : ENNReal.ofReal K ≠ 0 := (ENNReal.ofReal_pos.mpr hK).ne'
  -- the induced maps commute with `meetToSum`
  have hcomm (b : meet C.ι₀ C.ι₁) :
      meetToSum D.ι₀ D.ι₁ (T.meetMap b) = T.sumMap (meetToSum C.ι₀ C.ι₁ b) := by
    obtain ⟨⟨a₀, a₁⟩, hb⟩ := b
    rw [Hom.meetMap_apply, meetToSum_apply, meetToSum_apply, inl₀_eq_mk, inl₀_eq_mk,
      Hom.sumMap_mk, map_zero]
  -- pointwise comparison of the weighted sequences, with the index shifted by `k`
  have hpt (u : ℤ → meet C.ι₀ C.ι₁) (ν : ℤ) :
      ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional D.ι₀ D.ι₁ (2 ^ ν) (T.meetMap (u (ν + k))) ≤
        K * (((2 : ℝ) ^ (ν + k)) ^ (-θ) * JFunctional C.ι₀ C.ι₁ (2 ^ (ν + k)) (u (ν + k))) := by
    have h2ν : 0 < (2 : ℝ) ^ ν := zpow_pos two_pos ν
    have h2k : 0 < (2 : ℝ) ^ k := zpow_pos two_pos k
    have hJ1 := T.jFunctional_meetMap_le (2 ^ ν) M₀ M₁ hM₀ h₀ h₁ (u (ν + k))
    have hJ2 := jFunctional_le_max_div_mul C.ι₀ C.ι₁ (zpow_pos two_pos (ν + k))
      (t := 2 ^ ν * M₁ / M₀) (u (ν + k))
    have hratio : max 1 ((2 : ℝ) ^ ν * M₁ / M₀ / 2 ^ (ν + k)) ≤ 2 := by
      have heq : (2 : ℝ) ^ ν * M₁ / M₀ / 2 ^ (ν + k) = lam / 2 ^ k := by
        rw [zpow_add₀ two_ne_zero, hlam_def]
        field_simp
      rw [heq, max_le_iff, div_le_iff₀ h2k]
      rw [zpow_add_one₀ two_ne_zero] at hk2
      exact ⟨one_le_two, by linarith⟩
    have hJC0 := jFunctional_nonneg C.ι₀ C.ι₁ (2 ^ (ν + k)) (u (ν + k))
    have hsplit : ((2 : ℝ) ^ ν) ^ (-θ) = ((2 : ℝ) ^ k) ^ θ * ((2 : ℝ) ^ (ν + k)) ^ (-θ) := by
      have hkθ : ((2 : ℝ) ^ k) ^ θ ≠ 0 := (Real.rpow_pos_of_pos h2k θ).ne'
      rw [zpow_add₀ two_ne_zero, Real.mul_rpow h2ν.le h2k.le, Real.rpow_neg h2k.le]
      field_simp
    have hM : M₀ * lam ^ θ = M₀ ^ (1 - θ) * M₁ ^ θ := by
      rw [Real.div_rpow hM₁.le hM₀.le, Real.rpow_sub hM₀, Real.rpow_one]
      field_simp
    calc ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional D.ι₀ D.ι₁ (2 ^ ν) (T.meetMap (u (ν + k)))
        ≤ ((2 : ℝ) ^ ν) ^ (-θ) * (M₀ * JFunctional C.ι₀ C.ι₁ (2 ^ ν * M₁ / M₀) (u (ν + k))) :=
          mul_le_mul_of_nonneg_left hJ1 (by positivity)
      _ ≤ ((2 : ℝ) ^ ν) ^ (-θ) *
            (M₀ * (2 * JFunctional C.ι₀ C.ι₁ (2 ^ (ν + k)) (u (ν + k)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hJ2.trans (mul_le_mul_of_nonneg_right hratio hJC0)) hM₀.le) (by positivity)
      _ = 2 * (M₀ * ((2 : ℝ) ^ k) ^ θ) *
            (((2 : ℝ) ^ (ν + k)) ^ (-θ) * JFunctional C.ι₀ C.ι₁ (2 ^ (ν + k)) (u (ν + k))) := by
          rw [hsplit]
          ring
      _ ≤ 2 * (M₀ * lam ^ θ) *
            (((2 : ℝ) ^ (ν + k)) ^ (-θ) * JFunctional C.ι₀ C.ι₁ (2 ^ (ν + k)) (u (ν + k))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h2k.le hk1 hθ) hM₀.le) zero_le_two)
            (mul_nonneg (by positivity) hJC0)
      _ = _ := by rw [hM]
  conv_rhs => rw [jInterpolationENorm, ENNReal.mul_iInf_of_ne hK0 ENNReal.ofReal_ne_top]
  refine le_iInf fun u => ?_
  rw [ENNReal.mul_iInf_of_ne hK0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hu => ?_
  have h1 : HasSum (fun μ => T.sumMap (meetToSum C.ι₀ C.ι₁ (u μ))) (T.sumMap a) :=
    hu.map T.sumMap T.sumMap.continuous
  have h2 := (Equiv.addRight k).hasSum_iff.mpr h1
  simp only [Function.comp_def, Equiv.coe_addRight] at h2
  have hw : HasSum (fun ν => meetToSum D.ι₀ D.ι₁ (T.meetMap (u (ν + k)))) (T.sumMap a) := by
    rw [funext fun ν => hcomm (u (ν + k))]
    exact h2
  refine (jInterpolationENorm_le D.ι₀ D.ι₁ θ q _ hw).trans ?_
  rw [jSequenceENorm_eq, jSequenceENorm_eq]
  set gC := fun μ : ℤ => ((2 : ℝ) ^ μ) ^ (-θ) * JFunctional C.ι₀ C.ι₁ (2 ^ μ) (u μ)
  calc eLpNorm (fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) *
        JFunctional D.ι₀ D.ι₁ (2 ^ ν) (T.meetMap (u (ν + k)))) q Measure.count
      ≤ eLpNorm (K • (gC ∘ fun ν => ν + k)) q Measure.count := by
        refine eLpNorm_mono_real Measurable.of_discrete.aestronglyMeasurable fun ν => ?_
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _)
          (jFunctional_nonneg D.ι₀ D.ι₁ _ _))]
        exact hpt u ν
    _ = ‖K‖ₑ * eLpNorm (gC ∘ fun ν => ν + k) q Measure.count := eLpNorm_const_smul _ _ _ _
    _ = ENNReal.ofReal K * eLpNorm gC q Measure.count := by
        rw [Real.enorm_of_nonneg hK.le, eLpNorm_comp_measurePreserving
          Measurable.of_discrete.aestronglyMeasurable (measurePreserving_add_right Measure.count k)]
