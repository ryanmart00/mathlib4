/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Hardy's inequality

Hardy's inequality on `(0, ∞)` with the Haar measure `dt/t`, in `ℝ≥0∞`-valued form: for
`λ > 0` and `s ≥ 1`,
`∫₀^∞ (t^{-λ} ∫₀ᵗ g)^s dt/t ≤ λ^{-s} ∫₀^∞ (t^{1-λ} g(t))^s dt/t`.

This is the analytic input of the K-method computations for Lorentz spaces (Triebel §1.18.6,
Theorem 1, and Bergh–Löfström §3.4).

The proof substitutes `u = tv` to write `t^{-λ} ∫₀ᵗ g = ∫₀¹ v^{λ-1} G(tv) dv` with
`G(w) = w^{1-λ} g(w)`, applies Jensen's inequality for the finite measure `v^{λ-1} dv` on `(0, 1]`
(`lintegral_mul_rpow_le`), swaps the integrals, and uses the dilation invariance of `dt/t`.

## Main results
* `lintegral_hardy`: Hardy's inequality.
* `lintegral_mul_rpow_le`: Jensen's inequality `(∫ w F)^s ≤ (∫ w)^{s-1} ∫ w F^s` for `s ≥ 1`.
-/

open MeasureTheory Set
open scoped ENNReal

/-- `∫₀¹ v^{λ-1} dv = 1/λ`, as a lower Lebesgue integral. -/
theorem lintegral_Ioc_zero_one_rpow {l : ℝ} (hl : 0 < l) :
    ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal v ^ (l - 1) = ENNReal.ofReal l⁻¹ := by
  have hcongr : ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal v ^ (l - 1) =
      ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal (v ^ (l - 1)) :=
    setLIntegral_congr_fun measurableSet_Ioc fun v hv => ENNReal.ofReal_rpow_of_pos hv.1
  have hii : IntervalIntegrable (fun x : ℝ => x ^ (l - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), 0 ≤ x ^ (l - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg hx.1.le _
  have hval : ∫ x in (0 : ℝ)..1, x ^ (l - 1) = l⁻¹ := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow hl.ne']
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hii.1 hnn,
    ← intervalIntegral.integral_of_le zero_le_one, hval]

/-- Rescaling `(0, t]` to `(0, 1]`: `∫₀ᵗ H(u) du = t ∫₀¹ H(tv) dv`. -/
theorem lintegral_Ioc_zero_eq_mul_lintegral_comp_mul {t : ℝ} (ht : 0 < t) (H : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioc 0 t, H u = ENNReal.ofReal t * ∫⁻ v in Ioc (0 : ℝ) 1, H (t * v) := by
  have hf' : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt (fun x : ℝ => t * x) t (Ioc (0 : ℝ) 1) x :=
    fun x _ => by simpa using ((hasDerivAt_id x).const_mul t).hasDerivWithinAt
  have hmono : MonotoneOn (fun x : ℝ => t * x) (Ioc (0 : ℝ) 1) :=
    fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy ht.le
  have himg : (fun x : ℝ => t * x) '' Ioc (0 : ℝ) 1 = Ioc 0 t := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      exact ⟨mul_pos ht hx0, by nlinarith⟩
    · rintro ⟨hy0, hy1⟩
      refine ⟨y / t, ⟨div_pos hy0 ht, (div_le_one ht).mpr hy1⟩, ?_⟩
      field_simp
  have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioc hf' hmono H
  rw [himg] at key
  rw [key, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Dilation invariance of the Haar measure `dt/t` on `(0, ∞)`. -/
theorem lintegral_Ioi_comp_mul_mul_inv {v : ℝ} (hv : 0 < v) (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), H (t * v) * ENNReal.ofReal t⁻¹ =
      ∫⁻ t in Ioi (0 : ℝ), H t * ENNReal.ofReal t⁻¹ := by
  have hf' : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x * v) v (Ioi (0 : ℝ)) x :=
    fun x _ => by simpa using ((hasDerivAt_id x).mul_const v).hasDerivWithinAt
  have hmono : MonotoneOn (fun x : ℝ => x * v) (Ioi (0 : ℝ)) :=
    fun x _ y _ hxy => mul_le_mul_of_nonneg_right hxy hv.le
  have himg : (fun x : ℝ => x * v) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mul_pos hx hv
    · intro hy
      exact ⟨y / v, div_pos hy hv, by field_simp⟩
  have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi hf' hmono
    (fun x => H x * ENNReal.ofReal x⁻¹)
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [mul_comm (ENNReal.ofReal v), mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr
    (mul_pos (mem_Ioi.mp ht) hv).le), mul_inv, mul_assoc, inv_mul_cancel₀ hv.ne', mul_one]

/-- Jensen's inequality for the power `s ≥ 1` and the weight `w`:
`(∫ w F)^s ≤ (∫ w)^{s-1} ∫ w F^s`. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {w F : α → ℝ≥0∞}
    (hw : Measurable w) (hF : Measurable F) {s : ℝ} (hs : 1 ≤ s) :
    (∫⁻ x, w x * F x ∂μ) ^ s ≤ (∫⁻ x, w x ∂μ) ^ (s - 1) * ∫⁻ x, w x * F x ^ s ∂μ := by
  have key := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (μ := μ.withDensity w) one_pos hs
    hF.aestronglyMeasurable
  simp only [eLpNorm', enorm_eq_self, ENNReal.rpow_one, div_one, withDensity_apply _
    MeasurableSet.univ, Measure.restrict_univ] at key
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF,
    lintegral_withDensity_eq_lintegral_mul _ hw (hF.pow_const s)] at key
  have hs0 : 0 < s := by linarith
  calc (∫⁻ x, w x * F x ∂μ) ^ s
      ≤ ((∫⁻ x, w x * F x ^ s ∂μ) ^ (1 / s) * (∫⁻ x, w x ∂μ) ^ (1 - 1 / s)) ^ s := by
        gcongr
        simpa using key
    _ = (∫⁻ x, w x ∂μ) ^ (s - 1) * ∫⁻ x, w x * F x ^ s ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hs0.ne', ENNReal.rpow_one, sub_mul, one_mul,
          one_div_mul_cancel hs0.ne', mul_comm]

/-- **Hardy's inequality**: `∫₀^∞ (t^{-λ} ∫₀ᵗ g)^s dt/t ≤ λ^{-s} ∫₀^∞ (t^{1-λ} g(t))^s dt/t`
for measurable `g ≥ 0`, `λ > 0` and `s ≥ 1`. -/
theorem lintegral_hardy {g : ℝ → ℝ≥0∞} (hg : Measurable g) {l s : ℝ} (hl : 0 < l)
    (hs : 1 ≤ s) :
    ∫⁻ t in Ioi 0, (ENNReal.ofReal t ^ (-l) * ∫⁻ u in Ioc 0 t, g u) ^ s * ENNReal.ofReal t⁻¹ ≤
      ENNReal.ofReal l⁻¹ ^ s *
        ∫⁻ t in Ioi 0, (ENNReal.ofReal t ^ (1 - l) * g t) ^ s * ENNReal.ofReal t⁻¹ := by
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal x ^ (1 - l) * g x with hGdef
  set w : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal v ^ (l - 1) with hwdef
  have hG : Measurable G := (ENNReal.measurable_ofReal.pow_const _).mul hg
  have hw : Measurable w := ENNReal.measurable_ofReal.pow_const _
  have h1 : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal t ^ (-l) * ∫⁻ u in Ioc 0 t, g u =
      ∫⁻ v in Ioc (0 : ℝ) 1, w v * G (t * v) := by
    intro t ht
    rw [lintegral_Ioc_zero_eq_mul_lintegral_comp_mul ht, ← mul_assoc, ← lintegral_const_mul'
      _ _ (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr ht).ne'
        ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)]
    refine setLIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
    have hv0 : ENNReal.ofReal v ≠ 0 := (ENNReal.ofReal_pos.mpr hv.1).ne'
    simp only [hGdef, hwdef]
    rw [ENNReal.ofReal_mul (le_of_lt ht), ENNReal.mul_rpow_of_ne_zero ht0 hv0]
    calc ENNReal.ofReal t ^ (-l) * ENNReal.ofReal t * g (t * v)
        = ENNReal.ofReal t ^ (1 - l) * g (t * v) := by
          rw [show 1 - l = -l + 1 by ring, ENNReal.rpow_add _ _ ht0 ENNReal.ofReal_ne_top,
            ENNReal.rpow_one]
      _ = _ := by
          rw [show ENNReal.ofReal v ^ (l - 1) * (ENNReal.ofReal t ^ (1 - l) *
              ENNReal.ofReal v ^ (1 - l) * g (t * v)) =
              ENNReal.ofReal t ^ (1 - l) * (ENNReal.ofReal v ^ (l - 1) *
              ENNReal.ofReal v ^ (1 - l)) * g (t * v) by ring,
            ← ENNReal.rpow_add _ _ hv0 ENNReal.ofReal_ne_top]
          simp
  have hint : ∫⁻ v in Ioc (0 : ℝ) 1, w v = ENNReal.ofReal l⁻¹ := lintegral_Ioc_zero_one_rpow hl
  calc ∫⁻ t in Ioi 0, (ENNReal.ofReal t ^ (-l) * ∫⁻ u in Ioc 0 t, g u) ^ s *
        ENNReal.ofReal t⁻¹
      = ∫⁻ t in Ioi 0, (∫⁻ v in Ioc (0 : ℝ) 1, w v * G (t * v)) ^ s * ENNReal.ofReal t⁻¹ :=
        setLIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [h1 t ht]
    _ ≤ ∫⁻ t in Ioi 0, (ENNReal.ofReal l⁻¹ ^ (s - 1) *
          ∫⁻ v in Ioc (0 : ℝ) 1, w v * G (t * v) ^ s) * ENNReal.ofReal t⁻¹ := by
        refine lintegral_mono fun t => ?_
        gcongr
        rw [← hint]
        exact lintegral_mul_rpow_le _ hw (hG.comp (measurable_const.mul measurable_id)) hs
    _ = ENNReal.ofReal l⁻¹ ^ (s - 1) * ∫⁻ v in Ioc (0 : ℝ) 1,
          w v * ∫⁻ t in Ioi 0, G (t * v) ^ s * ENNReal.ofReal t⁻¹ := by
        have hmeas : Measurable (Function.uncurry fun (t v : ℝ) =>
            w v * G (t * v) ^ s * ENNReal.ofReal t⁻¹) :=
          ((hw.comp measurable_snd).mul ((hG.comp (measurable_fst.mul measurable_snd)).pow_const
            s)).mul (ENNReal.measurable_ofReal.comp (measurable_fst.inv))
        simp_rw [mul_assoc (ENNReal.ofReal l⁻¹ ^ (s - 1))]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          ENNReal.ofReal_ne_top)]
        congr 1
        have e1 : ∀ t : ℝ, (∫⁻ v in Ioc (0 : ℝ) 1, w v * G (t * v) ^ s) * ENNReal.ofReal t⁻¹ =
            ∫⁻ v in Ioc (0 : ℝ) 1, w v * G (t * v) ^ s * ENNReal.ofReal t⁻¹ := fun t =>
          (lintegral_mul_const _
            (hw.mul ((hG.comp (measurable_const.mul measurable_id)).pow_const s))).symm
        have e2 : ∀ v : ℝ, w v * ∫⁻ t in Ioi 0, G (t * v) ^ s * ENNReal.ofReal t⁻¹ =
            ∫⁻ t in Ioi 0, w v * G (t * v) ^ s * ENNReal.ofReal t⁻¹ := fun v => by
          have hm : Measurable fun t : ℝ => G (t * v) ^ s * ENNReal.ofReal t⁻¹ :=
            ((hG.comp (measurable_id.mul measurable_const)).pow_const s).mul
              (ENNReal.measurable_ofReal.comp measurable_inv)
          rw [← lintegral_const_mul _ hm]
          simp_rw [mul_assoc]
        simp_rw [e1, e2]
        exact lintegral_lintegral_swap hmeas.aemeasurable
    _ = ENNReal.ofReal l⁻¹ ^ (s - 1) * ∫⁻ v in Ioc (0 : ℝ) 1,
          w v * ∫⁻ t in Ioi 0, G t ^ s * ENNReal.ofReal t⁻¹ := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
        rw [lintegral_Ioi_comp_mul_mul_inv hv.1 (fun x => G x ^ s)]
    _ = ENNReal.ofReal l⁻¹ ^ s * ∫⁻ t in Ioi 0, G t ^ s * ENNReal.ofReal t⁻¹ := by
        have hl0 : ENNReal.ofReal l⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hl)).ne'
        rw [lintegral_mul_const _ hw, hint, ← mul_assoc]
        congr 1
        rw [show s = s - 1 + 1 from by ring, ENNReal.rpow_add _ _ hl0 ENNReal.ofReal_ne_top,
          ENNReal.rpow_one, sub_add_cancel]

/-- Power substitution for the Haar measure `dt/t`: `∫₀^∞ H(tᵃ) dt/t = a⁻¹ ∫₀^∞ H(T) dT/T`. -/
theorem lintegral_Ioi_comp_rpow_mul_inv {a : ℝ} (ha : 0 < a) (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), H (t ^ a) * ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal a⁻¹ * ∫⁻ t in Ioi (0 : ℝ), H t * ENNReal.ofReal t⁻¹ := by
  have hf' : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ a) (a * x ^ (a - 1))
      (Ioi (0 : ℝ)) x := fun x hx => (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).hasDerivWithinAt
  have hmono : MonotoneOn (fun x : ℝ => x ^ a) (Ioi (0 : ℝ)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow hx.le hxy ha.le
  have himg : (fun x : ℝ => x ^ a) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Real.rpow_pos_of_pos hx a
    · intro hy
      exact ⟨y ^ a⁻¹, Real.rpow_pos_of_pos hy _, Real.rpow_inv_rpow hy.le ha.ne'⟩
  have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi hf' hmono
    (fun x => H x * ENNReal.ofReal x⁻¹)
  rw [himg] at key
  have hkey : ∫⁻ t in Ioi (0 : ℝ), H t * ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal a * ∫⁻ t in Ioi (0 : ℝ), H (t ^ a) * ENNReal.ofReal t⁻¹ := by
    rw [key, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : 0 < t := ht
    have e : ENNReal.ofReal (a * t ^ (a - 1)) * ENNReal.ofReal (t ^ a)⁻¹ =
        ENNReal.ofReal a * ENNReal.ofReal t⁻¹ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ha.le]
      congr 1
      rw [Real.rpow_sub ht', Real.rpow_one]
      field_simp
    calc ENNReal.ofReal (a * t ^ (a - 1)) * (H (t ^ a) * ENNReal.ofReal (t ^ a)⁻¹)
        = (ENNReal.ofReal (a * t ^ (a - 1)) * ENNReal.ofReal (t ^ a)⁻¹) * H (t ^ a) := by ring
      _ = _ := by rw [e]; ring
  rw [hkey, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne',
    ENNReal.ofReal_one, one_mul]

/-- Pointwise domination `F ≤ c G` on `(0, ∞)` passes to `∫₀^∞ F^s dt/t ≤ c^s ∫₀^∞ G^s dt/t`. -/
theorem lintegral_rpow_mul_inv_le_of_le {F G : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤) {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ t ∈ Ioi (0 : ℝ), F t ≤ c * G t) :
    ∫⁻ t in Ioi 0, F t ^ s * ENNReal.ofReal t⁻¹ ≤
      c ^ s * ∫⁻ t in Ioi 0, G t ^ s * ENNReal.ofReal t⁻¹ := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs hc)]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hs]
  gcongr
  exact h t ht

/-- `∫₀ᵀ u^{θ-1} du = T^θ / θ`. -/
theorem lintegral_Ioc_zero_rpow_sub_one {θ : ℝ} (hθ : 0 < θ) {T : ℝ} (hT : 0 < T) :
    ∫⁻ u in Ioc 0 T, ENNReal.ofReal u ^ (θ - 1) = ENNReal.ofReal T ^ θ * ENNReal.ofReal θ⁻¹ := by
  have hT0 : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.mpr hT).ne'
  rw [lintegral_Ioc_zero_eq_mul_lintegral_comp_mul hT]
  have : ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal (T * v) ^ (θ - 1) =
      ENNReal.ofReal T ^ (θ - 1) * ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal v ^ (θ - 1) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT0 ENNReal.ofReal_ne_top)]
    refine setLIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    rw [ENNReal.ofReal_mul hT.le, ENNReal.mul_rpow_of_ne_zero hT0
      (ENNReal.ofReal_pos.mpr hv.1).ne']
  rw [this, lintegral_Ioc_zero_one_rpow hθ, ← mul_assoc]
  congr 1
  rw [show θ = 1 + (θ - 1) by ring, ENNReal.rpow_add _ _ hT0 ENNReal.ofReal_ne_top,
    ENNReal.rpow_one]
  ring_nf
