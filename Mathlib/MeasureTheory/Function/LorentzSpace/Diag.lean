/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# `L_{p,p} = Lᵖ`

Triebel, *Interpolation Theory, Function Spaces, Differential Operators* §1.18.6, Lemma: the
diagonal Lorentz space `L_{p,p}(μ)` is literally the ordinary `Lᵖ(μ)` space, both at the level of
the raw quasinorm formulas (`lorentzNorm_diag`) and of the bundled types (`LorentzSpace.eq_Lp`).

`lorentzNorm_diag` moved here from `Analysis/Interpolation/LpLorentz.lean` (now
`Analysis/Interpolation/Lorentz/Marcinkiewicz.lean`) at the 2026-09-20 statement review: it is
general-purpose Lorentz-space content with no dependence on the interpolation-couple machinery,
matching why `distributionFunction`/`decreasingRearrangement`/`lorentzNorm` themselves
already live in this directory rather than there. Its statement needs two hypotheses:
* `0 < p`: at `q = 0` (hence on the diagonal, `p = 0` too), `lorentzNorm` is the *constant*
  function `1` (see `LorentzSpace/Basic.lean`'s `instQuasinormedAddCommGroup` docstring, which is
  exactly why that instance requires `[Fact (0 < q)]`), while `eLpNorm f 0 μ = 0` always by
  Mathlib's own convention.
* `AEStronglyMeasurable f μ`: `distributionFunction` evaluates `μ` on possibly non-measurable
  super-level sets (i.e. uses the outer measure), while `∫⁻` approximates from inside, so for the
  indicator of a non-measurable set of inner measure `0` and outer measure `1` the two sides differ.
  Mathlib's `eLpNorm` is anyway defined to be `∞` on non-a.e.-strongly-measurable functions.

The proof: at `p = ⊤` both sides are `essSup ‖f‖ₑ` (`f*(0)` on the Lorentz side). At finite `p`,
`f*` and `‖f‖` are *equimeasurable* (`volume_lt_decreasingRearrangement`: `|{t > 0 : σ < f*(t)}| =
ϱ(f,σ)`, from right-continuity of `ϱ(f, ·)`), and the layer-cake formula
(`lintegral_rpow_eq_lintegral_meas_lt_mul`) turns this into `∫₀^∞ f*(t)^p dt = ∫_α ‖f‖^p dμ`
(`lintegral_decreasingRearrangement_rpow`).

`LorentzSpace.eq_Lp`: since `lorentzNorm_diag` gives *literal* equality of the defining
`ℝ≥0∞`-valued quasinorms (not just an equivalence up to constants), the two bundled types —
both literally `AddSubgroup (α →ₘ[μ] E)` cut out by their respective quasinorm being finite — have
identical carriers, hence are literally equal as `AddSubgroup`s (per Ryan, 2026-09-20: literal
equality rather than mere equivalence of quasi-Banach spaces).

## Main results
* `lorentzNorm_diag`: `‖f‖_{L_{p,p}} = ‖f‖_{Lᵖ}` for `0 < p ≤ ∞`, as raw `ℝ≥0∞` quasinorms.
* `LorentzSpace.eq_Lp`: `LorentzSpace E p p μ = Lp E p μ` for `0 < p ≤ ∞`, as bundled types.
* `lintegral_decreasingRearrangement_rpow`: `∫₀^∞ f*(t)^r dt = ∫_α ‖f‖^r dμ` for `0 < r`.
* Further rearrangement facts: `decreasingRearrangement_mono`,
  `distributionFunction_decreasingRearrangement_le`,
  `lorentzNorm_top_top` (`‖f‖_{L_{∞,∞}} = f*(0)`), `rpow_mul_decreasingRearrangement_le`,
  `lintegral_indicator_lt_decreasingRearrangement_le`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]

/-- Right-continuity of the distribution function: `ϱ(f,σ) = sup_n ϱ(f, σ + 1/n)`, by continuity
of `μ` from below (no measurability needed). -/
theorem distributionFunction_eq_iSup_inv (f : α → E) (σ : ℝ≥0∞) :
    distributionFunction μ f σ = ⨆ n : ℕ, distributionFunction μ f (σ + (n : ℝ≥0∞)⁻¹) := by
  unfold distributionFunction
  have hmono : Monotone fun n : ℕ => {x | σ + (n : ℝ≥0∞)⁻¹ < ‖f x‖ₑ} := by
    intro m n hmn x (hx : σ + (m : ℝ≥0∞)⁻¹ < ‖f x‖ₑ)
    refine lt_of_le_of_lt (?_ : σ + (n : ℝ≥0∞)⁻¹ ≤ σ + (m : ℝ≥0∞)⁻¹) hx
    gcongr
  rw [← hmono.measure_iUnion]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hx).ne'
    exact ⟨n, lt_tsub_iff_left.mp hn⟩
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt le_self_add hn

/-- `σ < f*(t) ↔ t < ϱ(f,σ)` for finite `σ`: the rearrangement and the distribution function are
generalized inverses of each other. The `←` direction uses right-continuity of `ϱ(f, ·)`
(`distributionFunction_eq_iSup_inv`). -/
theorem lt_decreasingRearrangement_iff (f : α → E) (t : ℝ≥0∞) {σ : ℝ≥0∞} (hσ : σ ≠ ⊤) :
    σ < decreasingRearrangement μ f t ↔ t < distributionFunction μ f σ := by
  constructor
  · intro h
    by_contra hc
    exact (sInf_le (not_lt.mp hc) : decreasingRearrangement μ f t ≤ σ).not_gt h
  · intro h
    rw [distributionFunction_eq_iSup_inv μ f σ, lt_iSup_iff] at h
    obtain ⟨n, hn⟩ := h
    exact (ENNReal.lt_add_right hσ (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))).trans_le
      (le_decreasingRearrangement_of_lt_distributionFunction f t _ hn)

/-- **Equimeasurability** of `f*` and `‖f‖`: the super-level set `{t > 0 : σ < f*(t)}` has
Lebesgue measure `ϱ(f,σ)`, for finite `σ`. -/
theorem volume_lt_decreasingRearrangement (f : α → E) {σ : ℝ≥0∞} (hσ : σ ≠ ⊤) :
    volume.restrict (Ioi (0 : ℝ)) {t : ℝ | σ < decreasingRearrangement μ f (ENNReal.ofReal t)} =
      distributionFunction μ f σ := by
  rw [Measure.restrict_apply' measurableSet_Ioi]
  simp_rw [lt_decreasingRearrangement_iff μ f _ hσ]
  by_cases hϱ : distributionFunction μ f σ = ⊤
  · simp [hϱ]
  · have : {t : ℝ | ENNReal.ofReal t < distributionFunction μ f σ} ∩ Ioi 0 =
        Ioo 0 (distributionFunction μ f σ).toReal := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h, ht⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le hϱ).mp h⟩
      · rintro ⟨ht, h⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht.le hϱ).mpr h, ht⟩
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hϱ]

/-- The decreasing rearrangement preserves `Lʳ` integrals: `∫₀^∞ f*(t)^r dt = ∫_α ‖f‖^r dμ`.

If `f*` is finite on `(0, ∞)`, this is the layer-cake formula on both sides plus
equimeasurability (`volume_lt_decreasingRearrangement`). Otherwise `f*(t₀) = ∞` for some `t₀ > 0`,
so the left side is `∞`, and `ϱ(f,σ) > t₀` for every finite `σ`, so Chebyshev's inequality makes
the right side `∞` too. -/
theorem lintegral_decreasingRearrangement_rpow {f : α → E} (hf : AEStronglyMeasurable f μ)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioi (0 : ℝ), decreasingRearrangement μ f (ENNReal.ofReal t) ^ r =
      ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  by_cases hfin : ∀ t : ℝ, 0 < t → decreasingRearrangement μ f (ENNReal.ofReal t) ≠ ⊤
  · have hL : ∫⁻ t in Ioi (0 : ℝ), decreasingRearrangement μ f (ENNReal.ofReal t) ^ r =
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal ((decreasingRearrangement μ f (ENNReal.ofReal t)).toReal ^ r) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr.le,
        ENNReal.ofReal_toReal (hfin t ht)]
    have hR : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ r) ∂μ := by
      congr 1 with x
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le, ofReal_norm]
    have hmeas : Measurable fun t : ℝ =>
        (decreasingRearrangement μ f (ENNReal.ofReal t)).toReal :=
      ((decreasingRearrangement_measurable f).comp ENNReal.measurable_ofReal).ennreal_toReal
    rw [hL, hR, lintegral_rpow_eq_lintegral_meas_lt_mul _
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hmeas.aemeasurable hr,
      lintegral_rpow_eq_lintegral_meas_lt_mul _ (Eventually.of_forall fun _ => norm_nonneg _)
        hf.norm.aemeasurable hr]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    congr 1
    have hset : {t : ℝ | s < (decreasingRearrangement μ f (ENNReal.ofReal t)).toReal} ∩ Ioi 0 =
        {t : ℝ | ENNReal.ofReal s < decreasingRearrangement μ f (ENNReal.ofReal t)} ∩ Ioi 0 := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, and_congr_left_iff]
      intro ht
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hs) (hfin t ht)).symm
    rw [Measure.restrict_apply' measurableSet_Ioi, hset,
      ← Measure.restrict_apply' measurableSet_Ioi,
      volume_lt_decreasingRearrangement μ f ENNReal.ofReal_ne_top]
    unfold distributionFunction
    congr 1 with x
    rw [mem_ofPred_eq, mem_ofPred_eq, ← ofReal_norm,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hs)]
  · push Not at hfin
    obtain ⟨t₀, ht₀, htop⟩ := hfin
    have hL : ∫⁻ t in Ioi (0 : ℝ), decreasingRearrangement μ f (ENNReal.ofReal t) ^ r = ⊤ := by
      refine eq_top_iff.mpr ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ t in Ioc 0 t₀, ⊤ := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
              ENNReal.top_mul (ENNReal.ofReal_pos.mpr ht₀).ne']
        _ = ∫⁻ t in Ioc 0 t₀, decreasingRearrangement μ f (ENNReal.ofReal t) ^ r := by
            refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
            have : decreasingRearrangement μ f (ENNReal.ofReal t) = ⊤ :=
              top_le_iff.mp (htop ▸ decreasingRearrangement_antitone f
                (ENNReal.ofReal_le_ofReal ht.2))
            rw [this, ENNReal.top_rpow_of_pos hr]
        _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self
    rw [hL, eq_comm]
    refine ENNReal.eq_top_of_forall_nnreal_le fun x => ?_
    set c := ENNReal.ofReal t₀
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr ht₀).ne'
    set σ := ((x : ℝ≥0∞) / c) ^ r⁻¹
    have hσ : σ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hr.le)
        (ENNReal.div_ne_top ENNReal.coe_ne_top hc0)
    have hϱ : c < distributionFunction μ f σ := by
      rw [← lt_decreasingRearrangement_iff μ f c hσ, htop]
      exact hσ.lt_top
    calc (x : ℝ≥0∞) = σ ^ r * c := by
          rw [ENNReal.rpow_inv_rpow hr.ne', ENNReal.div_mul_cancel hc0 ENNReal.ofReal_ne_top]
      _ ≤ σ ^ r * μ {x | σ ^ r ≤ ‖f x‖ₑ ^ r} := by
          gcongr
          refine hϱ.le.trans (measure_mono fun y hy => ?_)
          exact ENNReal.rpow_le_rpow (le_of_lt hy) hr.le
      _ ≤ ∫⁻ x, ‖f x‖ₑ ^ r ∂μ :=
          mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const r) _

/-- Triebel §1.18.6, Lemma: `L_{p,p} = Lᵖ`, as raw quasinorms. Needs `0 < p` and
`AEStronglyMeasurable f μ` — see the module docstring for why each is genuinely necessary. -/
theorem lorentzNorm_diag {p : ℝ≥0∞} (hp : 0 < p) {f : α → E} (hf : AEStronglyMeasurable f μ) :
    lorentzNorm μ p p f = eLpNorm f p μ := by
  by_cases hptop : p = ⊤
  · subst hptop
    rw [eLpNorm_exponent_top hf, eLpNormEssSup_eq_essSup_enorm, essSup_eq_sInf]
    simp only [lorentzNorm, ↓reduceIte, ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero,
      one_mul]
    refine le_antisymm (iSup_le fun t => ?_) (le_iSup_of_le 0 ?_)
    · refine (decreasingRearrangement_antitone f (zero_le : (0 : ℝ≥0∞) ≤ t)).trans_eq ?_
      simp [decreasingRearrangement, distributionFunction]
    · simp [decreasingRearrangement, distributionFunction]
  · have hr : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hptop
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp.ne' hptop hf, lorentzNorm, ite_eq_right hptop,
      ENNReal.toReal_inv, one_div, ← lintegral_decreasingRearrangement_rpow μ hf hr]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hr.ne',
      ENNReal.rpow_one, mul_comm, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
      inv_mul_cancel₀ (ne_of_gt ht), ENNReal.ofReal_one, one_mul]

/-- Triebel §1.18.6, Lemma, bundled-type form: the Lorentz space `L_{p,p}(μ)` is literally the
same `AddSubgroup` of `α →ₘ[μ] E` as the ordinary `Lᵖ(μ)`, since the underlying quasinorms agree
exactly (`lorentzNorm_diag`) rather than merely up to equivalence. -/
theorem LorentzSpace.eq_Lp {p : ℝ≥0∞} (hp : 0 < p) :
    LorentzSpace E p p μ = Lp E p μ := by
  ext f
  change lorentzNorm μ p p f < ∞ ↔ eLpNorm f p μ < ∞
  rw [lorentzNorm_diag μ hp f.aestronglyMeasurable]

section Rearrangement

/-! ### Further facts about the decreasing rearrangement -/

variable {μ}

/-- A pointwise smaller function has a smaller rearrangement. -/
theorem decreasingRearrangement_mono {f g : α → E} (h : ∀ x, ‖g x‖ₑ ≤ ‖f x‖ₑ) (t : ℝ≥0∞) :
    decreasingRearrangement μ g t ≤ decreasingRearrangement μ f t := by
  refine sInf_le_sInf fun σ (hσ : distributionFunction μ f σ ≤ t) => ?_
  exact (measure_mono fun x (hx : σ < ‖g x‖ₑ) => hx.trans_le (h x)).trans hσ

/-- The infimum defining `f*(t)` is attained when finite: `ϱ(f, f*(t)) ≤ t`. -/
theorem distributionFunction_decreasingRearrangement_le (f : α → E) (t : ℝ≥0∞)
    (h : decreasingRearrangement μ f t ≠ ⊤) :
    distributionFunction μ f (decreasingRearrangement μ f t) ≤ t := by
  by_contra hc
  exact lt_irrefl _ ((lt_decreasingRearrangement_iff μ f t h).mpr (not_le.mp hc))

/-- `‖f‖_{L_{∞,∞}} = f*(0)`, the essential supremum of `‖f‖`. -/
theorem lorentzNorm_top_top (f : α → E) :
    lorentzNorm μ ⊤ ⊤ f = decreasingRearrangement μ f 0 := by
  simp only [lorentzNorm, ↓reduceIte, ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero,
    one_mul]
  refine le_antisymm (iSup_le fun t => decreasingRearrangement_antitone f zero_le)
    (le_iSup_of_le 0 le_rfl)

/-- `(∫₀ᵀ f*ʳ)^{1/r}` dominates `T^{1/r} f*(T)`, since `f*` is antitone. -/
theorem rpow_mul_decreasingRearrangement_le {r : ℝ} (hr : 0 < r) (f : α → E) (T : ℝ) :
    ENNReal.ofReal T ^ r⁻¹ * decreasingRearrangement μ f (ENNReal.ofReal T) ≤
      (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r) ^ r⁻¹ := by
  have hle : ENNReal.ofReal T * decreasingRearrangement μ f (ENNReal.ofReal T) ^ r ≤
      ∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r := by
    calc ENNReal.ofReal T * decreasingRearrangement μ f (ENNReal.ofReal T) ^ r
        = ∫⁻ _ in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal T) ^ r := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
      _ ≤ _ := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          gcongr
          exact decreasingRearrangement_antitone f (ENNReal.ofReal_le_ofReal hs.2)
  calc ENNReal.ofReal T ^ r⁻¹ * decreasingRearrangement μ f (ENNReal.ofReal T)
      = (ENNReal.ofReal T * decreasingRearrangement μ f (ENNReal.ofReal T) ^ r) ^ r⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]
    _ ≤ _ := by gcongr

/-- The large part `f · 1_{‖f‖ > f*(T)}` of the level-`f*(T)` split of `f` has
`∫ ‖·‖ʳ ≤ ∫₀ᵀ f*ʳ`: its rearrangement is at most `f*` and vanishes after `T`. -/
theorem lintegral_indicator_lt_decreasingRearrangement_le {r : ℝ} (hr : 0 < r) {f : α → E}
    (hf : StronglyMeasurable f) (T : ℝ)
    (hlev : decreasingRearrangement μ f (ENNReal.ofReal T) ≠ ⊤) :
    ∫⁻ x, ‖{x | decreasingRearrangement μ f (ENNReal.ofReal T) < ‖f x‖ₑ}.indicator f x‖ₑ ^ r ∂μ ≤
      ∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r := by
  set lev := decreasingRearrangement μ f (ENNReal.ofReal T)
  set S := {x | lev < ‖f x‖ₑ}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.enorm
  set g := S.indicator f
  have hg : AEStronglyMeasurable g μ := (hf.indicator hS).aestronglyMeasurable
  have hgf : ∀ x, ‖g x‖ₑ ≤ ‖f x‖ₑ := fun x => by
    by_cases hx : x ∈ S <;> simp [g, hx]
  rw [← lintegral_decreasingRearrangement_rpow μ hg hr]
  calc ∫⁻ s in Ioi 0, decreasingRearrangement μ g (ENNReal.ofReal s) ^ r
      ≤ ∫⁻ s in Ioi 0, (Ioc 0 T).indicator
          (fun s => decreasingRearrangement μ f (ENNReal.ofReal s) ^ r) s := by
        refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
        by_cases hsT : s ≤ T
        · rw [indicator_of_mem (show s ∈ Ioc 0 T from ⟨hs, hsT⟩)]
          gcongr
          exact decreasingRearrangement_mono hgf _
        · have hg0 : decreasingRearrangement μ g (ENNReal.ofReal s) = 0 := by
            refine le_antisymm (sInf_le ?_) zero_le
            change μ {x | 0 < ‖g x‖ₑ} ≤ ENNReal.ofReal s
            calc μ {x | 0 < ‖g x‖ₑ} ≤ μ S := measure_mono fun x hx => by
                  by_contra hxS
                  simp [g, hxS] at hx
              _ ≤ ENNReal.ofReal T := distributionFunction_decreasingRearrangement_le f _ hlev
              _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (le_of_not_ge hsT)
          rw [hg0, ENNReal.zero_rpow_of_pos hr]
          exact zero_le
    _ = ∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r := by
        rw [setLIntegral_indicator measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]

end Rearrangement
