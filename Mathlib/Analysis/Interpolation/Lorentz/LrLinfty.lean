/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Lorentz.Couple
import Mathlib.Analysis.Interpolation.RealInterpolation.Basic
import Mathlib.MeasureTheory.Function.LorentzSpace.Diag
import Mathlib.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of the couple `(Lʳ, L^∞)`

DRAFT — statements only.

Triebel §1.18.6, Theorem 1, in the quasi-Banach form (Krée; Bergh–Löfström §5.3): for
`0 < r < ∞`, the couple `(Lʳ, L^∞)`, realized as `InterpolationCat.lorentz 𝕜 μ E r r ⊤ ⊤`
(`L_{r,r} = Lʳ` and `L_{∞,∞} = L^∞` by `LorentzSpace.eq_Lp`), has

* K-functional `K(t, f; Lʳ, L^∞) ≈ (∫₀^{tʳ} f*(s)ʳ ds)^{1/r}` (for `r = 1`: `∫₀ᵗ f*`), with
  constants depending only on `r` (`lorentz_kFunctional_le`, `le_lorentz_kFunctional`);
* real interpolation spaces `(Lʳ, L^∞)_{θ,q} = L_{p,q}` for `1/p = (1-θ)/r` and `r ≤ q`, as an
  isomorphism in `QuasiBanachCat` compatible with the inclusions into `L⁰(μ)`
  (`nonempty_iso_realInterpolation_lorentz_top`).

The hypothesis `r ≤ q` is what makes Hardy's inequality (`lintegral_hardy`, exponent `q/r ≥ 1`)
applicable. It costs nothing downstream: in the reiteration argument `r` can be chosen as small as
needed.

## Proof outline
* `K ≤ 2 (∫₀^{tʳ} f*ʳ)^{1/r}`: split `f` by truncating `‖f‖` at height `f*(tʳ)`.
* `(∫₀^{tʳ} f*ʳ)^{1/r} ≤ C K`: for `f = f₀ + f₁`, `f*(s) ≤ f₀*(s) + ‖f₁‖_∞`
  (`decreasingRearrangement_add_le`), then the quasi-triangle inequality in `Lʳ(0, tʳ)` and
  `∫₀^∞ f₀*ʳ = ‖f₀‖ʳ_r` (`lintegral_decreasingRearrangement_rpow`).
* Identification: substitute `T = tʳ` in the `(θ,q)`-quasinorm. The upper bound for the
  `(θ,q)`-quasinorm is Hardy's inequality with `g = f*ʳ`, `λ = θ`, `s = q/r`; the lower bound is
  `(∫₀^T f*ʳ)^{1/r} ≥ T^{1/r} f*(T)`.
-/

open MeasureTheory Set CategoryTheory
open scoped ENNReal NNReal

section Rearrangement

/-! ### Rearrangement facts used for the K-functional bounds -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

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

/-- The level-`f*(T)` split: if `(∫₀ᵀ f*ʳ)^{1/r} < ∞`, then `f = a₀ + a₁` with `a₀ ∈ Lʳ`,
`a₁ ∈ L^∞`, `‖a₀‖_r ≤ (∫₀ᵀ f*ʳ)^{1/r}` and `T^{1/r} ‖a₁‖_∞ ≤ (∫₀ᵀ f*ʳ)^{1/r}`. Here
`a₀ = f · 1_{‖f‖ > f*(T)}` and `a₁ = f · 1_{‖f‖ ≤ f*(T)}`. -/
theorem LorentzSpace.exists_Lr_add_Linfty {r : ℝ≥0∞} (hr0 : 0 < r) (hr : r ≠ ⊤)
    (f : α →ₘ[μ] E) {T : ℝ} (hT : 0 < T)
    (hI : (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r.toReal) ^
      r.toReal⁻¹ ≠ ⊤) :
    ∃ a₀ : LorentzSpace E r r μ, ∃ a₁ : LorentzSpace E ⊤ ⊤ μ,
      (a₀ : α →ₘ[μ] E) + a₁ = f ∧
      lorentzNorm μ r r a₀ ≤ (∫⁻ s in Ioc 0 T,
        decreasingRearrangement μ f (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ ∧
      ENNReal.ofReal T ^ r.toReal⁻¹ * lorentzNorm μ ⊤ ⊤ a₁ ≤ (∫⁻ s in Ioc 0 T,
        decreasingRearrangement μ f (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ := by
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hr
  set g : α → E := ⇑f with hgdef
  have hg : StronglyMeasurable g := AEEqFun.stronglyMeasurable f
  set I := (∫⁻ s in Ioc 0 T, decreasingRearrangement μ g (ENNReal.ofReal s) ^ r.toReal) ^
    r.toReal⁻¹ with hIdef
  set lev := decreasingRearrangement μ g (ENNReal.ofReal T) with hlevdef
  have hlevI : ENNReal.ofReal T ^ r.toReal⁻¹ * lev ≤ I :=
    rpow_mul_decreasingRearrangement_le hrr g T
  have hlev : lev ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hT)
      ENNReal.ofReal_ne_top).ne'] at hlevI
    exact hI (top_le_iff.mp hlevI)
  set S := {x | lev < ‖g x‖ₑ} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const hg.enorm
  have hm₀ : AEStronglyMeasurable (S.indicator g) μ := (hg.indicator hS).aestronglyMeasurable
  have hm₁ : AEStronglyMeasurable (Sᶜ.indicator g) μ :=
    (hg.indicator hS.compl).aestronglyMeasurable
  have h₀ : lorentzNorm μ r r (S.indicator g) ≤ I := by
    rw [lorentzNorm_diag μ hr0 hm₀, eLpNorm_eq_lintegral_rpow_enorm_toReal hr0.ne' hr hm₀,
      one_div, hIdef]
    exact ENNReal.rpow_le_rpow (lintegral_indicator_lt_decreasingRearrangement_le hrr hg T hlev)
      (inv_nonneg.mpr hrr.le)
  have h₁ : lorentzNorm μ ⊤ ⊤ (Sᶜ.indicator g) ≤ lev := by
    rw [lorentzNorm_top_top]
    refine sInf_le (le_of_eq ?_ : distributionFunction μ (Sᶜ.indicator g) lev ≤ 0)
    change μ {x | lev < ‖Sᶜ.indicator g x‖ₑ} = 0
    convert measure_empty (μ := μ)
    ext x
    by_cases hx : x ∈ S
    · simp [hx]
    · have hx' : ¬ lev < ‖g x‖ₑ := hx
      simpa [hx] using not_lt.mp hx'
  refine ⟨⟨AEEqFun.mk _ hm₀, ?_⟩, ⟨AEEqFun.mk _ hm₁, ?_⟩, ?_, ?_, ?_⟩
  · change lorentzNorm μ r r (AEEqFun.mk _ hm₀) < ⊤
    rw [lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₀)]
    exact h₀.trans_lt (lt_top_iff_ne_top.mpr hI)
  · change lorentzNorm μ ⊤ ⊤ (AEEqFun.mk _ hm₁) < ⊤
    rw [lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₁)]
    exact h₁.trans_lt (lt_top_iff_ne_top.mpr hlev)
  · change AEEqFun.mk _ hm₀ + AEEqFun.mk _ hm₁ = f
    rw [AEEqFun.mk_add_mk]
    conv_rhs => rw [← AEEqFun.mk_coeFn f]
    congr 1
    exact indicator_self_add_compl S g
  · change lorentzNorm μ r r (AEEqFun.mk _ hm₀) ≤ I
    rw [lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₀)]
    exact h₀
  · change ENNReal.ofReal T ^ r.toReal⁻¹ * lorentzNorm μ ⊤ ⊤ (AEEqFun.mk _ hm₁) ≤ I
    rw [lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₁)]
    exact (by gcongr : _ ≤ ENNReal.ofReal T ^ r.toReal⁻¹ * lev).trans hlevI

end Rearrangement

section Estimates

/-! ### Comparison of the Lorentz quasinorm with `T^{-θ/ρ} (∫₀ᵀ f*^ρ)^{1/ρ}` -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

/-- The Lorentz integrand `T^{(1-θ)/ρ} f*(T)` is at most `T^{-θ/ρ} (∫₀ᵀ f*^ρ)^{1/ρ}`. -/
theorem rpow_mul_decreasingRearrangement_le_rpow_mul {ρ θ : ℝ} (hρ : 0 < ρ) (f : α → E)
    {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal T ^ ((1 - θ) / ρ) * decreasingRearrangement μ f (ENNReal.ofReal T) ≤
      ENNReal.ofReal T ^ (-θ / ρ) *
        (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ ρ) ^ ρ⁻¹ := by
  have hT0 : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.mpr hT).ne'
  rw [show (1 - θ) / ρ = -θ / ρ + ρ⁻¹ by field_simp; ring,
    ENNReal.rpow_add _ _ hT0 ENNReal.ofReal_ne_top, mul_assoc]
  gcongr
  exact rpow_mul_decreasingRearrangement_le hρ f T

/-- Hardy's inequality applied to `g = f*^ρ` (exponent `s = q/ρ ≥ 1`):
`∫₀^∞ (T^{-θ/ρ} (∫₀ᵀ f*^ρ)^{1/ρ})^q dT/T ≤ θ^{-q/ρ} ∫₀^∞ (T^{(1-θ)/ρ} f*(T))^q dT/T`. -/
theorem lintegral_rearrangement_hardy {ρ θ q : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hρq : ρ ≤ q)
    (f : α → E) :
    ∫⁻ T in Ioi 0, (ENNReal.ofReal T ^ (-θ / ρ) *
        (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ ρ) ^ ρ⁻¹) ^ q *
        ENNReal.ofReal T⁻¹ ≤
      ENNReal.ofReal θ⁻¹ ^ (q / ρ) *
        ∫⁻ T in Ioi 0, (ENNReal.ofReal T ^ ((1 - θ) / ρ) *
          decreasingRearrangement μ f (ENNReal.ofReal T)) ^ q * ENNReal.ofReal T⁻¹ := by
  have hq : 0 < q := hρ.trans_le hρq
  have hs : 1 ≤ q / ρ := (one_le_div hρ).mpr hρq
  set g : ℝ → ℝ≥0∞ := fun s => decreasingRearrangement μ f (ENNReal.ofReal s) ^ ρ with hgdef
  have hg : Measurable g :=
    ((decreasingRearrangement_measurable f).comp ENNReal.measurable_ofReal).pow_const ρ
  have hL : ∀ T ∈ Ioi (0 : ℝ), (ENNReal.ofReal T ^ (-θ / ρ) *
      (∫⁻ s in Ioc 0 T, g s) ^ ρ⁻¹) ^ q =
      (ENNReal.ofReal T ^ (-θ) * ∫⁻ s in Ioc 0 T, g s) ^ (q / ρ) := by
    intro T _
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 2 <;> ring
  have hR : ∀ T ∈ Ioi (0 : ℝ), (ENNReal.ofReal T ^ (1 - θ) * g T) ^ (q / ρ) =
      (ENNReal.ofReal T ^ ((1 - θ) / ρ) *
        decreasingRearrangement μ f (ENNReal.ofReal T)) ^ q := by
    intro T _
    rw [hgdef, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    congr 2
    · field_simp
    · field_simp
  calc _ = ∫⁻ T in Ioi 0, (ENNReal.ofReal T ^ (-θ) * ∫⁻ s in Ioc 0 T, g s) ^ (q / ρ) *
          ENNReal.ofReal T⁻¹ :=
        setLIntegral_congr_fun measurableSet_Ioi fun T hT => by rw [hL T hT]
    _ ≤ ENNReal.ofReal θ⁻¹ ^ (q / ρ) *
          ∫⁻ T in Ioi 0, (ENNReal.ofReal T ^ (1 - θ) * g T) ^ (q / ρ) * ENNReal.ofReal T⁻¹ :=
        lintegral_hardy hg hθ hs
    _ = _ := by
        congr 1
        exact setLIntegral_congr_fun measurableSet_Ioi fun T hT => by rw [hR T hT]

/-- The `q = ∞` counterpart of `lintegral_rearrangement_hardy`:
`T^{-θ/ρ} (∫₀ᵀ f*^ρ)^{1/ρ} ≤ θ^{-1/ρ} ‖f‖_{p,∞}` for `1/p = (1-θ)/ρ`, since
`f*(u) ≤ u^{-1/p} ‖f‖_{p,∞}`. -/
theorem rpow_mul_rearrangement_le_lorentzNorm_top {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ)
    {p : ℝ≥0∞} (hp : p⁻¹.toReal = (1 - θ) / ρ) (f : α → E) {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal T ^ (-θ / ρ) *
        (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ ρ) ^ ρ⁻¹ ≤
      ENNReal.ofReal θ⁻¹ ^ ρ⁻¹ * lorentzNorm μ p ⊤ f := by
  set L := lorentzNorm μ p ⊤ f with hLdef
  have hT0 : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.mpr hT).ne'
  by_cases hL : L = ⊤
  · rw [hL, ENNReal.mul_top (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (inv_pos.mpr hθ))
      ENNReal.ofReal_ne_top).ne']
    exact le_top
  have hpt : ∀ u ∈ Ioc (0 : ℝ) T, decreasingRearrangement μ f (ENNReal.ofReal u) ^ ρ ≤
      L ^ ρ * ENNReal.ofReal u ^ (θ - 1) := by
    intro u hu
    have hu0 : ENNReal.ofReal u ≠ 0 := (ENNReal.ofReal_pos.mpr hu.1).ne'
    have h1 : ENNReal.ofReal u ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal u) ≤
        L := by
      rw [hLdef, lorentzNorm, ite_eq_left rfl]
      have := le_iSup (fun t : ℝ≥0 => (t : ℝ≥0∞) ^ p⁻¹.toReal *
        decreasingRearrangement μ f (t : ℝ≥0∞)) u.toNNReal
      simpa [ENNReal.ofReal] using this
    have h2 : decreasingRearrangement μ f (ENNReal.ofReal u) ≤
        L * ENNReal.ofReal u ^ (-p⁻¹.toReal) := by
      rw [ENNReal.rpow_neg, ← div_eq_mul_inv]
      rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hu.1)
        ENNReal.ofReal_ne_top).ne') (Or.inl (ENNReal.rpow_ne_top_of_ne_zero hu0
          ENNReal.ofReal_ne_top)), mul_comm]
      exact h1
    calc decreasingRearrangement μ f (ENNReal.ofReal u) ^ ρ
        ≤ (L * ENNReal.ofReal u ^ (-p⁻¹.toReal)) ^ ρ := by gcongr
      _ = L ^ ρ * ENNReal.ofReal u ^ (θ - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ← ENNReal.rpow_mul, hp]
          congr 2
          field_simp
          ring
  have hint : ∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ ρ ≤
      L ^ ρ * (ENNReal.ofReal T ^ θ * ENNReal.ofReal θ⁻¹) := by
    calc _ ≤ ∫⁻ s in Ioc 0 T, L ^ ρ * ENNReal.ofReal s ^ (θ - 1) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hρ.le hL),
            lintegral_Ioc_zero_rpow_sub_one hθ hT]
  calc _ ≤ ENNReal.ofReal T ^ (-θ / ρ) *
        (L ^ ρ * (ENNReal.ofReal T ^ θ * ENNReal.ofReal θ⁻¹)) ^ ρ⁻¹ := by
        gcongr
    _ = ENNReal.ofReal θ⁻¹ ^ ρ⁻¹ * L := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hρ.le),
          ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hρ.le), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, mul_inv_cancel₀ hρ.ne', ENNReal.rpow_one]
        rw [show ENNReal.ofReal T ^ (-θ / ρ) * (L * (ENNReal.ofReal T ^ (θ * ρ⁻¹) *
            ENNReal.ofReal θ⁻¹ ^ ρ⁻¹)) = (ENNReal.ofReal T ^ (-θ / ρ) *
            ENNReal.ofReal T ^ (θ * ρ⁻¹)) * (ENNReal.ofReal θ⁻¹ ^ ρ⁻¹ * L) by ring,
          ← ENNReal.rpow_add _ _ hT0 ENNReal.ofReal_ne_top,
          show -θ / ρ + θ * ρ⁻¹ = 0 by ring, ENNReal.rpow_zero, one_mul]

end Estimates

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable (r : ℝ≥0∞) [Fact (0 < r)]

namespace InterpolationCat

/-- Upper bound for the K-functional of `(Lʳ, L^∞)`:
`K(t, f) ≤ c (∫₀^{tʳ} f*(s)ʳ ds)^{1/r}`, uniformly in `t > 0` and `f ∈ Lʳ + L^∞`. -/
theorem lorentz_kFunctional_le (hr : r ≠ ⊤) :
    ∃ c : ℝ≥0, ∀ t : ℝ, 0 < t → ∀ a : InterpolationCouple.sum (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁,
      ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) ≤
        c * (∫⁻ s in Ioc 0 (t ^ r.toReal), decreasingRearrangement μ
          (lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a) (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ := by
  refine ⟨2, fun t ht a => ?_⟩
  have hrpos : 0 < r := Fact.out
  have hr0 : 0 < r.toReal := ENNReal.toReal_pos hrpos.ne' hr
  set F : α →ₘ[μ] E := lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a with hFdef
  set T := t ^ r.toReal with hTdef
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  set I := (∫⁻ s in Ioc 0 T, decreasingRearrangement μ F (ENNReal.ofReal s) ^ r.toReal) ^
    r.toReal⁻¹ with hIdef
  change ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) ≤ ((2 : ℝ≥0) : ℝ≥0∞) * I
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (by norm_num)]
    exact le_top
  -- split `f` at the level `f*(T)`
  obtain ⟨a₀, a₁, hsum, h₀, h₁⟩ := LorentzSpace.exists_Lr_add_Linfty hrpos hr F hT hI
  have hofT : ENNReal.ofReal T ^ r.toReal⁻¹ = ENNReal.ofReal t := by
    rw [ENNReal.ofReal_rpow_of_nonneg hT.le (inv_nonneg.mpr hr0.le),
      Real.rpow_rpow_inv ht.le hr0.ne']
  rw [hofT] at h₁
  have ha : (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum
      (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀ (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁) = a := by
    apply InterpolationCouple.sumToAmbient_injective
    change lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ (Submodule.Quotient.mk (a₀, a₁)) = F
    rw [lorentzSumToL0_mk]
    exact hsum
  have hK : InterpolationCouple.KFunctional _ _ t a ≤ ‖a₀‖ + t * ‖a₁‖ :=
    csInf_le (InterpolationCouple.kFunctional_set_boundedBelow _ _ t ht.le a) ⟨a₀, a₁, ha, rfl⟩
  calc ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a)
      ≤ ENNReal.ofReal (‖a₀‖ + t * ‖a₁‖) := ENNReal.ofReal_le_ofReal hK
    _ = lorentzNorm μ r r a₀ + ENNReal.ofReal t * lorentzNorm μ ⊤ ⊤ a₁ := by
        change ENNReal.ofReal ((lorentzNorm μ r r a₀).toReal +
          t * (lorentzNorm μ ⊤ ⊤ a₁).toReal) = _
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg ht.le ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal a₀.2.ne, ENNReal.ofReal_toReal a₁.2.ne]
    _ ≤ I + I := add_le_add h₀ h₁
    _ = ((2 : ℝ≥0) : ℝ≥0∞) * I := by rw [← two_mul]; norm_num

/-- Lower bound for the K-functional of `(Lʳ, L^∞)`:
`(∫₀^{tʳ} f*(s)ʳ ds)^{1/r} ≤ c K(t, f)`, uniformly in `t > 0` and `f ∈ Lʳ + L^∞`. -/
theorem le_lorentz_kFunctional (hr : r ≠ ⊤) :
    ∃ c : ℝ≥0, ∀ t : ℝ, 0 < t → ∀ a : InterpolationCouple.sum (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁,
      (∫⁻ s in Ioc 0 (t ^ r.toReal), decreasingRearrangement μ
          (lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a) (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ ≤
        c * ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) := by
  have hrpos : 0 < r := Fact.out
  have hr0 : 0 < r.toReal := ENNReal.toReal_pos hrpos.ne' hr
  have hri : 0 ≤ r.toReal⁻¹ := inv_nonneg.mpr hr0.le
  set C : ℝ≥0∞ := 2 * 2 ^ r.toReal⁻¹ with hCdef
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg hri
    (by norm_num))
  have hC0 : C ≠ 0 := mul_ne_zero (by norm_num) (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  refine ⟨C.toNNReal, fun t ht a => ?_⟩
  rw [ENNReal.coe_toNNReal hCtop]
  set f : α → E := ⇑(lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a : α →ₘ[μ] E) with hfdef
  set T := t ^ r.toReal with hTdef
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  have hofT : ENNReal.ofReal T = ENNReal.ofReal t ^ r.toReal := by
    rw [hTdef, ENNReal.ofReal_rpow_of_nonneg ht.le hr0.le]
  set I := (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r.toReal) ^
    r.toReal⁻¹ with hIdef
  change I ≤ C * _
  -- the bound for a single decomposition `f = a₀ + a₁`
  have hbound : ∀ a₀ : LorentzSpace E r r μ, ∀ a₁ : LorentzSpace E ⊤ ⊤ μ,
      (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀ (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁) = a →
      I ≤ C * (lorentzNorm μ r r a₀ + ENNReal.ofReal t * lorentzNorm μ ⊤ ⊤ a₁) := by
    intro a₀ a₁ ha
    set A := lorentzNorm μ r r a₀ with hAdef
    set M := lorentzNorm μ ⊤ ⊤ a₁ with hMdef
    have hfae : f =ᵐ[μ] ⇑a₀ + ⇑a₁ := by
      rw [hfdef, ← ha, lorentzSumToL0_mk]
      exact AEEqFun.coeFn_add _ _
    have hpt : ∀ s : ℝ, decreasingRearrangement μ f (ENNReal.ofReal s) ≤
        decreasingRearrangement μ a₀ (ENNReal.ofReal s) + M := by
      intro s
      rw [decreasingRearrangement_congr_ae hfae, hMdef, lorentzNorm_top_top]
      simpa using decreasingRearrangement_add_le (μ := μ) (⇑a₀) (⇑a₁) (ENNReal.ofReal s) 0
    have hA : ∫⁻ s in Ioc 0 T, decreasingRearrangement μ a₀ (ENNReal.ofReal s) ^ r.toReal ≤
        A ^ r.toReal := by
      have hm : AEStronglyMeasurable (⇑a₀) μ := (a₀ : α →ₘ[μ] E).aestronglyMeasurable
      calc _ ≤ ∫⁻ s in Ioi 0, decreasingRearrangement μ a₀ (ENNReal.ofReal s) ^ r.toReal :=
            lintegral_mono_set Ioc_subset_Ioi_self
        _ = ∫⁻ x, ‖a₀ x‖ₑ ^ r.toReal ∂μ := lintegral_decreasingRearrangement_rpow μ hm hr0
        _ = A ^ r.toReal := by
            rw [hAdef, lorentzNorm_diag μ hrpos hm,
              eLpNorm_eq_lintegral_rpow_enorm_toReal hrpos.ne' hr hm, ← ENNReal.rpow_mul,
              one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
    have hint : ∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r.toReal ≤
        2 ^ r.toReal * (A ^ r.toReal + (ENNReal.ofReal t * M) ^ r.toReal) := by
      calc _ ≤ ∫⁻ s in Ioc 0 T, 2 ^ r.toReal *
            (decreasingRearrangement μ a₀ (ENNReal.ofReal s) ^ r.toReal + M ^ r.toReal) := by
            refine lintegral_mono fun s => ?_
            exact (ENNReal.rpow_le_rpow (hpt s) hr0.le).trans
              (ENNReal.add_rpow_le_two_rpow_mul _ _ _ hr0.le)
        _ = 2 ^ r.toReal * ((∫⁻ s in Ioc 0 T,
              decreasingRearrangement μ a₀ (ENNReal.ofReal s) ^ r.toReal) +
              ENNReal.ofReal T * M ^ r.toReal) := by
            rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le (by norm_num)),
              lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc,
              sub_zero, mul_comm (M ^ r.toReal)]
        _ ≤ _ := by
            rw [hofT, ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
            gcongr
    have hAB : A ^ r.toReal + (ENNReal.ofReal t * M) ^ r.toReal ≤
        2 * (A + ENNReal.ofReal t * M) ^ r.toReal := by
      rw [two_mul]
      gcongr
      · exact le_self_add
      · exact le_add_self
    calc I ≤ (2 ^ r.toReal * (A ^ r.toReal + (ENNReal.ofReal t * M) ^ r.toReal)) ^
          r.toReal⁻¹ := ENNReal.rpow_le_rpow hint hri
      _ ≤ (2 ^ r.toReal * (2 * (A + ENNReal.ofReal t * M) ^ r.toReal)) ^ r.toReal⁻¹ := by
          gcongr
      _ = C * (A + ENNReal.ofReal t * M) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hri, ENNReal.mul_rpow_of_nonneg _ _ hri,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_inv_cancel₀ hr0.ne', ENNReal.rpow_one,
            ENNReal.rpow_one, hCdef, mul_assoc]
  -- pass to the infimum over decompositions
  have hS : ∀ x ∈ {x : ℝ | ∃ a₀ : LorentzSpace E r r μ, ∃ a₁ : LorentzSpace E ⊤ ⊤ μ,
      (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀ (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁) = a ∧ ‖a₀‖ + t * ‖a₁‖ = x},
      0 ≤ x ∧ I ≤ C * ENNReal.ofReal x := by
    rintro x ⟨a₀, a₁, ha, rfl⟩
    refine ⟨add_nonneg ENNReal.toReal_nonneg (mul_nonneg ht.le ENNReal.toReal_nonneg),
      (hbound a₀ a₁ ha).trans_eq ?_⟩
    change _ = C * ENNReal.ofReal ((lorentzNorm μ r r a₀).toReal +
      t * (lorentzNorm μ ⊤ ⊤ a₁).toReal)
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg ht.le ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal a₀.2.ne, ENNReal.ofReal_toReal a₁.2.ne]
  have hne := InterpolationCouple.kFunctional_set_nonempty _ _ t a
  have hItop : I ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hne
    exact ((hS x hx).2.trans_lt (ENNReal.mul_lt_top hCtop.lt_top ENNReal.ofReal_lt_top)).ne
  have hc' : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hle : I.toReal / C.toReal ≤ InterpolationCouple.KFunctional _ _ t a := by
    refine le_csInf hne fun x hx => ?_
    obtain ⟨hx0, hIx⟩ := hS x hx
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hCtop ENNReal.ofReal_ne_top) hIx
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0] at this
    rw [div_le_iff₀ hc']
    linarith
  calc I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hItop).symm
    _ ≤ ENNReal.ofReal (C.toReal * InterpolationCouple.KFunctional _ _ t a) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hc'] at hle
        linarith
    _ = C * ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) := by
        rw [ENNReal.ofReal_mul hc'.le, ENNReal.ofReal_toReal hCtop]

/-- Triebel §1.18.6, Theorem 1 (quasi-Banach form): `(Lʳ, L^∞)_{θ,q} = L_{p,q}` for
`1/p = (1-θ)/r` and `r ≤ q`, as an isomorphism of quasi-Banach spaces compatible with the
inclusions of both sides into `L⁰(μ)`. -/
theorem nonempty_iso_realInterpolation_lorentz_top (hr : r ≠ ⊤) (θ : ℝ) (q : ℝ≥0∞)
    [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] (hrq : r ≤ q) (p : ℝ≥0∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * r⁻¹) :
    ∃ e : (realInterpolationFunctor 𝕜 θ q).obj (lorentz 𝕜 μ E r r ⊤ ⊤) ≅
        QuasiBanachCat.of 𝕜 (LorentzSpace E p q μ),
      ∀ x, lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ ((realInterpolationFunctor 𝕜 θ q).toSum _ x) =
        LorentzSpace.toL0 μ E 𝕜 p q (e.hom.hom x) := by
  sorry

end InterpolationCat
