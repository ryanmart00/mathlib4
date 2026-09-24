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

end Rearrangement

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
  set f : α → E := ⇑F with hfdef
  have hf : StronglyMeasurable f := AEEqFun.stronglyMeasurable F
  set T := t ^ r.toReal with hTdef
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  set I := (∫⁻ s in Ioc 0 T, decreasingRearrangement μ f (ENNReal.ofReal s) ^ r.toReal) ^
    r.toReal⁻¹ with hIdef
  change ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) ≤ ((2 : ℝ≥0) : ℝ≥0∞) * I
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (by norm_num)]
    exact le_top
  -- split `f` at the level `f*(T)`
  set lev := decreasingRearrangement μ f (ENNReal.ofReal T) with hlevdef
  have hofT : ENNReal.ofReal T ^ r.toReal⁻¹ = ENNReal.ofReal t := by
    rw [ENNReal.ofReal_rpow_of_nonneg hT.le (inv_nonneg.mpr hr0.le),
      Real.rpow_rpow_inv ht.le hr0.ne']
  have hlevI : ENNReal.ofReal t * lev ≤ I := hofT ▸ rpow_mul_decreasingRearrangement_le hr0 f T
  have hlev : lev ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ht).ne'] at hlevI
    exact hI (top_le_iff.mp hlevI)
  set S := {x | lev < ‖f x‖ₑ} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.enorm
  have hm₀ : AEStronglyMeasurable (S.indicator f) μ := (hf.indicator hS).aestronglyMeasurable
  have hm₁ : AEStronglyMeasurable (Sᶜ.indicator f) μ :=
    (hf.indicator hS.compl).aestronglyMeasurable
  have h₀ : lorentzNorm μ r r (S.indicator f) ≤ I := by
    rw [lorentzNorm_diag μ hrpos hm₀, eLpNorm_eq_lintegral_rpow_enorm_toReal hrpos.ne' hr hm₀,
      one_div, hIdef]
    exact ENNReal.rpow_le_rpow (lintegral_indicator_lt_decreasingRearrangement_le hr0 hf T hlev)
      (inv_nonneg.mpr hr0.le)
  have h₁ : lorentzNorm μ ⊤ ⊤ (Sᶜ.indicator f) ≤ lev := by
    rw [lorentzNorm_top_top]
    refine sInf_le (le_of_eq ?_ : distributionFunction μ (Sᶜ.indicator f) lev ≤ 0)
    change μ {x | lev < ‖Sᶜ.indicator f x‖ₑ} = 0
    convert measure_empty (μ := μ)
    ext x
    by_cases hx : x ∈ S
    · simp [hx]
    · have hx' : ¬ lev < ‖f x‖ₑ := hx
      simpa [hx] using not_lt.mp hx'
  let a₀ : LorentzSpace E r r μ := ⟨AEEqFun.mk _ hm₀, by
    change lorentzNorm μ r r (AEEqFun.mk _ hm₀) < ⊤
    rw [lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₀)]
    exact h₀.trans_lt (lt_top_iff_ne_top.mpr hI)⟩
  let a₁ : LorentzSpace E ⊤ ⊤ μ := ⟨AEEqFun.mk _ hm₁, by
    change lorentzNorm μ ⊤ ⊤ (AEEqFun.mk _ hm₁) < ⊤
    rw [lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₁)]
    exact h₁.trans_lt (lt_top_iff_ne_top.mpr hlev)⟩
  have ha : (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum
      (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀ (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁) = a := by
    apply InterpolationCouple.sumToAmbient_injective
    change lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ (Submodule.Quotient.mk (a₀, a₁)) = F
    rw [lorentzSumToL0_mk]
    change (AEEqFun.mk _ hm₀ + AEEqFun.mk _ hm₁ : α →ₘ[μ] E) = F
    rw [AEEqFun.mk_add_mk]
    conv_rhs => rw [← AEEqFun.mk_coeFn F]
    congr 1
    exact indicator_self_add_compl S f
  have hK : InterpolationCouple.KFunctional _ _ t a ≤ ‖a₀‖ + t * ‖a₁‖ :=
    csInf_le (InterpolationCouple.kFunctional_set_boundedBelow _ _ t ht.le a) ⟨a₀, a₁, ha, rfl⟩
  have hn₀ : ENNReal.ofReal ‖a₀‖ = lorentzNorm μ r r (S.indicator f) := by
    change ENNReal.ofReal (lorentzNorm μ r r a₀).toReal = _
    rw [ENNReal.ofReal_toReal a₀.2.ne]
    exact lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₀)
  have hn₁ : ENNReal.ofReal ‖a₁‖ = lorentzNorm μ ⊤ ⊤ (Sᶜ.indicator f) := by
    change ENNReal.ofReal (lorentzNorm μ ⊤ ⊤ a₁).toReal = _
    rw [ENNReal.ofReal_toReal a₁.2.ne]
    exact lorentzNorm_congr_ae _ _ (AEEqFun.coeFn_mk _ hm₁)
  calc ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a)
      ≤ ENNReal.ofReal (‖a₀‖ + t * ‖a₁‖) := ENNReal.ofReal_le_ofReal hK
    _ = ENNReal.ofReal ‖a₀‖ + ENNReal.ofReal t * ENNReal.ofReal ‖a₁‖ := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_mul ht.le]
        · exact ENNReal.toReal_nonneg
        · exact mul_nonneg ht.le ENNReal.toReal_nonneg
    _ ≤ I + I := by
        rw [hn₀, hn₁]
        exact add_le_add h₀ ((by gcongr : ENNReal.ofReal t * lorentzNorm μ ⊤ ⊤ (Sᶜ.indicator f)
          ≤ ENNReal.ofReal t * lev).trans hlevI)
    _ = ((2 : ℝ≥0) : ℝ≥0∞) * I := by rw [← two_mul]; norm_num

/-- Lower bound for the K-functional of `(Lʳ, L^∞)`:
`(∫₀^{tʳ} f*(s)ʳ ds)^{1/r} ≤ c K(t, f)`, uniformly in `t > 0` and `f ∈ Lʳ + L^∞`. -/
theorem le_lorentz_kFunctional (hr : r ≠ ⊤) :
    ∃ c : ℝ≥0, ∀ t : ℝ, 0 < t → ∀ a : InterpolationCouple.sum (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁,
      (∫⁻ s in Ioc 0 (t ^ r.toReal), decreasingRearrangement μ
          (lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a) (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ ≤
        c * ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) := by
  sorry

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
