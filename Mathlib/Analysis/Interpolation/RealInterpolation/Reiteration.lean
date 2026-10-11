/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.Classes
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JInterpolationFunctor
import Mathlib.MeasureTheory.Integral.Hardy

/-!
# The reiteration theorem

Bergh–Löfström Theorem 3.5.3 (quasi-normed form: Theorem 3.11.5; Triebel §1.10.2): let
`Ā = (A₀, A₁)` and `X̄ = (X₀, X₁)` be couples (in the same ambient space) with `Xᵢ` complete and
of class `𝒞(θᵢ; Ā)`, `0 ≤ θᵢ ≤ 1`, `θ₀ ≠ θ₁`. For `0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`,
`X̄_{η,q} = Ā_{θ,q}` with equivalent quasinorms. In particular
`(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})_{η,q} = Ā_{θ,q}`.

The proof follows B–L.
* `X̄_{η,q} ⊂ Ā_{θ,q}` uses only the `𝒦(θᵢ)` conditions: `K(t, a; Ā) ≤ C t^{θ₀} K(t^{θ₁-θ₀}, a; X̄)`
  and the change of variables `s = t^{θ₁-θ₀}`.
* `Ā_{θ,q} ⊂ X̄_{η,q}` uses only the `𝒥(θᵢ)` conditions: represent `a = ∑ᵥ uᵥ` by the discrete
  J-method for `Ā` (equivalence theorem), estimate `K(2^{μ(θ₁-θ₀)}, a; X̄)` by Aoki–Rolewicz for
  the quasi-norm `K(t, ·; X̄)`, and conclude by the discrete K-method for `X̄` and Young's
  inequality, as in the proof of the equivalence theorem.

Both halves are first stated for the K-method backend, comparing elements of the two sum spaces
with the same image in the ambient space; the bundled form is an isomorphism of quasi-Banach spaces
compatible with the maps to the ambient space.

## Main definitions
* `InterpolationCat.ofEmbeddings A κ₀ κ₁`: the couple `(X₀, X₁)` embedded in the ambient space of
  `A`.
* `InterpolationCat.realInterpolationCouple A θ₀ q₀ θ₁ q₁`: the couple `(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})`.

## Main statements
* `InterpolationCouple.exists_realInterpolationENorm_le_of_isOfClassK`,
  `InterpolationCouple.exists_realInterpolationENorm_le_of_isOfClassJ`: the two inclusions.
* `InterpolationCat.nonempty_iso_realInterpolationFunctor_reiteration`: the reiteration theorem.
* `InterpolationCat.nonempty_iso_realInterpolationFunctor_realInterpolationCouple`:
  `(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})_{η,q} = Ā_{θ,q}`.
-/

universe v u

open CategoryTheory Filter MeasureTheory
open scoped ENNReal

namespace InterpolationCouple

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
variable {X₀ X₁ : Type*}
  [QuasinormedAddCommGroup X₀] [QuasiNormedSpace 𝕜 X₀]
  [QuasinormedAddCommGroup X₁] [QuasiNormedSpace 𝕜 X₁]
variable (κ₀ : X₀ →L[𝕜] 𝒜) (κ₁ : X₁ →L[𝕜] 𝒜)

/-- Reiteration, `X̄_{η,q} ⊂ Ā_{θ,q}` (B–L Theorem 3.5.3, first half; 3.11.5): if `Xᵢ` is of class
`𝒦(θᵢ; Ā)` with `θ₀ ≠ θ₁`, and `θ = (1 - η) θ₀ + η θ₁`, then every `a ∈ X₀ + X₁` lies in `A₀ + A₁`
(as the element `b` with the same image in the ambient space) with
`‖b‖_{Ā,θ,q} ≤ C ‖a‖_{X̄,η,q}`. -/
theorem exists_realInterpolationENorm_le_of_isOfClassK {θ₀ θ₁ η θ : ℝ} (hne : θ₀ ≠ θ₁)
    (hθ : θ = (1 - η) * θ₀ + η * θ₁) {q : ℝ≥0∞} (hq : 0 < q)
    (hK₀ : IsOfClassK ι₀ ι₁ θ₀ κ₀) (hK₁ : IsOfClassK ι₀ ι₁ θ₁ κ₁) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum κ₀ κ₁, ∃ b : sum ι₀ ι₁,
      sumToAmbient ι₀ ι₁ b = sumToAmbient κ₀ κ₁ a ∧
        realInterpolationENorm ι₀ ι₁ θ q b ≤ C * realInterpolationENorm κ₀ κ₁ η q a := by
  obtain ⟨C₀, hC₀⟩ := hK₀
  obtain ⟨C₁, hC₁⟩ := hK₁
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hCk : 0 < Ck :=
    QuasinormedAddCommGroup.quasiTriangleConst_pos.trans_le (le_max_left _ _)
  set Cm := max (max C₀ C₁) 1
  have hCm : 0 < Cm := zero_lt_one.trans_le (le_max_right _ _)
  set d := θ₁ - θ₀
  have hd : d ≠ 0 := sub_ne_zero.mpr hne.symm
  have hθd : θ₀ - θ = -(η * d) := by rw [hθ]; ring
  set D := ENNReal.ofReal (Ck * Cm) * ENNReal.ofReal |d|⁻¹ ^ q⁻¹.toReal
  refine ⟨D, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top), fun a => ?_⟩
  -- B–L: "suppose that `a = a₀ + a₁ ∈ X̄_{η,q}` with `aᵢ ∈ Xᵢ`"
  obtain ⟨⟨x₀, x₁⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b₀, hb₀, -⟩ := hC₀ x₀
  obtain ⟨b₁, hb₁, -⟩ := hC₁ x₁
  refine ⟨b₀ + b₁, by rw [map_add, hb₀, hb₁, sumToAmbient_mk], ?_⟩
  set a : sum κ₀ κ₁ := Submodule.Quotient.mk (x₀, x₁)
  -- B–L: "since `Xᵢ` is of class `𝒞(θᵢ; Ā)`, `K(t, a; Ā) ≤ C t^{θ₀} K(t^{θ₁-θ₀}, a; X̄)`"
  have hK (t : ℝ) (ht : 0 < t) : KFunctional ι₀ ι₁ t (b₀ + b₁) ≤
      Ck * Cm * t ^ θ₀ * KFunctional κ₀ κ₁ (t ^ d) a := by
    have hD : 0 < Ck * Cm * t ^ θ₀ := by positivity
    rw [← div_le_iff₀' hD]
    refine le_csInf (kFunctional_set_nonempty κ₀ κ₁ _ a) ?_
    rintro r ⟨y₀, y₁, hy, rfl⟩
    obtain ⟨c₀, hc₀, hc₀K⟩ := hC₀ y₀
    obtain ⟨c₁, hc₁, hc₁K⟩ := hC₁ y₁
    have hc : c₀ + c₁ = b₀ + b₁ := sumToAmbient_injective ι₀ ι₁ (by
      rw [map_add, map_add, hc₀, hc₁, hb₀, hb₁, ← sumToAmbient_mk, ← sumToAmbient_mk, hy])
    rw [div_le_iff₀' hD, ← hc]
    have hy₀ := QuasinormedAddCommGroup.norm_nonneg y₀
    have hy₁ := QuasinormedAddCommGroup.norm_nonneg y₁
    have h0 := hc₀K t ht
    have h1 := hc₁K t ht
    have hC₀m : C₀ ≤ Cm := (le_max_left _ _).trans (le_max_left _ _)
    have hC₁m : C₁ ≤ Cm := (le_max_right _ _).trans (le_max_left _ _)
    have ht0 := Real.rpow_pos_of_pos ht θ₀
    have ht1 := Real.rpow_pos_of_pos ht θ₁
    have hsplit : t ^ θ₁ = t ^ θ₀ * t ^ d := by
      rw [← Real.rpow_add ht, show θ₀ + d = θ₁ by simp [d]]
    calc KFunctional ι₀ ι₁ t (c₀ + c₁)
        ≤ Ck * (KFunctional ι₀ ι₁ t c₀ + KFunctional ι₀ ι₁ t c₁) :=
          kFunctional_add_le ι₀ ι₁ t ht.le c₀ c₁
      _ ≤ Ck * (Cm * t ^ θ₀ * ‖y₀‖ + Cm * t ^ θ₁ * ‖y₁‖) := by
          gcongr
          · exact h0.trans (by gcongr)
          · exact h1.trans (by gcongr)
      _ = Ck * Cm * t ^ θ₀ * (‖y₀‖ + t ^ d * ‖y₁‖) := by rw [hsplit]; ring
  -- hence `t^{-θ} K(t, a; Ā) ≤ C s^{-η} K(s, a; X̄)` with `s = t^{θ₁-θ₀}`
  have hpt (t : ℝ) (ht : 0 < t) : ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (b₀ + b₁)) ≤
      ENNReal.ofReal (Ck * Cm) *
        ENNReal.ofReal ((t ^ d) ^ (-η) * KFunctional κ₀ κ₁ (t ^ d) a) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : t ^ (-θ) * t ^ θ₀ = (t ^ d) ^ (-η) := by
      rw [← Real.rpow_add ht, ← Real.rpow_mul ht.le, neg_add_eq_sub, hθd]
      ring_nf
    calc t ^ (-θ) * KFunctional ι₀ ι₁ t (b₀ + b₁)
        ≤ t ^ (-θ) * (Ck * Cm * t ^ θ₀ * KFunctional κ₀ κ₁ (t ^ d) a) :=
          mul_le_mul_of_nonneg_left (hK t ht) (Real.rpow_nonneg ht.le _)
      _ = Ck * Cm * ((t ^ (-θ) * t ^ θ₀) * KFunctional κ₀ κ₁ (t ^ d) a) := by ring
      _ = _ := by rw [hpow]
  -- B–L: "if we change the variable in the integral, writing `s = t^{θ₁-θ₀}`"
  unfold realInterpolationENorm
  split_ifs with htop
  · subst htop
    simp only [D, ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, mul_one]
    refine iSup_le fun t => (hpt t t.2).trans ?_
    rw [ENNReal.mul_iSup]
    exact le_iSup_of_le ⟨(t : ℝ) ^ d, Set.mem_Ioi.mpr (Real.rpow_pos_of_pos t.2 d)⟩ le_rfl
  · have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
    set G : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-η) * KFunctional κ₀ κ₁ s a)
    have hint : ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (b₀ + b₁)) ^ q.toReal *
            ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (Ck * Cm) ^ q.toReal * ENNReal.ofReal |d|⁻¹ *
          ∫⁻ s in Set.Ioi (0 : ℝ), G s ^ q.toReal * ENNReal.ofReal s⁻¹ := by
      calc ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (b₀ + b₁)) ^ q.toReal *
              ENNReal.ofReal t⁻¹
          ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Ck * Cm) ^ q.toReal *
              (G (t ^ d) ^ q.toReal * ENNReal.ofReal t⁻¹) := by
            refine MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
            rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hr.le]
            gcongr
            exact hpt t ht
        _ = _ := by
            rw [MeasureTheory.lintegral_const_mul' _ _
                (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top),
              lintegral_Ioi_comp_rpow_mul_inv_of_ne_zero hd (fun s => G s ^ q.toReal), mul_assoc]
    calc (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-θ) * KFunctional ι₀ ι₁ t (b₀ + b₁)) ^ q.toReal *
            ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal
        ≤ (ENNReal.ofReal (Ck * Cm) ^ q.toReal * ENNReal.ofReal |d|⁻¹ *
            ∫⁻ s in Set.Ioi (0 : ℝ), G s ^ q.toReal * ENNReal.ofReal s⁻¹) ^ q⁻¹.toReal :=
          ENNReal.rpow_le_rpow hint ENNReal.toReal_nonneg
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
            ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
            ENNReal.toReal_inv, mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]
          simp only [D, ENNReal.toReal_inv, G]

/-- Lift `u ∈ A₀ ∩ A₁` to `w ∈ X₀ ∩ X₁` with the same ambient image, using the `𝒥(θᵢ)`
conditions: `‖w₀‖ ≤ C t^{-θ₀} J(t, u)`, `‖w₁‖ ≤ C t^{-θ₁} J(t, u)`. -/
private theorem exists_meet_lift_of_isOfClassJ {θ₀ θ₁ : ℝ} (hJ₀ : IsOfClassJ ι₀ ι₁ θ₀ κ₀)
    (hJ₁ : IsOfClassJ ι₀ ι₁ θ₁ κ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : meet ι₀ ι₁, ∃ w : meet κ₀ κ₁,
      sumToAmbient κ₀ κ₁ (meetToSum κ₀ κ₁ w) = sumToAmbient ι₀ ι₁ (meetToSum ι₀ ι₁ u) ∧
        ∀ t : ℝ, 0 < t → ‖(w : X₀ × X₁).1‖ ≤ C * t ^ (-θ₀) * JFunctional ι₀ ι₁ t u ∧
          ‖(w : X₀ × X₁).2‖ ≤ C * t ^ (-θ₁) * JFunctional ι₀ ι₁ t u := by
  obtain ⟨C₀, hC₀⟩ := hJ₀
  obtain ⟨C₁, hC₁⟩ := hJ₁
  refine ⟨max (max C₀ C₁) 0, le_max_right _ _, fun u => ?_⟩
  obtain ⟨x₀, hx₀, hb₀⟩ := hC₀ u
  obtain ⟨x₁, hx₁, hb₁⟩ := hC₁ u
  refine ⟨⟨(x₀, x₁), (mem_meet_iff κ₀ κ₁ x₀ x₁).mpr (hx₀.trans hx₁.symm)⟩, ?_, fun t ht => ?_⟩
  · rw [meetToSum_apply, sumToAmbient_inl₀, hx₀]
  have hJ := jFunctional_nonneg ι₀ ι₁ t u
  exact ⟨(hb₀ t ht).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (Real.rpow_nonneg ht.le _)) hJ),
    (hb₁ t ht).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) (Real.rpow_nonneg ht.le _)) hJ)⟩

/-- On the meet, `K(s, w) ≤ ‖w₀‖` and `K(s, w) ≤ s ‖w₁‖`. -/
private theorem kFunctional_meetToSum_le_fst_snd {s : ℝ} (hs : 0 ≤ s) (w : meet κ₀ κ₁) :
    KFunctional κ₀ κ₁ s (meetToSum κ₀ κ₁ w) ≤ ‖(w : X₀ × X₁).1‖ ∧
      KFunctional κ₀ κ₁ s (meetToSum κ₀ κ₁ w) ≤ s * ‖(w : X₀ × X₁).2‖ := by
  obtain ⟨⟨x₀, x₁⟩, hw⟩ := w
  have hι := (mem_meet_iff κ₀ κ₁ x₀ x₁).mp hw
  change KFunctional κ₀ κ₁ s (Submodule.Quotient.mk (x₀, 0)) ≤ ‖x₀‖ ∧
    KFunctional κ₀ κ₁ s (Submodule.Quotient.mk (x₀, 0)) ≤ s * ‖x₁‖
  have hbdd := kFunctional_set_boundedBelow κ₀ κ₁ s hs (Submodule.Quotient.mk (x₀, 0))
  refine ⟨csInf_le hbdd ⟨x₀, 0, rfl, by simp⟩, csInf_le hbdd ⟨0, x₁, ?_, by simp⟩⟩
  refine (Submodule.Quotient.eq _).mpr ?_
  simp [plus, hι]

/-- `r^e ≤ 2^{|e|}` for `1 ≤ r ≤ 2`. -/
private theorem rpow_le_two_rpow_abs {r e : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) : r ^ e ≤ 2 ^ |e| := by
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he]
    exact Real.rpow_le_rpow (by linarith) hr2 he
  · exact (Real.rpow_le_one_of_one_le_of_nonpos hr1 he).trans (Real.one_le_rpow one_le_two
      (abs_nonneg e))

omit [T2Space 𝒜] in
/-- B–L Lemma 3.1.3 for a power of `t`: on `2^μ ≤ t < 2^{μ+1}`,
`t^e K(t^d, a) ≤ 2^{|e|+|d|} (2^μ)^e K((2^μ)^d, a)`. -/
private theorem rpow_mul_kFunctional_le_of_mem_Ico (e d : ℝ) (μ : ℤ) {t : ℝ}
    (ht : t ∈ Set.Ico ((2 : ℝ) ^ μ) (2 ^ (μ + 1))) (a : sum κ₀ κ₁) :
    t ^ e * KFunctional κ₀ κ₁ (t ^ d) a ≤
      2 ^ (|e| + |d|) * (((2 : ℝ) ^ μ) ^ e * KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) a) := by
  have h2μ : (0 : ℝ) < 2 ^ μ := zpow_pos two_pos μ
  have ht0 : 0 < t := h2μ.trans_le ht.1
  set r := t / 2 ^ μ
  have hr1 : 1 ≤ r := (one_le_div h2μ).mpr ht.1
  have hr2 : r ≤ 2 := by
    rw [div_le_iff₀ h2μ]
    have := ht.2.le
    rwa [zpow_add_one₀ two_ne_zero, mul_comm] at this
  have hr0 : 0 < r := by positivity
  have htr : t = 2 ^ μ * r := by rw [mul_div_cancel₀ _ h2μ.ne']
  -- `K(t^d) ≤ 2^{|d|} K((2^μ)^d)` (B–L Lemma 3.1.1)
  have hK : KFunctional κ₀ κ₁ (t ^ d) a ≤
      2 ^ |d| * KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) a := by
    have h := min_one_div_mul_kFunctional_le κ₀ κ₁ (Real.rpow_pos_of_pos ht0 d)
      (Real.rpow_nonneg h2μ.le d) a
    have hq : ((2 : ℝ) ^ μ) ^ d / t ^ d = (r ^ d)⁻¹ := by
      rw [htr, Real.mul_rpow h2μ.le hr0.le]
      field_simp
    have hmin : (2 : ℝ) ^ (-|d|) ≤ min 1 (((2 : ℝ) ^ μ) ^ d / t ^ d) := by
      refine le_min (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (neg_nonpos.mpr
        (abs_nonneg d))) ?_
      rw [hq, Real.rpow_neg zero_le_two]
      exact inv_anti₀ (Real.rpow_pos_of_pos hr0 d) (rpow_le_two_rpow_abs hr1 hr2)
    have hK0 := kFunctional_nonneg κ₀ κ₁ _ (Real.rpow_nonneg ht0.le d) a
    have h2d : (2 : ℝ) ^ |d| * 2 ^ (-|d|) = 1 := by
      rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
    calc KFunctional κ₀ κ₁ (t ^ d) a
        = 2 ^ |d| * (2 ^ (-|d|) * KFunctional κ₀ κ₁ (t ^ d) a) := by
          rw [← mul_assoc, h2d, one_mul]
      _ ≤ 2 ^ |d| * (min 1 (((2 : ℝ) ^ μ) ^ d / t ^ d) * KFunctional κ₀ κ₁ (t ^ d) a) := by
          gcongr
      _ ≤ _ := by gcongr
  calc t ^ e * KFunctional κ₀ κ₁ (t ^ d) a
      = ((2 : ℝ) ^ μ) ^ e * r ^ e * KFunctional κ₀ κ₁ (t ^ d) a := by
        rw [htr, Real.mul_rpow h2μ.le hr0.le]
    _ ≤ ((2 : ℝ) ^ μ) ^ e * 2 ^ |e| *
          (2 ^ |d| * KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) a) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_two_rpow_abs hr1 hr2)
          (Real.rpow_nonneg h2μ.le _)) hK
          (kFunctional_nonneg κ₀ κ₁ _ (Real.rpow_nonneg ht0.le d) a) (by positivity)
    _ = _ := by rw [Real.rpow_add two_pos]; ring

/-- If `e₀ ≤ -δ` and `δ ≤ e₁` (or the reverse), `min((2^ν)^{e₀}, (2^ν)^{e₁}) ≤ (2^{-δ})^{|ν|}`. -/
private theorem min_zpow_rpow_le_pow_natAbs {e₀ e₁ δ : ℝ}
    (h : (e₀ ≤ -δ ∧ δ ≤ e₁) ∨ (e₁ ≤ -δ ∧ δ ≤ e₀)) (ν : ℤ) :
    min (((2 : ℝ) ^ ν) ^ e₀) (((2 : ℝ) ^ ν) ^ e₁) ≤ ((2 : ℝ) ^ (-δ)) ^ ν.natAbs := by
  -- `(2^ν)^e = 2^{νe}`; pick the exponent of the right sign
  have hpow (e : ℝ) : ((2 : ℝ) ^ ν) ^ e = (2 : ℝ) ^ ((ν : ℝ) * e) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul zero_le_two]
  have hgoal : ((2 : ℝ) ^ (-δ)) ^ ν.natAbs = (2 : ℝ) ^ ((ν.natAbs : ℝ) * (-δ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm]
  rw [hpow, hpow, hgoal]
  have hle (e : ℝ) (hν : (ν : ℝ) * e ≤ (ν.natAbs : ℝ) * (-δ)) :
      (2 : ℝ) ^ ((ν : ℝ) * e) ≤ (2 : ℝ) ^ ((ν.natAbs : ℝ) * (-δ)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two hν
  rcases le_total 0 ν with hν | hν
  · have habs : (ν.natAbs : ℝ) = ν := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (Int.cast_nonneg hν)]
    have hν' : (0 : ℝ) ≤ ν := by exact_mod_cast hν
    rcases h with ⟨h0, -⟩ | ⟨h1, -⟩
    · exact (min_le_left _ _).trans (hle e₀ (by rw [habs]; nlinarith))
    · exact (min_le_right _ _).trans (hle e₁ (by rw [habs]; nlinarith))
  · have habs : (ν.natAbs : ℝ) = -ν := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonpos (Int.cast_nonpos.mpr hν)]
    have hν' : (ν : ℝ) ≤ 0 := by exact_mod_cast hν
    rcases h with ⟨-, h1⟩ | ⟨-, h0⟩
    · exact (min_le_right _ _).trans (hle e₁ (by rw [habs]; nlinarith))
    · exact (min_le_left _ _).trans (hle e₀ (by rw [habs]; nlinarith))

/-- `(2^m)^e = 2^{m e}`. -/
private theorem zpow_rpow_eq_two_rpow (m : ℤ) (e : ℝ) :
    ((2 : ℝ) ^ m) ^ e = (2 : ℝ) ^ ((m : ℝ) * e) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul zero_le_two]

/-- Reiteration, `Ā_{θ,q} ⊂ X̄_{η,q}` (B–L Theorem 3.5.3, second half; 3.11.5): if `Xᵢ` is complete
and of class `𝒥(θᵢ; Ā)` with `θᵢ ∈ [0, 1]`, `θ₀ ≠ θ₁`, `0 < η < 1`, and `θ = (1 - η) θ₀ + η θ₁`,
then every `b ∈ A₀ + A₁` of finite `(θ,q)`-quasinorm lies in `X₀ + X₁` (as the element `a` with the
same image in the ambient space) with `‖a‖_{X̄,η,q} ≤ C ‖b‖_{Ā,θ,q}`. -/
theorem exists_realInterpolationENorm_le_of_isOfClassJ [CompleteSpace A₀] [CompleteSpace A₁]
    [CompleteSpace X₀] [CompleteSpace X₁] {θ₀ θ₁ η θ : ℝ} (hθ₀ : θ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hθ₁ : θ₁ ∈ Set.Icc (0 : ℝ) 1) (hne : θ₀ ≠ θ₁) (hη0 : 0 < η) (hη1 : η < 1)
    (hθ : θ = (1 - η) * θ₀ + η * θ₁) {q : ℝ≥0∞} (hq : 0 < q)
    (hJ₀ : IsOfClassJ ι₀ ι₁ θ₀ κ₀) (hJ₁ : IsOfClassJ ι₀ ι₁ θ₁ κ₁) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ b : sum ι₀ ι₁, realInterpolationENorm ι₀ ι₁ θ q b ≠ ⊤ →
      ∃ a : sum κ₀ κ₁, sumToAmbient κ₀ κ₁ a = sumToAmbient ι₀ ι₁ b ∧
        realInterpolationENorm κ₀ κ₁ η q a ≤ C * realInterpolationENorm ι₀ ι₁ θ q b := by
  set d := θ₁ - θ₀
  have hd : d ≠ 0 := sub_ne_zero.mpr hne.symm
  have he₀ : θ - θ₀ = η * d := by rw [hθ]; ring
  have he₁ : θ - θ₁ = -((1 - η) * d) := by rw [hθ]; ring
  have hθ01 : 0 < θ ∧ θ < 1 := by
    rcases hd.lt_or_gt with h | h
    · have h1 := mul_neg_of_pos_of_neg hη0 h
      have h2 := mul_neg_of_pos_of_neg (sub_pos.mpr hη1) h
      constructor <;> linarith [hθ₀.1, hθ₀.2, hθ₁.1, hθ₁.2]
    · have h1 := mul_pos hη0 h
      have h2 := mul_pos (sub_pos.mpr hη1) h
      constructor <;> linarith [hθ₀.1, hθ₀.2, hθ₁.1, hθ₁.2]
  obtain ⟨hθ0, hθ1⟩ := hθ01
  -- the exponents `θ₀ - θ = -η d` and `θ₁ - θ = (1 - η) d` have opposite signs
  set δ := min (η * |d|) ((1 - η) * |d|)
  have hδ : 0 < δ := lt_min (mul_pos hη0 (abs_pos.mpr hd))
    (mul_pos (sub_pos.mpr hη1) (abs_pos.mpr hd))
  have hsign : (θ₀ - θ ≤ -δ ∧ δ ≤ θ₁ - θ) ∨ (θ₁ - θ ≤ -δ ∧ δ ≤ θ₀ - θ) := by
    have h1 : δ ≤ η * |d| := min_le_left _ _
    have h2 : δ ≤ (1 - η) * |d| := min_le_right _ _
    rcases hd.lt_or_gt with h | h
    · right
      rw [abs_of_neg h] at h1 h2
      constructor <;> linarith
    · left
      rw [abs_of_pos h] at h1 h2
      constructor <;> linarith
  have hsign' : (θ - θ₀ ≤ -δ ∧ δ ≤ θ - θ₁) ∨ (θ - θ₁ ≤ -δ ∧ δ ≤ θ - θ₀) := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁))
  have hCk : 0 < Ck :=
    QuasinormedAddCommGroup.quasiTriangleConst_pos.trans_le (le_max_left _ _)
  set CkX := max (QuasinormedAddCommGroup.quasiTriangleConst (E := X₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := X₁))
  have hCkX1 : 1 ≤ CkX :=
    QuasinormedAddCommGroup.one_le_quasiTriangleConst.trans (le_max_left _ _)
  obtain ⟨Cw, hCw0, hlift⟩ := exists_meet_lift_of_isOfClassJ ι₀ ι₁ κ₀ κ₁ hJ₀ hJ₁
  -- B–L: "Lemma 3.10.2 ... for any `ρ > 0`, small enough": the Aoki–Rolewicz exponent `ρ ≤ q`
  -- for the quasi-norms `K(s, ·; X̄)`
  set C' := max CkX (2 ^ q⁻¹.toReal)
  have hC'1 : 1 ≤ C' := hCkX1.trans (le_max_left _ _)
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
  -- the kernel `φ(k) = min(2^{k(θ₀-θ)}, 2^{k(θ₁-θ)})` and `Φ = φ^ρ`
  set φ : ℤ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (min (((2 : ℝ) ^ k) ^ (θ₀ - θ)) (((2 : ℝ) ^ k) ^ (θ₁ - θ)))
  set Φ : ℤ → ℝ≥0∞ := fun k => φ k ^ ρ
  set r := ((2 : ℝ) ^ (-δ)) ^ ρ
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)) hρ
  have hΦle (k : ℤ) : Φ k ≤ ENNReal.ofReal (r ^ k.natAbs) := by
    calc Φ k ≤ ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ k.natAbs) ^ ρ :=
          ENNReal.rpow_le_rpow
            (ENNReal.ofReal_le_ofReal (min_zpow_rpow_le_pow_natAbs hsign k)) hρ.le
      _ = ENNReal.ofReal (r ^ k.natAbs) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hρ.le,
            ← Real.rpow_pow_comm (x := (2 : ℝ) ^ (-δ)) (by positivity)]
  have hΦtop : ∑' k, Φ k ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hΦle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => pow_nonneg hr0 _)
      (summable_pow_natAbs hr0 hr1)]
    exact ENNReal.ofReal_ne_top
  set DX := ENNReal.ofReal (CkX * 4 ^ ρ⁻¹)
  set c3 : ℝ := 2 ^ (|θ₀ - θ| + |d|)
  set L := ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal
  have hLtop : L ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hL0 : L ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two))
    ENNReal.ofReal_ne_top).ne'
  set E := (ENNReal.ofReal |d| * ENNReal.ofReal (Real.log 2)) ^ q⁻¹.toReal *
    ENNReal.ofReal c3 * DX * ENNReal.ofReal Cw * (∑' k, Φ k) ^ ρ⁻¹
  set F := ENNReal.ofReal (6 * Ck) * ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹
  have hEtop : E ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (inv_pos.mpr hρ).le hΦtop)
  have hFtop : F ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) (ENNReal.inv_ne_top.mpr hL0)
  refine ⟨E * F, ENNReal.mul_ne_top hEtop hFtop, fun b hb => ?_⟩
  -- B–L: "choose a representation `a = ∑ᵥ uᵥ`" (here of `b`, by the equivalence theorem)
  obtain ⟨u, hu, hJu⟩ :=
    exists_hasSum_jFunctional_le_kFunctional ι₀ ι₁ hθ0 hθ1 hq hb one_pos
  have hJu' (ν : ℤ) :
      JFunctional ι₀ ι₁ (2 ^ ν) (u ν) ≤ 6 * Ck * KFunctional ι₀ ι₁ (2 ^ ν) b := by
    have h := hJu ν
    rwa [show (3 : ℝ) * (1 + 1) = 6 by norm_num] at h
  obtain ⟨M, hM⟩ := exists_kFunctional_le_mul_rpow ι₀ ι₁ θ hq hb
  have hM0 : 0 ≤ M := by
    simpa using (kFunctional_nonneg ι₀ ι₁ 1 zero_le_one b).trans (hM 1 one_pos)
  -- lift each `uᵥ` to `wᵥ ∈ X₀ ∩ X₁` (classes `𝒥(θᵢ)`)
  choose w hwamb hwbd using fun ν => hlift (u ν)
  set x : ℤ → sum κ₀ κ₁ := fun ν => meetToSum κ₀ κ₁ (w ν)
  set W : ℤ → ℝ≥0∞ := fun ν =>
    ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν))
  -- B–L: `K(s, uᵥ; X̄) ≤ C J(2^ν, uᵥ; Ā) min(2^{-νθ₀}, s 2^{-νθ₁})`
  have hKw (ν : ℤ) {s : ℝ} (hs : 0 ≤ s) : KFunctional κ₀ κ₁ s (x ν) ≤
      Cw * JFunctional ι₀ ι₁ (2 ^ ν) (u ν) *
        min (((2 : ℝ) ^ ν) ^ (-θ₀)) (s * ((2 : ℝ) ^ ν) ^ (-θ₁)) := by
    have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
    obtain ⟨h0, h1⟩ := kFunctional_meetToSum_le_fst_snd κ₀ κ₁ hs (w ν)
    obtain ⟨hw0, hw1⟩ := hwbd ν (2 ^ ν) h2ν
    have hJ := jFunctional_nonneg ι₀ ι₁ (2 ^ ν) (u ν)
    rw [mul_min_of_nonneg _ _ (mul_nonneg hCw0 hJ)]
    refine le_min (h0.trans (hw0.trans_eq (by ring))) (h1.trans ?_)
    calc s * ‖(w ν : X₀ × X₁).2‖
        ≤ s * (Cw * ((2 : ℝ) ^ ν) ^ (-θ₁) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)) :=
          mul_le_mul_of_nonneg_left hw1 hs
      _ = _ := by ring
  -- `∑ᵥ wᵥ` converges in the complete space `X₀ + X₁`: `‖wᵥ‖` decays geometrically
  set C1 := Cw * (6 * Ck * M)
  have hC1 : 0 ≤ C1 := by positivity
  have hxnorm (ν : ℤ) : ‖x ν‖ ≤ C1 * ((2 : ℝ) ^ (-δ)) ^ ν.natAbs := by
    have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
    have hk := min_mul_norm_le_kFunctional κ₀ κ₁ 1 zero_le_one (x ν)
    rw [min_self, one_mul] at hk
    have hJ2 : JFunctional ι₀ ι₁ (2 ^ ν) (u ν) ≤ 6 * Ck * M * ((2 : ℝ) ^ ν) ^ θ :=
      (hJu' ν).trans (by
        rw [mul_assoc (6 * Ck)]
        exact mul_le_mul_of_nonneg_left (hM _ h2ν) (by positivity))
    have e0 : ((2 : ℝ) ^ ν) ^ (θ - θ₀) = ((2 : ℝ) ^ ν) ^ θ * ((2 : ℝ) ^ ν) ^ (-θ₀) := by
      rw [sub_eq_add_neg, Real.rpow_add h2ν]
    have e1 : ((2 : ℝ) ^ ν) ^ (θ - θ₁) = ((2 : ℝ) ^ ν) ^ θ * ((2 : ℝ) ^ ν) ^ (-θ₁) := by
      rw [sub_eq_add_neg, Real.rpow_add h2ν]
    have hmin0 : 0 ≤ min (((2 : ℝ) ^ ν) ^ (-θ₀)) (((2 : ℝ) ^ ν) ^ (-θ₁)) :=
      le_min (Real.rpow_nonneg h2ν.le _) (Real.rpow_nonneg h2ν.le _)
    calc ‖x ν‖ ≤ KFunctional κ₀ κ₁ 1 (x ν) := hk
      _ ≤ Cw * JFunctional ι₀ ι₁ (2 ^ ν) (u ν) *
            min (((2 : ℝ) ^ ν) ^ (-θ₀)) (1 * ((2 : ℝ) ^ ν) ^ (-θ₁)) := hKw ν zero_le_one
      _ ≤ Cw * (6 * Ck * M * ((2 : ℝ) ^ ν) ^ θ) *
            min (((2 : ℝ) ^ ν) ^ (-θ₀)) (((2 : ℝ) ^ ν) ^ (-θ₁)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ2 hCw0) hmin0
      _ = C1 * min (((2 : ℝ) ^ ν) ^ (θ - θ₀)) (((2 : ℝ) ^ ν) ^ (θ - θ₁)) := by
          rw [e0, e1, ← mul_min_of_nonneg _ _ (Real.rpow_nonneg h2ν.le _)]
          ring
      _ ≤ C1 * ((2 : ℝ) ^ (-δ)) ^ ν.natAbs :=
          mul_le_mul_of_nonneg_left (min_zpow_rpow_le_pow_natAbs hsign' ν) hC1
  set ρX := QuasinormedAddCommGroup.aokiRolewiczExponent (sum κ₀ κ₁)
  have hρX : 0 < ρX := QuasinormedAddCommGroup.aokiRolewiczExponent_pos _
  set rX := ((2 : ℝ) ^ (-δ)) ^ ρX
  have hrX0 : 0 ≤ rX := by positivity
  have hrX1 : rX < 1 := Real.rpow_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)) hρX
  have hsumm : Summable fun ν => ‖x ν‖ ^ ρX := by
    refine Summable.of_nonneg_of_le
      (fun _ => Real.rpow_nonneg (QuasinormedAddCommGroup.norm_nonneg _) _) (fun ν => ?_)
      ((summable_pow_natAbs hrX0 hrX1).mul_right (C1 ^ ρX))
    calc ‖x ν‖ ^ ρX ≤ (C1 * ((2 : ℝ) ^ (-δ)) ^ ν.natAbs) ^ ρX :=
          Real.rpow_le_rpow (QuasinormedAddCommGroup.norm_nonneg _) (hxnorm ν) hρX.le
      _ = rX ^ ν.natAbs * C1 ^ ρX := by
          rw [Real.mul_rpow hC1 (by positivity),
            ← Real.rpow_pow_comm (x := (2 : ℝ) ^ (-δ)) (by positivity), mul_comm]
  have ha := (QuasinormedAddCommGroup.summable_of_summable_norm_rpow hsumm).hasSum
  set a := ∑' ν, x ν
  refine ⟨a, ?_, ?_⟩
  · -- same image in the ambient space
    have h1 := ha.map (sumToAmbient κ₀ κ₁) (sumToAmbient κ₀ κ₁).continuous
    have h2 := hu.map (sumToAmbient ι₀ ι₁) (sumToAmbient ι₀ ι₁).continuous
    have heq : (sumToAmbient κ₀ κ₁ ∘ x) =
        (sumToAmbient ι₀ ι₁ ∘ fun ν => meetToSum ι₀ ι₁ (u ν)) := funext fun ν => hwamb ν
    rw [heq] at h1
    exact h1.unique h2
  -- B–L: `2^{μθ₀} K(2^{μ(θ₁-θ₀)}, uᵥ; X̄) ≤ C 2^{(μ-ν)θ₀} min(1, 2^{(μ-ν)(θ₁-θ₀)}) J(2^ν, uᵥ; Ā)`
  -- and Lemma 3.10.2: `2^{μ(θ₀-θ)} K(2^{μ(θ₁-θ₀)}, a; X̄) ≤ C (∑ᵥ (φ(μ-ν) Wᵥ)^ρ)^{1/ρ}`
  set γ : ℤ → ℝ≥0∞ := fun μ =>
    ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (θ₀ - θ) * KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) a)
  have hγ (μ : ℤ) : γ μ ≤ DX * ENNReal.ofReal Cw * (∑' ν, Φ (μ - ν) * W ν ^ ρ) ^ ρ⁻¹ := by
    have h2μ : (0 : ℝ) < 2 ^ μ := zpow_pos two_pos μ
    have hs : 0 < ((2 : ℝ) ^ μ) ^ d := Real.rpow_pos_of_pos h2μ d
    have hc : 0 ≤ ((2 : ℝ) ^ μ) ^ (θ₀ - θ) := Real.rpow_nonneg h2μ.le _
    have h1 := ofReal_kFunctional_le_tsum_rpow κ₀ κ₁ (C' := C') (le_max_left CkX _) hs ha
    have hterm (ν : ℤ) : ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (θ₀ - θ)) *
        ENNReal.ofReal (KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) (x ν)) ≤
          ENNReal.ofReal Cw * (φ (μ - ν) * W ν) := by
      have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
      have hJ := jFunctional_nonneg ι₀ ι₁ (2 ^ ν) (u ν)
      have hm0 : 0 ≤ min (((2 : ℝ) ^ (μ - ν)) ^ (θ₀ - θ)) (((2 : ℝ) ^ (μ - ν)) ^ (θ₁ - θ)) :=
        le_min (Real.rpow_nonneg (zpow_pos two_pos _).le _)
          (Real.rpow_nonneg (zpow_pos two_pos _).le _)
      rw [← ENNReal.ofReal_mul hc]
      change _ ≤ ENNReal.ofReal Cw * (ENNReal.ofReal _ * ENNReal.ofReal _)
      rw [← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_mul hCw0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hK := hKw ν hs.le
      have i0 : ((2 : ℝ) ^ μ) ^ (θ₀ - θ) * ((2 : ℝ) ^ ν) ^ (-θ₀) =
          ((2 : ℝ) ^ ν) ^ (-θ) * ((2 : ℝ) ^ (μ - ν)) ^ (θ₀ - θ) := by
        simp only [zpow_rpow_eq_two_rpow]
        rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
      have i1 : ((2 : ℝ) ^ μ) ^ (θ₀ - θ) * (((2 : ℝ) ^ μ) ^ d * ((2 : ℝ) ^ ν) ^ (-θ₁)) =
          ((2 : ℝ) ^ ν) ^ (-θ) * ((2 : ℝ) ^ (μ - ν)) ^ (θ₁ - θ) := by
        simp only [zpow_rpow_eq_two_rpow]
        rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        simp only [d]
        ring
      calc ((2 : ℝ) ^ μ) ^ (θ₀ - θ) * KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) (x ν)
          ≤ ((2 : ℝ) ^ μ) ^ (θ₀ - θ) * (Cw * JFunctional ι₀ ι₁ (2 ^ ν) (u ν) *
              min (((2 : ℝ) ^ ν) ^ (-θ₀)) (((2 : ℝ) ^ μ) ^ d * ((2 : ℝ) ^ ν) ^ (-θ₁))) :=
            mul_le_mul_of_nonneg_left hK hc
        _ = Cw * JFunctional ι₀ ι₁ (2 ^ ν) (u ν) *
              min (((2 : ℝ) ^ μ) ^ (θ₀ - θ) * ((2 : ℝ) ^ ν) ^ (-θ₀))
                (((2 : ℝ) ^ μ) ^ (θ₀ - θ) * (((2 : ℝ) ^ μ) ^ d * ((2 : ℝ) ^ ν) ^ (-θ₁))) := by
            rw [mul_left_comm, mul_min_of_nonneg _ _ hc]
        _ = Cw * (min (((2 : ℝ) ^ (μ - ν)) ^ (θ₀ - θ)) (((2 : ℝ) ^ (μ - ν)) ^ (θ₁ - θ)) *
              (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν))) := by
            rw [i0, i1, ← mul_min_of_nonneg _ _ (Real.rpow_nonneg h2ν.le _)]
            ring
    calc γ μ = ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (θ₀ - θ)) *
          ENNReal.ofReal (KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) a) := ENNReal.ofReal_mul hc
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (θ₀ - θ)) * (DX * (∑' ν,
            ENNReal.ofReal (KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) (x ν)) ^ ρ) ^ ρ⁻¹) :=
          mul_le_mul_right h1 _
      _ = DX * (∑' ν, (ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (θ₀ - θ)) *
            ENNReal.ofReal (KFunctional κ₀ κ₁ (((2 : ℝ) ^ μ) ^ d) (x ν))) ^ ρ) ^ ρ⁻¹ := by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ hρ.le]
          rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (inv_pos.mpr hρ).le,
            ← ENNReal.rpow_mul, mul_inv_cancel₀ hρ.ne', ENNReal.rpow_one]
          ring
      _ ≤ DX * (∑' ν, (ENNReal.ofReal Cw * (φ (μ - ν) * W ν)) ^ ρ) ^ ρ⁻¹ :=
          mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun ν =>
            ENNReal.rpow_le_rpow (hterm ν) hρ.le) (inv_pos.mpr hρ).le) _
      _ = DX * ENNReal.ofReal Cw * (∑' ν, Φ (μ - ν) * W ν ^ ρ) ^ ρ⁻¹ := by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ hρ.le]
          rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (inv_pos.mpr hρ).le,
            ← ENNReal.rpow_mul, mul_inv_cancel₀ hρ.ne', ENNReal.rpow_one]
          ring
  have hreindex (V : ℤ → ℝ≥0∞) (μ : ℤ) :
      ∑' ν, Φ (μ - ν) * V ν = ∑' k, Φ k * V (μ - k) := by
    refine ((Equiv.subLeft μ).tsum_eq (fun ν => Φ (μ - ν) * V ν)).symm.trans ?_
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
  -- B–L: "we change variables and then apply Lemma 3.1.3": on `2^μ ≤ t < 2^{μ+1}`,
  -- `(t^d)^{-η} K(t^d, a) ≤ c₃ γ_μ`
  have hdy (μ : ℤ) {t : ℝ} (ht : t ∈ Set.Ico ((2 : ℝ) ^ μ) (2 ^ (μ + 1))) :
      ENNReal.ofReal ((t ^ d) ^ (-η) * KFunctional κ₀ κ₁ (t ^ d) a) ≤
        ENNReal.ofReal c3 * γ μ := by
    have ht0 : 0 < t := (zpow_pos two_pos μ).trans_le ht.1
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : (t ^ d) ^ (-η) = t ^ (θ₀ - θ) := by
      rw [← Real.rpow_mul ht0.le]
      congr 1
      linear_combination he₀
    rw [hexp]
    exact rpow_mul_kFunctional_le_of_mem_Ico κ₀ κ₁ (θ₀ - θ) d μ ht a
  -- `‖a‖_{X̄,η,q} ≤ E ‖(2^{-νθ} J(2^ν, uᵥ; Ā))‖_{ℓ^q}` (B–L: "by Minkowski's inequality")
  have hmain : realInterpolationENorm κ₀ κ₁ η q a ≤ E * jSequenceENorm ι₀ ι₁ θ q u := by
    unfold realInterpolationENorm jSequenceENorm
    split_ifs with htop
    · subst htop
      rw [eLpNorm_exponent_top Measurable.of_discrete.aestronglyMeasurable, eLpNormEssSup,
        essSup_count_eq_ciSup (OrderTop.bddAbove _)]
      simp only [enorm_eq_self, E, ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero,
        one_mul]
      refine iSup_le fun s => ?_
      have hs : (0 : ℝ) < s := s.2
      obtain ⟨μ, hμ⟩ := exists_mem_Ico_zpow (Real.rpow_pos_of_pos hs d⁻¹) one_lt_two
      have hst : ((s : ℝ) ^ d⁻¹) ^ d = s := by
        rw [← Real.rpow_mul hs.le, inv_mul_cancel₀ hd, Real.rpow_one]
      set S := ⨆ ν, W ν
      calc ENNReal.ofReal ((s : ℝ) ^ (-η) * KFunctional κ₀ κ₁ s a)
          = ENNReal.ofReal ((((s : ℝ) ^ d⁻¹) ^ d) ^ (-η) *
              KFunctional κ₀ κ₁ (((s : ℝ) ^ d⁻¹) ^ d) a) := by rw [hst]
        _ ≤ ENNReal.ofReal c3 * γ μ := hdy μ hμ
        _ ≤ ENNReal.ofReal c3 *
              (DX * ENNReal.ofReal Cw * (∑' ν, Φ (μ - ν) * W ν ^ ρ) ^ ρ⁻¹) :=
            mul_le_mul_right (hγ μ) _
        _ ≤ ENNReal.ofReal c3 * (DX * ENNReal.ofReal Cw * (∑' ν, Φ (μ - ν) * S ^ ρ) ^ ρ⁻¹) :=
            mul_le_mul_right (mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum
              fun ν => mul_le_mul_right (ENNReal.rpow_le_rpow (le_iSup W ν) hρ.le) _)
              (inv_pos.mpr hρ).le) _) _
        _ = ENNReal.ofReal c3 * DX * ENNReal.ofReal Cw * (∑' k, Φ k) ^ ρ⁻¹ * S := by
            have hshift : ∑' ν, Φ (μ - ν) = ∑' k, Φ k := by
              simpa using hreindex (fun _ => 1) μ
            rw [ENNReal.tsum_mul_right, hshift,
              ENNReal.mul_rpow_of_nonneg _ _ (inv_pos.mpr hρ).le, ← ENNReal.rpow_mul,
              mul_inv_cancel₀ hρ.ne', ENNReal.rpow_one]
            ring
    · have hr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' htop
      have hp : 1 ≤ q.toReal / ρ := (one_le_div hρ).mpr (hρq htop)
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq.ne' htop
          Measurable.of_discrete.aestronglyMeasurable, lintegral_count]
      simp only [enorm_eq_self]
      rw [← ENNReal.rpow_le_rpow_iff hr]
      have e1 : q⁻¹.toReal * q.toReal = 1 := by
        rw [ENNReal.toReal_inv, inv_mul_cancel₀ hr.ne']
      have e2 : 1 / q.toReal * q.toReal = 1 := by rw [one_div, inv_mul_cancel₀ hr.ne']
      have hEr : (E * (∑' ν, W ν ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal =
          ENNReal.ofReal |d| * ENNReal.ofReal (Real.log 2) *
            (ENNReal.ofReal c3 * DX * ENNReal.ofReal Cw) ^ q.toReal *
              ((∑' k, Φ k) ^ (q.toReal / ρ) * ∑' ν, W ν ^ q.toReal) := by
        simp only [E, ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, e1, e2,
          ENNReal.rpow_one, inv_mul_eq_div]
        ring
      have hsub : ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (s ^ (-η) * KFunctional κ₀ κ₁ s a) ^ q.toReal * ENNReal.ofReal s⁻¹ =
          ENNReal.ofReal |d| * ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((t ^ d) ^ (-η) * KFunctional κ₀ κ₁ (t ^ d) a) ^ q.toReal *
              ENNReal.ofReal t⁻¹ := by
        rw [lintegral_Ioi_comp_rpow_mul_inv_of_ne_zero hd
            (fun s => ENNReal.ofReal (s ^ (-η) * KFunctional κ₀ κ₁ s a) ^ q.toReal),
          ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg d),
          mul_inv_cancel₀ (abs_ne_zero.mpr hd), ENNReal.ofReal_one, one_mul]
      rw [hEr, ← ENNReal.rpow_mul, e1, ENNReal.rpow_one, hsub, lintegral_Ioi_eq_tsum]
      calc ENNReal.ofReal |d| * ∑' μ : ℤ, ∫⁻ t in Set.Ico ((2 : ℝ) ^ μ) (2 ^ (μ + 1)),
            ENNReal.ofReal ((t ^ d) ^ (-η) * KFunctional κ₀ κ₁ (t ^ d) a) ^ q.toReal *
              ENNReal.ofReal t⁻¹
          ≤ ENNReal.ofReal |d| * ∑' μ,
              (ENNReal.ofReal c3 * γ μ) ^ q.toReal * ENNReal.ofReal (Real.log 2) := by
            refine mul_le_mul_right (ENNReal.tsum_le_tsum fun μ => ?_) _
            calc _ ≤ ∫⁻ t in Set.Ico ((2 : ℝ) ^ μ) (2 ^ (μ + 1)),
                    (ENNReal.ofReal c3 * γ μ) ^ q.toReal * ENNReal.ofReal t⁻¹ := by
                  refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
                  gcongr
                  exact hdy μ ht
              _ = _ := by
                  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le
                    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)),
                    lintegral_Ico_zpow_inv]
        _ ≤ ENNReal.ofReal |d| * ∑' μ, (ENNReal.ofReal c3 * (DX * ENNReal.ofReal Cw *
              (∑' k, Φ k * W (μ - k) ^ ρ) ^ ρ⁻¹)) ^ q.toReal *
                ENNReal.ofReal (Real.log 2) := by
            refine mul_le_mul_right (ENNReal.tsum_le_tsum fun μ => ?_) _
            rw [← hreindex (fun ν => W ν ^ ρ) μ]
            gcongr
            exact hγ μ
        _ = ENNReal.ofReal |d| * ENNReal.ofReal (Real.log 2) *
              (ENNReal.ofReal c3 * DX * ENNReal.ofReal Cw) ^ q.toReal *
                ∑' μ, (∑' k, Φ k * W (μ - k) ^ ρ) ^ (q.toReal / ρ) := by
            have hterm (μ : ℤ) : (ENNReal.ofReal c3 * (DX * ENNReal.ofReal Cw *
                (∑' k, Φ k * W (μ - k) ^ ρ) ^ ρ⁻¹)) ^ q.toReal * ENNReal.ofReal (Real.log 2) =
                  (ENNReal.ofReal (Real.log 2) *
                    (ENNReal.ofReal c3 * DX * ENNReal.ofReal Cw) ^ q.toReal) *
                    (∑' k, Φ k * W (μ - k) ^ ρ) ^ (q.toReal / ρ) := by
              simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
                inv_mul_eq_div]
              ring
            rw [tsum_congr hterm, ENNReal.tsum_mul_left]
            ring
        _ ≤ ENNReal.ofReal |d| * ENNReal.ofReal (Real.log 2) *
              (ENNReal.ofReal c3 * DX * ENNReal.ofReal Cw) ^ q.toReal *
                ((∑' k, Φ k) ^ (q.toReal / ρ) * ∑' ν, (W ν ^ ρ) ^ (q.toReal / ρ)) :=
            mul_le_mul_right (tsum_conv_rpow_le Φ (fun ν => W ν ^ ρ) hp) _
        _ = _ := by
            have e3 : ρ * (q.toReal / ρ) = q.toReal := by field_simp
            simp only [← ENNReal.rpow_mul, e3]
  -- and `‖(2^{-νθ} J(2^ν, uᵥ))‖_{ℓ^q} ≤ 6 C_k 2^θ (log 2)^{-1/q} ‖b‖_{Ā,θ,q}`
  have hseq : jSequenceENorm ι₀ ι₁ θ q u ≤ F * realInterpolationENorm ι₀ ι₁ θ q b := by
    set h : ℤ → ℝ := fun ν => ((2 : ℝ) ^ ν) ^ (-θ) * KFunctional ι₀ ι₁ (2 ^ ν) b
    have hh (ν : ℤ) : 0 ≤ h ν := mul_nonneg (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _)
      (kFunctional_nonneg ι₀ ι₁ _ (zpow_nonneg zero_le_two _) b)
    have hk : kSequenceENorm ι₀ ι₁ θ q b = eLpNorm h q Measure.count :=
      eLpNorm_congr_enorm_ae Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aestronglyMeasurable (Eventually.of_forall fun ν => by
          rw [enorm_eq_self, Real.enorm_of_nonneg (hh ν)])
    have h1 : jSequenceENorm ι₀ ι₁ θ q u ≤
        ENNReal.ofReal (6 * Ck) * kSequenceENorm ι₀ ι₁ θ q b := by
      calc jSequenceENorm ι₀ ι₁ θ q u ≤ eLpNorm ((6 * Ck) • h) q Measure.count := by
            refine eLpNorm_mono_enorm Measurable.of_discrete.aestronglyMeasurable fun ν => ?_
            rw [enorm_eq_self, Pi.smul_apply, smul_eq_mul,
              Real.enorm_of_nonneg (mul_nonneg (by positivity) (hh ν))]
            refine ENNReal.ofReal_le_ofReal ?_
            calc ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)
                ≤ ((2 : ℝ) ^ ν) ^ (-θ) * (6 * Ck * KFunctional ι₀ ι₁ (2 ^ ν) b) :=
                  mul_le_mul_of_nonneg_left (hJu' ν)
                    (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _)
              _ = 6 * Ck * h ν := by ring
        _ = ENNReal.ofReal (6 * Ck) * kSequenceENorm ι₀ ι₁ θ q b := by
            rw [eLpNorm_const_smul, hk, Real.enorm_of_nonneg (by positivity)]
    have hdisc := ofReal_mul_kSequenceENorm_le_realInterpolationENorm ι₀ ι₁ hθ0.le hq b
    have h2θ : ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * ENNReal.ofReal ((2 : ℝ) ^ θ) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos, neg_add_cancel,
        Real.rpow_zero, ENNReal.ofReal_one]
    have hk2 : kSequenceENorm ι₀ ι₁ θ q b ≤
        ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ * realInterpolationENorm ι₀ ι₁ θ q b := by
      calc kSequenceENorm ι₀ ι₁ θ q b
          = ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ *
              (ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * L * kSequenceENorm ι₀ ι₁ θ q b) := by
            rw [show ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ *
                (ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * L * kSequenceENorm ι₀ ι₁ θ q b) =
                (ENNReal.ofReal ((2 : ℝ) ^ (-θ)) * ENNReal.ofReal ((2 : ℝ) ^ θ)) * (L⁻¹ * L) *
                  kSequenceENorm ι₀ ι₁ θ q b by ring,
              h2θ, ENNReal.inv_mul_cancel hL0 hLtop, one_mul, one_mul]
        _ ≤ _ := by gcongr
    calc jSequenceENorm ι₀ ι₁ θ q u
        ≤ ENNReal.ofReal (6 * Ck) * kSequenceENorm ι₀ ι₁ θ q b := h1
      _ ≤ ENNReal.ofReal (6 * Ck) *
            (ENNReal.ofReal ((2 : ℝ) ^ θ) * L⁻¹ * realInterpolationENorm ι₀ ι₁ θ q b) := by
          gcongr
      _ = F * realInterpolationENorm ι₀ ι₁ θ q b := by simp only [F]; ring
  calc realInterpolationENorm κ₀ κ₁ η q a ≤ E * jSequenceENorm ι₀ ι₁ θ q u := hmain
    _ ≤ E * (F * realInterpolationENorm ι₀ ι₁ θ q b) := mul_le_mul_right hseq _
    _ = E * F * realInterpolationENorm ι₀ ι₁ θ q b := (mul_assoc _ _ _).symm

end InterpolationCouple

namespace InterpolationCat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The couple `(X₀, X₁)` with embeddings `κᵢ` into the ambient space of the couple `A`. -/
abbrev ofEmbeddings (A : InterpolationCat.{v, u} 𝕜) {X₀ X₁ : Type v}
    [QuasinormedAddCommGroup X₀] [QuasiNormedSpace 𝕜 X₀] [CompleteSpace X₀]
    [QuasinormedAddCommGroup X₁] [QuasiNormedSpace 𝕜 X₁] [CompleteSpace X₁]
    (κ₀ : X₀ →L[𝕜] A.𝒜) (κ₁ : X₁ →L[𝕜] A.𝒜) (h₀ : Function.Injective κ₀)
    (h₁ : Function.Injective κ₁) : InterpolationCat.{v, u} 𝕜 where
  𝒜 := A.𝒜
  A₀ := X₀
  A₁ := X₁
  ι₀ := κ₀
  ι₁ := κ₁
  injective₀ := h₀
  injective₁ := h₁

/-- **The reiteration theorem** (B–L Theorem 3.5.3; quasi-normed form 3.11.5; Triebel §1.10.2): if
`X₀, X₁` (complete, embedded in the ambient space of `A`) are of class `𝒞(θ₀; Ā)` and
`𝒞(θ₁; Ā)` with `θᵢ ∈ [0, 1]`, `θ₀ ≠ θ₁`, then for `0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`,
`X̄_{η,q} ≅ Ā_{θ,q}`, compatibly with the maps to the ambient space. -/
theorem nonempty_iso_realInterpolationFunctor_reiteration (A : InterpolationCat.{v, u} 𝕜)
    {X₀ X₁ : Type v}
    [QuasinormedAddCommGroup X₀] [QuasiNormedSpace 𝕜 X₀] [CompleteSpace X₀]
    [QuasinormedAddCommGroup X₁] [QuasiNormedSpace 𝕜 X₁] [CompleteSpace X₁]
    (κ₀ : X₀ →L[𝕜] A.𝒜) (κ₁ : X₁ →L[𝕜] A.𝒜) (h₀ : Function.Injective κ₀)
    (h₁ : Function.Injective κ₁) {θ₀ θ₁ : ℝ} (hθ₀ : θ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hθ₁ : θ₁ ∈ Set.Icc (0 : ℝ) 1) (hne : θ₀ ≠ θ₁)
    (hX₀ : InterpolationCouple.IsOfClassK A.ι₀ A.ι₁ θ₀ κ₀ ∧
      InterpolationCouple.IsOfClassJ A.ι₀ A.ι₁ θ₀ κ₀)
    (hX₁ : InterpolationCouple.IsOfClassK A.ι₀ A.ι₁ θ₁ κ₁ ∧
      InterpolationCouple.IsOfClassJ A.ι₀ A.ι₁ θ₁ κ₁)
    (η : ℝ) [Fact (0 < η)] [Fact (η < 1)] (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 1)]
    (hθ : θ = (1 - η) * θ₀ + η * θ₁) (q : ℝ≥0∞) [Fact (0 < q)] :
    ∃ e : (realInterpolationFunctor 𝕜 η q).obj (A.ofEmbeddings κ₀ κ₁ h₀ h₁) ≅
        (realInterpolationFunctor 𝕜 θ q).obj A,
      ∀ x, InterpolationCouple.sumToAmbient A.ι₀ A.ι₁
          ((realInterpolationFunctor 𝕜 θ q).toSum A (e.hom.hom x)) =
        InterpolationCouple.sumToAmbient κ₀ κ₁
          ((realInterpolationFunctor 𝕜 η q).toSum (A.ofEmbeddings κ₀ κ₁ h₀ h₁) x) := by
  have hq : 0 < q := Fact.out
  have hη0 : 0 < η := Fact.out
  have hη1 : η < 1 := Fact.out
  set Xb := A.ofEmbeddings κ₀ κ₁ h₀ h₁
  -- the two inclusions (K-method backend)
  obtain ⟨C1, hC1, hR1⟩ := InterpolationCouple.exists_realInterpolationENorm_le_of_isOfClassK
    A.ι₀ A.ι₁ κ₀ κ₁ hne hθ hq hX₀.1 hX₁.1
  obtain ⟨C2, hC2, hR2⟩ := InterpolationCouple.exists_realInterpolationENorm_le_of_isOfClassJ
    A.ι₀ A.ι₁ κ₀ κ₁ hθ₀ hθ₁ hne hη0 hη1 hθ hq hX₀.2 hX₁.2
  -- `X̄_{η,q} ≅ Ā_{θ,q}` for the K-method: the same subspace of the ambient space, with
  -- equivalent quasinorms
  obtain ⟨e, he⟩ := QuasiBanachCat.exists_iso_of_bounded_correspondence
    (X := (kInterpolationFunctor 𝕜 η q).obj Xb) (Y := (kInterpolationFunctor 𝕜 θ q).obj A)
    ((InterpolationCouple.sumToAmbient κ₀ κ₁).toLinearMap ∘ₗ
      (InterpolationCouple.RealInterpolationSpace.toSum κ₀ κ₁ η q).toLinearMap)
    ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).toLinearMap ∘ₗ
      (InterpolationCouple.RealInterpolationSpace.toSum A.ι₀ A.ι₁ θ q).toLinearMap)
    (fun x y h => InterpolationCouple.RealInterpolationSpace.toSum_injective κ₀ κ₁
      (InterpolationCouple.sumToAmbient_injective _ _ h))
    (fun x y h => InterpolationCouple.RealInterpolationSpace.toSum_injective A.ι₀ A.ι₁
      (InterpolationCouple.sumToAmbient_injective _ _ h)) (C₁ := C1.toReal) (C₂ := C2.toReal)
    (fun (z : InterpolationCouple.RealInterpolationSpace κ₀ κ₁ η q) => by
      obtain ⟨b, hb, hbn⟩ := hR1 z
      refine ⟨⟨b, hbn.trans_lt (ENNReal.mul_lt_top hC1.lt_top z.2)⟩, hb, ?_⟩
      change (InterpolationCouple.realInterpolationENorm A.ι₀ A.ι₁ θ q b).toReal ≤
        C1.toReal * (InterpolationCouple.realInterpolationENorm κ₀ κ₁ η q z).toReal
      rw [← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC1 z.2.ne) hbn)
    (fun (y : InterpolationCouple.RealInterpolationSpace A.ι₀ A.ι₁ θ q) => by
      obtain ⟨a, ha, han⟩ := hR2 y y.2.ne
      refine ⟨⟨a, han.trans_lt (ENNReal.mul_lt_top hC2.lt_top y.2)⟩, ha, ?_⟩
      change (InterpolationCouple.realInterpolationENorm κ₀ κ₁ η q a).toReal ≤
        C2.toReal * (InterpolationCouple.realInterpolationENorm A.ι₀ A.ι₁ θ q y).toReal
      rw [← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC2 y.2.ne) han)
  -- transport along the canonical identifications with the K-method on both sides
  refine ⟨(realInterpolationFunctorEquivK η q).iso Xb ≪≫ e ≪≫
    ((realInterpolationFunctorEquivK θ q).iso A).symm, fun x => ?_⟩
  have h1 := DFunLike.congr_fun
    (InterpolationFunctor.Equiv.toSum_comp_inv (realInterpolationFunctorEquivK θ q) A)
  have h2 := DFunLike.congr_fun
    (InterpolationFunctor.Equiv.toSum_comp_hom (realInterpolationFunctorEquivK η q) Xb) x
  simp only [ContinuousLinearMap.comp_apply] at h1 h2
  simp only [Iso.trans_hom, Iso.symm_hom, QuasiBanachCat.hom_comp,
    ContinuousLinearMap.comp_apply]
  rw [h1, ← h2]
  exact he _

/-- The canonical real interpolation space `Ā_{θ,q}` is of class `𝒦(θ; Ā)` (transported from
`RealInterpolationSpace.isOfClassK` along `realInterpolationFunctorEquivK`). -/
private theorem isOfClassK_realInterpolationFunctor (A : InterpolationCat.{v, u} 𝕜) (θ : ℝ)
    (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    InterpolationCouple.IsOfClassK A.ι₀ A.ι₁ θ
      ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).comp
        ((realInterpolationFunctor 𝕜 θ q).toSum A)) := by
  obtain ⟨C, hC⟩ := InterpolationCouple.RealInterpolationSpace.isOfClassK A.ι₀ A.ι₁ θ q
  set i := (realInterpolationFunctorEquivK θ q).iso A
  refine ⟨max C 0 * QuasinormedAddCommGroup.opQuasiNorm i.hom.hom, fun x => ?_⟩
  obtain ⟨b, hb, hK⟩ := hC (i.hom.hom x)
  have hsum := DFunLike.congr_fun
    (InterpolationFunctor.Equiv.toSum_comp_hom (realInterpolationFunctorEquivK θ q) A) x
  simp only [ContinuousLinearMap.comp_apply] at hsum
  refine ⟨b, ?_, fun t ht => ?_⟩
  · rw [hb]
    simp only [ContinuousLinearMap.comp_apply]
    exact congrArg _ hsum
  have hn := QuasinormedAddCommGroup.le_opQuasiNorm i.hom.hom x
  have hp : 0 ≤ max C 0 * t ^ θ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg ht.le _)
  calc InterpolationCouple.KFunctional A.ι₀ A.ι₁ t b
      ≤ C * t ^ θ * ‖i.hom.hom x‖ := hK t ht
    _ ≤ max C 0 * t ^ θ * ‖i.hom.hom x‖ := by
        gcongr
        · exact QuasinormedAddCommGroup.norm_nonneg _
        · exact le_max_left _ _
    _ ≤ max C 0 * t ^ θ * (QuasinormedAddCommGroup.opQuasiNorm i.hom.hom * ‖x‖) :=
        mul_le_mul_of_nonneg_left hn hp
    _ = _ := by ring

/-- The canonical real interpolation space `Ā_{θ,q}` is of class `𝒥(θ; Ā)` (transported from
`RealInterpolationSpace.isOfClassJ` along `realInterpolationFunctorEquivK`). -/
private theorem isOfClassJ_realInterpolationFunctor (A : InterpolationCat.{v, u} 𝕜) (θ : ℝ)
    (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    InterpolationCouple.IsOfClassJ A.ι₀ A.ι₁ θ
      ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).comp
        ((realInterpolationFunctor 𝕜 θ q).toSum A)) := by
  obtain ⟨C, hC⟩ := InterpolationCouple.RealInterpolationSpace.isOfClassJ A.ι₀ A.ι₁ θ q
  set i := (realInterpolationFunctorEquivK θ q).iso A
  set M := QuasinormedAddCommGroup.opQuasiNorm i.inv.hom
  refine ⟨M * max C 0, fun b => ?_⟩
  obtain ⟨y, hy, hJ⟩ := hC b
  have hsum := DFunLike.congr_fun
    (InterpolationFunctor.Equiv.toSum_comp_inv (realInterpolationFunctorEquivK θ q) A) y
  refine ⟨i.inv.hom y, ?_, fun t ht => ?_⟩
  · exact (congrArg (InterpolationCouple.sumToAmbient A.ι₀ A.ι₁) hsum).trans hy
  have hn := QuasinormedAddCommGroup.le_opQuasiNorm i.inv.hom y
  have hM := QuasinormedAddCommGroup.opQuasiNorm_nonneg i.inv.hom
  calc ‖i.inv.hom y‖ ≤ M * ‖y‖ := hn
    _ ≤ M * (max C 0 * t ^ (-θ) * InterpolationCouple.JFunctional A.ι₀ A.ι₁ t b) := by
        refine mul_le_mul_of_nonneg_left ((hJ t ht).trans ?_) hM
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
          (Real.rpow_nonneg ht.le _)) (InterpolationCouple.jFunctional_nonneg A.ι₀ A.ι₁ t b)
    _ = _ := by ring

variable (θ₀ : ℝ) (q₀ : ℝ≥0∞) [Fact (0 < θ₀)] [Fact (θ₀ < 1)] [Fact (0 < q₀)]
variable (θ₁ : ℝ) (q₁ : ℝ≥0∞) [Fact (0 < θ₁)] [Fact (θ₁ < 1)] [Fact (0 < q₁)]

/-- The couple `(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})` of real interpolation spaces of `A`, embedded in the
ambient space of `A` through `A₀ + A₁`. -/
noncomputable abbrev realInterpolationCouple (A : InterpolationCat.{v, u} 𝕜) :
    InterpolationCat.{v, u} 𝕜 :=
  A.ofEmbeddings
    ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).comp ((realInterpolationFunctor 𝕜 θ₀ q₀).toSum A))
    ((InterpolationCouple.sumToAmbient A.ι₀ A.ι₁).comp ((realInterpolationFunctor 𝕜 θ₁ q₁).toSum A))
    (fun _ _ h => (realInterpolationFunctor 𝕜 θ₀ q₀).toSum_injective A
      (InterpolationCouple.sumToAmbient_injective _ _ h))
    (fun _ _ h => (realInterpolationFunctor 𝕜 θ₁ q₁).toSum_injective A
      (InterpolationCouple.sumToAmbient_injective _ _ h))

/-- Reiteration for real interpolation spaces (B–L Theorem 3.5.3 / 3.11.5, "in particular"):
for `0 < θ₀ ≠ θ₁ < 1`, `0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`,
`(Ā_{θ₀,q₀}, Ā_{θ₁,q₁})_{η,q} ≅ Ā_{θ,q}`, compatibly with the maps to the ambient space. -/
theorem nonempty_iso_realInterpolationFunctor_realInterpolationCouple
    (A : InterpolationCat.{v, u} 𝕜) (hne : θ₀ ≠ θ₁) (η : ℝ) [Fact (0 < η)] [Fact (η < 1)]
    (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 1)] (hθ : θ = (1 - η) * θ₀ + η * θ₁)
    (q : ℝ≥0∞) [Fact (0 < q)] :
    ∃ e : (realInterpolationFunctor 𝕜 η q).obj (A.realInterpolationCouple θ₀ q₀ θ₁ q₁) ≅
        (realInterpolationFunctor 𝕜 θ q).obj A,
      ∀ x, InterpolationCouple.sumToAmbient A.ι₀ A.ι₁
          ((realInterpolationFunctor 𝕜 θ q).toSum A (e.hom.hom x)) =
        InterpolationCouple.sumToAmbient (A.realInterpolationCouple θ₀ q₀ θ₁ q₁).ι₀
          (A.realInterpolationCouple θ₀ q₀ θ₁ q₁).ι₁
          ((realInterpolationFunctor 𝕜 η q).toSum (A.realInterpolationCouple θ₀ q₀ θ₁ q₁) x) := by
  -- B–L: "`Ā_{θ,q}` is of class `𝒞(θ; Ā)` if `0 < θ < 1`"
  have h0 : θ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨(Fact.out : 0 < θ₀).le, (Fact.out : θ₀ < 1).le⟩
  have h1 : θ₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨(Fact.out : 0 < θ₁).le, (Fact.out : θ₁ < 1).le⟩
  exact nonempty_iso_realInterpolationFunctor_reiteration A _ _ _ _ h0 h1 hne
    ⟨isOfClassK_realInterpolationFunctor A θ₀ q₀, isOfClassJ_realInterpolationFunctor A θ₀ q₀⟩
    ⟨isOfClassK_realInterpolationFunctor A θ₁ q₁, isOfClassJ_realInterpolationFunctor A θ₁ q₁⟩
    η θ hθ q

end InterpolationCat
