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

open CategoryTheory
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
        realInterpolationENorm κ₀ κ₁ η q a ≤ C * realInterpolationENorm ι₀ ι₁ θ q b :=
  sorry

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
          ((realInterpolationFunctor 𝕜 η q).toSum (A.ofEmbeddings κ₀ κ₁ h₀ h₁) x) :=
  sorry

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
          ((realInterpolationFunctor 𝕜 η q).toSum (A.realInterpolationCouple θ₀ q₀ θ₁ q₁) x) :=
  sorry

end InterpolationCat
