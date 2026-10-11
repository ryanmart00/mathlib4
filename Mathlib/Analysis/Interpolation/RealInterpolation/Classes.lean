/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.Equivalence

/-!
# Spaces of class `𝒦(θ)`, `𝒥(θ)` and `𝒞(θ)`

Bergh–Löfström Definition 3.5.1 (Triebel §1.10.1): a space `X` between `A₀ ∩ A₁` and `A₀ + A₁`
is of class `𝒦(θ; Ā)` if `K(t, a; Ā) ≤ C t^θ ‖a‖_X` for `a ∈ X`, and of class `𝒥(θ; Ā)` if
`‖a‖_X ≤ C t^{-θ} J(t, a; Ā)` for `a ∈ A₀ ∩ A₁`; of class `𝒞(θ; Ā)` if both. These are the
hypotheses of the reiteration theorem (`RealInterpolation/Reiteration.lean`).

As everywhere in this framework, `X` is located by a continuous linear embedding `κ : X →L[𝕜] 𝒜`
into the ambient space of the couple, and membership in `A₀ + A₁` / `A₀ ∩ A₁` is read through the
injective `sumToAmbient`. So the class conditions also assert `X ⊂ A₀ + A₁` (for `𝒦(θ)`) and
`A₀ ∩ A₁ ⊂ X` (for `𝒥(θ)`).

## Main definitions
* `InterpolationCouple.IsOfClassK θ κ`, `InterpolationCouple.IsOfClassJ θ κ`.

## Main statements
* `isOfClassK_zero_ι₀`, `isOfClassJ_zero_ι₀`, `isOfClassK_one_ι₁`, `isOfClassJ_one_ι₁`: `A₀` is of
  class `𝒞(0; Ā)` and `A₁` of class `𝒞(1; Ā)`.
* `RealInterpolationSpace.isOfClassK`, `RealInterpolationSpace.isOfClassJ`: for `0 < θ < 1`,
  `(A₀, A₁)_{θ,q}` is of class `𝒞(θ; Ā)` (B–L, after Definition 3.5.1, from Theorems 3.1.2 and
  3.2.2 / 3.11.2).
-/

open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
variable {X : Type*} [QuasinormedAddCommGroup X] [QuasiNormedSpace 𝕜 X]

namespace InterpolationCouple

/-- `X` (embedded in the ambient space by `κ`) is of class `𝒦(θ; Ā)` (B–L Definition 3.5.1 (a)):
every `x ∈ X` lies in `A₀ + A₁`, and `K(t, x; Ā) ≤ C t^θ ‖x‖_X` for all `t > 0`. -/
def IsOfClassK (θ : ℝ) (κ : X →L[𝕜] 𝒜) : Prop :=
  ∃ C : ℝ, ∀ x : X, ∃ b : sum ι₀ ι₁, sumToAmbient ι₀ ι₁ b = κ x ∧
    ∀ t : ℝ, 0 < t → KFunctional ι₀ ι₁ t b ≤ C * t ^ θ * ‖x‖

/-- `X` (embedded in the ambient space by `κ`) is of class `𝒥(θ; Ā)` (B–L Definition 3.5.1 (b)):
every `b ∈ A₀ ∩ A₁` lies in `X`, and `‖b‖_X ≤ C t^{-θ} J(t, b; Ā)` for all `t > 0`. -/
def IsOfClassJ (θ : ℝ) (κ : X →L[𝕜] 𝒜) : Prop :=
  ∃ C : ℝ, ∀ b : meet ι₀ ι₁, ∃ x : X, κ x = sumToAmbient ι₀ ι₁ (meetToSum ι₀ ι₁ b) ∧
    ∀ t : ℝ, 0 < t → ‖x‖ ≤ C * t ^ (-θ) * JFunctional ι₀ ι₁ t b

omit [T2Space 𝒜] in
/-- `K(t, b) ≤ ‖a₀‖ + t ‖a₁‖` for any decomposition `b = [(a₀, a₁)]`. -/
private theorem kFunctional_mk_le {t : ℝ} (ht : 0 ≤ t) (a₀ : A₀) (a₁ : A₁) :
    KFunctional ι₀ ι₁ t (Submodule.Quotient.mk (a₀, a₁)) ≤ ‖a₀‖ + t * ‖a₁‖ :=
  csInf_le (kFunctional_set_boundedBelow ι₀ ι₁ t ht _) ⟨a₀, a₁, rfl, rfl⟩

/-- `A₀` is of class `𝒦(0; Ā)` (B–L, after Definition 3.5.1: `K(t, a) ≤ ‖a‖_{A₀}`). -/
theorem isOfClassK_zero_ι₀ : IsOfClassK ι₀ ι₁ 0 ι₀ := by
  refine ⟨1, fun x => ⟨inl₀ ι₀ ι₁ x, sumToAmbient_inl₀ ι₀ ι₁ x, fun t ht => ?_⟩⟩
  rw [Real.rpow_zero, one_mul, one_mul, inl₀_eq_mk]
  simpa using kFunctional_mk_le ι₀ ι₁ ht.le x 0

/-- `A₀` is of class `𝒥(0; Ā)` (`‖b‖_{A₀} ≤ J(t, b)`). -/
theorem isOfClassJ_zero_ι₀ : IsOfClassJ ι₀ ι₁ 0 ι₀ := by
  refine ⟨1, fun b => ⟨(b : A₀ × A₁).1, ?_, fun t ht => ?_⟩⟩
  · obtain ⟨⟨a₀, a₁⟩, hb⟩ := b
    rw [meetToSum_apply, sumToAmbient_inl₀]
  · rw [neg_zero, Real.rpow_zero, one_mul, one_mul]
    exact le_max_left _ _

/-- `A₁` is of class `𝒦(1; Ā)` (`K(t, a) ≤ t ‖a‖_{A₁}`). -/
theorem isOfClassK_one_ι₁ : IsOfClassK ι₀ ι₁ 1 ι₁ := by
  refine ⟨1, fun x => ⟨inl₁ ι₀ ι₁ x, sumToAmbient_inl₁ ι₀ ι₁ x, fun t ht => ?_⟩⟩
  rw [Real.rpow_one, one_mul, inl₁_eq_mk]
  simpa using kFunctional_mk_le ι₀ ι₁ ht.le 0 x

/-- `A₁` is of class `𝒥(1; Ā)` (`‖b‖_{A₁} ≤ t⁻¹ J(t, b)`). -/
theorem isOfClassJ_one_ι₁ : IsOfClassJ ι₀ ι₁ 1 ι₁ := by
  refine ⟨1, fun b => ⟨(b : A₀ × A₁).2, ?_, fun t ht => ?_⟩⟩
  · obtain ⟨⟨a₀, a₁⟩, hb⟩ := b
    rw [meetToSum_apply, sumToAmbient_inl₀]
    exact ((mem_meet_iff ι₀ ι₁ a₀ a₁).mp hb).symm
  · rw [Real.rpow_neg_one, one_mul, ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact le_max_right _ _

section Transport

variable {Y : Type*} [QuasinormedAddCommGroup Y] [QuasiNormedSpace 𝕜 Y]

/-- Class `𝒦(θ)` passes to a space `Y` mapped into `X` compatibly with the embeddings: if
`κ ∘ S = κ'` for a bounded `S : Y → X`, then `X ∈ 𝒦(θ; Ā)` implies `Y ∈ 𝒦(θ; Ā)`. -/
theorem IsOfClassK.of_comp {θ : ℝ} {κ : X →L[𝕜] 𝒜} (h : IsOfClassK ι₀ ι₁ θ κ)
    {κ' : Y →L[𝕜] 𝒜} (S : Y →L[𝕜] X) (hS : κ.comp S = κ') : IsOfClassK ι₀ ι₁ θ κ' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0 * QuasinormedAddCommGroup.opQuasiNorm S, fun y => ?_⟩
  obtain ⟨b, hb, hK⟩ := hC (S y)
  refine ⟨b, by rw [hb, ← hS, ContinuousLinearMap.comp_apply], fun t ht => ?_⟩
  have hp : 0 ≤ max C 0 * t ^ θ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg ht.le _)
  calc KFunctional ι₀ ι₁ t b ≤ C * t ^ θ * ‖S y‖ := hK t ht
    _ ≤ max C 0 * t ^ θ * ‖S y‖ := by
        gcongr
        · exact QuasinormedAddCommGroup.norm_nonneg _
        · exact le_max_left _ _
    _ ≤ max C 0 * t ^ θ * (QuasinormedAddCommGroup.opQuasiNorm S * ‖y‖) :=
        mul_le_mul_of_nonneg_left (QuasinormedAddCommGroup.le_opQuasiNorm S y) hp
    _ = _ := by ring

/-- Class `𝒥(θ)` passes to a space `Y` into which `X` maps compatibly with the embeddings: if
`κ' ∘ T = κ` for a bounded `T : X → Y`, then `X ∈ 𝒥(θ; Ā)` implies `Y ∈ 𝒥(θ; Ā)`. -/
theorem IsOfClassJ.of_comp {θ : ℝ} {κ : X →L[𝕜] 𝒜} (h : IsOfClassJ ι₀ ι₁ θ κ)
    {κ' : Y →L[𝕜] 𝒜} (T : X →L[𝕜] Y) (hT : κ'.comp T = κ) : IsOfClassJ ι₀ ι₁ θ κ' := by
  obtain ⟨C, hC⟩ := h
  set M := QuasinormedAddCommGroup.opQuasiNorm T
  refine ⟨M * max C 0, fun b => ?_⟩
  obtain ⟨x, hx, hJ⟩ := hC b
  refine ⟨T x, by rw [← hx, ← hT, ContinuousLinearMap.comp_apply], fun t ht => ?_⟩
  calc ‖T x‖ ≤ M * ‖x‖ := QuasinormedAddCommGroup.le_opQuasiNorm T x
    _ ≤ M * (max C 0 * t ^ (-θ) * JFunctional ι₀ ι₁ t b) := by
        refine mul_le_mul_of_nonneg_left ((hJ t ht).trans ?_)
          (QuasinormedAddCommGroup.opQuasiNorm_nonneg T)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
          (Real.rpow_nonneg ht.le _)) (jFunctional_nonneg ι₀ ι₁ t b)
    _ = _ := by ring

end Transport

/-- B–L Theorem 3.2.2, formula (6), for the discrete J-method: the one-term representation
`b = u_ν` gives `‖b‖_{θ,q;J} ≤ 2^{-νθ} J(2^ν, b)`. -/
theorem jInterpolationENorm_meetToSum_le_zpow (θ : ℝ) (q : ℝ≥0∞) (b : meet ι₀ ι₁) (ν : ℤ) :
    jInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b) ≤
      ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) b) := by
  set u : ℤ → meet ι₀ ι₁ := Pi.single ν b with hu_def
  have hu : HasSum (fun μ => meetToSum ι₀ ι₁ (u μ)) (meetToSum ι₀ ι₁ b) := by
    simpa [hu_def] using hasSum_single ν
      (f := fun μ => meetToSum ι₀ ι₁ (u μ)) fun μ hμ => by simp [hu_def, hμ]
  refine (jInterpolationENorm_le ι₀ ι₁ θ q _ hu).trans ?_
  have hg : (fun μ : ℤ => ENNReal.ofReal (((2 : ℝ) ^ μ) ^ (-θ) *
      JFunctional ι₀ ι₁ (2 ^ μ) (u μ))) =
        ({ν} : Set ℤ).indicator fun _ =>
          ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) b) := by
    funext μ
    by_cases hμ : μ = ν
    · subst hμ
      simp [hu_def]
    · simp [hu_def, hμ, jFunctional_zero]
  rw [jSequenceENorm, hg]
  refine (MeasureTheory.eLpNorm_indicator_const_le _ q
    (measurableSet_singleton ν).nullMeasurableSet).trans ?_
  simp

namespace RealInterpolationSpace

variable (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]

/-- `(A₀, A₁)_{θ,q}` is of class `𝒦(θ; Ā)`: `K(t, a) ≤ C t^θ ‖a‖_{θ,q}` (B–L Theorem 3.1.2 (6) /
3.11.2 (3); here `ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le`). -/
theorem isOfClassK :
    IsOfClassK ι₀ ι₁ θ ((sumToAmbient ι₀ ι₁).comp (RealInterpolationSpace.toSum ι₀ ι₁ θ q)) := by
  have hθ0 : 0 < θ := Fact.out
  have hθ1 : θ < 1 := Fact.out
  have hq : 0 < q := Fact.out
  set c := realInterpolationConst θ q
  have hc0 : c ≠ 0 := (realInterpolationConst_pos θ q).ne'
  have hctop : c ≠ ⊤ := (realInterpolationConst_lt_top hθ0 hθ1 q).ne
  have hcR : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  refine ⟨c.toReal⁻¹, fun x => ⟨(x : sum ι₀ ι₁), rfl, fun t ht => ?_⟩⟩
  -- B–L Theorem 3.1.2 (6): `t^{-θ} K(t, x) c ≤ ‖x‖_{θ,q}`
  have h6 := ofReal_rpow_neg_mul_kFunctional_mul_realInterpolationConst_le ι₀ ι₁ θ hq
    (x : sum ι₀ ι₁) ht
  have hfin : realInterpolationENorm ι₀ ι₁ θ q (x : sum ι₀ ι₁) ≠ ⊤ :=
    (show realInterpolationENorm ι₀ ι₁ θ q (x : sum ι₀ ι₁) < ⊤ from x.2).ne
  have hpos : 0 ≤ t ^ (-θ) * KFunctional ι₀ ι₁ t (x : sum ι₀ ι₁) :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ι₀ ι₁ t ht.le _)
  have h6' := ENNReal.toReal_mono hfin h6
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos] at h6'
  rw [norm_def]
  have hsplit : KFunctional ι₀ ι₁ t (x : sum ι₀ ι₁) =
      t ^ θ * (t ^ (-θ) * KFunctional ι₀ ι₁ t (x : sum ι₀ ι₁)) := by
    rw [← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
  rw [hsplit]
  calc t ^ θ * (t ^ (-θ) * KFunctional ι₀ ι₁ t (x : sum ι₀ ι₁))
      ≤ t ^ θ * ((realInterpolationENorm ι₀ ι₁ θ q (x : sum ι₀ ι₁)).toReal / c.toReal) := by
        gcongr
        rw [le_div_iff₀ hcR]
        exact h6'
    _ = _ := by ring

/-- `(A₀, A₁)_{θ,q}` is of class `𝒥(θ; Ā)`: `‖b‖_{θ,q} ≤ C t^{-θ} J(t, b)` for `b ∈ A₀ ∩ A₁`
(B–L Theorem 3.2.2 (6) / 3.11.2 (4); for the K-quasinorm this follows from
`K(s, b) ≤ min(1, s/t) J(t, b)` and the scaling identity, as for Theorem 3.1.2 (6)). -/
theorem isOfClassJ :
    IsOfClassJ ι₀ ι₁ θ ((sumToAmbient ι₀ ι₁).comp (RealInterpolationSpace.toSum ι₀ ι₁ θ q)) := by
  have hθ0 : 0 < θ := Fact.out
  have hθ1 : θ < 1 := Fact.out
  have hq : 0 < q := Fact.out
  -- B–L: from Theorem 3.2.2 (6) for the J-method and the equivalence theorem
  obtain ⟨C, hC, hKJ⟩ :=
    exists_realInterpolationENorm_le_mul_jInterpolationENorm ι₀ ι₁ hθ0 hθ1 hq
  refine ⟨C.toReal * 2 ^ θ, fun b => ⟨RealInterpolationSpace.fromMeet ι₀ ι₁ θ q b, ?_,
    fun t ht => ?_⟩⟩
  · simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.comp_apply (RealInterpolationSpace.toSum ι₀ ι₁ θ q),
      toSum_comp_fromMeet]
    rfl
  obtain ⟨ν, hν⟩ := exists_mem_Ico_zpow ht one_lt_two
  have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
  have hx : ((RealInterpolationSpace.fromMeet ι₀ ι₁ θ q b : RealInterpolationSpace ι₀ ι₁ θ q) :
      sum ι₀ ι₁) = meetToSum ι₀ ι₁ b := by
    rw [← toSum_apply, ← ContinuousLinearMap.comp_apply, toSum_comp_fromMeet]
    rfl
  have hJ0 : 0 ≤ JFunctional ι₀ ι₁ t b := jFunctional_nonneg ι₀ ι₁ t b
  -- `2^{-νθ} J(2^ν, b) ≤ 2^θ t^{-θ} J(t, b)` for `2^ν ≤ t < 2^{ν+1}`
  have hpow : ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) b ≤
      2 ^ θ * t ^ (-θ) * JFunctional ι₀ ι₁ t b := by
    have h1 : ((2 : ℝ) ^ ν) ^ (-θ) ≤ 2 ^ θ * t ^ (-θ) := by
      have h2t : t ≤ 2 * 2 ^ ν := by
        have := hν.2.le
        rwa [zpow_add_one₀ two_ne_zero, mul_comm] at this
      calc ((2 : ℝ) ^ ν) ^ (-θ) = 2 ^ θ * (2 * 2 ^ ν) ^ (-θ) := by
            rw [Real.mul_rpow zero_le_two h2ν.le, ← mul_assoc, ← Real.rpow_add two_pos,
              add_neg_cancel, Real.rpow_zero, one_mul]
        _ ≤ 2 ^ θ * t ^ (-θ) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos ht h2t (neg_nonpos.mpr hθ0.le)) (by positivity)
    exact mul_le_mul h1 (jFunctional_mono ι₀ ι₁ hν.1 b) (jFunctional_nonneg ι₀ ι₁ _ b)
      (by positivity)
  have hle : realInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b) ≤
      C * ENNReal.ofReal (2 ^ θ * t ^ (-θ) * JFunctional ι₀ ι₁ t b) :=
    (hKJ _).trans (mul_le_mul_right ((jInterpolationENorm_meetToSum_le_zpow ι₀ ι₁ θ q b ν).trans
      (ENNReal.ofReal_le_ofReal hpow)) _)
  rw [norm_def, hx]
  calc (realInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b)).toReal
      ≤ (C * ENNReal.ofReal (2 ^ θ * t ^ (-θ) * JFunctional ι₀ ι₁ t b)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hle
    _ = C.toReal * 2 ^ θ * t ^ (-θ) * JFunctional ι₀ ι₁ t b := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        ring

end RealInterpolationSpace

end InterpolationCouple
