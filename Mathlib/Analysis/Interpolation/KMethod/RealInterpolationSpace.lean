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
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁] [CompleteSpace A₁]
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
  sorry

theorem realInterpolationConst_lt_top {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) :
    realInterpolationConst θ q < ⊤ := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
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

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
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

theorem realInterpolationENorm_eq_zero_iff (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) (a : sum ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q a = 0 ↔ a = 0 := by
  sorry

/-- The quasi-triangle inequality for `realInterpolationENorm` with a *finite, real* constant
`≥ 1`, as needed for `QuasinormedAddCommGroup.quasiTriangleConst` (strengthens
`realInterpolationENorm_add_le`, whose constant is only known to be positive). -/
theorem exists_realInterpolationENorm_add_le (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : sum ι₀ ι₁,
      realInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        ENNReal.ofReal C *
          (realInterpolationENorm ι₀ ι₁ θ q a + realInterpolationENorm ι₀ ι₁ θ q b) := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
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

/-- The "`A₀ ∩ A₁ ⊂`" half of the sandwich, quantitatively: `‖a‖_{θ,q} ≤ c_{θ,q} ‖a‖_{A₀∩A₁}`
(strengthens `realInterpolationENorm_meetToSum_lt_top`). -/
theorem realInterpolationENorm_meetToSum_le (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q) (b : meet ι₀ ι₁) :
    realInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b) ≤
      realInterpolationConst θ q * ENNReal.ofReal ‖b‖ := by
  sorry

/-! ### The space -/

/-- The submodule of `A₀ + A₁` of elements of finite `(θ,q)`-quasinorm. Defined for every `θ, q`
(at `q = 0` the quasinorm is constantly `1` and this is all of `A₀ + A₁`). The quasi-Banach space
`(A₀, A₁)_{θ,q}` is `RealInterpolationSpace`, a type synonym of this submodule. -/
noncomputable def realInterpolationSubmodule (θ : ℝ) (q : ℝ≥0∞) : Submodule 𝕜 (sum ι₀ ι₁) where
  carrier := {a | realInterpolationENorm ι₀ ι₁ θ q a < ⊤}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

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
    ‖a‖ = (realInterpolationENorm ι₀ ι₁ θ q a).toReal := by
  sorry

variable (θ q) in
/-- The quasi-triangle constant of `(A₀, A₁)_{θ,q}`, extracted from
`exists_realInterpolationENorm_add_le`. -/
noncomputable def quasiTriangleConst [Fact (0 < q)] : ℝ :=
  Classical.choose (exists_realInterpolationENorm_add_le ι₀ ι₁ θ (Fact.out : 0 < q))

theorem one_le_quasiTriangleConst [Fact (0 < q)] : 1 ≤ quasiTriangleConst ι₀ ι₁ θ q := by
  sorry

theorem norm_add_le [Fact (0 < q)] (a b : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖a + b‖ ≤ quasiTriangleConst ι₀ ι₁ θ q * (‖a‖ + ‖b‖) := by
  sorry

theorem norm_neg (a : RealInterpolationSpace ι₀ ι₁ θ q) : ‖-a‖ = ‖a‖ := by
  sorry

theorem norm_eq_zero_iff [Fact (0 < q)] (a : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖a‖ = 0 ↔ a = 0 := by
  sorry

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
      toIsTopologicalAddGroup := sorry
      toIsUniformAddGroup := sorry
      nhds_zero_hasBasis := sorry }

theorem norm_smul [Fact (0 < q)] (c : 𝕜) (a : RealInterpolationSpace ι₀ ι₁ θ q) :
    ‖c • a‖ = ‖c‖ * ‖a‖ := by
  sorry

noncomputable instance instQuasiNormedSpace [Fact (0 < q)] :
    QuasiNormedSpace 𝕜 (RealInterpolationSpace ι₀ ι₁ θ q) where
  norm_smul_le c a := (norm_smul ι₀ ι₁ c a).le

/-- `(A₀, A₁)_{θ,q}` is complete (Triebel §1.3.2, Theorem 1(a)): a Cauchy sequence is Cauchy in
`A₀ + A₁` (by the sandwich bound), converges there, and the limit is also its limit in
`(A₀, A₁)_{θ,q}` by a Fatou argument on the K-functional. -/
instance instCompleteSpace [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
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
    sorry

@[simp]
theorem toSum_apply [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]
    (a : RealInterpolationSpace ι₀ ι₁ θ q) : toSum ι₀ ι₁ θ q a = (a : sum ι₀ ι₁) := by
  sorry

theorem toSum_injective [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    Function.Injective (toSum ι₀ ι₁ θ q) := by
  sorry

variable (θ q) in
/-- The inclusion `A₀ ∩ A₁ ↪ (A₀, A₁)_{θ,q}`, continuous by
`realInterpolationENorm_meetToSum_le`. -/
noncomputable def fromMeet [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    meet ι₀ ι₁ →L[𝕜] RealInterpolationSpace ι₀ ι₁ θ q where
  toLinearMap := (meetToSum ι₀ ι₁ : meet ι₀ ι₁ →ₗ[𝕜] sum ι₀ ι₁).codRestrict _ (by
    sorry)
  cont := by
    sorry

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
