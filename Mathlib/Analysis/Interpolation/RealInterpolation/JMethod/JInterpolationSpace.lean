/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JInterpolation
import Mathlib.Analysis.Interpolation.InterpolationCat

/-!
# The discrete J-method space `(A₀, A₁)_{θ,q;J}` as a quasi-normed space

The unbundled form of the discrete J-method, mirroring `KMethod/RealInterpolationSpace.lean`: the
submodule of `A₀ + A₁` of elements of finite J-quasinorm `jInterpolationENorm`, as a type synonym
`JInterpolationSpace ι₀ ι₁ θ q` with its quasi-normed structure (for `0 < θ < 1`, `0 < q`), the
sandwich maps `A₀ ∩ A₁ ↪ (A₀, A₁)_{θ,q;J} ↪ A₀ + A₁`, and the maps induced by morphisms of couples.

Completeness is deliberately not proved here: it follows from the equivalence theorem `K = J`
(the J- and K-spaces are the same submodule of `A₀ + A₁` with equivalent quasinorms), after which
the J-method is bundled as an `InterpolationFunctor`.

## Main definitions
* `InterpolationCouple.jInterpolationSubmodule ι₀ ι₁ θ q : Submodule 𝕜 (sum ι₀ ι₁)`.
* `InterpolationCouple.JInterpolationSpace ι₀ ι₁ θ q`: the type synonym.
* `JInterpolationSpace.toSum`, `JInterpolationSpace.fromMeet`: the sandwich maps.
* `InterpolationCat.Hom.jInterpolationMap`: the map induced by a morphism of couples.

## Main statements
* `JInterpolationSpace.instQuasinormedAddCommGroup`, `instQuasiNormedSpace`.
* `InterpolationCat.Hom.norm_jInterpolationMap_le`: `‖T a‖ ≤ 2 M₀^{1-θ} M₁^θ ‖a‖`.
-/

open scoped ENNReal QuasinormedAddCommGroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- The submodule of `A₀ + A₁` of elements of finite discrete J-quasinorm. -/
noncomputable def jInterpolationSubmodule (θ : ℝ) (q : ℝ≥0∞) : Submodule 𝕜 (sum ι₀ ι₁) where
  carrier := {a | jInterpolationENorm ι₀ ι₁ θ q a < ⊤}
  zero_mem' := by
    change jInterpolationENorm ι₀ ι₁ θ q 0 < ⊤
    rw [jInterpolationENorm_zero]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro a b (ha : jInterpolationENorm ι₀ ι₁ θ q a < ⊤) (hb : jInterpolationENorm ι₀ ι₁ θ q b < ⊤)
    change jInterpolationENorm ι₀ ι₁ θ q (a + b) < ⊤
    obtain ⟨C, -, hC⟩ := exists_jInterpolationENorm_add_le ι₀ ι₁ θ q
    exact (hC a b).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨ha, hb⟩))
  smul_mem' := by
    intro c a (ha : jInterpolationENorm ι₀ ι₁ θ q a < ⊤)
    change jInterpolationENorm ι₀ ι₁ θ q (c • a) < ⊤
    rw [jInterpolationENorm_smul]
    exact ENNReal.mul_lt_top enorm_lt_top ha

/-- `(A₀, A₁)_{θ,q;J}`: the elements of `A₀ + A₁` of finite discrete J-quasinorm. A type synonym
for `jInterpolationSubmodule`, for the same reason as `RealInterpolationSpace` (the coerced
submodule would carry the subtype topology of `A₀ + A₁`). -/
def JInterpolationSpace (θ : ℝ) (q : ℝ≥0∞) : Type _ :=
  jInterpolationSubmodule ι₀ ι₁ θ q

namespace JInterpolationSpace

variable {θ : ℝ} {q : ℝ≥0∞}

noncomputable instance instAddCommGroup : AddCommGroup (JInterpolationSpace ι₀ ι₁ θ q) :=
  inferInstanceAs (AddCommGroup (jInterpolationSubmodule ι₀ ι₁ θ q))

noncomputable instance instModule : Module 𝕜 (JInterpolationSpace ι₀ ι₁ θ q) :=
  inferInstanceAs (Module 𝕜 (jInterpolationSubmodule ι₀ ι₁ θ q))

/-- Elements of `(A₀, A₁)_{θ,q;J}` coerce to `A₀ + A₁`. -/
instance instCoeOut : CoeOut (JInterpolationSpace ι₀ ι₁ θ q) (sum ι₀ ι₁) :=
  ⟨fun a => Subtype.val (p := (· ∈ jInterpolationSubmodule ι₀ ι₁ θ q)) a⟩

noncomputable instance instNorm : Norm (JInterpolationSpace ι₀ ι₁ θ q) where
  norm a := (jInterpolationENorm ι₀ ι₁ θ q a).toReal

theorem norm_def (a : JInterpolationSpace ι₀ ι₁ θ q) :
    ‖a‖ = (jInterpolationENorm ι₀ ι₁ θ q a).toReal :=
  rfl

variable (θ q) in
/-- A constant in the quasi-triangle inequality of `(A₀, A₁)_{θ,q;J}`, extracted from
`exists_jInterpolationENorm_add_le`. It is an upper bound for the best constant
`QuasinormedAddCommGroup.quasiTriangleConst (JInterpolationSpace ι₀ ι₁ θ q)`. -/
noncomputable def quasiTriangleBound : ℝ :=
  Classical.choose (exists_jInterpolationENorm_add_le ι₀ ι₁ θ q)

theorem one_le_quasiTriangleBound : 1 ≤ quasiTriangleBound ι₀ ι₁ θ q :=
  (Classical.choose_spec (exists_jInterpolationENorm_add_le ι₀ ι₁ θ q)).1

theorem norm_add_le (a b : JInterpolationSpace ι₀ ι₁ θ q) :
    ‖a + b‖ ≤ quasiTriangleBound ι₀ ι₁ θ q * (‖a‖ + ‖b‖) := by
  have hC := (Classical.choose_spec (exists_jInterpolationENorm_add_le ι₀ ι₁ θ q)).2 a b
  have ha : jInterpolationENorm ι₀ ι₁ θ q (a : sum ι₀ ι₁) < ⊤ := a.2
  have hb : jInterpolationENorm ι₀ ι₁ θ q (b : sum ι₀ ι₁) < ⊤ := b.2
  have h1 : 0 ≤ quasiTriangleBound ι₀ ι₁ θ q := zero_le_one.trans (one_le_quasiTriangleBound ι₀ ι₁)
  rw [norm_def, norm_def, norm_def]
  calc (jInterpolationENorm ι₀ ι₁ θ q ((a + b : JInterpolationSpace ι₀ ι₁ θ q) :
          sum ι₀ ι₁)).toReal
      ≤ (ENNReal.ofReal (quasiTriangleBound ι₀ ι₁ θ q) *
          (jInterpolationENorm ι₀ ι₁ θ q a + jInterpolationENorm ι₀ ι₁ θ q b)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_lt_top.mpr ⟨ha, hb⟩).ne) hC
    _ = quasiTriangleBound ι₀ ι₁ θ q * ((jInterpolationENorm ι₀ ι₁ θ q a).toReal +
          (jInterpolationENorm ι₀ ι₁ θ q b).toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, ENNReal.toReal_add ha.ne hb.ne]

theorem norm_neg (a : JInterpolationSpace ι₀ ι₁ θ q) : ‖-a‖ = ‖a‖ := by
  rw [norm_def, norm_def]
  congr 1
  change jInterpolationENorm ι₀ ι₁ θ q (-(a : sum ι₀ ι₁)) = _
  rw [← neg_one_smul 𝕜 (a : sum ι₀ ι₁), jInterpolationENorm_smul, enorm_neg, enorm_one, one_mul]

theorem norm_eq_zero_iff [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]
    (a : JInterpolationSpace ι₀ ι₁ θ q) : ‖a‖ = 0 ↔ a = 0 := by
  have ha : jInterpolationENorm ι₀ ι₁ θ q (a : sum ι₀ ι₁) < ⊤ := a.2
  rw [norm_def, ENNReal.toReal_eq_zero_iff, or_iff_left ha.ne,
    jInterpolationENorm_eq_zero_iff ι₀ ι₁ θ Fact.out Fact.out Fact.out]
  exact Submodule.coe_eq_zero (x := (a : jInterpolationSubmodule ι₀ ι₁ θ q))

/-- The quasi-normed group structure on `(A₀, A₁)_{θ,q;J}`, for `0 < θ < 1`, `0 < q` (unlike the
K-method, definiteness of the J-quasinorm uses the sandwich bound, hence the conditions on `θ`). -/
noncomputable instance instQuasinormedAddCommGroup [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    QuasinormedAddCommGroup (JInterpolationSpace ι₀ ι₁ θ q) := by
  let hB : AddGroupFilterBasis (JInterpolationSpace ι₀ ι₁ θ q) :=
    AddGroupFilterBasis.ofQuasiNorm ⟨_, norm_add_le ι₀ ι₁⟩ (norm_neg ι₀ ι₁)
      (norm_eq_zero_iff ι₀ ι₁)
  exact
    { exists_norm_add_le := ⟨_, norm_add_le ι₀ ι₁⟩
      norm_neg := norm_neg ι₀ ι₁
      norm_eq_zero_iff := norm_eq_zero_iff ι₀ ι₁
      toUniformSpace := hB.uniformSpace
      toIsTopologicalAddGroup := hB.isTopologicalAddGroup
      toIsUniformAddGroup := hB.isUniformAddGroup
      nhds_zero_hasBasis := by
        change (@nhds _ hB.uniformSpace.toTopologicalSpace 0).HasBasis (0 < ·)
          fun ε : ℝ => {x : JInterpolationSpace ι₀ ι₁ θ q | ‖x‖ < ε}
        rw [hB.nhds_eq (x₀ := 0), AddGroupFilterBasis.N_zero]
        refine (FilterBasis.hasBasis hB.toFilterBasis).to_hasBasis' ?_ ?_
        · rintro s ⟨ε, hε, rfl⟩
          exact ⟨ε, hε, subset_rfl⟩
        · rintro ε hε
          exact FilterBasis.mem_filter_of_mem _ ⟨ε, hε, rfl⟩ }

theorem norm_smul (c : 𝕜)
    (a : JInterpolationSpace ι₀ ι₁ θ q) : ‖c • a‖ = ‖c‖ * ‖a‖ := by
  rw [norm_def, norm_def]
  change (jInterpolationENorm ι₀ ι₁ θ q (c • (a : sum ι₀ ι₁))).toReal = _
  rw [jInterpolationENorm_smul, ENNReal.toReal_mul, toReal_enorm]

noncomputable instance instQuasiNormedSpace [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    QuasiNormedSpace 𝕜 (JInterpolationSpace ι₀ ι₁ θ q) where
  norm_smul_le c a := (norm_smul ι₀ ι₁ c a).le

/-! ### The sandwich maps -/

variable (θ q) in
/-- The inclusion `(A₀, A₁)_{θ,q;J} ↪ A₀ + A₁`, continuous by
`exists_ofReal_mul_norm_le_jInterpolationENorm`. -/
noncomputable def toSum [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    JInterpolationSpace ι₀ ι₁ θ q →L[𝕜] sum ι₀ ι₁ where
  toLinearMap := (jInterpolationSubmodule ι₀ ι₁ θ q).subtype
  cont := by
    obtain ⟨c, hc, hle⟩ := exists_ofReal_mul_norm_le_jInterpolationENorm ι₀ ι₁ θ
      (Fact.out : 0 < θ) (Fact.out : θ < 1) (Fact.out : 0 < q)
    refine QuasinormedAddCommGroup.continuous_of_bound (E := JInterpolationSpace ι₀ ι₁ θ q)
      (F := sum ι₀ ι₁) (jInterpolationSubmodule ι₀ ι₁ θ q).subtype.toAddMonoidHom c⁻¹
      fun a => ?_
    have ha : jInterpolationENorm ι₀ ι₁ θ q (a : sum ι₀ ι₁) < ⊤ := a.2
    have h := ENNReal.toReal_mono ha.ne (hle (a : sum ι₀ ι₁))
    rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (QuasinormedAddCommGroup.norm_nonneg _))] at h
    change ‖(a : sum ι₀ ι₁)‖ ≤ c⁻¹ * (jInterpolationENorm ι₀ ι₁ θ q a).toReal
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h

theorem toSum_apply [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]
    (a : JInterpolationSpace ι₀ ι₁ θ q) : toSum ι₀ ι₁ θ q a = (a : sum ι₀ ι₁) :=
  rfl

theorem toSum_injective [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    Function.Injective (toSum ι₀ ι₁ θ q) :=
  Subtype.val_injective

variable (θ q) in
/-- The inclusion `A₀ ∩ A₁ ↪ (A₀, A₁)_{θ,q;J}`, continuous (with constant `1`) by
`jInterpolationENorm_meetToSum_le`. -/
noncomputable def fromMeet [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    meet ι₀ ι₁ →L[𝕜] JInterpolationSpace ι₀ ι₁ θ q where
  toLinearMap := (meetToSum ι₀ ι₁ : meet ι₀ ι₁ →ₗ[𝕜] sum ι₀ ι₁).codRestrict _ fun b =>
    (jInterpolationENorm_meetToSum_le ι₀ ι₁ θ q b).trans_lt ENNReal.ofReal_lt_top
  cont := by
    refine QuasinormedAddCommGroup.continuous_of_bound (E := meet ι₀ ι₁)
      (F := JInterpolationSpace ι₀ ι₁ θ q)
      (LinearMap.toAddMonoidHom <| (meetToSum ι₀ ι₁ : meet ι₀ ι₁ →ₗ[𝕜] sum ι₀ ι₁).codRestrict
        (jInterpolationSubmodule ι₀ ι₁ θ q) fun b =>
          (jInterpolationENorm_meetToSum_le ι₀ ι₁ θ q b).trans_lt ENNReal.ofReal_lt_top)
      1 fun b => ?_
    change (jInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b)).toReal ≤ 1 * ‖b‖
    rw [one_mul]
    exact ENNReal.toReal_le_of_le_ofReal (QuasinormedAddCommGroup.norm_nonneg b)
      (jInterpolationENorm_meetToSum_le ι₀ ι₁ θ q b)

theorem toSum_comp_fromMeet [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] :
    (toSum ι₀ ι₁ θ q).comp (fromMeet ι₀ ι₁ θ q) = meetToSum ι₀ ι₁ :=
  ContinuousLinearMap.ext fun _ => rfl

end JInterpolationSpace

end InterpolationCouple

/-! ### Functoriality -/

namespace InterpolationCat.Hom

open CategoryTheory InterpolationCouple

variable {C D E : InterpolationCat 𝕜} (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)]
  [Fact (0 < q)]

/-- The linear map underlying `jInterpolationMap`: the restriction of `T.sumMap`. -/
noncomputable def jInterpolationMapₗ (T : C ⟶ D) :
    JInterpolationSpace C.ι₀ C.ι₁ θ q →ₗ[𝕜] JInterpolationSpace D.ι₀ D.ι₁ θ q :=
  ((T.sumMap : sum C.ι₀ C.ι₁ →ₗ[𝕜] sum D.ι₀ D.ι₁).comp
    (jInterpolationSubmodule C.ι₀ C.ι₁ θ q).subtype).codRestrict _ (by
      intro a
      change jInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap (a : sum C.ι₀ C.ι₁)) < ⊤
      have ha : jInterpolationENorm C.ι₀ C.ι₁ θ q (a : sum C.ι₀ C.ι₁) < ⊤ := a.2
      have h₀ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₀
      have h₁ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₁
      exact (T.jInterpolationENorm_sumMap_le θ (Fact.out : 0 < θ).le q _ _ (by linarith)
        (by linarith) (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_right zero_le_one)
          a).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha))

omit [Fact (θ < 1)] [Fact (0 < q)] in
theorem norm_jInterpolationMapₗ_le (T : C ⟶ D) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ‖T.f₀‖ₒₚ ≤ M₀) (h₁ : ‖T.f₁‖ₒₚ ≤ M₁)
    (a : JInterpolationSpace C.ι₀ C.ι₁ θ q) :
    ‖T.jInterpolationMapₗ θ q a‖ ≤ 2 * (M₀ ^ (1 - θ) * M₁ ^ θ) * ‖a‖ := by
  have ha : jInterpolationENorm C.ι₀ C.ι₁ θ q (a : sum C.ι₀ C.ι₁) < ⊤ := a.2
  have hb := T.jInterpolationENorm_sumMap_le θ (Fact.out : 0 < θ).le q M₀ M₁ hM₀ hM₁ h₀ h₁
    (a : sum C.ι₀ C.ι₁)
  have hM : 0 ≤ 2 * (M₀ ^ (1 - θ) * M₁ ^ θ) := by positivity
  rw [JInterpolationSpace.norm_def, JInterpolationSpace.norm_def]
  change (jInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap (a : sum C.ι₀ C.ι₁))).toReal ≤ _
  calc (jInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap (a : sum C.ι₀ C.ι₁))).toReal
      ≤ (ENNReal.ofReal (2 * (M₀ ^ (1 - θ) * M₁ ^ θ)) *
          jInterpolationENorm C.ι₀ C.ι₁ θ q (a : sum C.ι₀ C.ι₁)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.ne) hb
    _ = 2 * (M₀ ^ (1 - θ) * M₁ ^ θ) * (jInterpolationENorm C.ι₀ C.ι₁ θ q a).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-- The map `(C.A₀, C.A₁)_{θ,q;J} → (D.A₀, D.A₁)_{θ,q;J}` induced by a morphism of couples: the
restriction of `T.sumMap`, bounded by `jInterpolationENorm_sumMap_le`. -/
noncomputable def jInterpolationMap (T : C ⟶ D) :
    JInterpolationSpace C.ι₀ C.ι₁ θ q →L[𝕜] JInterpolationSpace D.ι₀ D.ι₁ θ q where
  toLinearMap := T.jInterpolationMapₗ θ q
  cont := by
    have h₀ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₀
    have h₁ := QuasinormedAddCommGroup.opQuasiNorm_nonneg T.f₁
    exact QuasinormedAddCommGroup.continuous_of_bound (T.jInterpolationMapₗ θ q).toAddMonoidHom
      _ (T.norm_jInterpolationMapₗ_le θ q (by linarith) (by linarith)
        (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_right zero_le_one))

theorem toSum_comp_jInterpolationMap (T : C ⟶ D) :
    (JInterpolationSpace.toSum D.ι₀ D.ι₁ θ q).comp (T.jInterpolationMap θ q) =
      T.sumMap.comp (JInterpolationSpace.toSum C.ι₀ C.ι₁ θ q) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem jInterpolationMap_id (C : InterpolationCat 𝕜) :
    (𝟙 C : C ⟶ C).jInterpolationMap θ q = ContinuousLinearMap.id 𝕜 _ := by
  refine ContinuousLinearMap.ext fun a => Subtype.ext ?_
  change (𝟙 C : C ⟶ C).sumMap (a : sum C.ι₀ C.ι₁) = a
  rw [Hom.sumMap_id]
  rfl

theorem jInterpolationMap_comp (φ : C ⟶ D) (ψ : D ⟶ E) :
    (φ ≫ ψ).jInterpolationMap θ q =
      (ψ.jInterpolationMap θ q).comp (φ.jInterpolationMap θ q) := by
  refine ContinuousLinearMap.ext fun a => Subtype.ext ?_
  change (φ ≫ ψ).sumMap (a : sum C.ι₀ C.ι₁) = ψ.sumMap (φ.sumMap (a : sum C.ι₀ C.ι₁))
  rw [Hom.sumMap_comp]
  rfl

/-- The discrete J-method is of type `θ` up to the factor `2`: if `‖T.f₀‖ ≤ M₀` and
`‖T.f₁‖ ≤ M₁`, the induced map has quasinorm at most `2 M₀^{1-θ} M₁^θ`. -/
theorem norm_jInterpolationMap_le (T : C ⟶ D) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ‖T.f₀‖ₒₚ ≤ M₀) (h₁ : ‖T.f₁‖ₒₚ ≤ M₁)
    (a : JInterpolationSpace C.ι₀ C.ι₁ θ q) :
    ‖T.jInterpolationMap θ q a‖ ≤ 2 * (M₀ ^ (1 - θ) * M₁ ^ θ) * ‖a‖ :=
  T.norm_jInterpolationMapₗ_le θ q hM₀ hM₁ h₀ h₁ a

end InterpolationCat.Hom
