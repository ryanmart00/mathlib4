/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.KFunctional
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Real interpolation spaces via the K-functional

Unit 4 of the quasi-Banach generalization of the interpolation-couple framework (see
`PROGRESS-interpolation-theory.md`) — DONE, zero sorries.

Lives in its own `KMethod` directory (alongside `KFunctional.lean`), rather than folded into
`KFunctional.lean` itself, on the expectation that other real-interpolation methods (e.g. the
L-method) will eventually get their own sibling directories/files.

## Main definitions

* `InterpolationCouple.realInterpolationENorm`: Triebel §1.3.2's `(θ,q)`-quasinorm,
  `(∫₀^∞ (t^{-θ}K(t,a))^q dt/t)^{1/q}` for `q < ∞`, `sup_{t>0} t^{-θ}K(t,a)` for `q = ∞`.
  `ℝ≥0∞`-valued (mirroring Mathlib's own `eLpNorm`), so it can genuinely be infinite for an `a`
  that doesn't belong to the space, rather than being an always-finite `ℝ` that would need some
  other way to express non-membership.
The space `(A₀,A₁)_{θ,q}` itself, with its quasi-Banach structure, is built in
`KMethod/RealInterpolationSpace.lean`, and the K-method interpolation functor in
`KMethod/KInterpolationFunctor.lean`.

## Main theorems (all proved)

* `realInterpolationENorm_meetToSum_lt_top`: the "`A₀∩A₁` embeds" half of Triebel's sandwich
  `A₀∩A₁ ⊂ (A₀,A₁)_{θ,q} ⊂ A₀+A₁`.
* `realInterpolationENorm_add_le`: the quasi-triangle inequality for `realInterpolationENorm`,
  the fact that actually makes `RealInterpolationSpace` a quasi-normed group once instances are
  built.
* `realInterpolationENorm_sumMap_le`: the K-method's type-`θ` transformation property lifted from
  the K-functional's own naturality lemma (`InterpolationCat.Hom.kFunctional_sumMap_le`,
  `KFunctional.lean`) to the `(θ,q)`-quasinorm — Triebel §1.3.3's "exact interpolation functor of
  type `θ`" claim, in inequality form.
* `InterpolationCat.Hom.realInterpolationENorm_iso_le`: Unit 5's two-sided quasi-norm-equivalence
  transport corollary, lifted from `kFunctional_iso_le` (`KFunctional.lean`).
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

/-- The `(θ,q)` real-interpolation quasinorm built from the K-functional (Triebel §1.3.2):
`(∫₀^∞ (t^{-θ}K(t,a))^q dt/t)^{1/q}` for `q < ∞`, `sup_{t>0} t^{-θ}K(t,a)` for `q = ∞`. The `q = ⊤`
case is genuinely special-cased (not folded into the general formula by relying on
`(⊤ : ℝ≥0∞).toReal = 0`) — that shortcut is what `Lorentz/Marcinkiewicz.lean`'s existing (draft,
unproved) `lorentzRealInterpolationNorm` does, and it's wrong: with every exponent silently
becoming `0`, that formula collapses to the constant `1` for every `a` when `q = ⊤`, not the
intended supremum. Worth fixing there too when `Lorentz/Marcinkiewicz.lean` is eventually rewritten
against this file (Unit 6). -/
noncomputable def InterpolationCouple.realInterpolationENorm (θ : ℝ) (q : ℝ≥0∞)
    (a : InterpolationCouple.sum ι₀ ι₁) : ℝ≥0∞ :=
  if q = ⊤ then
    ⨆ t : Ioi (0 : ℝ), ENNReal.ofReal ((t : ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a)
  else
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a) ^ q.toReal *
        ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal

/-- Algebraic identity combining a power-law bound `t^p·C` on the K-functional with the `dt/t`
weight into a single power of `t`: `ofReal(t^p·C)^n · ofReal(t⁻¹) = ofReal(C^n) · ofReal(t^{pn-1})`.
Purely `rpow`/`ENNReal` algebra, not specific to interpolation theory. -/
theorem InterpolationCouple.rpow_pow_dtOverT_eq {t p C n : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hn : 0 ≤ n) :
    ENNReal.ofReal (t ^ p * C) ^ n * ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (C ^ n) * ENNReal.ofReal (t ^ (p * n - 1)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hn, Real.mul_rpow (Real.rpow_nonneg ht.le _) hC,
    ← Real.rpow_mul ht.le, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [mul_right_comm, ← Real.rpow_neg_one t, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    ← Real.rpow_add ht, show p * n + -1 = p * n - 1 by ring]
  rw [mul_comm (ENNReal.ofReal (C ^ n))]

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The K-functional, extended to all of `ℝ` via `max t 0`, is globally measurable — monotone
(via `kFunctional_mono`, itself only proved on `t ≥ 0`) composed with the globally-monotone `max
· 0`. `K` itself is *not* known to be measurable on all of `ℝ` (its behaviour for `t < 0` was never
pinned down), so this `max`-extended stand-in, agreeing with `K` exactly on `Ioi 0`
(`kFunctional_max_eq`), is used wherever a *globally* measurable stand-in for `K` is needed on a
`Set.Ioi 0`-restricted integral or supremum. -/
theorem InterpolationCouple.kFunctional_max_measurable
    (a : InterpolationCouple.sum ι₀ ι₁) :
    Measurable (fun t : ℝ => InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) a) := by
  have hmono : Monotone (fun t : ℝ =>
      InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) a) := by
    intro s t hst
    exact InterpolationCouple.kFunctional_mono ι₀ ι₁ (le_max_right s 0)
      (max_le_max hst le_rfl) a
  exact Monotone.measurable hmono

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_max_eq
    (a : InterpolationCouple.sum ι₀ ι₁) {t : ℝ} (ht : 0 < t) :
    InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) a =
      InterpolationCouple.KFunctional ι₀ ι₁ t a := by
  rw [max_eq_left ht.le]

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `q = ⊤` case of `realInterpolationENorm_meetToSum_lt_top`: for `a` in the meet, `K(t,a)` is
bounded by `min(‖a₀‖, t‖a₁‖)` (via either representation of the same ambient point,
`inl₀_fst_eq_inl₁_snd`), so `t^{-θ}K(t,a) ≤ max(‖a₀‖,‖a₁‖)` uniformly (split at `t = 1`), giving a
finite bound on the `q = ⊤` supremum directly, with no integrability argument needed. -/
theorem InterpolationCouple.meetToSum_lt_top_of_eq_top (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (a₀ : A₀) (a₁ : A₁) (ha : (a₀, a₁) ∈ InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ ⊤
      (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) < ⊤ := by
  have hb0 : ∀ t : ℝ, 0 ≤ t → InterpolationCouple.KFunctional ι₀ ι₁ t
      (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ ‖a₀‖ := by
    intro t ht
    rw [InterpolationCouple.meetToSum_apply, InterpolationCouple.inl₀_eq_mk]
    have h := csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht
      (Submodule.Quotient.mk (a₀, 0))) ⟨a₀, 0, rfl, rfl⟩
    rw [QuasinormedAddCommGroup.norm_zero, mul_zero, add_zero] at h
    exact h
  have hb1 : ∀ t : ℝ, 0 ≤ t → InterpolationCouple.KFunctional ι₀ ι₁ t
      (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ t * ‖a₁‖ := by
    intro t ht
    have ha' := ha
    rw [InterpolationCouple.mem_meet_iff] at ha'
    rw [InterpolationCouple.meetToSum_apply,
      InterpolationCouple.inl₀_fst_eq_inl₁_snd ι₀ ι₁ ha', InterpolationCouple.inl₁_eq_mk]
    have h := csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht
      (Submodule.Quotient.mk (0, a₁))) ⟨0, a₁, rfl, rfl⟩
    rw [QuasinormedAddCommGroup.norm_zero, zero_add] at h
    exact h
  unfold InterpolationCouple.realInterpolationENorm
  simp only [ite_true]
  have hbound : (⨆ t : ↥(Ioi (0:ℝ)), ENNReal.ofReal ((t:ℝ) ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ)
        (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩))) ≤
      ENNReal.ofReal (max ‖a₀‖ ‖a₁‖) := by
    apply iSup_le
    intro t
    apply ENNReal.ofReal_le_ofReal
    have ht : (0:ℝ) < t := t.2
    rcases le_total (t:ℝ) 1 with hle | hlt
    · have hK : InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ)
          (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ (t:ℝ) * ‖a₁‖ := hb1 t ht.le
      have hnn : (0:ℝ) ≤ (t:ℝ) ^ (-θ) := Real.rpow_nonneg ht.le _
      calc (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ)
            (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)
          ≤ (t:ℝ) ^ (-θ) * ((t:ℝ) * ‖a₁‖) := mul_le_mul_of_nonneg_left hK hnn
        _ = (t:ℝ) ^ (1 - θ) * ‖a₁‖ := by
            have hrw : (t:ℝ) ^ (-θ) * (t:ℝ) = (t:ℝ) ^ (1 - θ) := by
              rw [show (1:ℝ) - θ = -θ + 1 by ring, Real.rpow_add ht, Real.rpow_one]
            rw [← mul_assoc, hrw]
        _ ≤ 1 * ‖a₁‖ := by
            apply mul_le_mul_of_nonneg_right _ (QuasinormedAddCommGroup.norm_nonneg a₁)
            exact Real.rpow_le_one ht.le hle (by linarith)
        _ = ‖a₁‖ := one_mul _
        _ ≤ max ‖a₀‖ ‖a₁‖ := le_max_right _ _
    · have hK : InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ)
          (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ ‖a₀‖ := hb0 t ht.le
      have hnn : (0:ℝ) ≤ (t:ℝ) ^ (-θ) := Real.rpow_nonneg ht.le _
      calc (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ)
            (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)
          ≤ (t:ℝ) ^ (-θ) * ‖a₀‖ := mul_le_mul_of_nonneg_left hK hnn
        _ ≤ 1 * ‖a₀‖ := by
            apply mul_le_mul_of_nonneg_right _ (QuasinormedAddCommGroup.norm_nonneg a₀)
            exact Real.rpow_le_one_of_one_le_of_nonpos hlt (by linarith)
        _ = ‖a₀‖ := one_mul _
        _ ≤ max ‖a₀‖ ‖a₁‖ := le_max_left _ _
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `q < ⊤` case of `realInterpolationENorm_meetToSum_lt_top`: split the `dt/t`-integral at `t = 1`
and bound each piece by an integrable power of `t` (`t^{(1-θ)q-1}` near `0` needs `θ < 1`,
`t^{-θq-1}` near `∞` needs `θ > 0`), using `rpow_pow_dtOverT_eq` to fold the K-functional bound and
the `dt/t` weight into a single power. -/
theorem InterpolationCouple.meetToSum_lt_top_of_ne_top (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (q : ℝ≥0∞) (hq0 : 0 < q) (hqtop : q ≠ ⊤) (a₀ : A₀) (a₁ : A₁)
    (ha : (a₀, a₁) ∈ InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q
      (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) < ⊤ := by
  have hb0 : ∀ t : ℝ, 0 ≤ t → InterpolationCouple.KFunctional ι₀ ι₁ t
      (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ ‖a₀‖ := by
    intro t ht
    rw [InterpolationCouple.meetToSum_apply, InterpolationCouple.inl₀_eq_mk]
    have h := csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht
      (Submodule.Quotient.mk (a₀, 0))) ⟨a₀, 0, rfl, rfl⟩
    rw [QuasinormedAddCommGroup.norm_zero, mul_zero, add_zero] at h
    exact h
  have hb1 : ∀ t : ℝ, 0 ≤ t → InterpolationCouple.KFunctional ι₀ ι₁ t
      (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ t * ‖a₁‖ := by
    intro t ht
    have ha' := ha
    rw [InterpolationCouple.mem_meet_iff] at ha'
    rw [InterpolationCouple.meetToSum_apply,
      InterpolationCouple.inl₀_fst_eq_inl₁_snd ι₀ ι₁ ha', InterpolationCouple.inl₁_eq_mk]
    have h := csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht
      (Submodule.Quotient.mk (0, a₁))) ⟨0, a₁, rfl, rfl⟩
    rw [QuasinormedAddCommGroup.norm_zero, zero_add] at h
    exact h
  have hqtoreal : 0 < q.toReal := ENNReal.toReal_pos hq0.ne' hqtop
  have hqinvtoreal : 0 ≤ q⁻¹.toReal := ENNReal.toReal_nonneg
  unfold InterpolationCouple.realInterpolationENorm
  simp only [hqtop, ite_false]
  suffices hfin : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ t
        (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal *
        ENNReal.ofReal t⁻¹ < ⊤ by
    rw [← ENNReal.ofReal_toReal hfin.ne,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hqinvtoreal]
    exact ENNReal.ofReal_lt_top
  have hle1 : ∀ t ∈ Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ t
        (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal * ENNReal.ofReal t⁻¹ ≤
      ENNReal.ofReal (‖a₁‖ ^ q.toReal) * ENNReal.ofReal (t ^ ((1 - θ) * q.toReal - 1)) := by
    rintro t ⟨ht0, ht1⟩
    rw [← InterpolationCouple.rpow_pow_dtOverT_eq (p := 1 - θ) ht0
      (QuasinormedAddCommGroup.norm_nonneg a₁) hqtoreal.le]
    have hreal : t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t
          (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ t ^ (1 - θ) * ‖a₁‖ := by
      have hK := hb1 t ht0.le
      have hnn : (0:ℝ) ≤ t ^ (-θ) := Real.rpow_nonneg ht0.le _
      calc t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t
            (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)
          ≤ t ^ (-θ) * (t * ‖a₁‖) := mul_le_mul_of_nonneg_left hK hnn
        _ = t ^ (1 - θ) * ‖a₁‖ := by
            have hrw : t ^ (-θ) * t = t ^ (1 - θ) := by
              rw [show (1:ℝ) - θ = -θ + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
            rw [← mul_assoc, hrw]
    gcongr
  have hle2 : ∀ t ∈ Ioi (1:ℝ), ENNReal.ofReal (t ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ t
        (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal * ENNReal.ofReal t⁻¹ ≤
      ENNReal.ofReal (‖a₀‖ ^ q.toReal) * ENNReal.ofReal (t ^ (-θ * q.toReal - 1)) := by
    intro t ht1
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht1
    rw [← InterpolationCouple.rpow_pow_dtOverT_eq (p := -θ) ht0
      (QuasinormedAddCommGroup.norm_nonneg a₀) hqtoreal.le]
    have hreal : t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t
          (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩) ≤ t ^ (-θ) * ‖a₀‖ := by
      have hK := hb0 t ht0.le
      have hnn : (0:ℝ) ≤ t ^ (-θ) := Real.rpow_nonneg ht0.le _
      exact mul_le_mul_of_nonneg_left hK hnn
    gcongr
  have hint1 : ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ ((1 - θ) * q.toReal - 1)) < ⊤ := by
    apply IntegrableOn.setLIntegral_lt_top
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by nlinarith))
  have hint2 : ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (t ^ (-θ * q.toReal - 1)) < ⊤ :=
    (integrableOn_Ioi_rpow_of_lt (by nlinarith) one_pos).setLIntegral_lt_top
  have hpiece1 : ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ t
        (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal *
      ENNReal.ofReal t⁻¹ < ⊤ := by
    calc ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional ι₀ ι₁ t
            (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal *
          ENNReal.ofReal t⁻¹
        ≤ ∫⁻ t in Ioc (0:ℝ) 1,
            ENNReal.ofReal (‖a₁‖ ^ q.toReal) * ENNReal.ofReal (t ^ ((1 - θ) * q.toReal - 1)) :=
          setLIntegral_mono' measurableSet_Ioc hle1
      _ = ENNReal.ofReal (‖a₁‖ ^ q.toReal) *
            ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ ((1 - θ) * q.toReal - 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint1
  have hpiece2 : ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (t ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ t
        (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal *
      ENNReal.ofReal t⁻¹ < ⊤ := by
    calc ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional ι₀ ι₁ t
            (InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩)) ^ q.toReal *
          ENNReal.ofReal t⁻¹
        ≤ ∫⁻ t in Ioi (1:ℝ),
            ENNReal.ofReal (‖a₀‖ ^ q.toReal) * ENNReal.ofReal (t ^ (-θ * q.toReal - 1)) :=
          setLIntegral_mono' measurableSet_Ioi hle2
      _ = ENNReal.ofReal (‖a₀‖ ^ q.toReal) *
            ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (t ^ (-θ * q.toReal - 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint2
  have hsplit : Ioi (0:ℝ) = Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ) := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (not_le.mp h)
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · linarith
  rw [hsplit]
  exact lt_of_le_of_lt (lintegral_union_le _ _ _) (ENNReal.add_lt_top.2 ⟨hpiece1, hpiece2⟩)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `A₀∩A₁` (viewed inside `A₀+A₁` via `meetToSum`) always has finite `(θ,q)`-quasinorm, for any
`0 < θ < 1` and `0 < q ≤ ∞` — the "`A₀∩A₁` embeds into `(A₀,A₁)_{θ,q}`" half of Triebel's sandwich.
The actual content: for `a` in the meet, `K(t,a)` is bounded by `min(‖a₀‖, t‖a₁‖)` for *either*
representation `a₀`/`a₁` of the *same* ambient point (`inl₀_fst_eq_inl₁_snd`), and
`t ↦ t^{-θ}·min(C₀, tC₁)` is integrable against `dt/t` over `(0,∞)` exactly when `0 < θ < 1` — the
elementary calculus fact this whole sandwich rests on. Split into the `q = ⊤` case
(`meetToSum_lt_top_of_eq_top`) and the `q < ⊤` case (`meetToSum_lt_top_of_ne_top`) above. -/
theorem InterpolationCouple.realInterpolationENorm_meetToSum_lt_top
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q)
    (a : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q
      (InterpolationCouple.meetToSum ι₀ ι₁ a) < ⊤ := by
  obtain ⟨⟨a₀, a₁⟩, ha⟩ := a
  by_cases hqtop : q = ⊤
  · subst hqtop
    exact InterpolationCouple.meetToSum_lt_top_of_eq_top ι₀ ι₁ θ hθ0 hθ1 a₀ a₁ ha
  · exact InterpolationCouple.meetToSum_lt_top_of_ne_top ι₀ ι₁ θ hθ0 hθ1 q hq hqtop a₀ a₁ ha

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The quasi-triangle inequality for `realInterpolationENorm`: a Minkowski-type inequality for
the `(θ,q)`-quasinorm, with some constant `C` depending on `q` and the legs' own
`quasiTriangleConst`s (in fact, not on `θ` at all — the pointwise `K`-subadditivity step is
`θ`-independent). This is what will let `RealInterpolationSpace` actually be built as a
`QuasinormedAddCommGroup` (closure of the defining subtype under `+`, plus the class's own
`norm_add_le` field).

Proof: `K(t,a+b) ≤ Ck·(K(t,a)+K(t,b))` (`kFunctional_add_le`, `Ck := max` of the legs'
`quasiTriangleConst`s) gives, pointwise in `t`, `t^{-θ}K(t,a+b) ≤ Ck·(t^{-θ}K(t,a)+t^{-θ}K(t,b))`.
For `q = ⊤` this is already enough (`sup` of a sum is at most the sum of `sup`s). For `q < ⊤`,
raise to the `q`-th power and apply `ENNReal.rpow_add_le_mul_rpow_add_rpow'` (the *unconditional*
`0 < p` generalization of Minkowski's inequality's pointwise step, via the `LpAddConst`
machinery — valid for every `p`, not just `p ≥ 1`, which is exactly what makes `0 < q < ∞`
tractable here without splitting into `q ≥ 1`/`q < 1` sub-cases) to fold the `Ck`-bound and the
sum into a single constant times `(t^{-θ}K(t,a))^q+(t^{-θ}K(t,a))^q`; integrate `dt/t`; apply the
same `rpow_add_le_mul_rpow_add_rpow'` fact a *second* time (now at the reciprocal exponent
`q⁻¹.toReal`) to pull the `1/q`-th root of a sum apart into a sum of `1/q`-th roots.

The constant is real and `≥ 1`, as needed for `QuasinormedAddCommGroup.quasiTriangleConst`. -/
theorem InterpolationCouple.exists_realInterpolationENorm_add_le (θ : ℝ) {q : ℝ≥0∞}
    (hq : 0 < q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : InterpolationCouple.sum ι₀ ι₁,
      InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        ENNReal.ofReal C * (InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q a +
          InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q b) := by
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) with hCkdef
  have hCk_pos : 0 < Ck := lt_of_lt_of_le zero_lt_one
    (le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst)
  have hpt : ∀ (a b : InterpolationCouple.sum ι₀ ι₁) (t : ℝ), 0 ≤ t →
      ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)) ≤
        ENNReal.ofReal Ck * (ENNReal.ofReal (t ^ (-θ) *
            InterpolationCouple.KFunctional ι₀ ι₁ t a) +
          ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b)) := by
    intro a b t ht
    have hK := InterpolationCouple.kFunctional_add_le ι₀ ι₁ t ht a b
    have hnn : (0:ℝ) ≤ t ^ (-θ) := Real.rpow_nonneg ht _
    have hnnKa : (0:ℝ) ≤ t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a :=
      mul_nonneg hnn (InterpolationCouple.kFunctional_nonneg ι₀ ι₁ t ht a)
    have hnnKb : (0:ℝ) ≤ t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b :=
      mul_nonneg hnn (InterpolationCouple.kFunctional_nonneg ι₀ ι₁ t ht b)
    have hrw : t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b) ≤
        Ck * (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a +
          t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b) := by
      calc t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)
          ≤ t ^ (-θ) * (Ck * (InterpolationCouple.KFunctional ι₀ ι₁ t a +
              InterpolationCouple.KFunctional ι₀ ι₁ t b)) := mul_le_mul_of_nonneg_left hK hnn
        _ = Ck * (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a +
              t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b) := by ring
    calc ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b))
        ≤ ENNReal.ofReal (Ck * (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a +
            t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b)) :=
          ENNReal.ofReal_le_ofReal hrw
      _ = ENNReal.ofReal Ck * ENNReal.ofReal (t ^ (-θ) *
            InterpolationCouple.KFunctional ι₀ ι₁ t a +
            t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b) :=
          ENNReal.ofReal_mul hCk_pos.le
      _ = ENNReal.ofReal Ck * (ENNReal.ofReal (t ^ (-θ) *
            InterpolationCouple.KFunctional ι₀ ι₁ t a) +
            ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b)) := by
          rw [ENNReal.ofReal_add hnnKa hnnKb]
  by_cases hqtop : q = ⊤
  · subst hqtop
    refine ⟨Ck, le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst,
      fun a b => ?_⟩
    unfold InterpolationCouple.realInterpolationENorm
    simp only [ite_true]
    apply iSup_le
    intro t
    have ht : (0:ℝ) < (t:ℝ) := t.2
    calc ENNReal.ofReal ((t:ℝ) ^ (-θ) *
          InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ) (a + b))
        ≤ ENNReal.ofReal Ck * (ENNReal.ofReal ((t:ℝ) ^ (-θ) *
            InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ) a) +
            ENNReal.ofReal ((t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (t:ℝ) b)) :=
          hpt a b (t:ℝ) ht.le
      _ ≤ ENNReal.ofReal Ck * ((⨆ s : Ioi (0:ℝ), ENNReal.ofReal
            ((s:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (s:ℝ) a)) +
            (⨆ s : Ioi (0:ℝ), ENNReal.ofReal
              ((s:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (s:ℝ) b))) := by
          gcongr
          · exact le_iSup (fun s : ↥(Ioi (0:ℝ)) => ENNReal.ofReal
              ((s:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (s:ℝ) a)) t
          · exact le_iSup (fun s : ↥(Ioi (0:ℝ)) => ENNReal.ofReal
              ((s:ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (s:ℝ) b)) t
  · have hq' : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    have hqinv' : 0 < q⁻¹.toReal := by
      rw [ENNReal.toReal_inv]; positivity
    set q' := q.toReal with hq'def
    set L1 := ENNReal.LpAddConst (ENNReal.ofReal q')⁻¹ with hL1def
    set L2 := ENNReal.LpAddConst (ENNReal.ofReal q⁻¹.toReal)⁻¹ with hL2def
    have hL1_pos : 0 < L1 := pos_iff_ne_zero.mpr (ENNReal.LpAddConst_ne_zero _)
    have hL1_lt_top : L1 < ⊤ := ENNReal.LpAddConst_lt_top _
    have hL2_pos : 0 < L2 := pos_iff_ne_zero.mpr (ENNReal.LpAddConst_ne_zero _)
    have hL2_lt_top : L2 < ⊤ := ENNReal.LpAddConst_lt_top _
    set K1 := ENNReal.ofReal Ck ^ q' * L1 with hK1def
    have hK1_pos : 0 < K1 := by
      apply ENNReal.mul_pos
      · exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hCk_pos) ENNReal.ofReal_ne_top).ne'
      · exact hL1_pos.ne'
    have hK1_lt_top : K1 < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.rpow_lt_top_of_nonneg hq'.le ENNReal.ofReal_ne_top
      · exact hL1_lt_top
    set C := K1 ^ q⁻¹.toReal * L2 with hCdef
    have hC_pos : 0 < C := by
      apply ENNReal.mul_pos
      · exact (ENNReal.rpow_pos hK1_pos hK1_lt_top.ne).ne'
      · exact hL2_pos.ne'
    have hC_lt_top : C < ⊤ := ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hK1_lt_top.ne) hL2_lt_top
    have hCle : C ≤ ENNReal.ofReal (max 1 C.toReal) :=
      calc C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC_lt_top.ne).symm
        _ ≤ ENNReal.ofReal (max 1 C.toReal) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
    refine ⟨max 1 C.toReal, le_max_left _ _,
      fun a b => le_trans ?_ (mul_le_mul_of_nonneg_right hCle zero_le)⟩
    set Ha : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ (max s 0) a) ^ q' with hHadef
    set Hb : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ (max s 0) b) ^ q' with hHbdef
    set Hab : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-θ) *
      InterpolationCouple.KFunctional ι₀ ι₁ (max s 0) (a + b)) ^ q' with hHabdef
    have hHa_meas : Measurable Ha :=
      (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
        (InterpolationCouple.kFunctional_max_measurable ι₀ ι₁ a))).pow_const _
    have hHb_meas : Measurable Hb :=
      (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
        (InterpolationCouple.kFunctional_max_measurable ι₀ ι₁ b))).pow_const _
    have heqA : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-θ) *
        InterpolationCouple.KFunctional ι₀ ι₁ t a) ^ q' * ENNReal.ofReal t⁻¹ =
        ∫⁻ t in Ioi (0:ℝ), Ha t * ENNReal.ofReal t⁻¹ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [hHadef]
      simp only [InterpolationCouple.kFunctional_max_eq ι₀ ι₁ a (mem_Ioi.mp ht)]
    have heqB : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-θ) *
        InterpolationCouple.KFunctional ι₀ ι₁ t b) ^ q' * ENNReal.ofReal t⁻¹ =
        ∫⁻ t in Ioi (0:ℝ), Hb t * ENNReal.ofReal t⁻¹ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [hHbdef]
      simp only [InterpolationCouple.kFunctional_max_eq ι₀ ι₁ b (mem_Ioi.mp ht)]
    have heqAB : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-θ) *
        InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)) ^ q' * ENNReal.ofReal t⁻¹ =
        ∫⁻ t in Ioi (0:ℝ), Hab t * ENNReal.ofReal t⁻¹ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [hHabdef]
      simp only [InterpolationCouple.kFunctional_max_eq ι₀ ι₁ (a + b) (mem_Ioi.mp ht)]
    unfold InterpolationCouple.realInterpolationENorm
    simp only [hqtop, ite_false, ← hq'def, heqA, heqB, heqAB]
    change (∫⁻ t in Ioi (0:ℝ), Hab t * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal ≤
      C * ((∫⁻ t in Ioi (0:ℝ), Ha t * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal +
        (∫⁻ t in Ioi (0:ℝ), Hb t * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal)
    have hptq : ∀ t ∈ Ioi (0:ℝ), Hab t ≤ K1 * (Ha t + Hb t) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      have hHab_eq : Hab t = ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)) ^ q' := by
        rw [hHabdef]; simp only [InterpolationCouple.kFunctional_max_eq ι₀ ι₁ (a + b) ht0]
      have hHa_eq : Ha t = ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional ι₀ ι₁ t a) ^ q' := by
        rw [hHadef]; simp only [InterpolationCouple.kFunctional_max_eq ι₀ ι₁ a ht0]
      have hHb_eq : Hb t = ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional ι₀ ι₁ t b) ^ q' := by
        rw [hHbdef]; simp only [InterpolationCouple.kFunctional_max_eq ι₀ ι₁ b ht0]
      rw [hHab_eq, hHa_eq, hHb_eq]
      have hstep := hpt a b t ht0.le
      have hpow : ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)) ^ q' ≤
          (ENNReal.ofReal Ck * (ENNReal.ofReal (t ^ (-θ) *
            InterpolationCouple.KFunctional ι₀ ι₁ t a) +
            ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b))) ^ q' :=
        ENNReal.rpow_le_rpow hstep hq'.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq'.le] at hpow
      calc ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)) ^ q'
          ≤ ENNReal.ofReal Ck ^ q' * (ENNReal.ofReal (t ^ (-θ) *
              InterpolationCouple.KFunctional ι₀ ι₁ t a) +
              ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b)) ^ q' := hpow
        _ ≤ ENNReal.ofReal Ck ^ q' * (L1 * (ENNReal.ofReal (t ^ (-θ) *
              InterpolationCouple.KFunctional ι₀ ι₁ t a) ^ q' +
              ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b) ^ q')) := by
            gcongr
            exact ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ hq'.le
        _ = K1 * (ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a) ^ q' +
              ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b) ^ q') := by
            rw [hK1def]; ring
    have hmeasinv : Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹) :=
      ENNReal.measurable_ofReal.comp measurable_inv
    set Ia := ∫⁻ t in Ioi (0:ℝ), Ha t * ENNReal.ofReal t⁻¹ with hIadef
    set Ib := ∫⁻ t in Ioi (0:ℝ), Hb t * ENNReal.ofReal t⁻¹ with hIbdef
    set Iab := ∫⁻ t in Ioi (0:ℝ), Hab t * ENNReal.ofReal t⁻¹ with hIabdef
    have hmulA : Measurable (fun t : ℝ => Ha t * ENNReal.ofReal t⁻¹) := hHa_meas.mul hmeasinv
    have hintstep : Iab ≤ K1 * (Ia + Ib) := by
      rw [hIadef, hIbdef, hIabdef, ← lintegral_add_left' hmulA.aemeasurable,
        ← lintegral_const_mul' _ _ hK1_lt_top.ne]
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      calc Hab t * ENNReal.ofReal t⁻¹
          ≤ K1 * (Ha t + Hb t) * ENNReal.ofReal t⁻¹ := by gcongr; exact hptq t ht
        _ = K1 * (Ha t * ENNReal.ofReal t⁻¹ + Hb t * ENNReal.ofReal t⁻¹) := by ring
    have hfinal1 := ENNReal.rpow_le_rpow hintstep hqinv'.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hqinv'.le] at hfinal1
    change Iab ^ q⁻¹.toReal ≤ C * (Ia ^ q⁻¹.toReal + Ib ^ q⁻¹.toReal)
    calc Iab ^ q⁻¹.toReal
        ≤ K1 ^ q⁻¹.toReal * (Ia + Ib) ^ q⁻¹.toReal := hfinal1
      _ ≤ K1 ^ q⁻¹.toReal * (L2 * (Ia ^ q⁻¹.toReal + Ib ^ q⁻¹.toReal)) := by
          gcongr
          exact ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ hqinv'.le
      _ = C * (Ia ^ q⁻¹.toReal + Ib ^ q⁻¹.toReal) := by
          rw [hCdef]; ring

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The quasi-triangle inequality for `realInterpolationENorm`, with a positive `ℝ≥0∞` constant;
see `exists_realInterpolationENorm_add_le` for the (stronger) real-constant form. -/
theorem InterpolationCouple.realInterpolationENorm_add_le
    (θ : ℝ) (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q) :
    ∃ C : ℝ≥0∞, 0 < C ∧ ∀ a b : InterpolationCouple.sum ι₀ ι₁,
      InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        C * (InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q a +
          InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q b) := by
  obtain ⟨C, hC, h⟩ := InterpolationCouple.exists_realInterpolationENorm_add_le ι₀ ι₁ θ hq
  exact ⟨ENNReal.ofReal C, ENNReal.ofReal_pos.mpr (by linarith), h⟩

/-- Rescale `x` by a power of `c` (any element of norm `> 1`) to land in the "shell"
`[ε/‖c‖, ε)`. Pure real-number `rpow` algebra: the identity that lets `kFunctional_sumMap_le`'s
`t ↦ t·M₁/M₀` substitution turn into the `M₀^{1-θ}M₁^θ` factor in
`realInterpolationENorm_sumMap_le`'s statement. -/
theorem InterpolationCouple.rpow_scale_identity {θ M₀ M₁ t : ℝ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (ht : 0 < t) :
    t ^ (-θ) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ) := by
  have hs : 0 < t * M₁ / M₀ := by positivity
  rw [Real.div_rpow (by positivity) hM₀.le, Real.mul_rpow ht.le hM₁.le]
  rw [Real.rpow_neg ht.le, Real.rpow_neg (by positivity), Real.rpow_neg hM₀.le]
  have h1 : M₀ ^ (1 - θ) = M₀ ^ (1:ℝ) * M₀ ^ (-θ) := by
    rw [← Real.rpow_add hM₀]; ring_nf
  rw [h1, Real.rpow_one, Real.rpow_neg hM₀.le]
  have ht' : t ^ θ ≠ 0 := (Real.rpow_pos_of_pos ht θ).ne'
  have hM₀' : M₀ ^ θ ≠ 0 := (Real.rpow_pos_of_pos hM₀ θ).ne'
  have hM₁' : M₁ ^ θ ≠ 0 := (Real.rpow_pos_of_pos hM₁ θ).ne'
  field_simp

/-- The `dt/t` measure (the Haar measure on the multiplicative group of positive reals) is
invariant under dilation `t ↦ c·t`. No such lemma (or the multiplicative-Haar-measure
infrastructure it would come from) currently exists in Mathlib for `lintegral`; proved from
scratch via the *additive* Haar measure's own dilation formula (`Real.map_volume_mul_left`) and
`MeasureTheory.setLIntegral_map`, splitting off and cancelling the resulting constant factor. -/
theorem InterpolationCouple.lintegral_Ioi_comp_mul_left_div_self {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t in Set.Ioi (0:ℝ), F (c * t) * ENNReal.ofReal t⁻¹ =
    ∫⁻ t in Set.Ioi (0:ℝ), F t * ENNReal.ofReal t⁻¹ := by
  have hg : Measurable (fun t : ℝ => c * t) := measurable_const_mul c
  have hf : Measurable (fun y : ℝ => F y * ENNReal.ofReal y⁻¹) :=
    hF.mul (ENNReal.measurable_ofReal.comp measurable_inv)
  have hs : MeasurableSet (Set.Ioi (0:ℝ)) := measurableSet_Ioi
  have hmap := MeasureTheory.setLIntegral_map (μ := volume) hs hf hg
  rw [show (fun t : ℝ => c * t) ⁻¹' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) by
    rw [preimage_const_mul_Ioi₀ (0:ℝ) hc]; simp] at hmap
  rw [Real.map_volume_mul_left (ne_of_gt hc)] at hmap
  simp only [abs_of_pos (inv_pos.2 hc)] at hmap
  rw [MeasureTheory.Measure.restrict_smul, MeasureTheory.lintegral_smul_measure,
    smul_eq_mul] at hmap
  have hrw : ∀ x : ℝ, F (c * x) * ENNReal.ofReal (c * x)⁻¹ =
      ENNReal.ofReal c⁻¹ * (F (c * x) * ENNReal.ofReal x⁻¹) := by
    intro x
    rw [mul_inv, ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hc))]
    ring
  simp only [hrw] at hmap
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmap
  have h0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have htop : ENNReal.ofReal c⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 := congrArg ((ENNReal.ofReal c⁻¹)⁻¹ * ·) hmap
  rw [ENNReal.inv_mul_cancel_left h0 htop, ENNReal.inv_mul_cancel_left h0 htop] at h1
  exact h1.symm

/-- Triebel §1.3.3's "exact interpolation functor of type `θ`" property, in inequality form: a
morphism `T : C ⟶ D` bounded by `M₀, M₁` on the legs (in the same "arbitrary upper bound" sense as
`InterpolationCat.Hom.kFunctional_sumMap_le`) scales the `(θ,q)`-quasinorm by `M₀^{1-θ}M₁^θ`.

Needs **both** `M₀ > 0` and `M₁ > 0` (unlike `kFunctional_sumMap_le`, which only needed `M₀ > 0`):
if `M₁ = 0` were allowed (a valid hypothesis choice whenever `T.f₁ ≡ 0`), the RHS collapses to `0`
(since `M₁ ^ θ = 0` for `θ > 0`, and `0 * x = 0` in `ℝ≥0∞` even for `x = ⊤`), falsely asserting
`T.sumMap a = 0` for every `a` whenever `T.f₁ ≡ 0` — false whenever `T.f₀ ≠ 0`, since then
`T.sumMap a = inl₀ (T.f₀ a₀)` is generically a nonzero (hence positive-`(θ,q)`-norm) element of
`D`'s sum space. `kFunctional_sumMap_le` doesn't have this issue since `M₁` only ever appears
*linearly* inside `K_C`'s argument there, giving a genuinely valid (if weak, `t`-independent)
bound at `M₁ = 0`, rather than a vanishing exponent. Caught while attempting this proof; matches
how the classical type-`θ` operator-norm inequality is standardly used for operators with both
leg-norms positive, the degenerate case being a recognized but usually-implicit technicality.
Signed off by Ryan.

The proof needs `θ` to be a plain real (never `0 < θ < 1`) — that hypothesis, part of the signed-off
statement, turns out unused here; it matters for `realInterpolationENorm_meetToSum_lt_top`/
`.._add_le` above, not for this one, and is kept for consistency with the rest of the `(θ,q)` API.

Proved with the help of the three lemmas above (`rpow_scale_identity`,
`lintegral_Ioi_comp_mul_left_div_self`, `kFunctional_max_measurable`/`.._max_eq`), none of which
have a Mathlib home yet — they're general facts about `rpow` algebra and the `dt/t` measure, not
specific to interpolation theory, so may be worth upstreaming separately later. -/
theorem InterpolationCat.Hom.realInterpolationENorm_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (θ : ℝ) (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.realInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap a) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
        InterpolationCouple.realInterpolationENorm C.ι₀ C.ι₁ θ q a := by
  by_cases hqtop : q = ⊤
  · subst hqtop
    unfold InterpolationCouple.realInterpolationENorm
    simp only [ite_true]
    refine iSup_le fun t => ?_
    have ht : (0:ℝ) < t := t.2
    set s : ℝ := t * M₁ / M₀ with hsdef
    have hs : 0 < s := by rw [hsdef]; positivity
    have hK : InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a) ≤
        M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a :=
      InterpolationCat.Hom.kFunctional_sumMap_le T (t:ℝ) ht.le M₀ M₁ hM₀ h₀ h₁ a
    have halg : (t:ℝ) ^ (-θ) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ * s ^ (-θ) :=
      InterpolationCouple.rpow_scale_identity hM₀ hM₁ ht
    have hnn : (0:ℝ) ≤ InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a :=
      InterpolationCouple.kFunctional_nonneg C.ι₀ C.ι₁ s hs.le a
    have hstep : (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a) ≤
        M₀ ^ (1 - θ) * M₁ ^ θ * (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := by
      have h1 : (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a) ≤
          (t:ℝ) ^ (-θ) * (M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) :=
        mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg ht.le _)
      calc (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a)
          ≤ (t:ℝ) ^ (-θ) * (M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := h1
        _ = ((t:ℝ) ^ (-θ) * M₀) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a := by ring
        _ = (M₀ ^ (1 - θ) * M₁ ^ θ * s ^ (-θ)) *
              InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a := by rw [halg]
        _ = M₀ ^ (1 - θ) * M₁ ^ θ * (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := by
            ring
    calc ENNReal.ofReal ((t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ)
        (T.sumMap a))
        ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ *
            (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a)) :=
          ENNReal.ofReal_le_ofReal hstep
      _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ENNReal.ofReal (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ⨆ s' : ↥(Ioi (0:ℝ)), ENNReal.ofReal
              ((s':ℝ) ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (s':ℝ) a) := by
          gcongr
          exact le_iSup (fun s' : ↥(Ioi (0:ℝ)) => ENNReal.ofReal
            ((s':ℝ) ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (s':ℝ) a)) ⟨s, hs⟩
  · set c : ℝ := M₁ / M₀ with hcdef
    have hc : 0 < c := by rw [hcdef]; positivity
    set H : ℝ → ℝ≥0∞ :=
      fun s => ENNReal.ofReal (s ^ (-θ) *
        InterpolationCouple.KFunctional C.ι₀ C.ι₁ (max s 0) a) ^ q.toReal with hHdef
    have hHmeas : Measurable H := by
      rw [hHdef]
      exact (ENNReal.measurable_ofReal.comp
        ((measurable_id.pow_const _).mul
          (InterpolationCouple.kFunctional_max_measurable C.ι₀ C.ι₁ a))).pow_const _
    have heqC : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ t a) ^
          q.toReal * ENNReal.ofReal t⁻¹ = ∫⁻ t in Set.Ioi (0:ℝ), H t * ENNReal.ofReal t⁻¹ := by
      apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [hHdef]
      simp only [InterpolationCouple.kFunctional_max_eq C.ι₀ C.ι₁ a (Set.mem_Ioi.mp ht)]
    unfold InterpolationCouple.realInterpolationENorm
    simp only [hqtop, ite_false, heqC]
    have hqtoreal : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    have hqinvtoreal : 0 ≤ q⁻¹.toReal := ENNReal.toReal_nonneg
    have hMq : ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal =
        ENNReal.ofReal ((M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hqtoreal.le
    have hstep1 : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ^
          q.toReal * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal *
          ∫⁻ t in Set.Ioi (0:ℝ), H (c * t) * ENNReal.ofReal t⁻¹ := by
      rw [hMq, ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply MeasureTheory.setLIntegral_mono' measurableSet_Ioi
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      have hreal : t ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
          M₀ ^ (1 - θ) * M₁ ^ θ * ((c * t) ^ (-θ) *
            InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a) := by
        have hK : InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
            M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a :=
          InterpolationCat.Hom.kFunctional_sumMap_le T t ht0.le M₀ M₁ hM₀ h₀ h₁ a
        have hcalc : c * t = t * M₁ / M₀ := by rw [hcdef]; ring
        rw [hcalc]
        have hnn : (0:ℝ) ≤ InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a :=
          InterpolationCouple.kFunctional_nonneg C.ι₀ C.ι₁ (t * M₁ / M₀) (by positivity) a
        calc t ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)
            ≤ t ^ (-θ) * (M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a) :=
              mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg ht0.le _)
          _ = (t ^ (-θ) * M₀) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a := by
              ring
          _ = (M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ)) *
                InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a := by
              rw [InterpolationCouple.rpow_scale_identity hM₀ hM₁ ht0]
          _ = M₀ ^ (1 - θ) * M₁ ^ θ * ((t * M₁ / M₀) ^ (-θ) *
                InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a) := by ring
      have hENN : ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ≤
          ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ENNReal.ofReal ((c * t) ^ (-θ) *
              InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hreal
      have hpow : ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ^ q.toReal ≤
          (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ENNReal.ofReal ((c * t) ^ (-θ) *
              InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a)) ^ q.toReal :=
        ENNReal.rpow_le_rpow hENN hqtoreal.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqtoreal.le, hMq] at hpow
      calc ENNReal.ofReal (t ^ (-θ) *
            InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ^ q.toReal *
            ENNReal.ofReal t⁻¹
          ≤ (ENNReal.ofReal ((M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) *
              ENNReal.ofReal ((c * t) ^ (-θ) *
                InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a) ^ q.toReal) *
            ENNReal.ofReal t⁻¹ := by gcongr
        _ = ENNReal.ofReal ((M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) *
            (H (c * t) * ENNReal.ofReal t⁻¹) := by
            have hct : max (c * t) 0 = c * t := max_eq_left (by positivity)
            rw [hHdef]; simp only [hct]; ring
    rw [InterpolationCouple.lintegral_Ioi_comp_mul_left_div_self hc hHmeas] at hstep1
    have hfinal := ENNReal.rpow_le_rpow hstep1 hqinvtoreal
    rw [ENNReal.mul_rpow_of_nonneg _ _ hqinvtoreal] at hfinal
    have hconst : (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) ^ q⁻¹.toReal =
        ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) := by
      rw [← ENNReal.rpow_mul]
      have : q.toReal * q⁻¹.toReal = 1 := by
        rw [ENNReal.toReal_inv]
        exact mul_inv_cancel₀ hqtoreal.ne'
      rw [this, ENNReal.rpow_one]
    rwa [hconst] at hfinal

/-- Unit 5's promised "transport" payoff, lifted from `kFunctional_iso_le` to the `(θ,q)`-
quasinorm: a couple-level quasi-norm equivalence (`e : C ≅ D` in `InterpolationCat 𝕜`) bounds
`realInterpolationENorm` in *both* directions, by applying `realInterpolationENorm_sumMap_le` to
`e.hom` and separately to `e.inv`. In particular (not stated separately, since it's an immediate
corollary of either inequality having a finite RHS iff its LHS is finite): `a` has finite
`(θ,q)`-quasinorm in `C` iff `e.hom.sumMap a` does in `D` — i.e. `e.hom.sumMap` restricts to a map
between the two `RealInterpolationSpace`s. STATEMENT ONLY — proof deferred. -/
theorem InterpolationCat.Hom.realInterpolationENorm_iso_le {C D : InterpolationCat 𝕜} (e : C ≅ D)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q)
    (M₀ M₁ N₀ N₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hN₀ : 0 < N₀) (hN₁ : 0 < N₁)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm e.hom.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm e.hom.f₁ ≤ M₁)
    (g₀ : QuasinormedAddCommGroup.opQuasiNorm e.inv.f₀ ≤ N₀)
    (g₁ : QuasinormedAddCommGroup.opQuasiNorm e.inv.f₁ ≤ N₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.realInterpolationENorm D.ι₀ D.ι₁ θ q (e.hom.sumMap a) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
        InterpolationCouple.realInterpolationENorm C.ι₀ C.ι₁ θ q a ∧
    InterpolationCouple.realInterpolationENorm C.ι₀ C.ι₁ θ q a ≤
      ENNReal.ofReal (N₀ ^ (1 - θ) * N₁ ^ θ) *
        InterpolationCouple.realInterpolationENorm D.ι₀ D.ι₁ θ q (e.hom.sumMap a) := by
  have hcomp := congrArg InterpolationCat.Hom.sumMap e.hom_inv_id
  rw [InterpolationCat.Hom.sumMap_comp, InterpolationCat.Hom.sumMap_id] at hcomp
  have hinv : e.inv.sumMap (e.hom.sumMap a) = a := by
    have := DFunLike.congr_fun hcomp a
    simpa using this
  refine ⟨InterpolationCat.Hom.realInterpolationENorm_sumMap_le e.hom θ hθ0 hθ1 q hq
    M₀ M₁ hM₀ hM₁ h₀ h₁ a, ?_⟩
  have hstep := InterpolationCat.Hom.realInterpolationENorm_sumMap_le e.inv θ hθ0 hθ1 q hq
    N₀ N₁ hN₀ hN₁ g₀ g₁ (e.hom.sumMap a)
  rwa [hinv] at hstep
