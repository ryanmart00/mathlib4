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
open scoped ENNReal QuasinormedAddCommGroup

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
/-- The quasi-triangle inequality for `realInterpolationENorm`, with an explicit constant: the
larger of the legs' constants (from `kFunctional_add_le`) times the `Lᵠ` constant
`ENNReal.LpAddConst q` (Minkowski's inequality in `Lᵠ(dt/t)`; it is `1` for `q ≥ 1`). In
particular the constant is `1` for normed legs and `q ≥ 1`. -/
theorem InterpolationCouple.realInterpolationENorm_add_le (θ : ℝ) {q : ℝ≥0∞} (hq : 0 < q)
    (a b : InterpolationCouple.sum ι₀ ι₁) :
    InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
      ENNReal.ofReal (max (QuasinormedAddCommGroup.quasiTriangleConst A₀)
          (QuasinormedAddCommGroup.quasiTriangleConst A₁)) * ENNReal.LpAddConst q *
        (InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q a +
          InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q b) := by
  -- B–L, Thm 3.1.2: `K(t, ·)` is a quasi-norm on `A₀ + A₁` (constant `Ck`) and `Φ_{θ,q}` is a
  -- monotone quasi-norm (constant `LpAddConst q`); compose the two.
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst A₀)
    (QuasinormedAddCommGroup.quasiTriangleConst A₁)
  have hCk : 0 ≤ Ck :=
    zero_le_one.trans (le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst)
  -- Step 1: `t^{-θ} K(t, a + b) ≤ Ck (t^{-θ} K(t, a) + t^{-θ} K(t, b))`.
  have hpt (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)) ≤
        ENNReal.ofReal Ck *
          (ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a) +
            ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t b)) := by
    have hw : 0 ≤ t ^ (-θ) := Real.rpow_nonneg ht.le _
    rw [← ENNReal.ofReal_add
      (mul_nonneg hw (InterpolationCouple.kFunctional_nonneg ι₀ ι₁ t ht.le a))
      (mul_nonneg hw (InterpolationCouple.kFunctional_nonneg ι₀ ι₁ t ht.le b)),
      ← ENNReal.ofReal_mul hCk]
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ t ^ (-θ) * (Ck * (InterpolationCouple.KFunctional ι₀ ι₁ t a +
          InterpolationCouple.KFunctional ι₀ ι₁ t b)) :=
          mul_le_mul_of_nonneg_left (InterpolationCouple.kFunctional_add_le ι₀ ι₁ t ht.le a b) hw
      _ = _ := by ring
  unfold InterpolationCouple.realInterpolationENorm
  split_ifs with hqtop
  · -- Step 2, `q = ∞`: the supremum of a sum is at most the sum of the suprema.
    subst hqtop
    rw [ENNReal.LpAddConst_of_one_le le_top, mul_one]
    refine iSup_le fun t => (hpt t t.2).trans ?_
    gcongr
    · exact le_iSup (fun s : Ioi (0 : ℝ) => ENNReal.ofReal ((s : ℝ) ^ (-θ) *
        InterpolationCouple.KFunctional ι₀ ι₁ s a)) t
    · exact le_iSup (fun s : Ioi (0 : ℝ) => ENNReal.ofReal ((s : ℝ) ^ (-θ) *
        InterpolationCouple.KFunctional ι₀ ι₁ s b)) t
  -- Step 2, `q < ∞`: Minkowski's inequality in `Lᵠ(μ)`, `μ = dt/t` on `(0, ∞)`, applied to the
  -- globally measurable stand-ins `F x t = t^{-θ} K(max t 0, x)`.
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
  rw [ENNReal.toReal_inv]
  set p := q.toReal
  set μ : Measure ℝ := (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal t⁻¹ with hμ
  set F : InterpolationCouple.sum ι₀ ι₁ → ℝ → ℝ≥0∞ := fun x t =>
    ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) x)
  have hF (x : InterpolationCouple.sum ι₀ ι₁) : Measurable (F x) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_id.pow_const _).mul (InterpolationCouple.kFunctional_max_measurable ι₀ ι₁ x))
  have hI (x : InterpolationCouple.sum ι₀ ι₁) :
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-θ) *
        InterpolationCouple.KFunctional ι₀ ι₁ t x) ^ p * ENNReal.ofReal t⁻¹ =
        ∫⁻ t, F x t ^ p ∂μ := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ (f := fun t : ℝ => ENNReal.ofReal t⁻¹)
      (ENNReal.measurable_ofReal.comp measurable_inv) ((hF x).pow_const p)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [F, Pi.mul_apply, InterpolationCouple.kFunctional_max_eq ι₀ ι₁ x ht, mul_comm]
  rw [hI, hI, hI]
  have hle : ∫⁻ t, F (a + b) t ^ p ∂μ ≤
      ENNReal.ofReal Ck ^ p * ∫⁻ t, (F a t + F b t) ^ p ∂μ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono_ae ?_
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioi)] with t ht
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    refine ENNReal.rpow_le_rpow ?_ hp.le
    simpa only [F, InterpolationCouple.kFunctional_max_eq ι₀ ι₁ _ ht] using hpt t ht
  have hmink : (∫⁻ t, (F a t + F b t) ^ p ∂μ) ^ p⁻¹ ≤ ENNReal.LpAddConst q *
      ((∫⁻ t, F a t ^ p ∂μ) ^ p⁻¹ + (∫⁻ t, F b t ^ p ∂μ) ^ p⁻¹) := by
    rw [← one_div]
    rcases le_or_gt 1 p with hp1 | hp1
    · rw [ENNReal.LpAddConst_of_one_le
        (by simpa using (ENNReal.ofReal_le_iff_le_toReal hqtop).mpr hp1), one_mul]
      exact ENNReal.lintegral_Lp_add_le (hF a).aemeasurable (hF b).aemeasurable hp1
    · have hq1 : q < 1 := (ENNReal.toReal_lt_toReal hqtop ENNReal.one_ne_top).mp
        (by rwa [ENNReal.toReal_one])
      rw [ENNReal.LpAddConst, ite_eq_left ⟨hq, hq1⟩]
      exact ENNReal.lintegral_Lp_add_le_of_le_one (hF a).aemeasurable hp.le hp1.le
  calc (∫⁻ t, F (a + b) t ^ p ∂μ) ^ p⁻¹
      ≤ (ENNReal.ofReal Ck ^ p * ∫⁻ t, (F a t + F b t) ^ p ∂μ) ^ p⁻¹ :=
        ENNReal.rpow_le_rpow hle (inv_nonneg.mpr hp.le)
    _ = ENNReal.ofReal Ck * (∫⁻ t, (F a t + F b t) ^ p ∂μ) ^ p⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le), ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ _ := by
        rw [mul_assoc]
        gcongr

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
    (h₀ : ‖T.f₀‖ₒₚ ≤ M₀) (h₁ : ‖T.f₁‖ₒₚ ≤ M₁)
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
    (h₀ : ‖e.hom.f₀‖ₒₚ ≤ M₀) (h₁ : ‖e.hom.f₁‖ₒₚ ≤ M₁)
    (g₀ : ‖e.inv.f₀‖ₒₚ ≤ N₀) (g₁ : ‖e.inv.f₁‖ₒₚ ≤ N₁)
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
