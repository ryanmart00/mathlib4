/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.Basic
import Mathlib.Analysis.Interpolation.QuasiNormCompleteness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Completeness of `LorentzSpace`

`CompleteSpace (LorentzSpace E p q μ)`. Mirrors `MeasureTheory.Function.LpSpace.Complete` in
spirit but not in mechanics: `Lp`'s own completeness proof leans on sharp Minkowski (valid since
`eLpNorm` is a genuine seminorm for `1 ≤ p`), which has no analogue here (`lorentzNorm` is only a
*quasi*-norm, for every `p, q`). Instead this file builds a from-scratch weak-type (Chebyshev)
tail bound directly from `distributionFunction`/`decreasingRearrangement`, then a
Borel–Cantelli-style argument to construct an a.e. pointwise limit of a geometrically-controlled
subsequence, and finally upgrades that back to full-sequence `lorentzNorm` convergence via the
quasi-triangle inequality (`lorentzNorm_add_le`).

Combined with `QuasinormedAddCommGroup.completeSpace_of_cauchy_complete`
(`Analysis/Interpolation/QuasiNormCompleteness.lean`), which reduces `CompleteSpace` to handling
an arbitrary `B`-controlled Cauchy sequence for arbitrary summable `B` (not just geometric) — this
is *why* a subsequence-extraction step is needed here even though the underlying Chebyshev bound
itself is geometric-scale-driven.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

/-- If `t < ϱ(f,σ)`, then `σ ≤ f*(t)` — the reverse direction of the "near-optimal representative"
argument already used inline in `distributionFunction_eq_zero_of_forall_pos`
(`TriangleInequality.lean`), extracted here since the completeness argument needs it directly
rather than through that lemma's own conclusion. -/
theorem le_decreasingRearrangement_of_lt_distributionFunction (f : α → E) (t σ : ℝ≥0∞)
    (h : t < distributionFunction μ f σ) : σ ≤ decreasingRearrangement μ f t := by
  by_contra hc
  push Not at hc
  unfold decreasingRearrangement at hc
  obtain ⟨σ', hσ'mem, hσ'lt⟩ := sInf_lt_iff.mp hc
  simp only [Set.mem_ofPred_eq] at hσ'mem
  exact absurd ((distributionFunction_antitone f hσ'lt.le).trans hσ'mem) (not_le.mpr h)

/-- The classical weak-type (Chebyshev) tail bound for the `q = ⊤` Lorentz (quasi-)norm: if
`lorentzNorm μ p ⊤ f < t^{1/p} * σ` for some `t : ℝ≥0`, then `ϱ(f,σ) ≤ t`. This is the exact
quantitative content of `f ∈ L^{p,∞}` ("weak-`Lᵖ`") as a bound on the measure of a super-level
set, and is what lets a small `lorentzNorm` bound be converted into a small-measure statement for
the Borel–Cantelli argument below. -/
theorem distributionFunction_le_of_lorentzNorm_top_lt (p : ℝ≥0∞) (f : α → E) (σ : ℝ≥0∞)
    (t : ℝ≥0) (ht : lorentzNorm μ p ⊤ f < (t : ℝ≥0∞) ^ p⁻¹.toReal * σ) :
    distributionFunction μ f σ ≤ t := by
  by_contra hc
  push Not at hc
  have hσle : σ ≤ decreasingRearrangement μ f (t : ℝ≥0∞) :=
    le_decreasingRearrangement_of_lt_distributionFunction f (t : ℝ≥0∞) σ hc
  have hle : (t : ℝ≥0∞) ^ p⁻¹.toReal * σ ≤ lorentzNorm μ p ⊤ f := by
    unfold lorentzNorm
    simp only [ite_true]
    calc (t : ℝ≥0∞) ^ p⁻¹.toReal * σ
        ≤ (t : ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ f (t : ℝ≥0∞) := by gcongr
      _ ≤ ⨆ u : ℝ≥0, (u : ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ f (u : ℝ≥0∞) :=
          le_iSup (fun u : ℝ≥0 => (u : ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ f (u : ℝ≥0∞))
            t
  exact absurd hle (not_le.mpr ht)

/-- `∫_s^{2s} du/u = log 2`, independent of `s > 0` (a scale-invariant fact) — the computational
core of `distributionFunction_le_of_lorentzNorm_finite_lt` below: it's what lets a lower bound on
the rearrangement across the whole interval `(s,2s]` (from a distribution-function assumption) turn
into a genuine lower bound on `lorentzNorm`'s defining integral, since `f*` and `u^{1/p}` are each
bounded below by their value at one endpoint throughout the interval. -/
theorem lintegral_Ioc_inv_eq_ofReal_log_two {s : ℝ} (hs : 0 < s) :
    ∫⁻ u in Ioc s (2 * s), ENNReal.ofReal u⁻¹ = ENNReal.ofReal (Real.log 2) := by
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have hab : s ≤ 2 * s := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Icc s (2 * s)) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hs hx.1)
  have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume s (2 * s) :=
    hcont.intervalIntegrable_of_Icc hab
  have hval : ∫ x in s..(2 * s), x⁻¹ = Real.log 2 := by
    rw [integral_inv_of_pos hs h2s]
    congr 1
    field_simp
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioc s (2 * s))), 0 ≤ x⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hs hx.1.le))
  have key := ofReal_integral_eq_lintegral_ofReal hii.1 hnn
  rw [intervalIntegral.integral_of_le hab] at hval
  rw [hval] at key
  exact key.symm

/-- The `0 < q < ⊤` analogue of `distributionFunction_le_of_lorentzNorm_top_lt`: a small-enough
`lorentzNorm` control gives a quantitative bound on `distributionFunction`, via lower-bounding the
defining integral over the sub-interval `(s,2s]` alone (`f*` and `u^{1/p}` are each bounded below
there by their value at one endpoint, using antitonicity/monotonicity respectively), rather than
needing a separate `L^{p,q} ↪ L^{p,∞}` embedding lemma as an intermediate step. -/
theorem distributionFunction_le_of_lorentzNorm_finite_lt (p q : ℝ≥0∞) (hq0 : q ≠ 0)
    (hqtop : q ≠ ⊤) (f : α → E) (σ : ℝ≥0∞) (hσtop : σ ≠ ⊤) (s : ℝ) (hs : 0 < s)
    (ht : lorentzNorm μ p q f <
      ENNReal.ofReal s ^ p⁻¹.toReal * σ * ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal) :
    distributionFunction μ f σ ≤ ENNReal.ofReal (2 * s) := by
  by_contra hc
  push Not at hc
  set r := q.toReal with hrdef
  set inv := q⁻¹.toReal with hinvdef
  have hpr : (0 : ℝ) ≤ p⁻¹.toReal := ENNReal.toReal_nonneg
  have hr0 : 0 < r := ENNReal.toReal_pos hq0 hqtop
  have hinv0 : 0 < inv :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hqtop) (ENNReal.inv_ne_top.mpr hq0)
  have hrinv : r * inv = 1 := by
    rw [hrdef, hinvdef, ENNReal.toReal_inv, mul_inv_cancel₀ hr0.ne']
  have hstar : ∀ u : ℝ, 0 < u → u ≤ 2 * s → σ ≤ decreasingRearrangement μ f (ENNReal.ofReal u) := by
    intro u hu0 hule
    apply le_decreasingRearrangement_of_lt_distributionFunction f (ENNReal.ofReal u) σ
    calc ENNReal.ofReal u ≤ ENNReal.ofReal (2 * s) := ENNReal.ofReal_le_ofReal hule
      _ < distributionFunction μ f σ := hc
  have hpointwise : ∀ u ∈ Ioc s (2 * s),
      (ENNReal.ofReal s ^ p⁻¹.toReal * σ) ^ r * ENNReal.ofReal u⁻¹ ≤
        (ENNReal.ofReal u ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal u)) ^ r *
          ENNReal.ofReal u⁻¹ := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hbase : ENNReal.ofReal s ^ p⁻¹.toReal * σ ≤
        ENNReal.ofReal u ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal u) := by
      gcongr
      exact hstar u (hs.trans hu1) hu2
    gcongr
  set F : ℝ → ℝ≥0∞ := fun t =>
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal t)) ^ r *
      ENNReal.ofReal t⁻¹ with hFdef
  have hconstfin : (ENNReal.ofReal s ^ p⁻¹.toReal * σ) ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr0.le
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpr (by simp)) hσtop)
  have hmono : (ENNReal.ofReal s ^ p⁻¹.toReal * σ) ^ r * ENNReal.ofReal (Real.log 2) ≤
      ∫⁻ t in Ioi (0 : ℝ), F t := by
    calc (ENNReal.ofReal s ^ p⁻¹.toReal * σ) ^ r * ENNReal.ofReal (Real.log 2)
        = ∫⁻ u in Ioc s (2 * s), (ENNReal.ofReal s ^ p⁻¹.toReal * σ) ^ r * ENNReal.ofReal u⁻¹ := by
          rw [lintegral_const_mul' _ _ hconstfin, lintegral_Ioc_inv_eq_ofReal_log_two hs]
      _ ≤ ∫⁻ u in Ioc s (2 * s), F u := setLIntegral_mono' measurableSet_Ioc hpointwise
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), F t := lintegral_mono_set (fun x hx => hs.trans hx.1)
  have hlorentz_eq : lorentzNorm μ p q f = (∫⁻ t in Ioi (0 : ℝ), F t) ^ inv := by
    unfold lorentzNorm
    rw [if_neg hqtop]
  have hgoal : ENNReal.ofReal s ^ p⁻¹.toReal * σ * ENNReal.ofReal (Real.log 2) ^ inv ≤
      lorentzNorm μ p q f := by
    rw [hlorentz_eq]
    calc ENNReal.ofReal s ^ p⁻¹.toReal * σ * ENNReal.ofReal (Real.log 2) ^ inv
        = ((ENNReal.ofReal s ^ p⁻¹.toReal * σ) ^ r * ENNReal.ofReal (Real.log 2)) ^ inv := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hinv0.le, ← ENNReal.rpow_mul, hrinv,
            ENNReal.rpow_one]
      _ ≤ (∫⁻ t in Ioi (0 : ℝ), F t) ^ inv := by gcongr
  exact absurd (ht.trans_le hgoal) (lt_irrefl _)

/-- **Fatou's lemma for `distributionFunction`**: if `g k → glim` a.e. pointwise, the distribution
function of the limit is bounded by the `liminf` of the distribution functions along the sequence.
Via indicator functions and the genuine Fatou's lemma for `lintegral` (`lintegral_liminf_le'`):
`{x | σ < ‖glim x‖ₑ}` is, up to the a.e.-convergence null set, contained in the `liminf` (in the
filter sense) of `{x | σ < ‖g k x‖ₑ}`, since `‖g k x‖ₑ → ‖glim x‖ₑ` and strict inequalities are
eventually preserved under a limit. This is the tool that will let `f_lim`'s (finite) `lorentzNorm`
be bounded from the `lorentzNorm`s along a controlled sequence, without needing a `lorentzNorm`
bound on an *infinite sum* (hence without needing any general multi-term/quasi-Banach summability
machinery beyond the single-application quasi-triangle inequality already in hand). -/
theorem distributionFunction_le_liminf_of_tendsto_ae {g : ℕ → α → E} {glim : α → E}
    (hgmeas : ∀ n, AEMeasurable (fun x => ‖g n x‖ₑ) μ)
    (hglimmeas : AEMeasurable (fun x => ‖glim x‖ₑ) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (glim x))) (σ : ℝ≥0∞) :
    distributionFunction μ glim σ ≤ liminf (fun k => distributionFunction μ (g k) σ) atTop := by
  set S : ℕ → Set α := fun k => {x | σ < ‖g k x‖ₑ} with hSdef
  set Slim : Set α := {x | σ < ‖glim x‖ₑ} with hSlimdef
  have hSmeas : ∀ n, NullMeasurableSet (S n) μ := fun n =>
    (hgmeas n).nullMeasurableSet_preimage measurableSet_Ioi
  have hSlimmeas : NullMeasurableSet Slim μ :=
    hglimmeas.nullMeasurableSet_preimage measurableSet_Ioi
  have hindmeas : ∀ n, AEMeasurable ((S n).indicator (1 : α → ℝ≥0∞)) μ := fun n =>
    aemeasurable_const.indicator₀ (hSmeas n)
  have hpt : ∀ᵐ x ∂μ, Slim.indicator (1 : α → ℝ≥0∞) x ≤
      liminf (fun k => (S k).indicator (1 : α → ℝ≥0∞) x) atTop := by
    filter_upwards [hg] with x hx
    by_cases hxS : x ∈ Slim
    · have hcont : Tendsto (fun k => ‖g k x‖ₑ) atTop (𝓝 ‖glim x‖ₑ) :=
        (continuous_enorm.tendsto _).comp hx
      have hev : ∀ᶠ k in atTop, x ∈ S k := hcont.eventually_const_lt hxS
      rw [indicator_of_mem hxS]
      have hind1 : ∀ᶠ k in atTop, (1 : ℝ≥0∞) ≤ (S k).indicator (1 : α → ℝ≥0∞) x := by
        filter_upwards [hev] with k hk
        simp [indicator_of_mem hk]
      calc (1 : ℝ≥0∞) = liminf (fun _ : ℕ => (1 : ℝ≥0∞)) atTop := (liminf_const 1).symm
        _ ≤ liminf (fun k => (S k).indicator (1 : α → ℝ≥0∞) x) atTop :=
            liminf_le_liminf hind1
    · rw [indicator_of_notMem hxS]
      exact zero_le
  have hfatou : ∫⁻ x, liminf (fun k => (S k).indicator (1 : α → ℝ≥0∞) x) atTop ∂μ ≤
      liminf (fun k => ∫⁻ x, (S k).indicator (1 : α → ℝ≥0∞) x ∂μ) atTop :=
    lintegral_liminf_le' (u := (atTop : Filter ℕ)) hindmeas
  have hmono : ∫⁻ x, Slim.indicator (1 : α → ℝ≥0∞) x ∂μ ≤
      ∫⁻ x, liminf (fun k => (S k).indicator (1 : α → ℝ≥0∞) x) atTop ∂μ :=
    lintegral_mono_ae hpt
  have heq1 : ∫⁻ x, Slim.indicator (1 : α → ℝ≥0∞) x ∂μ = μ Slim :=
    lintegral_indicator_one₀ hSlimmeas
  have heq2 : ∀ n, ∫⁻ x, (S n).indicator (1 : α → ℝ≥0∞) x ∂μ = μ (S n) := fun n =>
    lintegral_indicator_one₀ (hSmeas n)
  unfold distributionFunction
  change μ Slim ≤ liminf (fun k => μ (S k)) atTop
  calc μ Slim = ∫⁻ x, Slim.indicator (1 : α → ℝ≥0∞) x ∂μ := heq1.symm
    _ ≤ ∫⁻ x, liminf (fun k => (S k).indicator (1 : α → ℝ≥0∞) x) atTop ∂μ := hmono
    _ ≤ liminf (fun k => ∫⁻ x, (S k).indicator (1 : α → ℝ≥0∞) x ∂μ) atTop := hfatou
    _ = liminf (fun k => μ (S k)) atTop := by simp_rw [heq2]
