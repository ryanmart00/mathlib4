/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.Basic
import Mathlib.Analysis.Normed.Quasi.Completeness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

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
(`Analysis/Normed/Quasi/Completeness.lean`), which reduces `CompleteSpace` to handling
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
    rw [ite_eq_right hqtop]
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

/-- The reverse direction of `le_decreasingRearrangement_of_lt_distributionFunction`: if `f*(t) <
σ`, then `ϱ(f,σ) ≤ t` (a near-optimal representative `σ' < σ` from `f*(t)`'s defining `sInf`
gives `ϱ(f,σ) ≤ ϱ(f,σ') ≤ t`). Mirrors the inline argument already used in
`distributionFunction_eq_zero_of_forall_pos` (`TriangleInequality.lean`), extracted here for
`decreasingRearrangement_le_liminf_of_tendsto_ae`'s own use. -/
theorem distributionFunction_le_of_lt_decreasingRearrangement (f : α → E) (t σ : ℝ≥0∞)
    (h : decreasingRearrangement μ f t < σ) : distributionFunction μ f σ ≤ t := by
  unfold decreasingRearrangement at h
  obtain ⟨σ', hσ'mem, hσ'lt⟩ := sInf_lt_iff.mp h
  simp only [Set.mem_ofPred_eq] at hσ'mem
  exact (distributionFunction_antitone f hσ'lt.le).trans hσ'mem

/-- **Fatou's lemma for `decreasingRearrangement`**: derived from the `distributionFunction`
version above via the rearrangement's own `sInf`-based defining property. For `σ > L` (`L` the
target `liminf`), `L < σ` gives (`frequently_lt_of_liminf_lt`) infinitely many `k` with
`(g k)*(t) < σ`, hence `ϱ(g k,σ) ≤ t` for infinitely many `k`
(`distributionFunction_le_of_lt_decreasingRearrangement`), hence `liminf_k ϱ(g k,σ) ≤ t`
(`liminf_le_of_frequently_le'`); combined with the `distributionFunction` Fatou bound at this same
`σ`, `ϱ(glim,σ) ≤ t`, i.e. `σ` is itself a valid candidate in `glim*(t)`'s defining `sInf` set, so
`glim*(t) ≤ σ`. Taking `σ ↓ L` (via `ENNReal.le_of_forall_pos_le_add`) gives `glim*(t) ≤ L`. -/
theorem decreasingRearrangement_le_liminf_of_tendsto_ae {g : ℕ → α → E} {glim : α → E}
    (hgmeas : ∀ n, AEMeasurable (fun x => ‖g n x‖ₑ) μ)
    (hglimmeas : AEMeasurable (fun x => ‖glim x‖ₑ) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (glim x))) (t : ℝ≥0∞) :
    decreasingRearrangement μ glim t ≤
      liminf (fun k => decreasingRearrangement μ (g k) t) atTop := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  set L := liminf (fun k => decreasingRearrangement μ (g k) t) atTop with hLdef
  rcases eq_or_ne L ⊤ with hLtop | hLtop
  · rw [hLtop, top_add]
    exact le_top
  have hLlt : L < L + (ε : ℝ≥0∞) := ENNReal.lt_add_right hLtop (by exact_mod_cast hε.ne')
  have hfreq : ∃ᶠ k in atTop, decreasingRearrangement μ (g k) t < L + ε :=
    frequently_lt_of_liminf_lt (h := hLlt)
  have hfreq2 : ∃ᶠ k in atTop, distributionFunction μ (g k) (L + ε) ≤ t :=
    hfreq.mono (fun k hk => distributionFunction_le_of_lt_decreasingRearrangement (g k) t _ hk)
  have hliminf_le_t : liminf (fun k => distributionFunction μ (g k) (L + ε)) atTop ≤ t :=
    liminf_le_of_frequently_le' hfreq2
  have hbound : distributionFunction μ glim (L + ε) ≤
      liminf (fun k => distributionFunction μ (g k) (L + ε)) atTop :=
    distributionFunction_le_liminf_of_tendsto_ae hgmeas hglimmeas hg (L + ε)
  have hle : distributionFunction μ glim (L + ε) ≤ t := hbound.trans hliminf_le_t
  unfold decreasingRearrangement
  exact csInf_le' hle

/-- **Fatou's lemma for `lorentzNorm`, `q = ⊤` case**: `glim`'s `lorentzNorm` is bounded by the
`liminf` of the `lorentzNorm`s along an a.e.-convergent sequence. Since `lorentzNorm` at `q = ⊤` is
a plain `iSup` (no integral), this is immediate from the `decreasingRearrangement` Fatou bound
above plus constant-multiplication commuting with `liminf`
(`ENNReal.liminf_const_mul_of_ne_top`) — no further integral-level Fatou argument is needed here
(unlike the finite-`q` case). This is the tool `LorentzSpace`'s completeness proof needs to show
`f_lim` itself has finite `lorentzNorm` (`lorentzNorm(g k)` bounded uniformly in `k` from a single
quasi-triangle-inequality application, `liminf` of a bounded sequence is finite) and, applied again
to `g m - g k` as `m → ∞`, that `g k → f_lim` in `lorentzNorm`. -/
theorem lorentzNorm_top_le_liminf_of_tendsto_ae (p : ℝ≥0∞) {g : ℕ → α → E} {glim : α → E}
    (hgmeas : ∀ n, AEMeasurable (fun x => ‖g n x‖ₑ) μ)
    (hglimmeas : AEMeasurable (fun x => ‖glim x‖ₑ) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (glim x))) :
    lorentzNorm μ p ⊤ glim ≤ liminf (fun k => lorentzNorm μ p ⊤ (g k)) atTop := by
  unfold lorentzNorm
  simp only [ite_true]
  apply iSup_le
  intro u
  have hrearr := decreasingRearrangement_le_liminf_of_tendsto_ae hgmeas hglimmeas hg (u : ℝ≥0∞)
  have hane_top : (u : ℝ≥0∞) ^ p⁻¹.toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (by simp)
  calc (u : ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ glim (u : ℝ≥0∞)
      ≤ (u : ℝ≥0∞) ^ p⁻¹.toReal *
          liminf (fun k => decreasingRearrangement μ (g k) (u : ℝ≥0∞)) atTop := by gcongr
    _ = liminf (fun k => (u : ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ (g k) (u : ℝ≥0∞))
          atTop := (ENNReal.liminf_const_mul_of_ne_top hane_top).symm
    _ ≤ liminf (fun k => lorentzNorm μ p ⊤ (g k)) atTop := by
        have hle_all : ∀ k, (u : ℝ≥0∞) ^ p⁻¹.toReal *
            decreasingRearrangement μ (g k) (u : ℝ≥0∞) ≤ lorentzNorm μ p ⊤ (g k) := by
          intro k
          unfold lorentzNorm
          simp only [ite_true]
          exact le_iSup
            (fun v : ℝ≥0 => (v : ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ (g k) (v : ℝ≥0∞))
            u
        exact liminf_le_liminf (Filter.Eventually.of_forall hle_all)

/-- **Fatou's lemma for `lorentzNorm`, `0 < q < ⊤` case**: the same conclusion as
`lorentzNorm_top_le_liminf_of_tendsto_ae`, but needs one further layer of Fatou (for the defining
`lintegral` itself, via the genuine `lintegral_liminf_le'`) on top of the `decreasingRearrangement`
bound, since `lorentzNorm` at finite `q` is an integral, not a plain `iSup`. The pointwise-in-`t`
step and the final outer-power step both go through the same "monotone + continuous map commutes
with `liminf`" trick (`Monotone.map_liminf_of_continuousAt`), applied to `x ↦ (c*x)^r*d` and
`x ↦ x^{q⁻¹.toReal}` respectively. -/
theorem lorentzNorm_finite_le_liminf_of_tendsto_ae (p q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ⊤)
    {g : ℕ → α → E} {glim : α → E}
    (hgmeas : ∀ n, AEMeasurable (fun x => ‖g n x‖ₑ) μ)
    (hglimmeas : AEMeasurable (fun x => ‖glim x‖ₑ) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (glim x))) :
    lorentzNorm μ p q glim ≤ liminf (fun k => lorentzNorm μ p q (g k)) atTop := by
  set r := q.toReal with hrdef
  set inv := q⁻¹.toReal with hinvdef
  have hr0 : 0 < r := ENNReal.toReal_pos hq0 hqtop
  have hinv0 : 0 < inv :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hqtop) (ENNReal.inv_ne_top.mpr hq0)
  set F : ℕ → ℝ → ℝ≥0∞ := fun k t =>
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (g k) (ENNReal.ofReal t)) ^ r *
      ENNReal.ofReal t⁻¹ with hFdef
  set Flim : ℝ → ℝ≥0∞ := fun t =>
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ glim (ENNReal.ofReal t)) ^ r *
      ENNReal.ofReal t⁻¹ with hFlimdef
  have hpt : ∀ t : ℝ, Flim t ≤ liminf (fun k => F k t) atTop := by
    intro t
    have hrearr := decreasingRearrangement_le_liminf_of_tendsto_ae hgmeas hglimmeas hg
      (ENNReal.ofReal t)
    set φ : ℝ≥0∞ → ℝ≥0∞ := fun x => (ENNReal.ofReal t ^ p⁻¹.toReal * x) ^ r * ENNReal.ofReal t⁻¹
      with hφdef
    have hφmono : Monotone φ := by
      intro x y hxy
      simp only [hφdef]
      gcongr
    have hφcont : Continuous φ := by
      simp only [hφdef]
      have hcne : ENNReal.ofReal t ^ p⁻¹.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (by simp)
      have h1 : Continuous (fun x : ℝ≥0∞ => (ENNReal.ofReal t ^ p⁻¹.toReal * x) ^ r) :=
        (ENNReal.continuous_rpow_const).comp (ENNReal.continuous_const_mul hcne)
      exact ENNReal.continuous_mul_const (by simp) |>.comp h1
    have hkey : φ (decreasingRearrangement μ glim (ENNReal.ofReal t)) ≤
        φ (liminf (fun k => decreasingRearrangement μ (g k) (ENNReal.ofReal t)) atTop) :=
      hφmono hrearr
    rw [hφmono.map_liminf_of_continuousAt _ hφcont.continuousAt] at hkey
    exact hkey
  have hFmeas : ∀ k, Measurable (F k) := fun k => lorentzNorm_integrand_measurable' p (g k) r
  have hfatou : ∫⁻ t in Ioi (0 : ℝ), liminf (fun k => F k t) atTop ≤
      liminf (fun k => ∫⁻ t in Ioi (0 : ℝ), F k t) atTop :=
    lintegral_liminf_le' (fun k => (hFmeas k).aemeasurable)
  have hmono2 : ∫⁻ t in Ioi (0 : ℝ), Flim t ≤ ∫⁻ t in Ioi (0 : ℝ), liminf (fun k => F k t) atTop :=
    lintegral_mono hpt
  have hchain : ∫⁻ t in Ioi (0 : ℝ), Flim t ≤ liminf (fun k => ∫⁻ t in Ioi (0 : ℝ), F k t) atTop :=
    hmono2.trans hfatou
  set ψ : ℝ≥0∞ → ℝ≥0∞ := fun x => x ^ inv with hψdef
  have hψmono : Monotone ψ := fun x y hxy => by simp only [hψdef]; gcongr
  have hψcont : Continuous ψ := by
    simp only [hψdef]
    exact ENNReal.continuous_rpow_const
  have hstep3 : ψ (∫⁻ t in Ioi (0 : ℝ), Flim t) ≤
      ψ (liminf (fun k => ∫⁻ t in Ioi (0 : ℝ), F k t) atTop) := hψmono hchain
  rw [hψmono.map_liminf_of_continuousAt _ hψcont.continuousAt] at hstep3
  have hlorentz_lim : lorentzNorm μ p q glim = ψ (∫⁻ t in Ioi (0 : ℝ), Flim t) := by
    unfold lorentzNorm
    rw [ite_eq_right hqtop]
  have hlorentz_k : ∀ k, lorentzNorm μ p q (g k) = ψ (∫⁻ t in Ioi (0 : ℝ), F k t) := by
    intro k
    unfold lorentzNorm
    rw [ite_eq_right hqtop]
  rw [hlorentz_lim]
  simp_rw [hlorentz_k]
  exact hstep3

/-- Extracts a strictly increasing `φ` along which `B` is dominated by any prescribed positive
target sequence `c`, from `B → 0`. Needed because `QuasinormedAddCommGroup.
completeSpace_of_cauchy_complete`'s hypothesis is universally quantified over *every* summable `B`
(matching `Lp`'s own hypothesis shape) — unlike `Lp`'s Minkowski-based argument, which controls an
arbitrary summable-`B`-bounded sum directly with no need for a subsequence, the quasi-triangle
inequality's constant blows up under naive repeated application to a growing number of terms, so
this file's Fatou-based approach instead only ever uses *pairwise* differences, needing a single
sequence along which those differences shrink at a rate the caller can choose in advance
(`ae_summable_norm_of_distributionFunction_le` below is what actually uses that freedom). -/
theorem exists_seq_lt_of_tendsto_zero {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) {B : ℕ → ℝ}
    (hB : Tendsto B atTop (𝓝 0)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, B (φ k) < c k := by
  have hstep : ∀ (k N : ℕ), ∃ n, n > N ∧ B n < c k := by
    intro k N
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hB _ (hc k)
    refine ⟨max (N + 1) N0, by omega, ?_⟩
    have hthis := hN0 (max (N + 1) N0) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_lt] at hthis
    exact hthis.2
  choose g hg using hstep
  let φ : ℕ → ℕ := fun k => Nat.rec (g 0 0) (fun n prev => g (n + 1) prev) k
  have hφsucc : ∀ n, φ (n + 1) = g (n + 1) (φ n) := fun n => rfl
  refine ⟨φ, strictMono_nat_of_lt_succ (fun n => ?_), fun k => ?_⟩
  · rw [hφsucc]
    exact (hg (n + 1) (φ n)).1
  · cases k with
    | zero => exact (hg 0 0).2
    | succ n => rw [hφsucc]; exact (hg (n + 1) (φ n)).2

/-- **The Borel–Cantelli-to-summability engine**: given, for each `k`, a bound on
`distributionFunction μ (h k)` at threshold `σ k` by a summable `t k`, the norms `‖h k x‖` are a.e.
eventually below the (summable) `σ k`, hence a.e. absolutely summable. Via Mathlib's own
`ae_eventually_notMem` (the first Borel–Cantelli lemma): `∑' k, μ {x | σ k < ‖h k x‖ₑ} ≤
∑' k, t k < ∞` forces a.e. eventual non-membership, i.e. `‖h k x‖ ≤ σ k` eventually; comparison
against the summable `σ` (past whatever finite point the "eventually" starts) then gives
`Summable (fun k => ‖h k x‖)`. This is the tool that turns the Chebyshev bounds
(`distributionFunction_le_of_lorentzNorm_top_lt`/`_finite_lt`) into a.e. absolute convergence of
the telescoping sum defining `f_lim`. -/
theorem ae_summable_norm_of_distributionFunction_le {h : ℕ → α → E}
    {σ t : ℕ → ℝ} (hσ0 : ∀ k, 0 ≤ σ k) (hσsum : Summable σ)
    (ht0 : ∀ k, 0 ≤ t k) (htsum : Summable t)
    (hbd : ∀ k, distributionFunction μ (h k) (ENNReal.ofReal (σ k)) ≤ ENNReal.ofReal (t k)) :
    ∀ᵐ x ∂μ, Summable (fun k => ‖h k x‖) := by
  set s : ℕ → Set α := fun k => {x | ENNReal.ofReal (σ k) < ‖h k x‖ₑ} with hsdef
  have hsum_finite : (∑' k, μ (s k)) ≠ ⊤ := by
    have h1 : ∑' k, μ (s k) ≤ ∑' k, ENNReal.ofReal (t k) := ENNReal.tsum_le_tsum hbd
    have h2 : ∑' k, ENNReal.ofReal (t k) = ENNReal.ofReal (∑' k, t k) :=
      (ENNReal.ofReal_tsum_of_nonneg ht0 htsum).symm
    rw [h2] at h1
    exact (h1.trans_lt ENNReal.ofReal_lt_top).ne
  have hae := ae_eventually_notMem hsum_finite
  filter_upwards [hae] with x hx
  simp only [hsdef, Set.mem_ofPred_eq, not_lt] at hx
  obtain ⟨N, hN⟩ := hx.exists_forall_of_atTop
  have hcomp : ∀ k ≥ N, ‖h k x‖ ≤ σ k := by
    intro k hk
    have hle := hN k hk
    rw [← ofReal_norm (h k x)] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (hσ0 k)).mp hle
  have hsummable_tail : Summable (fun k => ‖h (k + N) x‖) := by
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hcomp (k + N) (by omega))
    exact hσsum.comp_injective (add_left_injective N)
  exact (summable_nat_add_iff N).mp hsummable_tail

/-- Real-valued repackaging of `distributionFunction_le_of_lorentzNorm_top_lt`, matching the
shape `ae_summable_norm_of_distributionFunction_le` needs (`σ, t : ℕ → ℝ`, not `ℝ≥0∞`/`ℝ≥0`). -/
theorem distributionFunction_le_of_lorentzNorm_top_lt_real (p : ℝ≥0∞) (f : α → E) (σ t : ℝ)
    (ht : 0 ≤ t) (h : lorentzNorm μ p ⊤ f < ENNReal.ofReal (t ^ p⁻¹.toReal * σ)) :
    distributionFunction μ f (ENNReal.ofReal σ) ≤ ENNReal.ofReal t := by
  have hpr : (0 : ℝ) ≤ p⁻¹.toReal := ENNReal.toReal_nonneg
  have hcast : (t.toNNReal : ℝ≥0∞) ^ p⁻¹.toReal = ENNReal.ofReal (t ^ p⁻¹.toReal) := by
    rw [show ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t from rfl,
      ENNReal.ofReal_rpow_of_nonneg ht hpr]
  have h' : lorentzNorm μ p ⊤ f < (t.toNNReal : ℝ≥0∞) ^ p⁻¹.toReal * ENNReal.ofReal σ := by
    rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    exact h
  have key := distributionFunction_le_of_lorentzNorm_top_lt p f (ENNReal.ofReal σ) t.toNNReal h'
  rwa [show ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t from rfl] at key

/-- Real-valued repackaging of `distributionFunction_le_of_lorentzNorm_finite_lt` (same reason as
the `q = ⊤` version above). -/
theorem distributionFunction_le_of_lorentzNorm_finite_lt_real (p q : ℝ≥0∞) (hq0 : q ≠ 0)
    (hqtop : q ≠ ⊤) (f : α → E) (σ s : ℝ) (hσ : 0 ≤ σ) (hs : 0 < s)
    (h : lorentzNorm μ p q f <
      ENNReal.ofReal (s ^ p⁻¹.toReal * σ * Real.log 2 ^ q⁻¹.toReal)) :
    distributionFunction μ f (ENNReal.ofReal σ) ≤ ENNReal.ofReal (2 * s) := by
  have hpr : (0 : ℝ) ≤ p⁻¹.toReal := ENNReal.toReal_nonneg
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have heq : ENNReal.ofReal s ^ p⁻¹.toReal * ENNReal.ofReal σ *
      ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal =
      ENNReal.ofReal (s ^ p⁻¹.toReal * σ * Real.log 2 ^ q⁻¹.toReal) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hs.le hpr,
      ENNReal.ofReal_rpow_of_nonneg hlog2 ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have h' : lorentzNorm μ p q f <
      ENNReal.ofReal s ^ p⁻¹.toReal * ENNReal.ofReal σ *
        ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal := heq ▸ h
  exact distributionFunction_le_of_lorentzNorm_finite_lt p q hq0 hqtop f (ENNReal.ofReal σ)
    (ENNReal.ofReal_ne_top) s hs h'

/-- The geometric rate a controlled sequence's consecutive `lorentzNorm` differences need to decay
at, for `ae_summable_norm_of_distributionFunction_le` to apply at the concrete threshold/measure
scales `σ k = t k := (1/2)^(k+1)` used by `distributionFunction_le_of_lorentzBC` below. Chosen so
that (mirroring `Basic.lean`'s `quasiTriangleBound`) the same rate works uniformly whether `q = ⊤`
or `0 < q < ⊤`, since — as `distributionFunction_le_of_lorentzBC`'s proof shows — the two
Chebyshev bounds' required rates coincide exactly (only the required *constant* prefactor differs,
absorbed into `lorentzBCConst`). -/
noncomputable def lorentzBCRate (p : ℝ≥0∞) : ℝ := (1 / 2 : ℝ) ^ (p⁻¹.toReal + 1)

/-- The constant prefactor accompanying `lorentzBCRate`: the smaller of what the `q = ⊤` and
`0 < q < ⊤` Chebyshev bounds each need, so `distributionFunction_le_of_lorentzBC` can use a single
`κ * lorentzBCRate p ^ k` target regardless of which case `q` falls into. -/
noncomputable def lorentzBCConst (p q : ℝ≥0∞) : ℝ :=
  min ((1 / 2 : ℝ) ^ (p⁻¹.toReal + 1))
    ((1 / 2 : ℝ) ^ (2 * p⁻¹.toReal + 1) * Real.log 2 ^ q⁻¹.toReal)

theorem lorentzBCRate_pos (p : ℝ≥0∞) : 0 < lorentzBCRate p := by
  unfold lorentzBCRate; positivity

theorem lorentzBCRate_lt_one (p : ℝ≥0∞) : lorentzBCRate p < 1 := by
  unfold lorentzBCRate
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)

theorem lorentzBCConst_pos (p q : ℝ≥0∞) : 0 < lorentzBCConst p q := by
  unfold lorentzBCConst
  apply lt_min <;> positivity

/-- **The Chebyshev/Borel–Cantelli glue**: `lorentzNorm`-smallness at the `lorentzBCConst`/
`lorentzBCRate` geometric rate gives exactly the `distributionFunction` bound
`ae_summable_norm_of_distributionFunction_le` needs, at the concrete scales `σ k = t k =
(1/2)^(k+1)` — uniformly for **every** `q` (with `0 < q`, as required throughout this file), via
whichever of the two Chebyshev lemmas applies. The two case computations both reduce to a clean
algebraic identity (`lorentzBCRate p ^ (k+1)` — or its finite-`q` analogue with the extra
`(log 2)^{q⁻¹.toReal}` factor — equals exactly the target the corresponding Chebyshev lemma needs),
so `lorentzBCConst`'s role is only to handle the *initial* constant mismatch between the two
branches, never the exponential rate itself. -/
theorem distributionFunction_le_of_lorentzBC (p q : ℝ≥0∞) (hq0 : q ≠ 0) {h : α → E} (k : ℕ)
    (hsmall : lorentzNorm μ p q h < ENNReal.ofReal (lorentzBCConst p q * lorentzBCRate p ^ k)) :
    distributionFunction μ h (ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
  have hrate_nonneg : (0 : ℝ) ≤ lorentzBCRate p ^ k := pow_nonneg (lorentzBCRate_pos p).le k
  rcases eq_or_ne q ⊤ with hqtop | hqtop
  · subst hqtop
    apply distributionFunction_le_of_lorentzNorm_top_lt_real p h _ _ (by positivity)
    refine hsmall.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have heq : lorentzBCRate p ^ (k + 1) =
        ((1 / 2 : ℝ) ^ (k + 1)) ^ p⁻¹.toReal * (1 / 2 : ℝ) ^ (k + 1) := by
      unfold lorentzBCRate
      have hone : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      rw [hone, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ (p⁻¹.toReal + 1)) (k + 1),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_add (by norm_num)]
      ring_nf
    calc lorentzBCConst p ⊤ * lorentzBCRate p ^ k
        ≤ lorentzBCRate p * lorentzBCRate p ^ k :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hrate_nonneg
      _ = lorentzBCRate p ^ (k + 1) := (pow_succ' _ _).symm
      _ = ((1 / 2 : ℝ) ^ (k + 1)) ^ p⁻¹.toReal * (1 / 2 : ℝ) ^ (k + 1) := heq
  · have hs : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 2) := by positivity
    have key := distributionFunction_le_of_lorentzNorm_finite_lt_real (μ := μ) p q hq0 hqtop h
      ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ (k + 2)) (by positivity) hs (h := ?_)
    · rwa [show (2 : ℝ) * (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) from by ring] at key
    · refine hsmall.trans_le (ENNReal.ofReal_le_ofReal ?_)
      have hLHS : ((1 / 2 : ℝ) ^ (2 * p⁻¹.toReal + 1) * Real.log 2 ^ q⁻¹.toReal) *
          lorentzBCRate p ^ k =
          (1 / 2 : ℝ) ^ ((k + 2 : ℝ) * p⁻¹.toReal + (k + 1 : ℝ)) * Real.log 2 ^ q⁻¹.toReal := by
        unfold lorentzBCRate
        rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (p⁻¹.toReal + 1)) k, ← Real.rpow_mul (by norm_num),
          mul_right_comm, ← Real.rpow_add (by norm_num)]
        ring_nf
      have hRHS : ((1 / 2 : ℝ) ^ (k + 2)) ^ p⁻¹.toReal * (1 / 2 : ℝ) ^ (k + 1) *
            Real.log 2 ^ q⁻¹.toReal =
          (1 / 2 : ℝ) ^ ((k + 2 : ℝ) * p⁻¹.toReal + (k + 1 : ℝ)) * Real.log 2 ^ q⁻¹.toReal := by
        have hone : ∀ n : ℕ, (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ ((n : ℕ) : ℝ) := fun n =>
          (Real.rpow_natCast _ _).symm
        rw [hone (k + 1), hone (k + 2), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        push_cast
        ring_nf
      have heq : ((1 / 2 : ℝ) ^ (2 * p⁻¹.toReal + 1) * Real.log 2 ^ q⁻¹.toReal) *
          lorentzBCRate p ^ k =
          ((1 / 2 : ℝ) ^ (k + 2)) ^ p⁻¹.toReal * (1 / 2 : ℝ) ^ (k + 1) *
            Real.log 2 ^ q⁻¹.toReal := hLHS.trans hRHS.symm
      calc lorentzBCConst p q * lorentzBCRate p ^ k
          ≤ ((1 / 2 : ℝ) ^ (2 * p⁻¹.toReal + 1) * Real.log 2 ^ q⁻¹.toReal) * lorentzBCRate p ^ k :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hrate_nonneg
        _ = ((1 / 2 : ℝ) ^ (k + 2)) ^ p⁻¹.toReal * (1 / 2 : ℝ) ^ (k + 1) *
            Real.log 2 ^ q⁻¹.toReal := heq

/-- **The a.e. limit construction**: given a sequence of raw functions with `lorentzNorm`-summable
(at the `lorentzBCConst`/`lorentzBCRate` geometric rate) consecutive differences, the telescoping
partial sums converge a.e. Chains `distributionFunction_le_of_lorentzBC` (turning `lorentzNorm`
smallness into a `distributionFunction` bound) into `ae_summable_norm_of_distributionFunction_le`
(Borel–Cantelli) to get a.e. absolute summability of the differences, then a generic
(no `lorentzNorm` content) telescoping-sum argument — identical in spirit to the corresponding
step of `Lp.ae_tendsto_of_cauchy_eLpNorm'`, just reached via a different route (Borel–Cantelli
directly, rather than a Minkowski-inequality bound on the whole tail sum's `eLpNorm`). -/
theorem exists_ae_tendsto_of_lorentzNorm_lt [CompleteSpace E] (p q : ℝ≥0∞) (hq0 : q ≠ 0)
    {g : ℕ → α → E}
    (hsmall : ∀ k, lorentzNorm μ p q (g (k + 1) - g k) <
      ENNReal.ofReal (lorentzBCConst p q * lorentzBCRate p ^ k)) :
    ∀ᵐ x ∂μ, ∃ l : E, Tendsto (fun n => g n x) atTop (𝓝 l) := by
  have hσ0 : ∀ k : ℕ, (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) := fun k => by positivity
  have hσsum : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr summable_geometric_two
  have hbd : ∀ k, distributionFunction μ (g (k + 1) - g k)
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) :=
    fun k => distributionFunction_le_of_lorentzBC p q hq0 k (hsmall k)
  have hsummable_ae : ∀ᵐ x ∂μ, Summable (fun k => ‖(g (k + 1) - g k) x‖) :=
    ae_summable_norm_of_distributionFunction_le hσ0 hσsum hσ0 hσsum hbd
  refine hsummable_ae.mono fun x hx => ?_
  simp only [Pi.sub_apply] at hx
  have hsum : Summable (fun i => g (i + 1) x - g i x) := hx.of_norm
  have htel := hsum.hasSum.tendsto_sum_nat
  rw [funext fun n => Finset.sum_range_sub (fun m => g m x) n] at htel
  exact ⟨∑' i, (g (i + 1) x - g i x) + g 0 x, by simpa using htel.add_const (g 0 x)⟩

/-- `LorentzSpace`'s own quasinorm, on the coercion of a *difference* of two of its elements, back
to the underlying `distributionFunction`/`lorentzNorm` formulas on raw functions. Needed since the
rest of this file's argument works with raw functions throughout (mirroring
`distributionFunction`/`lorentzNorm`'s own domain), only ever returning to the bundled
`LorentzSpace` type at the very end. -/
theorem lorentzNorm_coe_sub_eq (p q : ℝ≥0∞) (f g : LorentzSpace E p q μ) :
    lorentzNorm μ p q ((f : α → E) - (g : α → E)) = ENNReal.ofReal ‖f - g‖ := by
  have hcoe : ((f - g : LorentzSpace E p q μ) : α →ₘ[μ] E) =
      (f : α →ₘ[μ] E) - (g : α →ₘ[μ] E) := rfl
  have h1 : (⇑(f - g) : α → E) = ((f - g : LorentzSpace E p q μ) : α →ₘ[μ] E) := rfl
  have h2 : lorentzNorm μ p q ((f : α → E) - (g : α → E)) =
      lorentzNorm μ p q (⇑(f - g)) := by
    rw [h1, hcoe]
    exact (lorentzNorm_congr_ae p q (AEEqFun.coeFn_sub (f : α →ₘ[μ] E) g)).symm
  rw [h2]
  change lorentzNorm μ p q (⇑(f - g)) = ENNReal.ofReal (lorentzNorm μ p q (⇑(f - g))).toReal
  rw [ENNReal.ofReal_toReal (f - g).2.ne]

/-- The unified (`q = ⊤` or `0 < q < ⊤`) form of the Fatou-for-`lorentzNorm` chain, combining
`lorentzNorm_top_le_liminf_of_tendsto_ae`/`_finite_le_liminf_of_tendsto_ae` — the two remaining
uses in this file (bounding the limit's `lorentzNorm` from a controlled sequence's) need this
regardless of which case `q` is in, so both are gated on `0 < q` (not split further) from here on,
matching `LorentzSpace.instQuasinormedAddCommGroup`'s own gating. -/
theorem lorentzNorm_le_liminf_of_tendsto_ae (p q : ℝ≥0∞) (hq0 : q ≠ 0) {g : ℕ → α → E}
    {glim : α → E} (hgmeas : ∀ n, AEMeasurable (fun x => ‖g n x‖ₑ) μ)
    (hglimmeas : AEMeasurable (fun x => ‖glim x‖ₑ) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (glim x))) :
    lorentzNorm μ p q glim ≤ liminf (fun k => lorentzNorm μ p q (g k)) atTop := by
  rcases eq_or_ne q ⊤ with hqtop | hqtop
  · subst hqtop
    exact lorentzNorm_top_le_liminf_of_tendsto_ae p hgmeas hglimmeas hg
  · exact lorentzNorm_finite_le_liminf_of_tendsto_ae p q hq0 hqtop hgmeas hglimmeas hg

/-- **`lorentzNorm(g n - glim) → 0`**, given genuine (arbitrary-pair, not just consecutive)
`lorentzNorm`-Cauchy control on `g` and a.e. pointwise convergence to `glim`. Mirrors
`Lp.cauchy_tendsto_of_tendsto` exactly: for fixed `n`, apply the Fatou bound above to the sequence
`m ↦ g n - g m` (converging a.e. to `g n - glim` as `m → ∞`), then bound the resulting `liminf`
using `h_cau` directly (frequently, for `m` large, `lorentzNorm (g n - g m) < B N ≤ ε` once `n`
itself is `≥ N`). -/
theorem lorentzNorm_tendsto_zero_of_tendsto_ae (p q : ℝ≥0∞) (hq0 : q ≠ 0)
    {g : ℕ → α → E} (hgmeas : ∀ n, AEStronglyMeasurable (g n) μ)
    {glim : α → E} (hglimmeas : AEStronglyMeasurable glim μ)
    {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ⊤)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → lorentzNorm μ p q (g n - g m) < B N)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (glim x))) :
    Tendsto (fun n => lorentzNorm μ p q (g n - glim)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨N, hBN⟩ : ∃ N : ℕ, B N ≤ ε := by
    suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε from
      ⟨h_tendsto_zero.choose, h_tendsto_zero.choose_spec _ le_rfl⟩
    exact (ENNReal.tendsto_atTop_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hsub_meas : ∀ m, AEMeasurable (fun x => ‖(g n - g m) x‖ₑ) μ := by
    intro m
    have h1 : AEMeasurable (fun x => ‖(g n - g m) x‖) μ :=
      ((hgmeas n).sub (hgmeas m)).norm.aemeasurable
    simpa only [ofReal_norm] using h1.ennreal_ofReal
  have hlim_meas : AEMeasurable (fun x => ‖(g n - glim) x‖ₑ) μ := by
    have h1 : AEMeasurable (fun x => ‖(g n - glim) x‖) μ :=
      ((hgmeas n).sub hglimmeas).norm.aemeasurable
    simpa only [ofReal_norm] using h1.ennreal_ofReal
  have h_ae : ∀ᵐ x ∂μ, Tendsto (fun m => (g n - g m) x) atTop (𝓝 ((g n - glim) x)) := by
    filter_upwards [h_lim] with x hx
    simpa using tendsto_const_nhds.sub hx
  have h_sub : lorentzNorm μ p q (g n - glim) ≤
      liminf (fun m => lorentzNorm μ p q (g n - g m)) atTop :=
    lorentzNorm_le_liminf_of_tendsto_ae p q hq0 hsub_meas hlim_meas h_ae
  refine h_sub.trans ?_
  refine liminf_le_of_frequently_le' (frequently_atTop.mpr ?_)
  refine fun N1 => ⟨max N N1, le_max_right _ _, ?_⟩
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans hBN

/-- **`lorentzNorm(glim) < ⊤`**, given each `g n` has finite `lorentzNorm` and
`lorentzNorm (g n - glim) → 0`. Mirrors `Lp.memLp_of_cauchy_tendsto`: pick `N` with
`lorentzNorm (g N - glim) ≤ 1` (from `h_tendsto`), write `glim = (glim - g N) + g N`, and bound via
a single application of the quasi-triangle inequality (`lorentzNorm_add_le`) — no infinite-sum
control needed, unlike a naive telescoping-sum bound. -/
theorem lorentzNorm_lt_top_of_tendsto_zero (p q : ℝ≥0∞) {g : ℕ → α → E}
    (hg : ∀ n, lorentzNorm μ p q (g n) < ⊤) (glim : α → E)
    (h_tendsto : Tendsto (fun n => lorentzNorm μ p q (g n - glim)) atTop (𝓝 0)) :
    lorentzNorm μ p q glim < ⊤ := by
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  obtain ⟨N, h1⟩ := h_tendsto 1 zero_lt_one
  specialize h1 N le_rfl
  have h_add : glim = (glim - g N) + g N := by abel
  rw [h_add]
  refine lt_of_le_of_lt (lorentzNorm_add_le p q _ _) ?_
  have h_neg : glim - g N = -(g N - glim) := by abel
  rw [h_neg, lorentzNorm_neg]
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)) ?_
  exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt h1 ENNReal.one_lt_top, hg N⟩

variable [CompleteSpace E] {p q : ℝ≥0∞}

/-- **The main theorem**: every `B`-controlled Cauchy sequence in `LorentzSpace E p q μ` converges,
discharging `QuasinormedAddCommGroup.completeSpace_of_cauchy_complete`'s hypothesis. The proof:
extract a subsequence `g = f ∘ φ` with `lorentzNorm`-consecutive-differences shrinking at the
`lorentzBCConst`/`lorentzBCRate` rate (`exists_seq_lt_of_tendsto_zero`); build an a.e. pointwise
limit `glim` of `g` (`exists_ae_tendsto_of_lorentzNorm_lt` +
`exists_stronglyMeasurable_limit_of_tendsto_ae`); show `lorentzNorm (g n - glim) → 0` and
`lorentzNorm glim < ⊤` from *genuine* (arbitrary-pair, not just consecutive) `lorentzNorm`-Cauchy
control on `g` (`lorentzNorm_tendsto_zero_of_tendsto_ae`, `lorentzNorm_lt_top_of_tendsto_zero`);
package `glim` as an actual `LorentzSpace` element and transfer the convergence
(`QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero`); finally upgrade `g → glimBundled`
to the *full* sequence `f → glimBundled`, via a single quasi-triangle-inequality application at
each step (`‖f n - glimBundled‖ ≤ C(‖f n - g k‖ + ‖g k - glimBundled‖)`, for `k` chosen so `φ k`
is at least as large as `n` and `B (φ k)`/`‖g k - glimBundled‖` are both small) — the standard
"Cauchy sequence with a convergent subsequence converges" argument. -/
theorem LorentzSpace.exists_tendsto_of_cauchy [Fact (0 < q)]
    (f : ℕ → LorentzSpace E p q μ) (B : ℕ → ℝ) (hB : Summable B)
    (hf : ∀ N n m : ℕ, N ≤ n → N ≤ m → ‖f n - f m‖ < B N) :
    ∃ f_lim : LorentzSpace E p q μ, Tendsto f atTop (𝓝 f_lim) := by
  have hq0 : q ≠ 0 := (Fact.out (p := 0 < q)).ne'
  have hB0 : Tendsto B atTop (𝓝 0) := hB.tendsto_atTop_zero
  obtain ⟨φ, hφmono, hφc⟩ := exists_seq_lt_of_tendsto_zero
    (c := fun k => lorentzBCConst p q * lorentzBCRate p ^ k)
    (fun k => mul_pos (lorentzBCConst_pos p q) (pow_pos (lorentzBCRate_pos p) k)) hB0
  set g : ℕ → LorentzSpace E p q μ := fun k => f (φ k) with hgdef
  have hgmeas : ∀ k, AEStronglyMeasurable ((g k : α → E)) μ :=
    fun k => (g k : α →ₘ[μ] E).aestronglyMeasurable
  have hgnorm_small_real : ∀ k, ‖g (k + 1) - g k‖ <
      lorentzBCConst p q * lorentzBCRate p ^ k := by
    intro k
    calc ‖g (k + 1) - g k‖ = ‖f (φ (k + 1)) - f (φ k)‖ := rfl
      _ < B (φ k) := hf (φ k) (φ (k + 1)) (φ k) (hφmono.le_iff_le.mpr (Nat.le_succ k)) le_rfl
      _ < lorentzBCConst p q * lorentzBCRate p ^ k := hφc k
  have hgnorm_small : ∀ k, lorentzNorm μ p q ((g (k + 1) : α → E) - (g k : α → E)) <
      ENNReal.ofReal (lorentzBCConst p q * lorentzBCRate p ^ k) := by
    intro k
    rw [lorentzNorm_coe_sub_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (lorentzBCConst_pos p q) (pow_pos (lorentzBCRate_pos p) k))).mpr
      (hgnorm_small_real k)
  have h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : E, Tendsto (fun k => (g k : α → E) x) atTop (𝓝 l) :=
    exists_ae_tendsto_of_lorentzNorm_lt p q hq0 hgnorm_small
  obtain ⟨glim, hglim_meas, hglim_tendsto⟩ :
      ∃ glim : α → E, StronglyMeasurable glim ∧
        ∀ᵐ x ∂μ, Tendsto (fun k => (g k : α → E) x) atTop (𝓝 (glim x)) :=
    exists_stronglyMeasurable_limit_of_tendsto_ae hgmeas h_ae_tendsto
  have hBφ_pos : ∀ k, 0 < B (φ k) := by
    intro k
    calc (0 : ℝ) = ‖g k - g k‖ := by simp
      _ < B (φ k) := hf (φ k) (φ k) (φ k) le_rfl le_rfl
  have hBφ_summable : Summable (fun k => B (φ k)) := hB.comp_injective hφmono.injective
  have hBφ_ne_top : (∑' k, ENNReal.ofReal (B (φ k))) ≠ ⊤ :=
    (ENNReal.ofReal_tsum_of_nonneg (fun k => (hBφ_pos k).le) hBφ_summable ▸
      ENNReal.ofReal_lt_top).ne
  have h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      lorentzNorm μ p q ((g n : α → E) - (g m : α → E)) < ENNReal.ofReal (B (φ N)) := by
    intro N n m hn hm
    rw [lorentzNorm_coe_sub_eq]
    exact ENNReal.ofReal_lt_ofReal_iff (hBφ_pos N) |>.mpr (hf (φ N) (φ n) (φ m)
      (hφmono.le_iff_le.mpr hn) (hφmono.le_iff_le.mpr hm))
  have h_tendsto_zero : Tendsto (fun n => lorentzNorm μ p q ((g n : α → E) - glim)) atTop (𝓝 0) :=
    lorentzNorm_tendsto_zero_of_tendsto_ae p q hq0 hgmeas hglim_meas.aestronglyMeasurable
      hBφ_ne_top h_cau hglim_tendsto
  have h_glim_finite : lorentzNorm μ p q glim < ⊤ :=
    lorentzNorm_lt_top_of_tendsto_zero p q (fun n => (g n).2) glim h_tendsto_zero
  set glimAE : α →ₘ[μ] E := AEEqFun.mk glim hglim_meas.aestronglyMeasurable with hglimAEdef
  have hglimAE_ae : (glimAE : α → E) =ᵐ[μ] glim := AEEqFun.coeFn_mk glim _
  have hglimAE_lorentzNorm : lorentzNorm μ p q (glimAE : α → E) < ⊤ := by
    rw [lorentzNorm_congr_ae p q hglimAE_ae]
    exact h_glim_finite
  set glimBundled : LorentzSpace E p q μ := ⟨glimAE, hglimAE_lorentzNorm⟩ with hglimBundleddef
  have h_g_tendsto : Tendsto g atTop (𝓝 glimBundled) := by
    rw [QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero]
    have heq : ∀ n, ‖g n - glimBundled‖ = (lorentzNorm μ p q ((g n : α → E) - glim)).toReal := by
      intro n
      have h1 : lorentzNorm μ p q (⇑(g n - glimBundled)) =
          lorentzNorm μ p q ((g n : α → E) - glim) := by
        have hcoe : ((g n - glimBundled : LorentzSpace E p q μ) : α →ₘ[μ] E) =
            (g n : α →ₘ[μ] E) - (glimAE : α →ₘ[μ] E) := rfl
        have h1' : (⇑(g n - glimBundled) : α → E) =
            ((g n - glimBundled : LorentzSpace E p q μ) : α →ₘ[μ] E) := rfl
        rw [h1', hcoe]
        rw [lorentzNorm_congr_ae p q (AEEqFun.coeFn_sub (g n : α →ₘ[μ] E) glimAE)]
        exact lorentzNorm_congr_ae p q (Filter.EventuallyEq.rfl.sub hglimAE_ae)
      change (lorentzNorm μ p q (⇑(g n - glimBundled))).toReal = _
      rw [h1]
    simp_rw [heq]
    rw [← ENNReal.toReal_zero]
    exact Tendsto.comp (g := ENNReal.toReal) (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
      h_tendsto_zero
  refine ⟨glimBundled, ?_⟩
  rw [QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
    at h_g_tendsto ⊢
  intro ε hε
  set C := LorentzSpace.quasiTriangleBound (p := p) (q := q) with hCdef
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one LorentzSpace.one_le_quasiTriangleBound
  have hεC : (0 : ℝ) < ε / (2 * C) := by positivity
  obtain ⟨K, hK0⟩ := h_g_tendsto (ε / (2 * C)) hεC
  have hK : ∀ n ≥ K, ‖g n - glimBundled‖ < ε / (2 * C) := by
    intro n hn
    have := hK0 n hn
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (QuasinormedAddCommGroup.norm_nonneg (g n - glimBundled))] at this
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hB0) (ε / (2 * C)) hεC
  refine ⟨N0, fun n hn => ?_⟩
  set k := max K n with hkdef
  have hkK : k ≥ K := le_max_left _ _
  have hkn : k ≥ n := le_max_right _ _
  have hphik : φ k ≥ n := le_trans hkn hφmono.le_apply
  have hBn_pos : 0 < B n := by
    have := hf n n n le_rfl le_rfl
    simpa using this
  have h1 : ‖f n - g k‖ < B n := hf n n (φ k) le_rfl hphik
  have h2 : B n < ε / (2 * C) := by
    have := hN0 n hn
    rwa [Real.dist_eq, sub_zero, abs_of_pos hBn_pos] at this
  have h3 : ‖g k - glimBundled‖ < ε / (2 * C) := hK k hkK
  have h4 : ‖f n - glimBundled‖ ≤ C * (‖f n - g k‖ + ‖g k - glimBundled‖) := by
    have heq : f n - glimBundled = (f n - g k) + (g k - glimBundled) := by abel
    rw [heq]
    exact LorentzSpace.norm_add_le μ (f n - g k) (g k - glimBundled)
  change dist ‖f n - glimBundled‖ 0 < ε
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (QuasinormedAddCommGroup.norm_nonneg (f n - glimBundled))]
  calc ‖f n - glimBundled‖ ≤ C * (‖f n - g k‖ + ‖g k - glimBundled‖) := h4
    _ < C * (ε / (2 * C) + ε / (2 * C)) := by gcongr; exact h1.trans h2
    _ = ε := by field_simp; ring

/-- **`LorentzSpace E p q μ` is complete**, for every `p, q` with `0 < q` (matching
`instQuasinormedAddCommGroup`'s own gating, `Basic.lean`) and `[CompleteSpace E]` (matching `Lp`'s
own requirement on its target space). -/
instance LorentzSpace.instCompleteSpace [Fact (0 < q)] : CompleteSpace (LorentzSpace E p q μ) :=
  QuasinormedAddCommGroup.completeSpace_of_cauchy_complete
    fun f B hB hf => LorentzSpace.exists_tendsto_of_cauchy f B hB hf
