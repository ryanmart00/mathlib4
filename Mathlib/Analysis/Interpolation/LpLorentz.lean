/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Classical interpolation of `Lᵖ` and Lorentz spaces

DRAFT — statements only, all proofs deferred (`sorry`).

Following Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, §1.18.4-7.
The end goal (per Ryan): the Marcinkiewicz interpolation theorem, i.e. that real-interpolating
two weak-`Lᵖ` (Lorentz `L_{p,∞}`) spaces gives the usual `Lᵖ` space.

Deliberately **not** yet wired through `InterpolationCouple`/`KFunctional`: weak-`Lᵖ` is only a
*quasi*-Banach space (its "norm" satisfies the triangle inequality only up to a constant) for
`p < ∞`, so it doesn't literally satisfy our couple framework's `NormedAddCommGroup` requirement
without extra work (an equivalent genuine norm). These definitions instead follow Triebel's own
classical-analysis formulas directly, self-contained, so the classical statements can be recorded
now; reconciling with the abstract framework is separate future work.

## Main definitions
* `distributionFunction`, `decreasingRearrangement` (§1.18.6).
* `lorentzNorm p q μ f` — the Lorentz `L_{p,q}` (quasi-)norm.
* `lorentzKFunctional p₀ q₀ p₁ q₁ t μ f` — the K-functional for the couple of Lorentz spaces
  `(L_{p₀,q₀}, L_{p₁,q₁})`, generalizing Triebel's `K(t,f;L1,L∞)`.

## Main results (all `sorry` for now)
* `lorentzNorm_diag`: `L_{p,p} = Lᵖ` (§1.18.6, Lemma).
* `lorentzNorm_top_eq_iSup`: `L_{p,∞}` is the classical weak-`Lᵖ`/Marcinkiewicz space.
* `kFunctional_L1_Linfty`: `K(t,f;L1,L∞) = ∫₀ᵗ f*(τ) dτ` (§1.18.6, Theorem 1 proof, eq. 9).
* `lorentzKFunctional_equiv_lorentzNorm`: the general identification (§1.18.6, Theorem 2).
* `marcinkiewicz_interpolation`: the `q₀=q₁=∞` specialization — weak-`Lᵖ⁰`/weak-`Lᵖ¹`
  interpolation gives `Lᵖ`, literally the Marcinkiewicz theorem in couple-identification form.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable {E : Type*} [NormedAddCommGroup E]

/-- The distribution function `ϱ(f,σ) = μ{x : σ < ‖f x‖}`, Triebel §1.18.6. -/
noncomputable def distributionFunction (f : α → E) (σ : ℝ≥0∞) : ℝ≥0∞ :=
  μ {x | σ < ‖f x‖ₑ}

/-- The decreasing rearrangement `f*(t) = inf{σ : ϱ(f,σ) ≤ t}`, Triebel §1.18.6. -/
noncomputable def decreasingRearrangement (f : α → E) (t : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {σ : ℝ≥0∞ | distributionFunction μ f σ ≤ t}

/-- The Lorentz (quasi-)norm `‖f‖_{L_{p,q}}`, Triebel §1.18.6:
`(∫₀^∞ (t^{1/p} f*(t))^q dt/t)^{1/q}` for `q < ∞`, `sup_t t^{1/p} f*(t)` for `q = ∞`. -/
noncomputable def lorentzNorm (p q : ℝ≥0∞) (f : α → E) : ℝ≥0∞ :=
  if q = ⊤ then
    ⨆ t : ℝ≥0, ENNReal.ofNNReal t ^ p⁻¹.toReal *
      decreasingRearrangement μ f (ENNReal.ofNNReal t)
  else
    (∫⁻ t in Ioi (0 : ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal *
        decreasingRearrangement μ f (ENNReal.ofReal t)) ^ q.toReal * ENNReal.ofReal t⁻¹)
      ^ q⁻¹.toReal

/-- The K-functional for the couple of Lorentz spaces `(L_{p₀,q₀}, L_{p₁,q₁})`, generalizing
Triebel's `K(t,f;L1,L∞)` to arbitrary Lorentz-space legs. -/
noncomputable def lorentzKFunctional (p₀ q₀ p₁ q₁ : ℝ≥0∞) (t : ℝ) (f : α → E) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ f₀ f₁ : α → E, f =ᵐ[μ] f₀ + f₁ ∧
    lorentzNorm μ p₀ q₀ f₀ + ENNReal.ofReal t * lorentzNorm μ p₁ q₁ f₁ = r}

/-- The `(θ,q)`-quasinorm built from a Lorentz-couple K-functional:
`(∫₀^∞ [t^{-θ} K(t,f)]^q dt/t)^{1/q}`. -/
noncomputable def lorentzRealInterpolationNorm (p₀ q₀ p₁ q₁ θ q : ℝ≥0∞) (f : α → E) : ℝ≥0∞ :=
  (∫⁻ t in Ioi (0 : ℝ),
    (ENNReal.ofReal t ^ (-θ.toReal) * lorentzKFunctional μ p₀ q₀ p₁ q₁ t f) ^ q.toReal *
      ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal

/-- Triebel §1.18.6, Lemma: `L_{p,p} = Lᵖ`. -/
theorem lorentzNorm_diag (p : ℝ≥0∞) (f : α → E) :
    lorentzNorm μ p p f = eLpNorm f p μ := by
  sorry

/-- Triebel §1.18.6, Lemma: `L_{p,∞}` is the classical weak-`Lᵖ` (Marcinkiewicz) space:
`‖f‖_{L_{p,∞}} = sup_σ σ · ϱ(f,σ)^{1/p}`. -/
theorem lorentzNorm_top_eq_iSup (p : ℝ≥0∞) (f : α → E) :
    lorentzNorm μ p ⊤ f = ⨆ σ : ℝ≥0∞, σ * distributionFunction μ f σ ^ p⁻¹.toReal := by
  sorry

/-- Triebel §1.18.6, Theorem 1 proof, eq. (9): `K(t,f;L1,L∞) = ∫₀ᵗ f*(τ) dτ`, the exact
computational core of the whole `Lᵖ`-interpolation theory. -/
theorem kFunctional_L1_Linfty (t : ℝ) (f : α → E) :
    lorentzKFunctional μ 1 1 ⊤ ⊤ t f = ∫⁻ τ in Ioc (0 : ℝ) t, decreasingRearrangement μ f
      (ENNReal.ofReal τ) := by
  sorry

/-- Triebel §1.18.6, Theorem 2 — the general `Lᵖ`/Lorentz real-interpolation identification:
for `0<θ<1`, `1≤p₀,p₁≤∞`, `p₀≠p₁`, `1≤q₀,q₁,q≤∞`, `1/p=(1-θ)/p₀+θ/p₁`, the `(θ,q)`-quasinorm
built from the `(L_{p₀,q₀},L_{p₁,q₁})` K-functional is equivalent to the `L_{p,q}` Lorentz norm. -/
theorem lorentzKFunctional_equiv_lorentzNorm {p₀ p₁ q₀ q₁ p q : ℝ≥0∞} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : α → E) :
    ∃ c₁ c₂ : ℝ≥0, 0 < c₁ ∧ 0 < c₂ ∧
      c₁ * lorentzRealInterpolationNorm μ p₀ q₀ p₁ q₁ (ENNReal.ofReal θ) q f ≤
        lorentzNorm μ p q f ∧
      lorentzNorm μ p q f ≤ c₂ * lorentzRealInterpolationNorm μ p₀ q₀ p₁ q₁
        (ENNReal.ofReal θ) q f := by
  sorry

/-- **The Marcinkiewicz interpolation theorem** (couple-identification form): the `q₀=q₁=∞`,
`q=p` specialization of `lorentzKFunctional_equiv_lorentzNorm` — interpolating weak-`Lᵖ⁰` and
weak-`Lᵖ¹` gives `Lᵖ`. This is literally Ryan's stated end goal for the K-method arc. -/
theorem marcinkiewicz_interpolation {p₀ p₁ p : ℝ≥0∞} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : α → E) :
    ∃ c₁ c₂ : ℝ≥0, 0 < c₁ ∧ 0 < c₂ ∧
      c₁ * lorentzRealInterpolationNorm μ p₀ ⊤ p₁ ⊤ (ENNReal.ofReal θ) p f ≤ eLpNorm f p μ ∧
      eLpNorm f p μ ≤ c₂ * lorentzRealInterpolationNorm μ p₀ ⊤ p₁ ⊤ (ENNReal.ofReal θ) p f := by
  sorry
