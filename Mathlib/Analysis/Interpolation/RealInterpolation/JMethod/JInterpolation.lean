/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JFunctional
import Mathlib.Analysis.Normed.Quasi.AokiRolewicz
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Real interpolation spaces via the discrete J-method

DRAFT — statements only, awaiting review.

The discrete J-method (Bergh–Löfström §3.10–3.11; the continuous version is Triebel §1.6.1).
For an interpolation couple `{A₀, A₁}`, `θ ∈ ℝ` and `0 < q ≤ ∞`, a *representation* of
`a ∈ A₀ + A₁` is a family `u : ℤ → A₀ ∩ A₁` with `a = ∑ᵥ uᵥ` in `A₀ + A₁` (unconditional
summation, `HasSum`). The `(θ,q)` J-quasinorm of `a` is the infimum over representations of the
`ℓ^q(ℤ)` quasinorm of `ν ↦ 2^{-νθ} J(2^ν, uᵥ)`, the latter taken as Mathlib's `eLpNorm` for the
counting measure (so `q = ∞` is the supremum automatically). It is `∞` when `a` has no
representation.

For quasi-Banach couples the series is the right object (an integral `∫ u(t) dt/t` would need a
Banach space); the Aoki–Rolewicz theorem controls `‖∑ᵥ uᵥ‖` in `A₀ + A₁`.

The space itself, as a quasi-normed space with its sandwich and morphism maps, is in
`JMethod/JInterpolationSpace.lean`.

## Main definitions
* `InterpolationCouple.jSequenceENorm θ q u`: `‖(2^{-νθ} J(2^ν, uᵥ))ᵥ‖_{ℓ^q}`.
* `InterpolationCouple.jInterpolationENorm θ q a`: its infimum over representations of `a`.

## Main statements
* `jInterpolationENorm_zero`, `jInterpolationENorm_smul`, `exists_jInterpolationENorm_add_le`.
* `jInterpolationENorm_meetToSum_le`: `‖b‖_J ≤ ‖b‖_{A₀ ∩ A₁}` (one-term representation).
* `exists_ofReal_mul_norm_le_jInterpolationENorm`: `c ‖a‖_{A₀ + A₁} ≤ ‖a‖_J` for `0 < θ < 1`,
  `0 < q` (via the K–J inequality and Aoki–Rolewicz in `A₀ + A₁`).
* `InterpolationCat.Hom.jInterpolationENorm_sumMap_le`: a morphism of couples with leg bounds
  `M₀, M₁` has `‖T a‖_J ≤ 2 M₀^{1-θ} M₁^θ ‖a‖_J`. The factor `2` comes from discretizing the
  rescaling `t ↦ t M₁ / M₀`; the discrete J-method is not exact.
-/

open MeasureTheory
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- The `ℓ^q(ℤ)` quasinorm of `ν ↦ 2^{-νθ} J(2^ν, uᵥ)` for a family `u : ℤ → A₀ ∩ A₁`. -/
noncomputable def jSequenceENorm (θ : ℝ) (q : ℝ≥0∞) (u : ℤ → meet ι₀ ι₁) : ℝ≥0∞ :=
  eLpNorm (fun ν : ℤ => ENNReal.ofReal (((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν)))
    q Measure.count

/-- The discrete J-method `(θ,q)` quasinorm: the infimum of `jSequenceENorm θ q u` over all
representations `a = ∑ᵥ uᵥ` (in `A₀ + A₁`) with `uᵥ ∈ A₀ ∩ A₁`; `∞` if there is none. -/
noncomputable def jInterpolationENorm (θ : ℝ) (q : ℝ≥0∞) (a : sum ι₀ ι₁) : ℝ≥0∞ :=
  ⨅ (u : ℤ → meet ι₀ ι₁) (_ : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a),
    jSequenceENorm ι₀ ι₁ θ q u

omit [T2Space 𝒜] in
/-- `jSequenceENorm` is the `eLpNorm` of the corresponding nonnegative real sequence, so the
real-valued `eLpNorm` API (scaling, quasi-triangle inequality) applies. -/
private theorem jSequenceENorm_eq (θ : ℝ) (q : ℝ≥0∞) (u : ℤ → meet ι₀ ι₁) :
    jSequenceENorm ι₀ ι₁ θ q u =
      eLpNorm (fun ν : ℤ => ((2 : ℝ) ^ ν) ^ (-θ) * JFunctional ι₀ ι₁ (2 ^ ν) (u ν))
        q Measure.count :=
  eLpNorm_congr_enorm_ae Measurable.of_discrete.aestronglyMeasurable
    Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun ν => by
      rw [enorm_eq_self, Real.enorm_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (zpow_nonneg zero_le_two _) _) (jFunctional_nonneg ι₀ ι₁ _ _))])

/-- Any representation bounds the J-quasinorm. -/
theorem jInterpolationENorm_le (θ : ℝ) (q : ℝ≥0∞) {a : sum ι₀ ι₁} (u : ℤ → meet ι₀ ι₁)
    (hu : HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a) :
    jInterpolationENorm ι₀ ι₁ θ q a ≤ jSequenceENorm ι₀ ι₁ θ q u :=
  iInf₂_le u hu

theorem jInterpolationENorm_zero (θ : ℝ) (q : ℝ≥0∞) :
    jInterpolationENorm ι₀ ι₁ θ q 0 = 0 := by
  sorry

theorem jInterpolationENorm_smul (θ : ℝ) (q : ℝ≥0∞) (c : 𝕜) (a : sum ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q (c • a) = ‖c‖ₑ * jInterpolationENorm ι₀ ι₁ θ q a := by
  sorry

/-- Quasi-triangle inequality for the J-quasinorm, with a real constant `C ≥ 1` (add the two
representations termwise; combine `jFunctional_add_le` with the `ℓ^q` quasi-triangle inequality). -/
theorem exists_jInterpolationENorm_add_le (θ : ℝ) (q : ℝ≥0∞) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : sum ι₀ ι₁,
      jInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        ENNReal.ofReal C * (jInterpolationENorm ι₀ ι₁ θ q a + jInterpolationENorm ι₀ ι₁ θ q b) := by
  sorry

/-- The "`A₀ ∩ A₁ ⊂`" half of the sandwich: the one-term representation `u₀ = b` gives
`‖b‖_J ≤ J(1, b) = ‖b‖`. -/
theorem jInterpolationENorm_meetToSum_le (θ : ℝ) (q : ℝ≥0∞) (b : meet ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q (meetToSum ι₀ ι₁ b) ≤ ENNReal.ofReal ‖b‖ := by
  sorry

/-- The "`⊂ A₀ + A₁`" half of the sandwich: `c ‖a‖_{A₀ + A₁} ≤ ‖a‖_J` for some `c > 0`. For a
representation, `‖uᵥ‖_{A₀+A₁} ≤ min(1, 2^{-ν}) J(2^ν, uᵥ) ≤ min(2^{νθ}, 2^{ν(θ-1)}) ‖x‖_{ℓ^q}`
(`x` the weighted sequence), and Aoki–Rolewicz in `A₀ + A₁` sums the geometric weights. -/
theorem exists_ofReal_mul_norm_le_jInterpolationENorm (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : sum ι₀ ι₁,
      ENNReal.ofReal (c * ‖a‖) ≤ jInterpolationENorm ι₀ ι₁ θ q a := by
  sorry

theorem jInterpolationENorm_eq_zero_iff (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞}
    (hq : 0 < q) (a : sum ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q a = 0 ↔ a = 0 := by
  sorry

end InterpolationCouple

/-- A morphism of couples `T` with `opQuasiNorm T.f₀ ≤ M₀`, `opQuasiNorm T.f₁ ≤ M₁` satisfies
`‖T a‖_J ≤ 2 M₀^{1-θ} M₁^θ ‖a‖_J` (`θ ≥ 0`). Proof: map a representation by `T.meetMap`, use
`Hom.jFunctional_meetMap_le`, and shift the index by the `k ∈ ℤ` with
`2^k ≤ M₁/M₀ < 2^{k+1}`; the mismatch costs `max(1, (M₁/M₀)/2^k) ≤ 2`. -/
theorem InterpolationCat.Hom.jInterpolationENorm_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ≥0∞)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.jInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap a) ≤
      ENNReal.ofReal (2 * (M₀ ^ (1 - θ) * M₁ ^ θ)) *
        InterpolationCouple.jInterpolationENorm C.ι₀ C.ι₁ θ q a := by
  sorry
