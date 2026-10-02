/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.KFunctional

/-!
# The J-functional

DRAFT — statements only, awaiting review.

For an interpolation couple `{A₀, A₁}`, `t ≥ 0`, and `a ∈ A₀ ∩ A₁`,
`J(t, a) = max(‖a‖_{A₀}, t ‖a‖_{A₁})` (Triebel §1.6.1; Bergh–Löfström §3.2). It is the dual
counterpart of the K-functional: `K(t, ·)` is an equivalent family of quasi-norms on `A₀ + A₁`,
and `J(t, ·)` one on `A₀ ∩ A₁`. Triebel's J-method is the continuous one, `a = ∫₀^∞ u(t) dt/t`;
we will use the discrete version (Bergh–Löfström §3.10–3.11), which describes `(A₀, A₁)_{θ,q}`
through decompositions `a = ∑ᵥ uᵥ` with `uᵥ ∈ A₀ ∩ A₁`, measured by `J(2^ν, uᵥ)`. Unlike the
integral, the series makes sense for quasi-Banach couples (by Aoki–Rolewicz).

An element `b` of the meet is a pair `(a₀, a₁)` with `ι₀ a₀ = ι₁ a₁`, so `J` reads off both
components; `J(1, b)` is exactly the meet's own quasi-norm (`jFunctional_one`).

## Main definitions
* `InterpolationCouple.JFunctional t b`: `max ‖b.1‖ (t * ‖b.2‖)`.

## Main results
* Basic properties: `jFunctional_nonneg`, `jFunctional_one`, `jFunctional_mono`,
  `jFunctional_le_max_div_mul` (`J(t, b) ≤ max(1, t/s) J(s, b)`), `jFunctional_zero`,
  `jFunctional_smul`, `jFunctional_add_le`.
* `kFunctional_meetToSum_le_jFunctional`: `K(t, b) ≤ min(1, t/s) J(s, b)`, the basic inequality
  linking the two functionals (used for the J ⊂ K half of the equivalence theorem).
* `InterpolationCat.Hom.jFunctional_meetMap_le`: naturality, the J-analogue of
  `Hom.kFunctional_sumMap_le`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁] [CompleteSpace A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

/-- The J-functional on the meet: `J(t, (a₀, a₁)) = max(‖a₀‖, t ‖a₁‖)`. -/
noncomputable def InterpolationCouple.JFunctional (t : ℝ) (b : InterpolationCouple.meet ι₀ ι₁) :
    ℝ :=
  max ‖(b : A₀ × A₁).1‖ (t * ‖(b : A₀ × A₁).2‖)

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.jFunctional_nonneg (t : ℝ) (b : InterpolationCouple.meet ι₀ ι₁) :
    0 ≤ InterpolationCouple.JFunctional ι₀ ι₁ t b :=
  le_max_of_le_left (QuasinormedAddCommGroup.norm_nonneg _)

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `J(1, ·)` is the meet's own quasi-norm (the max-norm of `A₀ × A₁`, restricted). -/
theorem InterpolationCouple.jFunctional_one (b : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.JFunctional ι₀ ι₁ 1 b = ‖b‖ := by
  change _ = ‖(b : A₀ × A₁)‖
  rw [InterpolationCouple.JFunctional, one_mul, Prod.norm_def]

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `J(t, b)` is monotone increasing in `t`. -/
theorem InterpolationCouple.jFunctional_mono {s t : ℝ} (hst : s ≤ t)
    (b : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.JFunctional ι₀ ι₁ s b ≤ InterpolationCouple.JFunctional ι₀ ι₁ t b :=
  max_le_max le_rfl (mul_le_mul_of_nonneg_right hst (QuasinormedAddCommGroup.norm_nonneg _))

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- Change of parameter: `J(t, b) ≤ max(1, t/s) J(s, b)` for `s > 0`. -/
theorem InterpolationCouple.jFunctional_le_max_div_mul {s t : ℝ} (hs : 0 < s)
    (b : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.JFunctional ι₀ ι₁ t b ≤
      max 1 (t / s) * InterpolationCouple.JFunctional ι₀ ι₁ s b := by
  have hx := QuasinormedAddCommGroup.norm_nonneg (b : A₀ × A₁).1
  have hy := QuasinormedAddCommGroup.norm_nonneg (b : A₀ × A₁).2
  have hm : 1 ≤ max 1 (t / s) := le_max_left _ _
  unfold InterpolationCouple.JFunctional
  refine max_le ?_ ?_
  · exact (le_max_left _ _).trans (le_mul_of_one_le_left (le_max_of_le_left hx) hm)
  · calc t * ‖(b : A₀ × A₁).2‖ = t / s * (s * ‖(b : A₀ × A₁).2‖) := by field_simp
      _ ≤ _ := mul_le_mul (le_max_right _ _) (le_max_right _ _) (mul_nonneg hs.le hy)
          (zero_le_one.trans hm)

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.jFunctional_zero (t : ℝ) :
    InterpolationCouple.JFunctional ι₀ ι₁ t 0 = 0 := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The J-functional is absolutely homogeneous: `J(t, c • b) = ‖c‖ · J(t, b)`. -/
theorem InterpolationCouple.jFunctional_smul (t : ℝ) (c : 𝕜)
    (b : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.JFunctional ι₀ ι₁ t (c • b) =
      ‖c‖ * InterpolationCouple.JFunctional ι₀ ι₁ t b := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- Quasi-subadditivity: `J(t, a + b) ≤ C (J(t, a) + J(t, b))`, with `C` the larger of the two
legs' quasi-triangle constants (as in `kFunctional_add_le`). -/
theorem InterpolationCouple.jFunctional_add_le (t : ℝ) (a b : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.JFunctional ι₀ ι₁ t (a + b) ≤
      max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
        (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) *
        (InterpolationCouple.JFunctional ι₀ ι₁ t a +
          InterpolationCouple.JFunctional ι₀ ι₁ t b) := by
  sorry

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The basic K–J inequality: for `b ∈ A₀ ∩ A₁`, `s > 0` and `t ≥ 0`,
`K(t, b) ≤ min(1, t/s) J(s, b)`. The case `s = 1` is `kFunctional_meetToSum_le`. -/
theorem InterpolationCouple.kFunctional_meetToSum_le_jFunctional {s t : ℝ} (hs : 0 < s)
    (ht : 0 ≤ t) (b : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.KFunctional ι₀ ι₁ t (InterpolationCouple.meetToSum ι₀ ι₁ b) ≤
      min 1 (t / s) * InterpolationCouple.JFunctional ι₀ ι₁ s b := by
  sorry

/-- Naturality of `J` (the analogue of `Hom.kFunctional_sumMap_le`): a morphism `T : C ⟶ D` with
`opQuasiNorm T.f₀ ≤ M₀`, `opQuasiNorm T.f₁ ≤ M₁` satisfies
`J_D(t, T b) ≤ M₀ · J_C(t M₁ / M₀, b)`. As there, `M₀ > 0` is a free upper bound rather than the
exact operator quasi-norm, to avoid the `x / 0 = 0` degenerate case. -/
theorem InterpolationCat.Hom.jFunctional_meetMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (t : ℝ) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (b : InterpolationCouple.meet C.ι₀ C.ι₁) :
    InterpolationCouple.JFunctional D.ι₀ D.ι₁ t (T.meetMap b) ≤
      M₀ * InterpolationCouple.JFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) b := by
  sorry
