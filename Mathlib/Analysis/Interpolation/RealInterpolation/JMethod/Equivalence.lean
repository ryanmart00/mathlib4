/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.FundamentalLemma
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JInterpolationSpace
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.DiscreteK
import Mathlib.Analysis.Interpolation.RealInterpolation.KMethod.RealInterpolationSpace

/-!
# The equivalence theorem `K = J`

Bergh–Löfström Theorem 3.11.3 (Theorem 3.3.1 for normed couples): for `0 < θ < 1` and
`0 < q ≤ ∞`, the discrete J-method and the K-method give the same subspace of `A₀ + A₁`, with
equivalent quasinorms.

* `K ⊂ J` (B–L's "converse inequality"): the fundamental lemma
  `exists_jFunctional_le_kFunctional` represents `a` by `uᵥ` with `J(2^ν, uᵥ) ≤ γ K(2^ν, a)`; the
  discrete K-method (`KMethod/DiscreteK.lean`) then bounds `‖a‖_J` by `‖a‖_K`. The fundamental
  lemma only gives symmetric partial sums; for `a` of finite K-quasinorm the terms decay
  geometrically, so (Aoki–Rolewicz, completeness of `A₀ + A₁`) the series converges
  unconditionally, as the J-method's representations require
  (`exists_hasSum_jFunctional_le_kFunctional`).
* `J ⊂ K`: for `a = ∑ᵥ uᵥ`, the Aoki–Rolewicz inequality for the quasi-norm `K(t, ·)` and
  `K(t, uᵥ) ≤ min(1, t 2^{-ν}) J(2^ν, uᵥ)` give
  `K(2^μ, a) ≲ (∑ᵥ (min(1, 2^ν) J(2^{μ-ν}, u_{μ-ν}))^ρ)^{1/ρ}`, and Minkowski's inequality in
  `ℓ^{q/ρ}` (with `ρ < q`) finishes the proof.

## Main statements
* `exists_hasSum_jFunctional_le_kFunctional`: J-representations from the fundamental lemma.
* `exists_jInterpolationENorm_le_mul_realInterpolationENorm`: `‖a‖_J ≤ C ‖a‖_K`.
* `exists_realInterpolationENorm_le_mul_jInterpolationENorm`: `‖a‖_K ≤ C ‖a‖_J`.
* `jInterpolationSubmodule_eq_realInterpolationSubmodule`: the two spaces coincide.
-/

open Filter
open scoped ENNReal Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- For `a` of finite `(θ,q)` K-quasinorm, the representation of the fundamental lemma converges
unconditionally: there is `u : ℤ → A₀ ∩ A₁` with `a = ∑ᵥ uᵥ` (`HasSum` in `A₀ + A₁`) and
`J(2^ν, uᵥ) ≤ 3 (1 + ε) C K(2^ν, a)`. -/
theorem exists_hasSum_jFunctional_le_kFunctional [CompleteSpace A₀] [CompleteSpace A₁]
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) {a : sum ι₀ ι₁}
    (ha : realInterpolationENorm ι₀ ι₁ θ q a ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℤ → meet ι₀ ι₁, HasSum (fun ν => meetToSum ι₀ ι₁ (u ν)) a ∧
      ∀ ν : ℤ, JFunctional ι₀ ι₁ (2 ^ ν) (u ν) ≤
        3 * (1 + ε) * max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
          (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) *
          KFunctional ι₀ ι₁ (2 ^ ν) a :=
  sorry

/-- `K ⊂ J` (B–L Theorem 3.11.3, via the fundamental lemma as in the proof of Theorem 3.3.1):
`‖a‖_{θ,q;J} ≤ 6 C 2^θ (log 2)^{-1/q} ‖a‖_{θ,q;K}`, with `C = max C₀ C₁` the larger
quasi-triangle constant. The fundamental lemma with `ε = 1` gives `J(2^ν, uᵥ) ≤ 6 C K(2^ν, a)`, and
`2^θ (log 2)^{-1/q}` is the inverse of the lower constant of the discrete K-method
(`ofReal_mul_kSequenceENorm_le_realInterpolationENorm`). -/
theorem jInterpolationENorm_le_mul_realInterpolationENorm [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q)
    (a : sum ι₀ ι₁) :
    jInterpolationENorm ι₀ ι₁ θ q a ≤
      ENNReal.ofReal (6 * max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
          (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) * 2 ^ θ) *
        (ENNReal.ofReal (Real.log 2) ^ q⁻¹.toReal)⁻¹ * realInterpolationENorm ι₀ ι₁ θ q a :=
  sorry

/-- `K ⊂ J` with an unspecified constant: `‖a‖_{θ,q;J} ≤ C ‖a‖_{θ,q;K}`. -/
theorem exists_jInterpolationENorm_le_mul_realInterpolationENorm [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum ι₀ ι₁,
      jInterpolationENorm ι₀ ι₁ θ q a ≤ C * realInterpolationENorm ι₀ ι₁ θ q a :=
  sorry

/-- `J ⊂ K` (B–L Theorem 3.11.3, first half): `‖a‖_{θ,q;K} ≤ C ‖a‖_{θ,q;J}`. -/
theorem exists_realInterpolationENorm_le_mul_jInterpolationENorm {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : sum ι₀ ι₁,
      realInterpolationENorm ι₀ ι₁ θ q a ≤ C * jInterpolationENorm ι₀ ι₁ θ q a :=
  sorry

/-- The equivalence theorem (B–L Theorem 3.11.3): `J_{θ,q}(A) = K_{θ,q}(A)` as subspaces of
`A₀ + A₁`. -/
theorem jInterpolationSubmodule_eq_realInterpolationSubmodule [CompleteSpace A₀]
    [CompleteSpace A₁] {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ≥0∞} (hq : 0 < q) :
    jInterpolationSubmodule ι₀ ι₁ θ q = realInterpolationSubmodule ι₀ ι₁ θ q :=
  sorry

end InterpolationCouple
