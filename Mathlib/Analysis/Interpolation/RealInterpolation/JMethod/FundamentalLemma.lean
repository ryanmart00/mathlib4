/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JFunctional
import Mathlib.Data.Int.Interval

/-!
# The fundamental lemma of interpolation theory

For an interpolation couple `{A₀, A₁}` and `a ∈ A₀ + A₁` with `K(t,a) → 0` as `t → 0⁺` and
`K(t,a)/t → 0` as `t → ∞`, there is a family `u : ℤ → A₀ ∩ A₁` with `a = ∑ᵥ uᵥ` and
`J(2^ν, uᵥ) ≤ γ K(2^ν, a)` for every `ν` (Bergh–Löfström Lemma 3.3.2; Triebel §1.3 for the
continuous version). This is the bridge from the K-method to the J-method: it is the `K ⊂ J`
half of the equivalence theorem.

The proof is a telescoping argument: pick near-optimal decompositions
`a = a₀(ν) + a₁(ν)` for `K(2^ν, a)` and set `uᵥ = a₀(ν) - a₀(ν-1) = a₁(ν-1) - a₁(ν)`.
For quasi-Banach couples the constant picks up the quasi-triangle constants of `A₀`, `A₁`:
`γ = 3 (1 + ε) C` with `C = max C₀ C₁`, recovering Bergh–Löfström's `3 (1 + ε)` for Banach
couples.

The series converges as *symmetric* partial sums `∑_{|ν| ≤ N} uᵥ`, which is all the telescoping
gives under these hypotheses. Unconditional convergence (`HasSum`, as in the J-method's
representations) needs decay of `‖uᵥ‖`, which holds for `a` in a real interpolation space and is
established where the lemma is applied.

## Main statements
* `InterpolationCouple.exists_jFunctional_le_kFunctional`: the fundamental lemma.
-/

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

namespace InterpolationCouple

/-- **The fundamental lemma of interpolation theory** (Bergh–Löfström Lemma 3.3.2), for
quasi-normed couples. If `K(t,a) → 0` as `t → 0⁺` and `K(t,a)/t → 0` as `t → ∞`, then for every
`ε > 0` there is `u : ℤ → A₀ ∩ A₁` whose symmetric partial sums converge to `a` in `A₀ + A₁`, with
`J(2^ν, uᵥ) ≤ 3 (1 + ε) C K(2^ν, a)`, `C` the larger of the quasi-triangle constants of `A₀`, `A₁`.
-/
theorem exists_jFunctional_le_kFunctional {a : sum ι₀ ι₁}
    (h0 : Tendsto (fun t => KFunctional ι₀ ι₁ t a) (𝓝[>] 0) (𝓝 0))
    (hT : Tendsto (fun t => KFunctional ι₀ ι₁ t a / t) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℤ → meet ι₀ ι₁,
      Tendsto (fun N : ℕ => ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, meetToSum ι₀ ι₁ (u ν)) atTop (𝓝 a) ∧
      ∀ ν : ℤ, JFunctional ι₀ ι₁ (2 ^ ν) (u ν) ≤
        3 * (1 + ε) * max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
          (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) *
          KFunctional ι₀ ι₁ (2 ^ ν) a :=
  sorry

end InterpolationCouple
