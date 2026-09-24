/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Lorentz.Couple
import Mathlib.Analysis.Interpolation.RealInterpolation.Basic
import Mathlib.MeasureTheory.Function.LorentzSpace.Diag
import Mathlib.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of the couple `(Lʳ, L^∞)`

DRAFT — statements only.

Triebel §1.18.6, Theorem 1, in the quasi-Banach form (Krée; Bergh–Löfström §5.3): for
`0 < r < ∞`, the couple `(Lʳ, L^∞)`, realized as `InterpolationCat.lorentz 𝕜 μ E r r ⊤ ⊤`
(`L_{r,r} = Lʳ` and `L_{∞,∞} = L^∞` by `LorentzSpace.eq_Lp`), has

* K-functional `K(t, f; Lʳ, L^∞) ≈ (∫₀^{tʳ} f*(s)ʳ ds)^{1/r}` (for `r = 1`: `∫₀ᵗ f*`), with
  constants depending only on `r` (`lorentz_kFunctional_le`, `le_lorentz_kFunctional`);
* real interpolation spaces `(Lʳ, L^∞)_{θ,q} = L_{p,q}` for `1/p = (1-θ)/r` and `r ≤ q`, as an
  isomorphism in `QuasiBanachCat` compatible with the inclusions into `L⁰(μ)`
  (`nonempty_iso_realInterpolation_lorentz_top`).

The hypothesis `r ≤ q` is what makes Hardy's inequality (`lintegral_hardy`, exponent `q/r ≥ 1`)
applicable. It costs nothing downstream: in the reiteration argument `r` can be chosen as small as
needed.

## Proof outline
* `K ≤ 2 (∫₀^{tʳ} f*ʳ)^{1/r}`: split `f` by truncating `‖f‖` at height `f*(tʳ)`.
* `(∫₀^{tʳ} f*ʳ)^{1/r} ≤ C K`: for `f = f₀ + f₁`, `f*(s) ≤ f₀*(s) + ‖f₁‖_∞`
  (`decreasingRearrangement_add_le`), then the quasi-triangle inequality in `Lʳ(0, tʳ)` and
  `∫₀^∞ f₀*ʳ = ‖f₀‖ʳ_r` (`lintegral_decreasingRearrangement_rpow`).
* Identification: substitute `T = tʳ` in the `(θ,q)`-quasinorm. The upper bound for the
  `(θ,q)`-quasinorm is Hardy's inequality with `g = f*ʳ`, `λ = θ`, `s = q/r`; the lower bound is
  `(∫₀^T f*ʳ)^{1/r} ≥ T^{1/r} f*(T)`.
-/

open MeasureTheory Set CategoryTheory
open scoped ENNReal NNReal

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable (r : ℝ≥0∞) [Fact (0 < r)]

namespace InterpolationCat

/-- Upper bound for the K-functional of `(Lʳ, L^∞)`:
`K(t, f) ≤ c (∫₀^{tʳ} f*(s)ʳ ds)^{1/r}`, uniformly in `t > 0` and `f ∈ Lʳ + L^∞`. -/
theorem lorentz_kFunctional_le (hr : r ≠ ⊤) :
    ∃ c : ℝ≥0, ∀ t : ℝ, 0 < t → ∀ a : InterpolationCouple.sum (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁,
      ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) ≤
        c * (∫⁻ s in Ioc 0 (t ^ r.toReal), decreasingRearrangement μ
          (lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a) (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ := by
  sorry

/-- Lower bound for the K-functional of `(Lʳ, L^∞)`:
`(∫₀^{tʳ} f*(s)ʳ ds)^{1/r} ≤ c K(t, f)`, uniformly in `t > 0` and `f ∈ Lʳ + L^∞`. -/
theorem le_lorentz_kFunctional (hr : r ≠ ⊤) :
    ∃ c : ℝ≥0, ∀ t : ℝ, 0 < t → ∀ a : InterpolationCouple.sum (lorentz 𝕜 μ E r r ⊤ ⊤).ι₀
        (lorentz 𝕜 μ E r r ⊤ ⊤).ι₁,
      (∫⁻ s in Ioc 0 (t ^ r.toReal), decreasingRearrangement μ
          (lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ a) (ENNReal.ofReal s) ^ r.toReal) ^ r.toReal⁻¹ ≤
        c * ENNReal.ofReal (InterpolationCouple.KFunctional _ _ t a) := by
  sorry

/-- Triebel §1.18.6, Theorem 1 (quasi-Banach form): `(Lʳ, L^∞)_{θ,q} = L_{p,q}` for
`1/p = (1-θ)/r` and `r ≤ q`, as an isomorphism of quasi-Banach spaces compatible with the
inclusions of both sides into `L⁰(μ)`. -/
theorem nonempty_iso_realInterpolation_lorentz_top (hr : r ≠ ⊤) (θ : ℝ) (q : ℝ≥0∞)
    [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)] (hrq : r ≤ q) (p : ℝ≥0∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * r⁻¹) :
    ∃ e : (realInterpolationFunctor 𝕜 θ q).obj (lorentz 𝕜 μ E r r ⊤ ⊤) ≅
        QuasiBanachCat.of 𝕜 (LorentzSpace E p q μ),
      ∀ x, lorentzSumToL0 𝕜 μ E r r ⊤ ⊤ ((realInterpolationFunctor 𝕜 θ q).toSum _ x) =
        LorentzSpace.toL0 μ E 𝕜 p q (e.hom.hom x) := by
  sorry

end InterpolationCat
