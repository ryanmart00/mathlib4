/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Lorentz.LrLinfty
import Mathlib.Analysis.Interpolation.RealInterpolation.Reiteration

/-!
# Real interpolation of Lorentz spaces and the Marcinkiewicz interpolation theorem

DRAFT — statements only, all proofs deferred (`sorry`).

We identify the real interpolation spaces of a couple of Lorentz spaces (Bergh–Löfström
Theorem 5.3.1; Triebel, *Interpolation Theory, Function Spaces, Differential Operators*,
§1.18.6, Theorem 2), and deduce the Marcinkiewicz interpolation theorem (Bergh–Löfström
Theorem 5.3.2). Following Bergh–Löfström, the identification is obtained from the base case
`(Lʳ, L^∞)_{θ,q} = L_{p,q}` (`InterpolationCat.nonempty_iso_realInterpolation_lorentz_top`) by
the reiteration theorem (`InterpolationCat.nonempty_iso_realInterpolationFunctor_reiteration`).

## Main results

* `InterpolationCat.nonempty_iso_realInterpolation_lorentz`:
  `(L_{p₀,q₀}, L_{p₁,q₁})_{θ,q} = L_{p,q}` for `p₀ ≠ p₁`, `1/p = (1-θ)/p₀ + θ/p₁`.
* `InterpolationCat.nonempty_iso_realInterpolation_lorentz_top_top`: interpolating two weak-`Lᵖ`
  spaces, `(L_{p₀,∞}, L_{p₁,∞})_{θ,p} = L_{p,p}` (which is `Lᵖ`, by `LorentzSpace.eq_Lp`).
* `LorentzSpace.exists_lorentzNorm_le_of_le`: `L_{p,q} ⊆ L_{p,r}` for `q ≤ r`.
* `InterpolationCat.exists_lorentz_interpolation`: the Marcinkiewicz interpolation theorem in
  Lorentz-space form (Bergh–Löfström Theorem 5.3.2, (4)).
* `InterpolationCat.exists_lp_interpolation`: its strong-type form (Bergh–Löfström Theorem 5.3.2,
  (5)): a map of weak types `(p₀, q₀)` and `(p₁, q₁)` is of strong type `(p, q)` when `p ≤ q`.
* `lorentzNorm_top_eq_iSup`: `L_{p,∞}` is the classical weak-`Lᵖ` space.
-/

open MeasureTheory CategoryTheory
open scoped ENNReal NNReal

section WeakLp

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]

/-- `L_{p,∞}` is the classical weak-`Lᵖ` (Marcinkiewicz) space (Triebel §1.18.6, Lemma):
`‖f‖_{L_{p,∞}} = sup_σ σ ϱ(f,σ)^{1/p}` for `0 < p < ∞`. -/
theorem lorentzNorm_top_eq_iSup {p : ℝ≥0∞} (hp0 : 0 < p) (hp : p ≠ ⊤) (f : α → E) :
    lorentzNorm μ p ⊤ f = ⨆ σ : ℝ≥0∞, σ * distributionFunction μ f σ ^ p⁻¹.toReal := by
  simp only [lorentzNorm, ↓reduceIte]
  set a := p⁻¹.toReal
  have ha0 : 0 < a :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hp) (ENNReal.inv_ne_top.2 hp0.ne')
  apply le_antisymm
  · -- `t^{1/p} f*(t) ≤ sup_σ σ ϱ(σ)^{1/p}`: every `σ < f*(t)` has `t < ϱ(σ)`
    refine iSup_le fun t => ?_
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [ENNReal.zero_rpow_of_pos ha0]
    have hta0 : (t : ℝ≥0∞) ^ a ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.2 (pos_iff_ne_zero.2 ht0)) ENNReal.coe_ne_top).ne'
    have htat : (t : ℝ≥0∞) ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha0.le ENNReal.coe_ne_top
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hta0) (Or.inl htat)]
    refine le_of_forall_lt_imp_le_of_dense fun σ hσ => ?_
    have hσt : t < distributionFunction μ f σ :=
      (lt_decreasingRearrangement_iff μ f t (ne_top_of_lt hσ)).1 hσ
    rw [ENNReal.le_div_iff_mul_le (Or.inl hta0) (Or.inl htat)]
    calc σ * (t : ℝ≥0∞) ^ a ≤ σ * distributionFunction μ f σ ^ a := by gcongr
      _ ≤ _ := le_iSup (fun σ => σ * distributionFunction μ f σ ^ a) σ
  · -- `σ ϱ(σ)^{1/p} ≤ sup_t t^{1/p} f*(t)`: every `t < ϱ(σ)` has `σ < f*(t)`
    refine iSup_le fun σ => ?_
    rcases eq_or_ne σ ⊤ with rfl | hσt
    · simp [distributionFunction, ENNReal.zero_rpow_of_pos ha0]
    rcases eq_or_ne σ 0 with rfl | hσ0
    · simp
    set L := ⨆ t : ℝ≥0, (t : ℝ≥0∞) ^ a * decreasingRearrangement μ f t
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hσ0) (Or.inl hσt),
      ← ENNReal.rpow_inv_rpow ha0.ne' (L / σ)]
    refine ENNReal.rpow_le_rpow (le_of_forall_lt_imp_le_of_dense fun t ht => ?_) ha0.le
    have hσlt : σ < decreasingRearrangement μ f t :=
      (lt_decreasingRearrangement_iff μ f t hσt).2 ht
    rw [← ENNReal.rpow_rpow_inv ha0.ne' t]
    refine ENNReal.rpow_le_rpow ?_ (inv_nonneg.2 ha0.le)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hσ0) (Or.inl hσt)]
    calc t ^ a * σ ≤ t ^ a * decreasingRearrangement μ f t := by gcongr
      _ ≤ L := by
        lift t to ℝ≥0 using ne_top_of_lt ht
        exact le_iSup (fun t : ℝ≥0 => (t : ℝ≥0∞) ^ a * decreasingRearrangement μ f t) t

variable [SigmaFinite μ]

/-- The Lorentz spaces increase with the second index: for `0 < p < ∞` and `0 < q ≤ r`,
`‖f‖_{p,r} ≤ C ‖f‖_{p,q}` (the inclusion `L_{p,q} ⊆ L_{p,r}` used in the proof of Bergh–Löfström
Theorem 5.3.2). Proof plan: by the base case
`InterpolationCat.nonempty_iso_realInterpolation_lorentz_top` (B–L Theorem 5.2.1), this is the
monotonicity of `(A₀, A₁)_{θ,q}` in `q` (B–L Theorem 3.4.1 (b),
`InterpolationCouple.realInterpolationENorm_le_of_le`), applied to `‖f‖ : α → ℝ`. -/
theorem LorentzSpace.exists_lorentzNorm_le_of_le {p : ℝ≥0∞} (hp0 : 0 < p) (hp : p ≠ ⊤)
    {q r : ℝ≥0∞} (hq : 0 < q) (hqr : q ≤ r) :
    ∃ C : ℝ≥0, ∀ f : α → E, AEStronglyMeasurable f μ →
      lorentzNorm μ p r f ≤ C * lorentzNorm μ p q f := by
  -- B–L Theorem 5.2.1: `L_{p,·} = (Lˢ, L^∞)_{θ,·}` for `s < p`, `s ≤ q`, `1/p = (1-θ)/s`
  set s := min p q / 2
  have hs0 : 0 < s := ENNReal.half_pos (lt_min hp0 hq).ne'
  have hsp : s < p :=
    (ENNReal.div_le_div_right (min_le_left p q) 2).trans_lt (ENNReal.half_lt_self hp0.ne' hp)
  have hsq : s ≤ q := ENNReal.half_le_self.trans (min_le_right p q)
  have hst : s ≠ ⊤ := ne_top_of_lt hsp
  have hs' : 0 < s.toReal := ENNReal.toReal_pos hs0.ne' hst
  have hsp' : s.toReal < p.toReal := ENNReal.toReal_strict_mono hp hsp
  set θ := 1 - s.toReal / p.toReal with hθ
  have hθ0 : 0 < θ := by rw [hθ, sub_pos, div_lt_one (hs'.trans hsp')]; exact hsp'
  have hθ1 : θ < 1 := by rw [hθ]; linarith [div_pos hs' (hs'.trans hsp')]
  have hpθ : p⁻¹ = ENNReal.ofReal (1 - θ) * s⁻¹ := by
    rw [hθ, sub_sub_cancel, ENNReal.ofReal_div_of_pos (hs'.trans hsp'), ENNReal.ofReal_toReal hst,
      ENNReal.ofReal_toReal hp, div_eq_mul_inv, mul_comm s, mul_assoc,
      ENNReal.mul_inv_cancel hs0.ne' hst, mul_one]
  have : Fact (0 < s) := ⟨hs0⟩
  have : Fact (0 < θ) := ⟨hθ0⟩
  have : Fact (θ < 1) := ⟨hθ1⟩
  have : Fact (0 < q) := ⟨hq⟩
  have : Fact (0 < r) := ⟨hq.trans_le hqr⟩
  obtain ⟨A, hA⟩ := InterpolationCat.lorentzNorm_le_realInterpolationENorm ℝ μ ℝ s hst θ r p hpθ
  obtain ⟨B, hB⟩ := InterpolationCat.realInterpolationENorm_le_lorentzNorm ℝ μ ℝ s hst θ q hsq p hpθ
  -- B–L Theorem 3.4.1 (b): `(Lˢ, L^∞)_{θ,q} ⊆ (Lˢ, L^∞)_{θ,r}`
  obtain ⟨c, hc, hmono⟩ := InterpolationCouple.exists_realInterpolationENorm_le_of_le
    (InterpolationCat.lorentz ℝ μ ℝ s s ⊤ ⊤).ι₀ (InterpolationCat.lorentz ℝ μ ℝ s s ⊤ ⊤).ι₁
    hθ0 hθ1 hq hqr
  refine ⟨max 1 (A * c.toNNReal * B), fun f hf => ?_⟩
  -- reduce to `‖f‖ : α → ℝ`, as an element `F` of `L⁰`
  have hnorm (p q : ℝ≥0∞) : lorentzNorm μ p q (fun x => ‖f x‖) = lorentzNorm μ p q f := by
    simp only [lorentzNorm, decreasingRearrangement, distributionFunction, enorm_norm]
  set F : α →ₘ[μ] ℝ := AEEqFun.mk (fun x => ‖f x‖) hf.norm
  have hF (p q : ℝ≥0∞) : lorentzNorm μ p q F = lorentzNorm μ p q f := by
    rw [lorentzNorm_congr_ae p q (AEEqFun.coeFn_mk _ _), hnorm]
  rcases eq_or_ne (lorentzNorm μ p q f) ⊤ with htop | hfin
  · rw [htop, ENNReal.mul_top (by simp)]
    exact le_top
  obtain ⟨a, ha⟩ := InterpolationCat.exists_lorentzSumToL0_eq ℝ μ ℝ s hst θ q hsq p hpθ
    (⟨F, show lorentzNorm μ p q F < ⊤ by rw [hF]; exact hfin.lt_top⟩ : LorentzSpace ℝ p q μ)
  have haF (p' q' : ℝ≥0∞) : lorentzNorm μ p' q' (InterpolationCat.lorentzSumToL0 ℝ μ ℝ s s ⊤ ⊤ a) =
      lorentzNorm μ p' q' f := by
    rw [ha]
    exact hF p' q'
  calc lorentzNorm μ p r f
      = lorentzNorm μ p r (InterpolationCat.lorentzSumToL0 ℝ μ ℝ s s ⊤ ⊤ a) := (haF p r).symm
    _ ≤ A * InterpolationCouple.realInterpolationENorm _ _ θ r a := hA a
    _ ≤ A * (c * InterpolationCouple.realInterpolationENorm _ _ θ q a) := by gcongr; exact hmono a
    _ ≤ A * (c * (B * lorentzNorm μ p q f)) := by gcongr; rw [← haF p q]; exact hB a
    _ = (A * c * B) * lorentzNorm μ p q f := by ring
    _ ≤ (max 1 (A * c.toNNReal * B) : ℝ≥0) * lorentzNorm μ p q f := by
        gcongr
        push_cast [ENNReal.coe_toNNReal hc]
        exact le_max_right _ _

end WeakLp

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace InterpolationCat

/-- Real interpolation of Lorentz spaces (Bergh–Löfström Theorem 5.3.1; Triebel §1.18.6,
Theorem 2): for `0 < p₀ ≠ p₁ ≤ ∞`, `0 < q₀, q₁, q ≤ ∞`, `0 < θ < 1` and
`1/p = (1-θ)/p₀ + θ/p₁`, `(L_{p₀,q₀}, L_{p₁,q₁})_{θ,q} = L_{p,q}`, as an isomorphism of quasi-Banach
spaces compatible with the inclusions of both sides into `L⁰(μ)`. An infinite `pᵢ` requires
`qᵢ = ∞`: `L_{∞,q} = 0` for `q < ∞`, and `(0, A₁)_{θ,q} = 0`. (B–L also treat `p₀ = p₁`, via
their Theorem 3.5.5; that case is not included here.)

Proof plan (B–L): pick `0 < r < min (p₀, p₁)` and set `1/pᵢ = (1-θᵢ)/r`. By the base case
`nonempty_iso_realInterpolation_lorentz_top` (B–L Theorem 5.2.1), `L_{pᵢ,qᵢ} = (Lʳ, L^∞)_{θᵢ,qᵢ}`
(for `pᵢ = ∞` it is the leg `L^∞` itself), so both legs are of class `𝒞(θᵢ)` for `(Lʳ, L^∞)`;
reiterate (B–L Theorem 3.5.3) with `θ = (1-η)θ₀ + ηθ₁`, and apply the base case once more.
The base case needs `r ≤ q` (B–L Theorem 5.2.1 (2) likewise assumes `p₀ < q`), so `r` is also
taken `≤ min (q₀, q₁, q)`, a requirement B–L's proof leaves implicit. -/
theorem nonempty_iso_realInterpolation_lorentz {p₀ q₀ p₁ q₁ : ℝ≥0∞} [Fact (0 < q₀)]
    [Fact (0 < q₁)] (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ ≠ p₁) (hq₀ : p₀ = ⊤ → q₀ = ⊤)
    (hq₁ : p₁ = ⊤ → q₁ = ⊤) (θ : ℝ) (q : ℝ≥0∞) [Fact (0 < θ)] [Fact (θ < 1)] [Fact (0 < q)]
    (p : ℝ≥0∞) (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    ∃ e : (realInterpolationFunctor 𝕜 θ q).obj (lorentz 𝕜 μ E p₀ q₀ p₁ q₁) ≅
        QuasiBanachCat.of 𝕜 (LorentzSpace E p q μ),
      ∀ x, lorentzSumToL0 𝕜 μ E p₀ q₀ p₁ q₁ ((realInterpolationFunctor 𝕜 θ q).toSum _ x) =
        LorentzSpace.toL0 μ E 𝕜 p q (e.hom.hom x) := by
  sorry

/-- Interpolating two weak-`Lᵖ` spaces gives `Lᵖ`: `(L_{p₀,∞}, L_{p₁,∞})_{θ,p} = L_{p,p}` for
`p₀ ≠ p₁`, `1/p = (1-θ)/p₀ + θ/p₁`. The right side is `Lᵖ(μ)` by `LorentzSpace.eq_Lp`; it is stated
as `L_{p,p}` because `Lp` is a `QuasiBanachCat` object only for `1 ≤ p`. A specialization of
`nonempty_iso_realInterpolation_lorentz`. -/
theorem nonempty_iso_realInterpolation_lorentz_top_top {p₀ p₁ : ℝ≥0∞} (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp₀₁ : p₀ ≠ p₁) (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 1)] (p : ℝ≥0∞)
    [Fact (0 < p)] (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    ∃ e : (realInterpolationFunctor 𝕜 θ p).obj (lorentz 𝕜 μ E p₀ ⊤ p₁ ⊤) ≅
        QuasiBanachCat.of 𝕜 (LorentzSpace E p p μ),
      ∀ x, lorentzSumToL0 𝕜 μ E p₀ ⊤ p₁ ⊤ ((realInterpolationFunctor 𝕜 θ p).toSum _ x) =
        LorentzSpace.toL0 μ E 𝕜 p p (e.hom.hom x) := by
  sorry

end InterpolationCat

/-! ### The Marcinkiewicz interpolation theorem

A morphism of Lorentz couples needs both couples in the same universe, so the measure spaces and
the target spaces share one universe here. -/

section Marcinkiewicz

universe v

variable {𝕜}
variable {α β : Type v} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace InterpolationCat

/-- **The Marcinkiewicz interpolation theorem**, Lorentz-space form (Bergh–Löfström Theorem 5.3.2,
(4)): let `T` map `L_{p₀,r₀}(μ) → L_{q₀,s₀}(ν)` with norm `≤ M₀` and `L_{p₁,r₁}(μ) → L_{q₁,s₁}(ν)`
with norm `≤ M₁` (compatibly), where `p₀ ≠ p₁`, `q₀ ≠ q₁`. Then for `0 < θ < 1`, `0 < r ≤ ∞`,
`1/p = (1-θ)/p₀ + θ/p₁`, `1/q = (1-θ)/q₀ + θ/q₁`, `T` maps `L_{p,r}(μ) → L_{q,r}(ν)`. B–L state
only the mapping property; we also record the norm bound `≤ C M₀^{1-θ} M₁^θ`, with `C`
independent of `T`, which the same proof gives by exactness of the real interpolation functor.

The map `S : L_{p,r} → L_{q,r}` is "`T` on `L_{p,r}`": whenever `f = f₀ + f₁` with
`fᵢ ∈ L_{pᵢ,rᵢ}`, `S f = T f₀ + T f₁`. Proof plan (B–L: "follows at once from Theorem 5.3.1"):
apply the real interpolation functor to `T` (`norm_realInterpolationFunctor_map_le`) and identify
both sides by `nonempty_iso_realInterpolation_lorentz`. -/
theorem exists_lorentz_interpolation {p₀ r₀ p₁ r₁ q₀ s₀ q₁ s₁ : ℝ≥0∞} [Fact (0 < r₀)]
    [Fact (0 < r₁)] [Fact (0 < s₀)] [Fact (0 < s₁)] (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀₁ : p₀ ≠ p₁) (hr₀ : p₀ = ⊤ → r₀ = ⊤) (hr₁ : p₁ = ⊤ → r₁ = ⊤) (hq₀ : 0 < q₀)
    (hq₁ : 0 < q₁) (hq₀₁ : q₀ ≠ q₁) (hs₀ : q₀ = ⊤ → s₀ = ⊤) (hs₁ : q₁ = ⊤ → s₁ = ⊤) (θ : ℝ)
    [Fact (0 < θ)] [Fact (θ < 1)] (r : ℝ≥0∞) [Fact (0 < r)] (p q : ℝ≥0∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) :
    ∃ C : ℝ, ∀ (T : lorentz 𝕜 μ E p₀ r₀ p₁ r₁ ⟶ lorentz 𝕜 ν F q₀ s₀ q₁ s₁) {M₀ M₁ : ℝ},
      0 < M₀ → 0 < M₁ → QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀ →
      QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁ →
      ∃ S : LorentzSpace E p r μ →L[𝕜] LorentzSpace F q r ν,
        (∀ (f : LorentzSpace E p r μ) (f₀ : LorentzSpace E p₀ r₀ μ) (f₁ : LorentzSpace E p₁ r₁ μ),
          LorentzSpace.toL0 μ E 𝕜 p r f =
              LorentzSpace.toL0 μ E 𝕜 p₀ r₀ f₀ + LorentzSpace.toL0 μ E 𝕜 p₁ r₁ f₁ →
            LorentzSpace.toL0 ν F 𝕜 q r (S f) =
              LorentzSpace.toL0 ν F 𝕜 q₀ s₀ (T.f₀ f₀) + LorentzSpace.toL0 ν F 𝕜 q₁ s₁ (T.f₁ f₁)) ∧
        ∀ f, ‖S f‖ ≤ C * M₀ ^ (1 - θ) * M₁ ^ θ * ‖f‖ := by
  sorry

/-- **The Marcinkiewicz interpolation theorem**, strong-type form (Bergh–Löfström Theorem 5.3.2,
(5)): if `T` is of weak type `(p₀, q₀)` and `(p₁, q₁)`, i.e. maps `L^{pᵢ}(μ) → L_{qᵢ,∞}(ν)` with
norm `≤ Mᵢ`, where `p₀ ≠ p₁`, `q₀ ≠ q₁`, then for `0 < θ < 1` with `p ≤ q`, `T` is of strong type
`(p, q)`: it maps `L^p(μ) → L^q(ν)` with norm `≤ C M₀^{1-θ} M₁^θ` (the bound as in
`exists_lorentz_interpolation`). Here `L^{pᵢ}` appears as `L_{pᵢ,pᵢ}` (`LorentzSpace.eq_Lp`).
Proof plan (B–L): `exists_lorentz_interpolation` with `r = p`, then the inclusion
`L_{q,p} ⊆ L_{q,q}` (`LorentzSpace.exists_lorentzNorm_le_of_le`). -/
theorem exists_lp_interpolation {p₀ p₁ q₀ q₁ : ℝ≥0∞} [Fact (0 < p₀)] [Fact (0 < p₁)]
    (hp₀₁ : p₀ ≠ p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀₁ : q₀ ≠ q₁) (θ : ℝ) [Fact (0 < θ)]
    [Fact (θ < 1)] (p q : ℝ≥0∞) [Fact (0 < p)] [Fact (0 < q)]
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) (hpq : p ≤ q) :
    ∃ C : ℝ, ∀ (T : lorentz 𝕜 μ E p₀ p₀ p₁ p₁ ⟶ lorentz 𝕜 ν F q₀ ⊤ q₁ ⊤) {M₀ M₁ : ℝ},
      0 < M₀ → 0 < M₁ → QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀ →
      QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁ →
      ∃ S : LorentzSpace E p p μ →L[𝕜] LorentzSpace F q q ν,
        (∀ (f : LorentzSpace E p p μ) (f₀ : LorentzSpace E p₀ p₀ μ) (f₁ : LorentzSpace E p₁ p₁ μ),
          LorentzSpace.toL0 μ E 𝕜 p p f =
              LorentzSpace.toL0 μ E 𝕜 p₀ p₀ f₀ + LorentzSpace.toL0 μ E 𝕜 p₁ p₁ f₁ →
            LorentzSpace.toL0 ν F 𝕜 q q (S f) =
              LorentzSpace.toL0 ν F 𝕜 q₀ ⊤ (T.f₀ f₀) + LorentzSpace.toL0 ν F 𝕜 q₁ ⊤ (T.f₁ f₁)) ∧
        ∀ f, ‖S f‖ ≤ C * M₀ ^ (1 - θ) * M₁ ^ θ * ‖f‖ := by
  sorry

end InterpolationCat

end Marcinkiewicz
