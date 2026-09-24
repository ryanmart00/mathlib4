/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Topology.Algebra.MulAction

/-!
# `L⁰`: the topology of convergence in measure

DRAFT — statement-review stage.

Built to serve as the common ambient topological vector space `𝒜` an `InterpolationCouple`
(`Analysis/Interpolation/Couple.lean`) needs, for a couple of Lorentz (or plain `Lᵖ`) spaces.
Neither `α →ₘ[μ] E` (`MeasureTheory.AEEqFun`) nor any variant of it carries a topology in Mathlib
for general `E`/`μ`: each `Lp E p μ`'s topology comes from its own `eLpNorm`, with no shared
ambient space for different `p`.

## Design

`L0 α E μ` is a type synonym for `α →ₘ[μ] E`. It is a synonym rather than an instance on
`α →ₘ[μ] E` itself because `Lp E p μ` and `LorentzSpace E p q μ` are `AddSubgroup`s of
`α →ₘ[μ] E` with their own norm topologies, which a subtype topology would conflict with.

Its uniform structure is *convergence in measure on every finite-measure set* (convergence in
local measure), defined canonically as an infimum over measurable sets `s` with `μ s ≠ ⊤` of the
uniformity of the Ky Fan extended distance
`AEEqFun.kyFanEdist μ s f g = ∫⁻ x in s, min 1 (edist (f x) (g x)) ∂μ`.
On a finite-measure set, a single Ky Fan distance induces convergence in measure
(`AEEqFun.tendsto_kyFanEdist_iff_tendstoInMeasure`); the infimum then handles genuinely infinite
`μ` without choosing an exhausting sequence. Being an infimum, the additive-group and
scalar-multiplication compatibility reduce to the corresponding facts for a single `s`
(`isUniformAddGroup_iInf`, `continuousSMul_iInf`).

No `σ`-finiteness is needed for the definition. It is needed for `T2Space`: for a measure which is
not semifinite (e.g. `∞ • dirac a`), a function supported on a set all of whose subsets have
measure `0` or `⊤` cannot be separated from `0`.

## Main definitions
* `MeasureTheory.AEEqFun.kyFanEdist μ s`: the Ky Fan extended distance on `s`.
* `MeasureTheory.L0 α E μ`: the type synonym for `α →ₘ[μ] E`.
* `MeasureTheory.L0.uniformSpaceOn μ s`: the uniformity of convergence in measure on `s`.
* `MeasureTheory.L0.instUniformSpace`: the infimum of `uniformSpaceOn μ s` over measurable `s`
  with `μ s ≠ ⊤`.

## Main statements
* `MeasureTheory.L0.instIsUniformAddGroup`, `MeasureTheory.L0.instContinuousSMul`.
* `MeasureTheory.L0.instT2Space`, for `SigmaFinite μ`.
* `MeasureTheory.L0.tendsto_iff_tendstoInMeasure`: convergence in `L0` is `TendstoInMeasure` on
  every finite-measure set.

## TODO
* `MetrizableSpace (L0 α E μ)` for `SigmaFinite μ` (the uniformity is countably generated).
-/

open Filter Set
open scoped ENNReal Topology

/-- Truncation at `1` preserves the triangle inequality. -/
theorem ENNReal.min_one_le_add_of_le {a b c : ℝ≥0∞} (h : a ≤ b + c) :
    min 1 a ≤ min 1 b + min 1 c := by
  refine (min_le_min le_rfl h).trans ?_
  by_cases hb : (1 : ℝ≥0∞) ≤ b
  · rw [min_eq_left hb]; exact (min_le_left _ _).trans le_self_add
  by_cases hc : (1 : ℝ≥0∞) ≤ c
  · rw [min_eq_left hc]; exact (min_le_left _ _).trans le_add_self
  rw [min_eq_right (not_le.mp hb).le, min_eq_right (not_le.mp hc).le]
  exact min_le_right _ _

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]

namespace AEEqFun

/-- The Ky Fan extended distance on a set `s`: the integral over `s` of the pointwise distance
truncated at `1`. When `μ s ≠ ⊤`, it induces convergence in measure on `s`
(`tendsto_kyFanEdist_iff_tendstoInMeasure`). -/
noncomputable def kyFanEdist (s : Set α) (f g : α →ₘ[μ] E) : ℝ≥0∞ :=
  ∫⁻ x in s, min 1 (edist (f x) (g x)) ∂μ

theorem kyFanEdist_self (s : Set α) (f : α →ₘ[μ] E) : kyFanEdist μ s f f = 0 := by
  simp [kyFanEdist]

theorem kyFanEdist_comm (s : Set α) (f g : α →ₘ[μ] E) :
    kyFanEdist μ s f g = kyFanEdist μ s g f := by
  simp_rw [kyFanEdist, edist_comm (f _)]

theorem kyFanEdist_triangle (s : Set α) (f g h : α →ₘ[μ] E) :
    kyFanEdist μ s f h ≤ kyFanEdist μ s f g + kyFanEdist μ s g h := by
  have hfg : AEMeasurable (fun x => min 1 (edist (f x) (g x))) (μ.restrict s) :=
    (aemeasurable_const.min (continuous_edist.comp_aestronglyMeasurable₂
      f.aestronglyMeasurable g.aestronglyMeasurable).aemeasurable).restrict
  rw [kyFanEdist, kyFanEdist, kyFanEdist, ← lintegral_add_left' hfg]
  exact MeasureTheory.lintegral_mono fun x => ENNReal.min_one_le_add_of_le (edist_triangle _ _ _)

theorem kyFanEdist_add_add (s : Set α) (f g h : α →ₘ[μ] E) :
    kyFanEdist μ s (f + h) (g + h) = kyFanEdist μ s f g := by
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [coeFn_add f h, coeFn_add g h] with x hxf hxg
  simp only [hxf, hxg, Pi.add_apply, edist_add_right]

theorem kyFanEdist_neg_neg (s : Set α) (f g : α →ₘ[μ] E) :
    kyFanEdist μ s (-f) (-g) = kyFanEdist μ s f g := by
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [coeFn_neg f, coeFn_neg g] with x hxf hxg
  simp only [hxf, hxg, Pi.neg_apply, edist_neg_neg]

theorem kyFanEdist_sub_sub_le (s : Set α) (f g f' g' : α →ₘ[μ] E) :
    kyFanEdist μ s (f - g) (f' - g') ≤ kyFanEdist μ s f f' + kyFanEdist μ s g g' := by
  have hff' : AEMeasurable (fun x => min 1 (edist (f x) (f' x))) (μ.restrict s) :=
    (aemeasurable_const.min (continuous_edist.comp_aestronglyMeasurable₂
      f.aestronglyMeasurable f'.aestronglyMeasurable).aemeasurable).restrict
  rw [kyFanEdist, kyFanEdist, kyFanEdist, ← lintegral_add_left' hff']
  refine MeasureTheory.lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [coeFn_sub f g, coeFn_sub f' g'] with x h1 h2
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, sub_eq_add_neg, sub_eq_add_neg]
  refine ENNReal.min_one_le_add_of_le ((edist_add_add_le _ _ _ _).trans_eq ?_)
  rw [edist_neg_neg]

/-- On a finite-measure set, the Ky Fan distance induces convergence in measure. -/
theorem tendsto_kyFanEdist_iff_tendstoInMeasure {ι : Type*} {l : Filter ι} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (f : ι → α →ₘ[μ] E) (g : α →ₘ[μ] E) :
    Tendsto (fun i => kyFanEdist μ s (f i) g) l (𝓝 0) ↔
      TendstoInMeasure (μ.restrict s) (fun i => ⇑(f i)) l ⇑g := by
  sorry

/-- For a `σ`-finite measure, two functions at Ky Fan distance `0` on every finite-measure set are
equal. This is what makes `L0` Hausdorff. -/
theorem eq_of_forall_kyFanEdist_eq_zero [SigmaFinite μ] {f g : α →ₘ[μ] E}
    (h : ∀ s, MeasurableSet s → μ s ≠ ⊤ → kyFanEdist μ s f g = 0) : f = g := by
  have hmeas : AEMeasurable (fun x => min 1 (edist (f x) (g x))) μ :=
    aemeasurable_const.min (continuous_edist.comp_aestronglyMeasurable₂
      f.aestronglyMeasurable g.aestronglyMeasurable).aemeasurable
  have hae (n : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ n → f x = g x := by
    have hn := h _ (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n).ne
    rw [kyFanEdist, setLIntegral_eq_zero_iff' (measurableSet_spanningSets μ n)
      hmeas.restrict] at hn
    filter_upwards [hn] with x hx hxs
    rcases le_total (edist (f x) (g x)) 1 with hle | hle
    · exact edist_eq_zero.mp (min_eq_right hle ▸ hx hxs)
    · exact absurd (min_eq_left hle ▸ hx hxs) one_ne_zero
  refine ext ?_
  filter_upwards [ae_all_iff.mpr hae] with x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp (iUnion_spanningSets μ ▸ mem_univ x)
  exact hx n hn

end AEEqFun

/-- `L⁰(α, E; μ)`: a.e.-equality classes of a.e.-strongly measurable functions `α → E`, as a type
synonym for `α →ₘ[μ] E` carrying the topology of convergence in measure on finite-measure sets.

This is a synonym rather than an instance on `α →ₘ[μ] E` itself because `Lp E p μ` (and
`LorentzSpace E p q μ`) are `AddSubgroup`s of `α →ₘ[μ] E` carrying their own norm topologies; a
topology on `α →ₘ[μ] E` would give them a second, non-defeq subtype topology. -/
def L0 (α E : Type*) [MeasurableSpace α] [TopologicalSpace E] (μ : Measure α) : Type _ :=
  α →ₘ[μ] E

namespace L0

instance : AddCommGroup (L0 α E μ) := inferInstanceAs (AddCommGroup (α →ₘ[μ] E))

/-- Elements of `L0` coerce to (a representative) function, as for `α →ₘ[μ] E`. -/
noncomputable instance : CoeFun (L0 α E μ) fun _ => α → E := ⟨fun f : α →ₘ[μ] E => ⇑f⟩

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance : Module 𝕜 (L0 α E μ) := inferInstanceAs (Module 𝕜 (α →ₘ[μ] E))

variable (𝕜) in
/-- The identity map from `α →ₘ[μ] E` to its synonym `L0 α E μ`, as a linear equivalence. -/
def toL0 : (α →ₘ[μ] E) ≃ₗ[𝕜] L0 α E μ := LinearEquiv.refl 𝕜 _

/-- The uniformity of convergence in measure on the set `s`, induced by `AEEqFun.kyFanEdist`.
It is only meaningful (and only used) for measurable `s` with `μ s ≠ ⊤`. -/
@[instance_reducible]
noncomputable def uniformSpaceOn (s : Set α) : UniformSpace (L0 α E μ) :=
  uniformSpaceOfEDist (AEEqFun.kyFanEdist μ s) (AEEqFun.kyFanEdist_self μ s)
    (AEEqFun.kyFanEdist_comm μ s) (AEEqFun.kyFanEdist_triangle μ s)

theorem isUniformAddGroup_uniformSpaceOn (s : Set α) :
    @IsUniformAddGroup (L0 α E μ) (uniformSpaceOn μ s) _ := by
  let _ : PseudoEMetricSpace (L0 α E μ) :=
    { edist := AEEqFun.kyFanEdist μ s
      edist_self := AEEqFun.kyFanEdist_self μ s
      edist_comm := AEEqFun.kyFanEdist_comm μ s
      edist_triangle := AEEqFun.kyFanEdist_triangle μ s
      toUniformSpace := uniformSpaceOn μ s
      uniformity_edist := rfl }
  refine ⟨EMetric.uniformContinuous_iff.mpr fun ε hε => ⟨ε / 2, ENNReal.half_pos hε.ne', ?_⟩⟩
  intro p q hpq
  rw [Prod.edist_eq, max_lt_iff] at hpq
  calc edist (p.1 - p.2) (q.1 - q.2) ≤ edist p.1 q.1 + edist p.2 q.2 :=
        AEEqFun.kyFanEdist_sub_sub_le μ s _ _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hpq.1 hpq.2
    _ = ε := ENNReal.add_halves ε

/-- Scalar multiplication is continuous for convergence in measure on a *finite-measure* set `s`.
(Finiteness is needed: on `s` of infinite measure, `c • 1 ↛ 0` as `c → 0`.) -/
theorem continuousSMul_uniformSpaceOn {s : Set α} (hμs : μ s ≠ ⊤) :
    @ContinuousSMul 𝕜 (L0 α E μ) _ _ (uniformSpaceOn μ s).toTopologicalSpace := by
  sorry

/-- The uniformity of convergence in measure on every finite-measure set. -/
noncomputable instance instUniformSpace : UniformSpace (L0 α E μ) :=
  ⨅ (s : Set α) (_ : MeasurableSet s) (_ : μ s ≠ ⊤), uniformSpaceOn μ s

instance instIsUniformAddGroup : IsUniformAddGroup (L0 α E μ) := by
  sorry

instance instContinuousSMul : ContinuousSMul 𝕜 (L0 α E μ) := by
  sorry

instance instT2Space [SigmaFinite μ] : T2Space (L0 α E μ) := by
  sorry

/-- Convergence in `L0` is convergence in measure on every finite-measure set. -/
theorem tendsto_iff_tendstoInMeasure {ι : Type*} {l : Filter ι} (f : ι → L0 α E μ)
    (g : L0 α E μ) :
    Tendsto f l (𝓝 g) ↔ ∀ s, MeasurableSet s → μ s ≠ ⊤ →
      TendstoInMeasure (μ.restrict s) (fun i => ⇑(f i)) l ⇑g := by
  sorry

end L0

end MeasureTheory
