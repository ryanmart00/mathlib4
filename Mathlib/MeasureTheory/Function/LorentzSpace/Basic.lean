/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.TriangleInequality
import Mathlib.Analysis.Normed.Quasi.NormedSpace

/-!
# Lorentz spaces: the bundled type

Mirrors `MeasureTheory.Lp` (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`) as closely as
possible: `LorentzSpace E p q μ`, the Lorentz space `L_{p,q}(μ)` as an `AddSubgroup (α →ₘ[μ] E)`,
cut out by `lorentzNorm p q μ f < ∞` in place of `eLpNorm f p μ < ∞`. A `Complete.lean` proving
`CompleteSpace` is expected to follow, mirroring `LpSpace/Complete.lean`.

Per Ryan (2026-09-20): unlike `Lp`, which is genuinely normed for `1 ≤ p`, `LorentzSpace` is given
only a `QuasinormedAddCommGroup` instance here, for **all** `p, q` — the literal `f*`-based Lorentz
quasinorm is not a genuine norm even for `p > 1` (Hunt's maximal-function `f**` trick is needed for
that, and is *not* attempted here). This is exactly the case the quasi-Banach generalization
(`Analysis/Normed/Quasi/` etc.) was built to accommodate. The fact that `L_{p,p}`
recovers the genuine `Lᵖ` space (as literal equality of subgroups) is `LorentzSpace.eq_Lp`
(`LorentzSpace/Diag.lean`).

## Main definitions
* `LorentzSpace E p q μ` — the bundled Lorentz space, mirroring `MeasureTheory.Lp`'s own definition.
* `LorentzSpace.instQuasinormedAddCommGroup` — its `QuasinormedAddCommGroup` instance (for `0 < q`,
  see its own docstring for why), using `TriangleInequality.lean`'s `lorentzNorm_add_le`/
  `lorentzNorm_eq_zero_iff` for its content. Every field, including the four bundled topology
  ones, has a real proof — this instance is fully done, zero `sorry`.
* `LorentzSpace.lorentzSubmodule`, `LorentzSpace.instModule` (every `p, q`) and
  `LorentzSpace.instQuasiNormedSpace` (`0 < q`), from the absolute homogeneity
  `lorentzNorm_const_smul` — mirroring `Lp.LpSubmodule`/`Lp.instModule`/`Lp.instNormedSpace`.

## A `Lp`-inspired elaboration-performance lesson

Building `instQuasinormedAddCommGroup`'s topology fields directly (via
`AddGroupFilterBasis.ofQuasiNorm`, mirroring the class's own field defaults) initially hit a wall:
every structurally-different way tried needed a heartbeat budget climbing past 4 million without
finishing in reasonable wall-clock time. Per Ryan's suggestion to look at how `Lp` itself is
structured: `Lp`'s own `instNormedAddCommGroup` (`LpSpace/Basic.lean`) is scrupulous about *never*
leaving a local definition's type to be inferred — every intermediate piece is either a separately
named, explicitly-typed instance (`Lp.instAddCommGroup : AddCommGroup (Lp E p μ) := inferInstance`)
or wrapped in `fast_instance%`. Applying that discipline here
(`let hB : AddGroupFilterBasis (LorentzSpace E p q μ) := ...`, with the type spelled out, instead
of `have hB := ...` left to be inferred) resolved the *entire* problem outright — down from a
multi-hundred-second non-terminating elaboration to under three seconds. `let` (not `have`) was
also needed so that
`hB`'s definition itself stays visible to later `rcases`/`rintro` calls that need to unfold it,
`have` bindings are opaque to reduction, but their type still gets fixed the same way `let`'s does,
which is what fixes the performance problem specifically.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `0 < ∞` as a `Fact`, so that `LorentzSpace E p ⊤ μ` (e.g. `L^∞ = L_{∞,∞}`) gets its
`[Fact (0 < q)]`-gated instances automatically. Mirrors `fact_one_le_top_ennreal`. -/
instance _root_.fact_zero_lt_top_ennreal : Fact ((0 : ℝ≥0∞) < ∞) :=
  ⟨ENNReal.zero_lt_top⟩

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]
variable (p q : ℝ≥0∞)

section ConstSMul

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- Scaling `f` by `c ≠ 0` rescales the distribution function's level: `ϱ(c • f, σ) =
ϱ(f, σ / ‖c‖)`. -/
theorem distributionFunction_const_smul {c : 𝕜} (hc : c ≠ 0) (f : α → E) (σ : ℝ≥0∞) :
    distributionFunction μ (c • f) σ = distributionFunction μ f (σ / ‖c‖ₑ) := by
  unfold distributionFunction
  congr 1
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Pi.smul_apply, enorm_smul, mul_comm,
    ENNReal.div_lt_iff (Or.inl (enorm_ne_zero.mpr hc)) (Or.inl enorm_ne_top)]

/-- The decreasing rearrangement is absolutely homogeneous: `(c • f)* = ‖c‖ • f*`. -/
theorem decreasingRearrangement_const_smul (c : 𝕜) (f : α → E) (t : ℝ≥0∞) :
    decreasingRearrangement μ (c • f) t = ‖c‖ₑ * decreasingRearrangement μ f t := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, enorm_zero, zero_mul]
    refine le_antisymm (sInf_le ?_) zero_le
    simp [distributionFunction]
  have hk0 : ‖c‖ₑ ≠ 0 := enorm_ne_zero.mpr hc
  have hkt : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  have hset : {σ | distributionFunction μ (c • f) σ ≤ t} =
      (‖c‖ₑ * ·) '' {τ | distributionFunction μ f τ ≤ t} := by
    ext σ
    simp only [distributionFunction_const_smul μ hc, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · exact fun hσ => ⟨σ / ‖c‖ₑ, hσ, ENNReal.mul_div_cancel hk0 hkt⟩
    · rintro ⟨τ, hτ, rfl⟩
      rwa [mul_comm, ENNReal.mul_div_cancel_right hk0 hkt]
  unfold decreasingRearrangement
  rw [hset, sInf_image, sInf_eq_iInf, ENNReal.mul_iInf_of_ne hk0 hkt]
  simp_rw [ENNReal.mul_iInf_of_ne hk0 hkt]

/-- The Lorentz quasinorm is absolutely homogeneous, for `q ≠ 0` (at `q = 0`, `lorentzNorm` is
constantly `1`). -/
theorem lorentzNorm_const_smul (hq : q ≠ 0) (c : 𝕜) (f : α → E) :
    lorentzNorm μ p q (c • f) = ‖c‖ₑ * lorentzNorm μ p q f := by
  unfold lorentzNorm
  simp_rw [decreasingRearrangement_const_smul μ c f, mul_left_comm _ ‖c‖ₑ]
  split_ifs with htop
  · exact (ENNReal.mul_iSup _ _).symm
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq htop
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, mul_assoc]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le enorm_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ENNReal.toReal_inv,
    mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]

end ConstSMul

/-- The Lorentz space `L_{p,q}(μ)`: elements of `α →ₘ[μ] E` such that `lorentzNorm p q μ f < ∞`.
Mirrors `MeasureTheory.Lp` exactly (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`), with
`lorentzNorm` in place of `eLpNorm`. -/
noncomputable def LorentzSpace {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lorentzNorm μ p q f < ∞ }
  zero_mem' := by
    rw [Set.mem_ofPred_eq, lorentzNorm_congr_ae p q AEEqFun.coeFn_zero]
    exact (lorentzNorm_zero_le_one p q).trans_lt ENNReal.one_lt_top
  add_mem' {f g} hf hg := by
    rw [Set.mem_ofPred_eq] at hf hg ⊢
    rw [lorentzNorm_congr_ae p q (AEEqFun.coeFn_add f g)]
    refine lt_of_le_of_lt (lorentzNorm_add_le p q f g) ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num))
      (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)
  neg_mem' {f} hf := by
    rw [Set.mem_ofPred_eq] at hf ⊢
    rwa [lorentzNorm_congr_ae p q (AEEqFun.coeFn_neg f), lorentzNorm_neg]

namespace LorentzSpace

/-- Coercion straight to functions `α → E`, bypassing the intermediate `α →ₘ[μ] E` — mirrors
`MeasureTheory.Lp.instCoeFun` exactly (needed so `lorentzNorm μ p q f` elaborates for
`f : LorentzSpace E p q μ` below). -/
noncomputable instance instCoeFun : CoeFun (LorentzSpace E p q μ) (fun _ => α → E) :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

/-- The Lorentz quasinorm on `LorentzSpace E p q μ`, via `ENNReal.toReal (lorentzNorm ...)` —
mirrors `MeasureTheory.Lp.instNorm` exactly. -/
noncomputable instance instNorm : Norm (LorentzSpace E p q μ) where
  norm f := (lorentzNorm μ p q f).toReal

/-- Mirrors `MeasureTheory.Lp.ext` exactly: two elements agreeing a.e. are equal. -/
theorem ext {f g : LorentzSpace E p q μ} (h : (f : α → E) =ᵐ[μ] (g : α → E)) : f = g := by
  ext
  exact h

variable {p q}

/-- The quasi-triangle constant, as a plain top-level definition (not just an instance field) so
the four bundled topology fields of `instQuasinormedAddCommGroup` below can refer to it by name —
see that instance's docstring for why they need to. -/
noncomputable def quasiTriangleConst : ℝ := (2 : ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal)

theorem one_le_quasiTriangleConst : (1 : ℝ) ≤ quasiTriangleConst (p := p) (q := q) := by
  unfold quasiTriangleConst
  calc (1:ℝ) = (2:ℝ) ^ (0:ℝ) := (Real.rpow_zero 2).symm
    _ ≤ (2:ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        positivity

theorem norm_add_le (f g : LorentzSpace E p q μ) :
    ‖f + g‖ ≤ quasiTriangleConst (p := p) (q := q) * (‖f‖ + ‖g‖) := by
  unfold quasiTriangleConst
  change (lorentzNorm μ p q (⇑(f + g))).toReal ≤
    (2:ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) * ((lorentzNorm μ p q f).toReal +
      (lorentzNorm μ p q g).toReal)
  have hcoe : ((f + g : LorentzSpace E p q μ) : α →ₘ[μ] E) =
      (f : α →ₘ[μ] E) + (g : α →ₘ[μ] E) := rfl
  rw [show (⇑(f + g) : α → E) = ((f + g : LorentzSpace E p q μ) : α →ₘ[μ] E) from rfl, hcoe,
    lorentzNorm_congr_ae p q (AEEqFun.coeFn_add (f : α →ₘ[μ] E) g)]
  have hfin : lorentzNorm μ p q (f : α → E) + lorentzNorm μ p q (g : α → E) ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨f.2, g.2⟩).ne
  have hrpow : (2:ℝ≥0∞) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)).ne
  have key : lorentzNorm μ p q ((f : α → E) + (g : α → E)) ≤
      (2:ℝ≥0∞) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) *
        (lorentzNorm μ p q (f : α → E) + lorentzNorm μ p q (g : α → E)) :=
    lorentzNorm_add_le p q (f : α → E) (g : α → E)
  have hrhsfin : (2:ℝ≥0∞) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) *
      (lorentzNorm μ p q (f : α → E) + lorentzNorm μ p q (g : α → E)) ≠ ⊤ :=
    ENNReal.mul_ne_top hrpow hfin
  have hlhsfin : lorentzNorm μ p q ((f : α → E) + (g : α → E)) ≠ ⊤ :=
    (key.trans_lt (lt_top_iff_ne_top.mpr hrhsfin)).ne
  rw [← ENNReal.toReal_le_toReal hlhsfin hrhsfin] at key
  rw [ENNReal.toReal_mul, ENNReal.toReal_add f.2.ne g.2.ne, ← ENNReal.toReal_rpow] at key
  rwa [show (2:ℝ≥0∞).toReal = (2:ℝ) from rfl] at key

theorem norm_neg (f : LorentzSpace E p q μ) : ‖-f‖ = ‖f‖ := by
  change (lorentzNorm μ p q (⇑(-f))).toReal = (lorentzNorm μ p q (⇑f)).toReal
  have hcoe : ((-f : LorentzSpace E p q μ) : α →ₘ[μ] E) = -(f : α →ₘ[μ] E) := rfl
  rw [show (⇑(-f) : α → E) = ((-f : LorentzSpace E p q μ) : α →ₘ[μ] E) from rfl, hcoe,
    lorentzNorm_congr_ae p q (AEEqFun.coeFn_neg (f : α →ₘ[μ] E)), lorentzNorm_neg]

theorem norm_eq_zero_iff [Fact (0 < q)] (f : LorentzSpace E p q μ) : ‖f‖ = 0 ↔ f = 0 := by
  have hq0 : 0 < q := Fact.out
  change (lorentzNorm μ p q (⇑f)).toReal = 0 ↔ f = 0
  rw [ENNReal.toReal_eq_zero_iff]
  constructor
  · rintro (h0 | htop)
    · rw [lorentzNorm_eq_zero_iff p q hq0] at h0
      apply ext
      show (⇑f : α → E) =ᵐ[μ] (⇑(0 : LorentzSpace E p q μ) : α → E)
      rw [show (⇑(0 : LorentzSpace E p q μ) : α → E) = ((0 : α →ₘ[μ] E) : α → E) from rfl]
      exact h0.trans AEEqFun.coeFn_zero.symm
    · exact absurd htop f.2.ne
  · intro hf
    subst hf
    left
    show lorentzNorm μ p q (⇑(0 : LorentzSpace E p q μ) : α → E) = 0
    rw [show (⇑(0 : LorentzSpace E p q μ) : α → E) = ((0 : α →ₘ[μ] E) : α → E) from rfl,
      lorentzNorm_congr_ae p q AEEqFun.coeFn_zero]
    exact lorentzNorm_zero_of_pos p hq0

/-- `QuasinormedAddCommGroup (LorentzSpace E p q μ)`, for `0 < q`. Per the module docstring,
`0 < q` is genuinely needed (not just a convenience hypothesis): at `q = 0`, `lorentzNorm` is
constantly `1`, so `norm_eq_zero_iff` would force `‖(0 : LorentzSpace E p 0 μ)‖ = 0 = 1`, which is
false. Mirrors `MeasureTheory.Lp`'s own `[Fact (1 ≤ p)]`-gated `NormedAddCommGroup` instance in
spirit —
`LorentzSpace` itself stays defined for every `p, q` regardless.

The four bundled topology fields are given explicitly (mirroring
`AddGroupFilterBasis.ofQuasiNorm`'s own docstring pattern, `Normed/Quasi/Basic.lean`) via the local
`hB` computed once below, rather than relying on the class's own default mechanism (which hit an
unrelated elaboration issue — an "unknown identifier" error referencing earlier fields — not
investigated further since this direct route works). See the module docstring's "elaboration-performance lesson" for why `hB` needs an explicit
type ascription and `let` rather than `have`. -/
noncomputable instance instQuasinormedAddCommGroup [Fact (0 < q)] :
    QuasinormedAddCommGroup (LorentzSpace E p q μ) := by
  let hB : AddGroupFilterBasis (LorentzSpace E p q μ) :=
    AddGroupFilterBasis.ofQuasiNorm (quasiTriangleConst (p := p) (q := q))
      one_le_quasiTriangleConst (norm_add_le μ) (norm_neg μ) (norm_eq_zero_iff μ)
  refine
    { quasiTriangleConst := quasiTriangleConst (p := p) (q := q)
      one_le_quasiTriangleConst := one_le_quasiTriangleConst
      norm_add_le := norm_add_le μ
      norm_neg := norm_neg μ
      norm_eq_zero_iff := norm_eq_zero_iff μ
      toUniformSpace := hB.uniformSpace
      toIsTopologicalAddGroup := ?_
      toIsUniformAddGroup := ?_
      nhds_zero_hasBasis := ?_ }
  · exact hB.isTopologicalAddGroup
  · exact hB.isUniformAddGroup
  · change (@nhds (LorentzSpace E p q μ) hB.uniformSpace.toTopologicalSpace 0).HasBasis (0 < ·)
      fun ε : ℝ => {x : LorentzSpace E p q μ | ‖x‖ < ε}
    rw [hB.nhds_eq (x₀ := 0), AddGroupFilterBasis.N_zero]
    refine (FilterBasis.hasBasis hB.toFilterBasis).to_hasBasis' ?_ ?_
    · rintro s ⟨ε, hε, rfl⟩
      exact ⟨ε, hε, subset_rfl⟩
    · rintro ε hε
      exact FilterBasis.mem_filter_of_mem _ ⟨ε, hε, rfl⟩

section Module

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- `LorentzSpace E p q μ` is closed under scalar multiplication, for every `p, q` (at `q = 0` it
is all of `α →ₘ[μ] E`). Mirrors `MeasureTheory.Lp.const_smul_mem_Lp`. -/
theorem const_smul_mem (c : 𝕜) {f : α →ₘ[μ] E} (hf : f ∈ LorentzSpace E p q μ) :
    c • f ∈ LorentzSpace E p q μ := by
  change lorentzNorm μ p q ⇑f < ∞ at hf
  change lorentzNorm μ p q ⇑(c • f) < ∞
  rw [lorentzNorm_congr_ae p q (AEEqFun.coeFn_smul c f)]
  rcases eq_or_ne q 0 with rfl | hq
  · simp [lorentzNorm]
  · rw [lorentzNorm_const_smul μ p q hq]
    exact ENNReal.mul_lt_top enorm_lt_top hf

variable (E p q 𝕜) in
/-- `LorentzSpace E p q μ` as a `𝕜`-submodule of `α →ₘ[μ] E`, with the same carrier. Mirrors
`MeasureTheory.Lp.LpSubmodule`. -/
noncomputable def lorentzSubmodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { LorentzSpace E p q μ with smul_mem' := fun c _ hf => const_smul_mem μ c hf }

/-- Mirrors `MeasureTheory.Lp.instModule`. -/
noncomputable instance instModule : Module 𝕜 (LorentzSpace E p q μ) :=
  { (lorentzSubmodule μ E p q 𝕜).module with }

theorem norm_const_smul [Fact (0 < q)] (c : 𝕜) (f : LorentzSpace E p q μ) :
    ‖c • f‖ = ‖c‖ * ‖f‖ := by
  have hq : q ≠ 0 := (Fact.out : 0 < q).ne'
  change (lorentzNorm μ p q ⇑(c • (f : α →ₘ[μ] E))).toReal = ‖c‖ * (lorentzNorm μ p q ⇑f).toReal
  rw [lorentzNorm_congr_ae p q (AEEqFun.coeFn_smul c (f : α →ₘ[μ] E)),
    lorentzNorm_const_smul μ p q hq, ENNReal.toReal_mul, toReal_enorm]

/-- Mirrors `MeasureTheory.Lp.instNormedSpace`. -/
noncomputable instance instQuasiNormedSpace [Fact (0 < q)] :
    QuasiNormedSpace 𝕜 (LorentzSpace E p q μ) where
  norm_smul_le c f := (norm_const_smul μ c f).le

end Module

end LorentzSpace
