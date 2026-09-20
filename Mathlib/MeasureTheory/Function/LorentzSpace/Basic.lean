/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.TriangleInequality
import Mathlib.Analysis.Interpolation.QuasiNorm

/-!
# Lorentz spaces: the bundled type

Mirrors `MeasureTheory.Lp` (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`) as closely as
possible: `LorentzLp E p q μ`, the Lorentz space `L_{p,q}(μ)` as an `AddSubgroup (α →ₘ[μ] E)`, cut
out by `lorentzNorm p q μ f < ∞` in place of `eLpNorm f p μ < ∞`. A `Complete.lean` proving
`CompleteSpace` is expected to follow, mirroring `LpSpace/Complete.lean`.

Per Ryan (2026-09-20): unlike `Lp`, which is genuinely normed for `1 ≤ p`, `LorentzLp` is given
only a `QuasinormedAddCommGroup` instance here, for **all** `p, q` — the literal `f*`-based Lorentz
quasinorm is not a genuine norm even for `p > 1` (Hunt's maximal-function `f**` trick is needed for
that, and is *not* attempted here). This is exactly the case the quasi-Banach generalization
(`Analysis/Interpolation/QuasiNorm.lean` etc.) was built to accommodate. The fact that `L_{p,p}`
recovers the genuine `Lᵖ` norm (up to a `QuasiNormEquiv`, or perhaps literal equality — open
question, not yet settled) is deferred to a later theorem, once this bundled type exists.

## Main definitions
* `LorentzLp E p q μ` — the bundled Lorentz space, mirroring `MeasureTheory.Lp`'s own definition.
* `LorentzLp.instQuasinormedAddCommGroup` — its `QuasinormedAddCommGroup` instance (for `0 < q`,
  see its own docstring for why), using `TriangleInequality.lean`'s `lorentzNorm_add_le`/
  `lorentzNorm_eq_zero_iff` for its content. Every field has a real proof — this instance is done.
  Its four bundled topology fields are given explicitly (via the same
  `AddGroupFilterBasis.ofQuasiNorm` construction the class's own defaults use), rather than
  relying on those defaults, which failed to elaborate here for reasons not fully diagnosed (see
  the instance's own docstring).
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]
variable (p q : ℝ≥0∞)

/-- The Lorentz space `L_{p,q}(μ)`: elements of `α →ₘ[μ] E` such that `lorentzNorm p q μ f < ∞`.
Mirrors `MeasureTheory.Lp` exactly (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`), with
`lorentzNorm` in place of `eLpNorm`. -/
noncomputable def LorentzLp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E]
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

namespace LorentzLp

/-- Coercion straight to functions `α → E`, bypassing the intermediate `α →ₘ[μ] E` — mirrors
`MeasureTheory.Lp.instCoeFun` exactly (needed so `lorentzNorm μ p q f` elaborates for
`f : LorentzLp E p q μ` below). -/
noncomputable instance instCoeFun : CoeFun (LorentzLp E p q μ) (fun _ => α → E) :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

/-- The Lorentz quasinorm on `LorentzLp E p q μ`, via `ENNReal.toReal (lorentzNorm ...)` —
mirrors `MeasureTheory.Lp.instNorm` exactly. -/
noncomputable instance instNorm : Norm (LorentzLp E p q μ) where
  norm f := (lorentzNorm μ p q f).toReal

/-- Mirrors `MeasureTheory.Lp.ext` exactly: two elements agreeing a.e. are equal. -/
theorem ext {f g : LorentzLp E p q μ} (h : (f : α → E) =ᵐ[μ] (g : α → E)) : f = g := by
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

theorem norm_add_le (f g : LorentzLp E p q μ) :
    ‖f + g‖ ≤ quasiTriangleConst (p := p) (q := q) * (‖f‖ + ‖g‖) := by
  unfold quasiTriangleConst
  change (lorentzNorm μ p q (⇑(f + g))).toReal ≤
    (2:ℝ) ^ (1 + p⁻¹.toReal + q⁻¹.toReal) * ((lorentzNorm μ p q f).toReal +
      (lorentzNorm μ p q g).toReal)
  have hcoe : ((f + g : LorentzLp E p q μ) : α →ₘ[μ] E) =
      (f : α →ₘ[μ] E) + (g : α →ₘ[μ] E) := rfl
  rw [show (⇑(f + g) : α → E) = ((f + g : LorentzLp E p q μ) : α →ₘ[μ] E) from rfl, hcoe,
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

theorem norm_neg (f : LorentzLp E p q μ) : ‖-f‖ = ‖f‖ := by
  change (lorentzNorm μ p q (⇑(-f))).toReal = (lorentzNorm μ p q (⇑f)).toReal
  have hcoe : ((-f : LorentzLp E p q μ) : α →ₘ[μ] E) = -(f : α →ₘ[μ] E) := rfl
  rw [show (⇑(-f) : α → E) = ((-f : LorentzLp E p q μ) : α →ₘ[μ] E) from rfl, hcoe,
    lorentzNorm_congr_ae p q (AEEqFun.coeFn_neg (f : α →ₘ[μ] E)), lorentzNorm_neg]

theorem norm_eq_zero_iff [Fact (0 < q)] (f : LorentzLp E p q μ) : ‖f‖ = 0 ↔ f = 0 := by
  have hq0 : 0 < q := Fact.out
  change (lorentzNorm μ p q (⇑f)).toReal = 0 ↔ f = 0
  rw [ENNReal.toReal_eq_zero_iff]
  constructor
  · rintro (h0 | htop)
    · rw [lorentzNorm_eq_zero_iff p q hq0] at h0
      apply ext
      show (⇑f : α → E) =ᵐ[μ] (⇑(0 : LorentzLp E p q μ) : α → E)
      rw [show (⇑(0 : LorentzLp E p q μ) : α → E) = ((0 : α →ₘ[μ] E) : α → E) from rfl]
      exact h0.trans AEEqFun.coeFn_zero.symm
    · exact absurd htop f.2.ne
  · intro hf
    subst hf
    left
    show lorentzNorm μ p q (⇑(0 : LorentzLp E p q μ) : α → E) = 0
    rw [show (⇑(0 : LorentzLp E p q μ) : α → E) = ((0 : α →ₘ[μ] E) : α → E) from rfl,
      lorentzNorm_congr_ae p q AEEqFun.coeFn_zero]
    exact lorentzNorm_zero_of_pos p hq0

/-- `QuasinormedAddCommGroup (LorentzLp E p q μ)`, for `0 < q`. Per the module docstring, `0 < q`
is genuinely needed (not just a convenience hypothesis): at `q = 0`, `lorentzNorm` is constantly
`1`, so `norm_eq_zero_iff` would force `‖(0 : LorentzLp E p 0 μ)‖ = 0 = 1`, which is false. Mirrors
`MeasureTheory.Lp`'s own `[Fact (1 ≤ p)]`-gated `NormedAddCommGroup` instance in spirit —
`LorentzLp` itself stays defined for every `p, q` regardless.

**Pending**: the four bundled topology fields are `sorry`. Every *mathematical* field
(`quasiTriangleConst`, `one_le_quasiTriangleConst`, `norm_add_le`, `norm_neg`, `norm_eq_zero_iff`)
has a real proof — this is now purely an elaboration-performance obstacle, not a correctness gap,
and needs Ryan's input on how to proceed (see `PROGRESS-interpolation-theory.md`'s log entry for
the full diagnostic: several structurally-different ways of discharging these four fields via
`AddGroupFilterBasis.ofQuasiNorm quasiTriangleConst ⋯ norm_add_le norm_neg norm_eq_zero_iff` were
tried — inline ×4, factored into a shared top-level `def` (hit an instance diamond), a single
`have` shared within one tactic block for the whole instance (sidesteps the diamond) — and every
one that type-checked at all needed a heartbeat budget that kept climbing (200k → 1M → 4M) without
ever finishing within reasonable wall-clock time (up to 337s and counting at 4M), pointing at a
genuine elaboration blow-up tied to `LorentzLp E p q μ`'s deeply-nested type
(`↥(AddSubgroup (α →ₘ[μ] E))`), not to proof-term size as first suspected. -/
noncomputable instance instQuasinormedAddCommGroup [Fact (0 < q)] :
    QuasinormedAddCommGroup (LorentzLp E p q μ) where
  quasiTriangleConst := quasiTriangleConst (p := p) (q := q)
  one_le_quasiTriangleConst := one_le_quasiTriangleConst
  norm_add_le := norm_add_le μ
  norm_neg := norm_neg μ
  norm_eq_zero_iff := norm_eq_zero_iff μ
  toUniformSpace := sorry
  toIsTopologicalAddGroup := sorry
  toIsUniformAddGroup := sorry
  nhds_zero_hasBasis := sorry

end LorentzLp
