/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.KMethod.KFunctional
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Real interpolation spaces via the K-functional

DRAFT — under review, statement-design stage (Unit 4 of the quasi-Banach generalization of the
interpolation-couple framework; see `PROGRESS-interpolation-theory.md`). No proof has been
attempted on anything below; this file exists to get the exact statements in front of Ryan before
any tactic is written, per the project's statement-review gate.

Lives in its own `KMethod` directory (alongside `KFunctional.lean`), rather than folded into
`KFunctional.lean` itself, on the expectation that other real-interpolation methods (e.g. the
L-method) will eventually get their own sibling directories/files.

## Main definitions

* `InterpolationCouple.realInterpolationENorm`: Triebel §1.3.2's `(θ,q)`-quasinorm,
  `(∫₀^∞ (t^{-θ}K(t,a))^q dt/t)^{1/q}` for `q < ∞`, `sup_{t>0} t^{-θ}K(t,a)` for `q = ∞`.
  `ℝ≥0∞`-valued (mirroring Mathlib's own `eLpNorm`), so it can genuinely be infinite for an `a`
  that doesn't belong to the space, rather than being an always-finite `ℝ` that would need some
  other way to express non-membership.
* `InterpolationCouple.RealInterpolationSpace`: `(A₀,A₁)_{θ,q}`, the subtype of `A₀+A₁` with
  finite `(θ,q)`-quasinorm. Deliberately just the bare subtype for now — no algebraic structure
  (`AddCommGroup`, let alone `QuasinormedAddCommGroup`) is registered on it yet, since
  constructing even the `AddCommGroup` instance needs the quasi-triangle inequality
  (`realInterpolationENorm_add_le` below) to know the subtype is closed under `+` at all. That
  instance work is deliberately left for *after* these statements are signed off and proved, not
  bundled into this drafting pass.

## Main statements (all `sorry`)

* `realInterpolationENorm_meetToSum_lt_top`: the "`A₀∩A₁` embeds" half of Triebel's sandwich
  `A₀∩A₁ ⊂ (A₀,A₁)_{θ,q} ⊂ A₀+A₁` — the "`⊂ A₀+A₁`" half is definitional (`RealInterpolationSpace`
  is *literally* a subtype of `sum`), so needs no separate statement.
* `realInterpolationENorm_add_le`: the quasi-triangle inequality for `realInterpolationENorm`,
  the fact that actually makes `RealInterpolationSpace` a quasi-normed group once instances are
  built.
* `realInterpolationENorm_sumMap_le`: the K-method's type-`θ` transformation property lifted from
  the K-functional's own naturality lemma (`InterpolationCat.Hom.kFunctional_sumMap_le`,
  `KFunctional.lean`) to the `(θ,q)`-quasinorm — Triebel §1.3.3's "exact interpolation functor of
  type `θ`" claim, in inequality form.
-/

open MeasureTheory Set
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁] [CompleteSpace A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

/-- The `(θ,q)` real-interpolation quasinorm built from the K-functional (Triebel §1.3.2):
`(∫₀^∞ (t^{-θ}K(t,a))^q dt/t)^{1/q}` for `q < ∞`, `sup_{t>0} t^{-θ}K(t,a)` for `q = ∞`. The `q = ⊤`
case is genuinely special-cased (not folded into the general formula by relying on
`(⊤ : ℝ≥0∞).toReal = 0`) — that shortcut is what `LpLorentz.lean`'s existing (draft, unproved)
`lorentzRealInterpolationNorm` does, and it's wrong: with every exponent silently becoming `0`,
that formula collapses to the constant `1` for every `a` when `q = ⊤`, not the intended supremum.
Worth fixing there too when `LpLorentz.lean` is eventually rewritten against this file (Unit 6). -/
noncomputable def InterpolationCouple.realInterpolationENorm (θ : ℝ) (q : ℝ≥0∞)
    (a : InterpolationCouple.sum ι₀ ι₁) : ℝ≥0∞ :=
  if q = ⊤ then
    ⨆ t : Ioi (0 : ℝ), ENNReal.ofReal ((t : ℝ) ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a)
  else
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional ι₀ ι₁ t a) ^ q.toReal *
        ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal

/-- `(A₀,A₁)_{θ,q}` (Triebel §1.3.2): the elements of `A₀+A₁` with finite `(θ,q)`-quasinorm. See
the module docstring for why this is deliberately left as a bare subtype for now. -/
def InterpolationCouple.RealInterpolationSpace (θ : ℝ) (q : ℝ≥0∞) : Type _ :=
  {a : InterpolationCouple.sum ι₀ ι₁ //
    InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q a < ⊤}

/-- `A₀∩A₁` (viewed inside `A₀+A₁` via `meetToSum`) always has finite `(θ,q)`-quasinorm, for any
`0 < θ < 1` and `0 < q ≤ ∞` — the "`A₀∩A₁` embeds into `(A₀,A₁)_{θ,q}`" half of Triebel's sandwich.
The actual content: for `a` in the meet, `K(t,a)` is bounded by `min(‖a₀‖, t‖a₁‖)` for *either*
representation `a₀`/`a₁` of the *same* ambient point (`inl₀_fst_eq_inl₁_snd`), and
`t ↦ t^{-θ}·min(C₀, tC₁)` is integrable against `dt/t` over `(0,∞)` exactly when `0 < θ < 1` — the
elementary calculus fact this whole sandwich rests on. STATEMENT ONLY — proof deferred. -/
theorem InterpolationCouple.realInterpolationENorm_meetToSum_lt_top
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q)
    (a : InterpolationCouple.meet ι₀ ι₁) :
    InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q
      (InterpolationCouple.meetToSum ι₀ ι₁ a) < ⊤ := by
  sorry

/-- The quasi-triangle inequality for `realInterpolationENorm`: a Minkowski-type inequality for
the `(θ,q)`-quasinorm, with some constant `C` depending on `θ`, `q`, and the legs' own
`quasiTriangleConst`s. This is what will let `RealInterpolationSpace` actually be built as a
`QuasinormedAddCommGroup` (closure of the defining subtype under `+`, plus the class's own
`norm_add_le` field) — no instance work has been attempted yet, this is purely the analytic fact
it would rest on. STATEMENT ONLY — proof deferred; likely the single hardest piece of Unit 4,
needing genuine control of `K(t, a+b)` against `K(t,a) + K(t,b)` (itself following from `K`'s own
subadditivity, an easy consequence of its defining infimum, propagated through the `(θ,q)`
integral/supremum via a Minkowski-style argument). -/
theorem InterpolationCouple.realInterpolationENorm_add_le
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q) :
    ∃ C : ℝ≥0∞, 0 < C ∧ ∀ a b : InterpolationCouple.sum ι₀ ι₁,
      InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q (a + b) ≤
        C * (InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q a +
          InterpolationCouple.realInterpolationENorm ι₀ ι₁ θ q b) := by
  sorry

/-- Triebel §1.3.3's "exact interpolation functor of type `θ`" property, in inequality form: a
morphism `T : C ⟶ D` bounded by `M₀, M₁` on the legs (in the same "arbitrary upper bound" sense as
`InterpolationCat.Hom.kFunctional_sumMap_le`) scales the `(θ,q)`-quasinorm by `M₀^{1-θ}M₁^θ`, up
to the same `(θ,q)`-dependent constant as `realInterpolationENorm_add_le`. Should follow fairly
directly from `kFunctional_sumMap_le` via a substitution `t ↦ t·(M₁/M₀)^θ`-style rescaling inside
the defining integral/supremum, once that machinery is in place — flagged as the most tractable
piece of Unit 4 to attempt first, once the statement itself is signed off. STATEMENT ONLY — proof
deferred. -/
theorem InterpolationCat.Hom.realInterpolationENorm_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.realInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap a) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
        InterpolationCouple.realInterpolationENorm C.ι₀ C.ι₁ θ q a := by
  sorry
