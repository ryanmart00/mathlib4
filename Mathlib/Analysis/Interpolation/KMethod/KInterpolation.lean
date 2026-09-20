/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.KMethod.KFunctional
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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

/-- Rescale `x` by a power of `c` (any element of norm `> 1`) to land in the "shell"
`[ε/‖c‖, ε)`. Pure real-number `rpow` algebra: the identity that lets `kFunctional_sumMap_le`'s
`t ↦ t·M₁/M₀` substitution turn into the `M₀^{1-θ}M₁^θ` factor in
`realInterpolationENorm_sumMap_le`'s statement. -/
theorem InterpolationCouple.rpow_scale_identity {θ M₀ M₁ t : ℝ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (ht : 0 < t) :
    t ^ (-θ) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ) := by
  have hs : 0 < t * M₁ / M₀ := by positivity
  rw [Real.div_rpow (by positivity) hM₀.le, Real.mul_rpow ht.le hM₁.le]
  rw [Real.rpow_neg ht.le, Real.rpow_neg (by positivity), Real.rpow_neg hM₀.le]
  have h1 : M₀ ^ (1 - θ) = M₀ ^ (1:ℝ) * M₀ ^ (-θ) := by
    rw [← Real.rpow_add hM₀]; ring_nf
  rw [h1, Real.rpow_one, Real.rpow_neg hM₀.le]
  have ht' : t ^ θ ≠ 0 := (Real.rpow_pos_of_pos ht θ).ne'
  have hM₀' : M₀ ^ θ ≠ 0 := (Real.rpow_pos_of_pos hM₀ θ).ne'
  have hM₁' : M₁ ^ θ ≠ 0 := (Real.rpow_pos_of_pos hM₁ θ).ne'
  field_simp

/-- The `dt/t` measure (the Haar measure on the multiplicative group of positive reals) is
invariant under dilation `t ↦ c·t`. No such lemma (or the multiplicative-Haar-measure
infrastructure it would come from) currently exists in Mathlib for `lintegral`; proved from
scratch via the *additive* Haar measure's own dilation formula (`Real.map_volume_mul_left`) and
`MeasureTheory.setLIntegral_map`, splitting off and cancelling the resulting constant factor. -/
theorem InterpolationCouple.lintegral_Ioi_comp_mul_left_div_self {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t in Set.Ioi (0:ℝ), F (c * t) * ENNReal.ofReal t⁻¹ =
    ∫⁻ t in Set.Ioi (0:ℝ), F t * ENNReal.ofReal t⁻¹ := by
  have hg : Measurable (fun t : ℝ => c * t) := measurable_const_mul c
  have hf : Measurable (fun y : ℝ => F y * ENNReal.ofReal y⁻¹) :=
    hF.mul (ENNReal.measurable_ofReal.comp measurable_inv)
  have hs : MeasurableSet (Set.Ioi (0:ℝ)) := measurableSet_Ioi
  have hmap := MeasureTheory.setLIntegral_map (μ := volume) hs hf hg
  rw [show (fun t : ℝ => c * t) ⁻¹' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) by
    rw [preimage_const_mul_Ioi₀ (0:ℝ) hc]; simp] at hmap
  rw [Real.map_volume_mul_left (ne_of_gt hc)] at hmap
  simp only [abs_of_pos (inv_pos.2 hc)] at hmap
  rw [MeasureTheory.Measure.restrict_smul, MeasureTheory.lintegral_smul_measure,
    smul_eq_mul] at hmap
  have hrw : ∀ x : ℝ, F (c * x) * ENNReal.ofReal (c * x)⁻¹ =
      ENNReal.ofReal c⁻¹ * (F (c * x) * ENNReal.ofReal x⁻¹) := by
    intro x
    rw [mul_inv, ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hc))]
    ring
  simp only [hrw] at hmap
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmap
  have h0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have htop : ENNReal.ofReal c⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 := congrArg ((ENNReal.ofReal c⁻¹)⁻¹ * ·) hmap
  rw [ENNReal.inv_mul_cancel_left h0 htop, ENNReal.inv_mul_cancel_left h0 htop] at h1
  exact h1.symm

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The K-functional, extended to all of `ℝ` via `max t 0`, is globally measurable — monotone
(via `kFunctional_mono`, itself only proved on `t ≥ 0`) composed with the globally-monotone `max
· 0`. `K` itself is *not* known to be measurable on all of `ℝ` (its behaviour for `t < 0` was never
pinned down), so this `max`-extended stand-in, agreeing with `K` exactly on `Ioi 0`
(`kFunctional_max_eq`), is what `lintegral_Ioi_comp_mul_left_div_self` above is actually applied
to. -/
theorem InterpolationCouple.kFunctional_max_measurable
    (a : InterpolationCouple.sum ι₀ ι₁) :
    Measurable (fun t : ℝ => InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) a) := by
  have hmono : Monotone (fun t : ℝ =>
      InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) a) := by
    intro s t hst
    exact InterpolationCouple.kFunctional_mono ι₀ ι₁ (le_max_right s 0)
      (max_le_max hst le_rfl) a
  exact Monotone.measurable hmono

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_max_eq
    (a : InterpolationCouple.sum ι₀ ι₁) {t : ℝ} (ht : 0 < t) :
    InterpolationCouple.KFunctional ι₀ ι₁ (max t 0) a =
      InterpolationCouple.KFunctional ι₀ ι₁ t a := by
  rw [max_eq_left ht.le]

/-- Triebel §1.3.3's "exact interpolation functor of type `θ`" property, in inequality form: a
morphism `T : C ⟶ D` bounded by `M₀, M₁` on the legs (in the same "arbitrary upper bound" sense as
`InterpolationCat.Hom.kFunctional_sumMap_le`) scales the `(θ,q)`-quasinorm by `M₀^{1-θ}M₁^θ`.

Needs **both** `M₀ > 0` and `M₁ > 0` (unlike `kFunctional_sumMap_le`, which only needed `M₀ > 0`):
if `M₁ = 0` were allowed (a valid hypothesis choice whenever `T.f₁ ≡ 0`), the RHS collapses to `0`
(since `M₁ ^ θ = 0` for `θ > 0`, and `0 * x = 0` in `ℝ≥0∞` even for `x = ⊤`), falsely asserting
`T.sumMap a = 0` for every `a` whenever `T.f₁ ≡ 0` — false whenever `T.f₀ ≠ 0`, since then
`T.sumMap a = inl₀ (T.f₀ a₀)` is generically a nonzero (hence positive-`(θ,q)`-norm) element of
`D`'s sum space. `kFunctional_sumMap_le` doesn't have this issue since `M₁` only ever appears
*linearly* inside `K_C`'s argument there, giving a genuinely valid (if weak, `t`-independent)
bound at `M₁ = 0`, rather than a vanishing exponent. Caught while attempting this proof; matches
how the classical type-`θ` operator-norm inequality is standardly used for operators with both
leg-norms positive, the degenerate case being a recognized but usually-implicit technicality.
Signed off by Ryan.

The proof needs `θ` to be a plain real (never `0 < θ < 1`) — that hypothesis, part of the signed-off
statement, turns out unused here; it matters for `realInterpolationENorm_meetToSum_lt_top`/
`.._add_le` above, not for this one, and is kept for consistency with the rest of the `(θ,q)` API.

Proved with the help of the three lemmas above (`rpow_scale_identity`,
`lintegral_Ioi_comp_mul_left_div_self`, `kFunctional_max_measurable`/`.._max_eq`), none of which
have a Mathlib home yet — they're general facts about `rpow` algebra and the `dt/t` measure, not
specific to interpolation theory, so may be worth upstreaming separately later. -/
theorem InterpolationCat.Hom.realInterpolationENorm_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (θ : ℝ) (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (q : ℝ≥0∞) (hq : 0 < q)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.realInterpolationENorm D.ι₀ D.ι₁ θ q (T.sumMap a) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
        InterpolationCouple.realInterpolationENorm C.ι₀ C.ι₁ θ q a := by
  by_cases hqtop : q = ⊤
  · subst hqtop
    unfold InterpolationCouple.realInterpolationENorm
    simp only [ite_true]
    refine iSup_le fun t => ?_
    have ht : (0:ℝ) < t := t.2
    set s : ℝ := t * M₁ / M₀ with hsdef
    have hs : 0 < s := by rw [hsdef]; positivity
    have hK : InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a) ≤
        M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a :=
      InterpolationCat.Hom.kFunctional_sumMap_le T (t:ℝ) ht.le M₀ M₁ hM₀ h₀ h₁ a
    have halg : (t:ℝ) ^ (-θ) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ * s ^ (-θ) :=
      InterpolationCouple.rpow_scale_identity hM₀ hM₁ ht
    have hnn : (0:ℝ) ≤ InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a :=
      InterpolationCouple.kFunctional_nonneg C.ι₀ C.ι₁ s hs.le a
    have hstep : (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a) ≤
        M₀ ^ (1 - θ) * M₁ ^ θ * (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := by
      have h1 : (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a) ≤
          (t:ℝ) ^ (-θ) * (M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) :=
        mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg ht.le _)
      calc (t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ) (T.sumMap a)
          ≤ (t:ℝ) ^ (-θ) * (M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := h1
        _ = ((t:ℝ) ^ (-θ) * M₀) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a := by ring
        _ = (M₀ ^ (1 - θ) * M₁ ^ θ * s ^ (-θ)) *
              InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a := by rw [halg]
        _ = M₀ ^ (1 - θ) * M₁ ^ θ * (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := by
            ring
    calc ENNReal.ofReal ((t:ℝ) ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t:ℝ)
        (T.sumMap a))
        ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ *
            (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a)) :=
          ENNReal.ofReal_le_ofReal hstep
      _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ENNReal.ofReal (s ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ⨆ s' : ↥(Ioi (0:ℝ)), ENNReal.ofReal
              ((s':ℝ) ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (s':ℝ) a) := by
          gcongr
          exact le_iSup (fun s' : ↥(Ioi (0:ℝ)) => ENNReal.ofReal
            ((s':ℝ) ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (s':ℝ) a)) ⟨s, hs⟩
  · set c : ℝ := M₁ / M₀ with hcdef
    have hc : 0 < c := by rw [hcdef]; positivity
    set H : ℝ → ℝ≥0∞ :=
      fun s => ENNReal.ofReal (s ^ (-θ) *
        InterpolationCouple.KFunctional C.ι₀ C.ι₁ (max s 0) a) ^ q.toReal with hHdef
    have hHmeas : Measurable H := by
      rw [hHdef]
      exact (ENNReal.measurable_ofReal.comp
        ((measurable_id.pow_const _).mul
          (InterpolationCouple.kFunctional_max_measurable C.ι₀ C.ι₁ a))).pow_const _
    have heqC : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ t a) ^
          q.toReal * ENNReal.ofReal t⁻¹ = ∫⁻ t in Set.Ioi (0:ℝ), H t * ENNReal.ofReal t⁻¹ := by
      apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [hHdef]
      simp only [InterpolationCouple.kFunctional_max_eq C.ι₀ C.ι₁ a (Set.mem_Ioi.mp ht)]
    unfold InterpolationCouple.realInterpolationENorm
    simp only [hqtop, ite_false, heqC]
    have hqtoreal : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    have hqinvtoreal : 0 ≤ q⁻¹.toReal := ENNReal.toReal_nonneg
    have hMq : ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal =
        ENNReal.ofReal ((M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hqtoreal.le
    have hstep1 : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ^
          q.toReal * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal *
          ∫⁻ t in Set.Ioi (0:ℝ), H (c * t) * ENNReal.ofReal t⁻¹ := by
      rw [hMq, ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply MeasureTheory.setLIntegral_mono' measurableSet_Ioi
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      have hreal : t ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
          M₀ ^ (1 - θ) * M₁ ^ θ * ((c * t) ^ (-θ) *
            InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a) := by
        have hK : InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
            M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a :=
          InterpolationCat.Hom.kFunctional_sumMap_le T t ht0.le M₀ M₁ hM₀ h₀ h₁ a
        have hcalc : c * t = t * M₁ / M₀ := by rw [hcdef]; ring
        rw [hcalc]
        have hnn : (0:ℝ) ≤ InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a :=
          InterpolationCouple.kFunctional_nonneg C.ι₀ C.ι₁ (t * M₁ / M₀) (by positivity) a
        calc t ^ (-θ) * InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)
            ≤ t ^ (-θ) * (M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a) :=
              mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg ht0.le _)
          _ = (t ^ (-θ) * M₀) * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a := by
              ring
          _ = (M₀ ^ (1 - θ) * M₁ ^ θ * (t * M₁ / M₀) ^ (-θ)) *
                InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a := by
              rw [InterpolationCouple.rpow_scale_identity hM₀ hM₁ ht0]
          _ = M₀ ^ (1 - θ) * M₁ ^ θ * ((t * M₁ / M₀) ^ (-θ) *
                InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a) := by ring
      have hENN : ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ≤
          ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ENNReal.ofReal ((c * t) ^ (-θ) *
              InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hreal
      have hpow : ENNReal.ofReal (t ^ (-θ) *
          InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ^ q.toReal ≤
          (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) *
            ENNReal.ofReal ((c * t) ^ (-θ) *
              InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a)) ^ q.toReal :=
        ENNReal.rpow_le_rpow hENN hqtoreal.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqtoreal.le, hMq] at hpow
      calc ENNReal.ofReal (t ^ (-θ) *
            InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a)) ^ q.toReal *
            ENNReal.ofReal t⁻¹
          ≤ (ENNReal.ofReal ((M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) *
              ENNReal.ofReal ((c * t) ^ (-θ) *
                InterpolationCouple.KFunctional C.ι₀ C.ι₁ (c * t) a) ^ q.toReal) *
            ENNReal.ofReal t⁻¹ := by gcongr
        _ = ENNReal.ofReal ((M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) *
            (H (c * t) * ENNReal.ofReal t⁻¹) := by
            have hct : max (c * t) 0 = c * t := max_eq_left (by positivity)
            rw [hHdef]; simp only [hct]; ring
    rw [InterpolationCouple.lintegral_Ioi_comp_mul_left_div_self hc hHmeas] at hstep1
    have hfinal := ENNReal.rpow_le_rpow hstep1 hqinvtoreal
    rw [ENNReal.mul_rpow_of_nonneg _ _ hqinvtoreal] at hfinal
    have hconst : (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) ^ q.toReal) ^ q⁻¹.toReal =
        ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) := by
      rw [← ENNReal.rpow_mul]
      have : q.toReal * q⁻¹.toReal = 1 := by
        rw [ENNReal.toReal_inv]
        exact mul_inv_cancel₀ hqtoreal.ne'
      rw [this, ENNReal.rpow_one]
    rwa [hconst] at hfinal
