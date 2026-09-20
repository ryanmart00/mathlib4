/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.MeasureTheory.Function.LorentzSpace.Defs
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The quasi-triangle inequality for `lorentzNorm`

Mirrors `MeasureTheory.Function.LpSeminorm.TriangleInequality` (relative to
`LpSeminorm.Defs`/`LpSpace.Basic`): basic algebraic facts about `lorentzNorm` (congruence under
a.e. equality, behavior on `0`/negation) plus the main result, `lorentzNorm_add_le` — a genuine
*quasi*-triangle inequality (constant `2 ^ (1 + p⁻¹.toReal + q⁻¹.toReal)`, not `1`), valid
uniformly for **all** `p q : ℝ≥0∞` including the degenerate `q = 0`/`q = ⊤` cases. This is what
lets `LorentzSpace/Basic.lean` close `LorentzLp.add_mem'` and
`LorentzLp.instQuasinormedAddCommGroup.norm_add_le`.

## Mathematical content

The proof is the classical Hardy–Littlewood-type argument: the decreasing rearrangement is
subadditive up to a shift, `(f+g)*(t) ≤ f*(t/2) + g*(t/2)` (`decreasingRearrangement_add_two_le`,
itself from the sub-additivity of the distribution function,
`ϱ(f+g,σ+τ) ≤ ϱ(f,σ)+ϱ(g,τ)`). Combined with the crude, uniformly-valid (for every real exponent
`r ≥ 0`, not just `r ≥ 1`) doubling bound `(a+b)^r ≤ 2^r*(a^r+b^r)` in place of sharp Minkowski
(which would need `r ≥ 1`), plus a change-of-variables `t ↦ 2u` rescaling identity for the
defining integral, this gives the triangle inequality with an explicit (not claimed sharp)
constant, for every `p, q` — including `q = 0`/`q = ⊤`, handled directly rather than excluded.

Also proves `lorentzNorm_eq_zero_iff` (`lorentzNorm p q μ f = 0 ↔ f =ᵐ[μ] 0`, for `0 < q`) — the
other axiom `LorentzLp.instQuasinormedAddCommGroup` needs. **Genuinely** needs `0 < q`: at `q = 0`,
`lorentzNorm` is constantly `1` (`lorentzNorm_zero_exponent`), so the forward direction is simply
false there, not just unproved (see `Basic.lean`'s module docstring/design discussion). The
argument: `lorentzNorm p q μ f = 0` forces the decreasing rearrangement `f*` to vanish on all of
`(0,∞)` (via `iSup`/`lintegral` both forcing "every term/a.e. value is `0`", then, in the
`lintegral` case, upgrading "a.e. `0`" to "everywhere `0`" using that `f*` is antitone —
`antitone_eq_zero_of_ae_restrict_eq_zero`, a short general argument comparing an antitone
function's null-set to a concrete interval `Ioc 0 t₀` of positive Lebesgue measure). `f*` vanishing
on `(0,∞)` then forces `f =ᵐ[μ] 0` via the distribution function (`ϱ(f,σ) = 0` for all `σ > 0`,
then a countable-union-of-null-sets argument, `ae_eq_zero_of_distributionFunction_eq_zero`).
-/

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

omit [MeasurableSpace α] in
/-- The crude "quasi-Minkowski" doubling bound `(a+b)^r ≤ 2^r*(a^r+b^r)`, valid for *every*
`r ≥ 0` (unlike sharp Minkowski, which needs `r ≥ 1`) — this is what lets the whole quasi-triangle
inequality below go through uniformly for all `p, q`, not just `p, q ≥ 1`. -/
theorem ENNReal.add_rpow_le_two_rpow_mul (a b : ℝ≥0∞) (r : ℝ) (hr : 0 ≤ r) :
    (a + b) ^ r ≤ 2 ^ r * (a ^ r + b ^ r) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ r ≤ (b + b) ^ r := by gcongr
      _ = 2 ^ r * b ^ r := by rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ hr]
      _ ≤ 2 ^ r * (a ^ r + b ^ r) := by gcongr; exact le_add_self
  · calc (a + b) ^ r ≤ (a + a) ^ r := by gcongr
      _ = 2 ^ r * a ^ r := by rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ hr]
      _ ≤ 2 ^ r * (a ^ r + b ^ r) := by gcongr; exact le_self_add

omit [MeasurableSpace α] in
/-- Rescaling `∫₀^∞` by `t ↦ 2u`: `∫⁻ t, H t = 2 * ∫⁻ u, H (2u)`, via the Jacobian `|d(2u)/du| = 2`.
The multiplicative building block for relating `lorentzNorm`'s defining integral at `f*(t/2)` back
to the same integral at `f*(u)`. -/
theorem lintegral_Ioi_eq_two_mul_lintegral_comp_two_mul (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0:ℝ), H t = 2 * ∫⁻ u in Ioi (0:ℝ), H (2 * u) := by
  have hs : MeasurableSet (Ioi (0:ℝ)) := measurableSet_Ioi
  have hf' : ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt (fun x : ℝ => 2 * x) (2:ℝ) (Ioi (0:ℝ)) x := by
    intro x _
    simpa using ((hasDerivAt_id x).const_mul (2:ℝ)).hasDerivWithinAt (s := Ioi (0:ℝ))
  have hmono : MonotoneOn (fun x : ℝ => 2 * x) (Ioi (0:ℝ)) := by
    intro x _ y _ hxy
    dsimp only
    linarith
  have himg : (fun x : ℝ => (2:ℝ) * x) '' Ioi (0:ℝ) = Ioi (0:ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [mem_Ioi] at hx ⊢
      linarith
    · intro hy
      simp only [mem_Ioi] at hy
      exact ⟨y / 2, by simp only [mem_Ioi]; linarith, by ring⟩
  have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hmono H
  rw [himg] at key
  simp only [ENNReal.ofReal_ofNat] at key
  rw [key, lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]

/-- `distributionFunction` only depends on `f` through its a.e.-equivalence class: altering `f` on
a `μ`-null set doesn't change the measure of any of its super-level sets. Needed so `lorentzNorm`
descends to `α →ₘ[μ] E` (`MeasureTheory.AEEqFun`), exactly as `eLpNorm_congr_ae` does for `eLpNorm`.
-/
theorem distributionFunction_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) (σ : ℝ≥0∞) :
    distributionFunction μ f σ = distributionFunction μ g σ := by
  unfold distributionFunction
  apply measure_congr
  filter_upwards [hfg] with x hx
  simp [hx]

theorem decreasingRearrangement_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) (t : ℝ≥0∞) :
    decreasingRearrangement μ f t = decreasingRearrangement μ g t := by
  unfold decreasingRearrangement
  congr 1
  ext σ
  simp only [Set.mem_ofPred_eq, distributionFunction_congr_ae hfg]

theorem lorentzNorm_congr_ae (p q : ℝ≥0∞) {f g : α → E} (hfg : f =ᵐ[μ] g) :
    lorentzNorm μ p q f = lorentzNorm μ p q g := by
  unfold lorentzNorm
  simp_rw [decreasingRearrangement_congr_ae hfg]

theorem distributionFunction_zero (σ : ℝ≥0∞) : distributionFunction μ (0 : α → E) σ = 0 := by
  unfold distributionFunction
  have : {x : α | σ < ‖(0 : α → E) x‖ₑ} = ∅ := by ext x; simp
  rw [this, measure_empty]

theorem decreasingRearrangement_zero (t : ℝ≥0∞) :
    decreasingRearrangement μ (0 : α → E) t = 0 := by
  unfold decreasingRearrangement
  simp [distributionFunction_zero]

/-- `lorentzNorm` of the zero function is at most `1` (in fact `0` unless `p = q = 0`, an
otherwise-unused degenerate case — `≤ 1` is all that's needed for `LorentzLp.zero_mem'`, and is
uniformly true, so no case restriction on `p, q` is imposed here). -/
theorem lorentzNorm_zero_le_one (p q : ℝ≥0∞) : lorentzNorm μ p q (0 : α → E) ≤ 1 := by
  unfold lorentzNorm
  split
  · simp [decreasingRearrangement_zero]
  · rename_i hqtop
    rcases eq_or_ne q 0 with hq0 | hq0
    · simp [hq0]
    · have hqtoReal : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
      simp [decreasingRearrangement_zero, ENNReal.zero_rpow_of_pos hqtoReal,
        ENNReal.zero_rpow_of_pos (inv_pos.mpr hqtoReal)]

theorem distributionFunction_neg (f : α → E) (σ : ℝ≥0∞) :
    distributionFunction μ (-f) σ = distributionFunction μ f σ := by
  unfold distributionFunction
  congr 1
  ext x
  simp

theorem decreasingRearrangement_neg (f : α → E) (t : ℝ≥0∞) :
    decreasingRearrangement μ (-f) t = decreasingRearrangement μ f t := by
  unfold decreasingRearrangement
  simp_rw [distributionFunction_neg]

theorem lorentzNorm_neg (p q : ℝ≥0∞) (f : α → E) :
    lorentzNorm μ p q (-f) = lorentzNorm μ p q f := by
  unfold lorentzNorm
  simp_rw [decreasingRearrangement_neg]

/-- Triebel's rearrangement sub-additivity: `ϱ(f+g,σ+τ) ≤ ϱ(f,σ)+ϱ(g,τ)`, from
`‖f x+g x‖ ≤ ‖f x‖+‖g x‖` pointwise. -/
theorem distributionFunction_add_le (f g : α → E) (σ τ : ℝ≥0∞) :
    distributionFunction μ (f + g) (σ + τ) ≤
      distributionFunction μ f σ + distributionFunction μ g τ := by
  unfold distributionFunction
  have hsub : {x : α | σ + τ < ‖(f + g) x‖ₑ} ⊆ {x | σ < ‖f x‖ₑ} ∪ {x | τ < ‖g x‖ₑ} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    have h1 : ‖f x + g x‖ₑ ≤ ‖f x‖ₑ + ‖g x‖ₑ := enorm_add_le _ _
    have h2 : ‖f x + g x‖ₑ ≤ σ + τ := h1.trans (add_le_add hcon.1 hcon.2)
    exact absurd h2 (not_le.mpr hx)
  calc μ {x | σ + τ < ‖(f + g) x‖ₑ}
      ≤ μ ({x | σ < ‖f x‖ₑ} ∪ {x | τ < ‖g x‖ₑ}) := measure_mono hsub
    _ ≤ μ {x | σ < ‖f x‖ₑ} + μ {x | τ < ‖g x‖ₑ} := measure_union_le _ _

/-- Triebel's decreasing-rearrangement sub-additivity: `(f+g)*(t+s) ≤ f*(t)+g*(s)`. -/
theorem decreasingRearrangement_add_le (f g : α → E) (t s : ℝ≥0∞) :
    decreasingRearrangement μ (f + g) (t + s) ≤
      decreasingRearrangement μ f t + decreasingRearrangement μ g s := by
  unfold decreasingRearrangement
  set A := sInf {σ : ℝ≥0∞ | distributionFunction μ f σ ≤ t} with hA
  set B := sInf {τ : ℝ≥0∞ | distributionFunction μ g τ ≤ s} with hB
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hAB
  have hεA : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
    ENNReal.div_pos (by exact_mod_cast hε.ne') (by norm_num)
  have hAlt : A < A + (ε : ℝ≥0∞) / 2 := by
    have hAfin : A < ∞ := lt_of_le_of_lt le_self_add hAB
    exact ENNReal.lt_add_right hAfin.ne hεA.ne'
  have hBlt : B < B + (ε : ℝ≥0∞) / 2 := by
    have hBfin : B < ∞ := lt_of_le_of_lt le_add_self hAB
    exact ENNReal.lt_add_right hBfin.ne hεA.ne'
  obtain ⟨σ₀, hσ₀mem, hσ₀lt⟩ := sInf_lt_iff.mp (hA ▸ hAlt)
  obtain ⟨τ₀, hτ₀mem, hτ₀lt⟩ := sInf_lt_iff.mp (hB ▸ hBlt)
  have hmem : σ₀ + τ₀ ∈ {σ : ℝ≥0∞ | distributionFunction μ (f + g) σ ≤ t + s} := by
    simp only [Set.mem_ofPred_eq]
    calc distributionFunction μ (f + g) (σ₀ + τ₀)
        ≤ distributionFunction μ f σ₀ + distributionFunction μ g τ₀ :=
          distributionFunction_add_le f g σ₀ τ₀
      _ ≤ t + s := add_le_add hσ₀mem hτ₀mem
  calc sInf {σ : ℝ≥0∞ | distributionFunction μ (f + g) σ ≤ t + s}
      ≤ σ₀ + τ₀ := csInf_le' hmem
    _ ≤ (A + (ε : ℝ≥0∞) / 2) + (B + (ε : ℝ≥0∞) / 2) := add_le_add hσ₀lt.le hτ₀lt.le
    _ = A + B + ε := by rw [add_add_add_comm, ENNReal.add_halves]

/-- The shifted form actually used below: `(f+g)*(t) ≤ f*(t/2)+g*(t/2)`. -/
theorem decreasingRearrangement_add_two_le (f g : α → E) (t : ℝ≥0∞) :
    decreasingRearrangement μ (f + g) t ≤
      decreasingRearrangement μ f (t / 2) + decreasingRearrangement μ g (t / 2) := by
  have := decreasingRearrangement_add_le (μ := μ) f g (t / 2) (t / 2)
  rwa [ENNReal.add_halves] at this

omit [MeasurableSpace α] in
theorem ofReal_div_two (t : ℝ) : ENNReal.ofReal t / 2 = ENNReal.ofReal (t / 2) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]

/-- The decreasing rearrangement is antitone in `t` (hence, being monotone between linear orders
with the order topology, automatically measurable — `decreasingRearrangement_measurable`). -/
theorem decreasingRearrangement_antitone (h : α → E) :
    Antitone (fun t => decreasingRearrangement μ h t) := by
  intro t₁ t₂ ht
  unfold decreasingRearrangement
  apply sInf_le_sInf
  intro σ hσ
  simp only [Set.mem_ofPred_eq] at hσ ⊢
  exact hσ.trans ht

theorem decreasingRearrangement_measurable (h : α → E) :
    Measurable (fun t => decreasingRearrangement μ h t) :=
  (decreasingRearrangement_antitone (μ := μ) h).measurable

/-- Measurability of `lorentzNorm`'s defining integrand (at the shifted argument `t/2`, as needed
for `lintegral_lorentzNorm_scale`/`lorentzNorm_finite_add_le` below) — needed to split
`∫⁻ (X + Y)` into `∫⁻X + ∫⁻Y`. -/
theorem lorentzNorm_integrand_measurable (p : ℝ≥0∞) (h : α → E) (r : ℝ) :
    Measurable (fun t : ℝ =>
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ h (ENNReal.ofReal (t / 2))) ^ r *
        ENNReal.ofReal t⁻¹) := by
  have h1 : Measurable (fun t : ℝ => ENNReal.ofReal t ^ p⁻¹.toReal) :=
    ENNReal.continuous_rpow_const.measurable.comp ENNReal.measurable_ofReal
  have h2 : Measurable (fun t : ℝ => decreasingRearrangement μ h (ENNReal.ofReal (t / 2))) :=
    (decreasingRearrangement_measurable h).comp
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const 2))
  have h3 : Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹) :=
    ENNReal.measurable_ofReal.comp measurable_inv
  exact (ENNReal.continuous_rpow_const.measurable.comp (h1.mul h2)).mul h3

/-- The rescaling identity behind the quasi-triangle inequality: substituting `t = 2u` in
`lorentzNorm`'s defining integral, evaluated at the shifted rearrangement `f*(t/2)`, recovers the
same integral evaluated at `f*(u)` directly, up to the constant `2^{r/p}`. -/
theorem lintegral_lorentzNorm_scale (p : ℝ≥0∞) (h : α → E) (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ t in Ioi (0:ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ h (ENNReal.ofReal (t / 2))) ^ r *
        ENNReal.ofReal t⁻¹
    = 2 ^ (r * p⁻¹.toReal) * ∫⁻ u in Ioi (0:ℝ),
        (ENNReal.ofReal u ^ p⁻¹.toReal * decreasingRearrangement μ h (ENNReal.ofReal u)) ^ r *
          ENNReal.ofReal u⁻¹ := by
  set inner : ℝ → ℝ≥0∞ := fun u =>
    (ENNReal.ofReal u ^ p⁻¹.toReal * decreasingRearrangement μ h (ENNReal.ofReal u)) ^ r *
      ENNReal.ofReal u⁻¹ with hinner
  set H : ℝ → ℝ≥0∞ := fun t =>
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ h (ENNReal.ofReal (t / 2))) ^ r *
      ENNReal.ofReal t⁻¹ with hH
  change ∫⁻ t in Ioi (0:ℝ), H t = 2 ^ (r * p⁻¹.toReal) * ∫⁻ u in Ioi (0:ℝ), inner u
  have hpointwise : ∀ u ∈ Ioi (0:ℝ), H (2 * u) = 2 ^ (r * p⁻¹.toReal) * (2:ℝ≥0∞)⁻¹ * inner u := by
    intro u hu
    simp only [mem_Ioi] at hu
    have h2u : (2 * u / 2 : ℝ) = u := by ring
    simp only [hH, hinner]
    rw [h2u]
    have hofReal2u : ENNReal.ofReal (2 * u) = 2 * ENNReal.ofReal u := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    have hofRealinv2u : ENNReal.ofReal (2 * u)⁻¹ = (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal u⁻¹ := by
      rw [show (2 * u : ℝ)⁻¹ = 2⁻¹ * u⁻¹ by ring, ENNReal.ofReal_mul (by norm_num)]
      rw [show (2⁻¹ : ℝ) = (2:ℝ)⁻¹ from rfl, ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    rw [hofReal2u, hofRealinv2u, ENNReal.mul_rpow_of_nonneg _ _ (ENNReal.toReal_nonneg (a := p⁻¹)),
      mul_assoc (2 ^ p⁻¹.toReal), ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul]
    rw [mul_mul_mul_comm, mul_comm p⁻¹.toReal r]
  rw [lintegral_Ioi_eq_two_mul_lintegral_comp_two_mul H]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpointwise]
  rw [lintegral_const_mul' _ _ (by
    apply ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))
    simp)]
  rw [← mul_assoc]
  congr 1
  rw [mul_comm (2:ℝ≥0∞), mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

/-- The quasi-triangle inequality, `0 < q < ⊤` case, spelled out against `lorentzNorm`'s literal
defining formula (unfolded, since the two exponents `q.toReal`/`q⁻¹.toReal` need to be treated as
a matched pair `r`/`s` with `r*s=1` throughout the proof). -/
theorem lorentzNorm_finite_add_le (p q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ⊤) (f g : α → E) :
    (∫⁻ t in Ioi (0:ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^
        q.toReal * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal ≤
    2 ^ (1 + p⁻¹.toReal + q⁻¹.toReal) *
      ((∫⁻ t in Ioi (0:ℝ),
          (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal t)) ^
            q.toReal * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal +
        (∫⁻ t in Ioi (0:ℝ),
          (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ g (ENNReal.ofReal t)) ^
            q.toReal * ENNReal.ofReal t⁻¹) ^ q⁻¹.toReal) := by
  set r := q.toReal with hrdef
  set s := q⁻¹.toReal with hsdef
  have hpr : (0:ℝ) ≤ p⁻¹.toReal := ENNReal.toReal_nonneg
  have hr0 : 0 < r := ENNReal.toReal_pos hq0 hqtop
  have hs0 : 0 < s :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hqtop) (ENNReal.inv_ne_top.mpr hq0)
  have hrs : r * s = 1 := by
    rw [hrdef, hsdef, ENNReal.toReal_inv, mul_inv_cancel₀ hr0.ne']
  set A := ∫⁻ t in Ioi (0:ℝ),
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal t)) ^ r *
      ENNReal.ofReal t⁻¹ with hA
  set B := ∫⁻ t in Ioi (0:ℝ),
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ g (ENNReal.ofReal t)) ^ r *
      ENNReal.ofReal t⁻¹ with hB
  change (∫⁻ t in Ioi (0:ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^ r *
        ENNReal.ofReal t⁻¹) ^ s ≤ 2 ^ (1 + p⁻¹.toReal + s) * (A ^ s + B ^ s)
  have hpointwise : ∀ t ∈ Ioi (0:ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^ r *
          ENNReal.ofReal t⁻¹ ≤
        2 ^ r *
          ((ENNReal.ofReal t ^ p⁻¹.toReal *
                decreasingRearrangement μ f (ENNReal.ofReal (t / 2))) ^ r *
              ENNReal.ofReal t⁻¹ +
            (ENNReal.ofReal t ^ p⁻¹.toReal *
                decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r *
              ENNReal.ofReal t⁻¹) := by
    intro t ht
    have hstep1 : decreasingRearrangement μ (f + g) (ENNReal.ofReal t) ≤
        decreasingRearrangement μ f (ENNReal.ofReal t / 2) +
          decreasingRearrangement μ g (ENNReal.ofReal t / 2) :=
      decreasingRearrangement_add_two_le f g (ENNReal.ofReal t)
    rw [ofReal_div_two] at hstep1
    have hrpow :
        (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^ r
          ≤ 2 ^ r *
            ((ENNReal.ofReal t ^ p⁻¹.toReal *
                  decreasingRearrangement μ f (ENNReal.ofReal (t / 2))) ^ r +
              (ENNReal.ofReal t ^ p⁻¹.toReal *
                  decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r) := by
      calc (ENNReal.ofReal t ^ p⁻¹.toReal *
            decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^ r
          ≤ (ENNReal.ofReal t ^ p⁻¹.toReal *
              (decreasingRearrangement μ f (ENNReal.ofReal (t / 2)) +
                decreasingRearrangement μ g (ENNReal.ofReal (t / 2)))) ^ r := by gcongr
        _ = (ENNReal.ofReal t ^ p⁻¹.toReal *
              decreasingRearrangement μ f (ENNReal.ofReal (t / 2)) +
              ENNReal.ofReal t ^ p⁻¹.toReal *
                decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r := by rw [mul_add]
        _ ≤ 2 ^ r *
              ((ENNReal.ofReal t ^ p⁻¹.toReal *
                    decreasingRearrangement μ f (ENNReal.ofReal (t / 2))) ^ r +
                (ENNReal.ofReal t ^ p⁻¹.toReal *
                    decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r) :=
          ENNReal.add_rpow_le_two_rpow_mul _ _ r hr0.le
    calc (ENNReal.ofReal t ^ p⁻¹.toReal *
          decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^ r * ENNReal.ofReal t⁻¹
        ≤ (2 ^ r *
              ((ENNReal.ofReal t ^ p⁻¹.toReal *
                    decreasingRearrangement μ f (ENNReal.ofReal (t / 2))) ^ r +
                (ENNReal.ofReal t ^ p⁻¹.toReal *
                    decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r)) *
            ENNReal.ofReal t⁻¹ := by gcongr
      _ = 2 ^ r *
            ((ENNReal.ofReal t ^ p⁻¹.toReal *
                  decreasingRearrangement μ f (ENNReal.ofReal (t / 2))) ^ r *
                ENNReal.ofReal t⁻¹ +
              (ENNReal.ofReal t ^ p⁻¹.toReal *
                  decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r *
                ENNReal.ofReal t⁻¹) := by ring
  have hmono : (∫⁻ t in Ioi (0:ℝ),
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^ r *
        ENNReal.ofReal t⁻¹) ≤
      ∫⁻ t in Ioi (0:ℝ), 2 ^ r *
        ((ENNReal.ofReal t ^ p⁻¹.toReal *
              decreasingRearrangement μ f (ENNReal.ofReal (t / 2))) ^ r * ENNReal.ofReal t⁻¹ +
          (ENNReal.ofReal t ^ p⁻¹.toReal *
              decreasingRearrangement μ g (ENNReal.ofReal (t / 2))) ^ r * ENNReal.ofReal t⁻¹) :=
    setLIntegral_mono' measurableSet_Ioi hpointwise
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le (by norm_num)),
    lintegral_add_left' (lorentzNorm_integrand_measurable p f r).aemeasurable,
    lintegral_lorentzNorm_scale p f r hr0.le, lintegral_lorentzNorm_scale p g r hr0.le,
    ← hA, ← hB] at hmono
  have hcollect :
      2 ^ r * (2 ^ (r * p⁻¹.toReal) * A + 2 ^ (r * p⁻¹.toReal) * B) =
        2 ^ (r * (1 + p⁻¹.toReal)) * (A + B) := by
    rw [← mul_add, ← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
      show r + r * p⁻¹.toReal = r * (1 + p⁻¹.toReal) by ring]
  rw [hcollect] at hmono
  calc (∫⁻ t in Ioi (0:ℝ),
        (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (ENNReal.ofReal t)) ^
          r * ENNReal.ofReal t⁻¹) ^ s
      ≤ (2 ^ (r * (1 + p⁻¹.toReal)) * (A + B)) ^ s := by gcongr
    _ = 2 ^ (1 + p⁻¹.toReal) * (A + B) ^ s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ← ENNReal.rpow_mul,
          mul_assoc r (1 + p⁻¹.toReal) s, mul_comm (1 + p⁻¹.toReal) s, ← mul_assoc, hrs, one_mul]
    _ ≤ 2 ^ (1 + p⁻¹.toReal) * (2 ^ s * (A ^ s + B ^ s)) := by
        gcongr
        exact ENNReal.add_rpow_le_two_rpow_mul A B s hs0.le
    _ = 2 ^ (1 + p⁻¹.toReal + s) * (A ^ s + B ^ s) := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]

/-- The quasi-triangle inequality, `q = ⊤` case (the weak-`Lᵖ` case, actually the one Marcinkiewicz
itself needs on the couple's legs). -/
theorem lorentzNorm_top_add_le (p : ℝ≥0∞) (f g : α → E) :
    lorentzNorm μ p ⊤ (f + g) ≤
      2 ^ (1 + p⁻¹.toReal) * (lorentzNorm μ p ⊤ f + lorentzNorm μ p ⊤ g) := by
  have hpr : (0:ℝ) ≤ p⁻¹.toReal := ENNReal.toReal_nonneg
  have hcoe_div : ∀ t : ℝ≥0, (t:ℝ≥0∞) / 2 = ((t / 2 : ℝ≥0) : ℝ≥0∞) := fun t => by
    rw [ENNReal.coe_div (by norm_num : (2:ℝ≥0) ≠ 0)]; norm_num
  have hcoe_mul : ∀ t : ℝ≥0, (t:ℝ≥0∞) = 2 * ((t / 2 : ℝ≥0) : ℝ≥0∞) := fun t => by
    rw [← hcoe_div t, ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]
  have term_le : ∀ (h : α → E) (t : ℝ≥0),
      (t:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ h ((t:ℝ≥0∞) / 2) ≤
        2 ^ p⁻¹.toReal * lorentzNorm μ p ⊤ h := by
    intro h t
    rw [hcoe_div t, hcoe_mul t, ENNReal.mul_rpow_of_nonneg _ _ hpr, mul_assoc]
    gcongr
    unfold lorentzNorm
    simp only [ite_true]
    exact le_iSup
      (fun u : ℝ≥0 => (u:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ h (u:ℝ≥0∞)) (t / 2)
  unfold lorentzNorm
  simp only [ite_true]
  apply iSup_le
  intro t
  calc (t:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ (f + g) (t:ℝ≥0∞)
      ≤ (t:ℝ≥0∞) ^ p⁻¹.toReal *
          (decreasingRearrangement μ f ((t:ℝ≥0∞) / 2) +
            decreasingRearrangement μ g ((t:ℝ≥0∞) / 2)) := by
        gcongr
        exact decreasingRearrangement_add_two_le f g (t:ℝ≥0∞)
    _ = (t:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ f ((t:ℝ≥0∞) / 2) +
          (t:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ g ((t:ℝ≥0∞) / 2) := mul_add _ _ _
    _ ≤ 2 ^ p⁻¹.toReal * lorentzNorm μ p ⊤ f + 2 ^ p⁻¹.toReal * lorentzNorm μ p ⊤ g :=
        add_le_add (term_le f t) (term_le g t)
    _ = 2 ^ p⁻¹.toReal * (lorentzNorm μ p ⊤ f + lorentzNorm μ p ⊤ g) := (mul_add _ _ _).symm
    _ ≤ 2 ^ (1 + p⁻¹.toReal) * (lorentzNorm μ p ⊤ f + lorentzNorm μ p ⊤ g) := by
        gcongr
        · norm_num
        · linarith

/-- The genuinely degenerate `q = 0` case: `lorentzNorm` is *constantly* `1`, independent of `f`
(the outer exponent `q⁻¹.toReal = 0` forces `X^0 = 1` regardless of what the inner integral `X`
evaluates to), so the triangle inequality holds trivially there. -/
theorem lorentzNorm_zero_exponent (p : ℝ≥0∞) (h : α → E) : lorentzNorm μ p 0 h = 1 := by
  unfold lorentzNorm
  rw [if_neg (by simp : (0:ℝ≥0∞) ≠ ⊤)]
  rw [show (0:ℝ≥0∞)⁻¹.toReal = 0 by simp]
  exact ENNReal.rpow_zero

/-- **The quasi-triangle inequality for `lorentzNorm`**, uniformly for all `p q : ℝ≥0∞` — no
positivity/finiteness hypotheses on `p, q` are needed: the degenerate cases `q = 0`/`q = ⊤` are
handled directly (giving a trivial or one-sided bound that the same constant still dominates)
rather than excluded. This is what makes `LorentzLp`'s `QuasinormedAddCommGroup` instance work for
*every* `p, q`, not just `p, q ≥ 1` (`LorentzSpace/Basic.lean`). -/
theorem lorentzNorm_add_le (p q : ℝ≥0∞) (f g : α → E) :
    lorentzNorm μ p q (f + g) ≤
      2 ^ (1 + p⁻¹.toReal + q⁻¹.toReal) * (lorentzNorm μ p q f + lorentzNorm μ p q g) := by
  rcases eq_or_ne q ⊤ with hqtop | hqtop
  · subst hqtop
    simpa using lorentzNorm_top_add_le p f g
  · rcases eq_or_ne q 0 with hq0 | hq0
    · subst hq0
      simp only [lorentzNorm_zero_exponent, ENNReal.inv_zero, ENNReal.toReal_top, add_zero]
      calc (1:ℝ≥0∞) ≤ 2 ^ (1 + p⁻¹.toReal) := by
            calc (1:ℝ≥0∞) = 2 ^ (0:ℝ) := ENNReal.rpow_zero.symm
              _ ≤ 2 ^ (1 + p⁻¹.toReal) := by
                  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
                  positivity
        _ ≤ 2 ^ (1 + p⁻¹.toReal) * (1 + 1) := by
            nth_rewrite 1 [← mul_one (2 ^ (1 + p⁻¹.toReal))]
            gcongr
            norm_num
    · unfold lorentzNorm
      simp only [if_neg hqtop]
      exact lorentzNorm_finite_add_le p q hq0 hqtop f g

/-- `ϱ(f,·)` is antitone: a bigger threshold gives a smaller-or-equal super-level set. -/
theorem distributionFunction_antitone (f : α → E) :
    Antitone (fun σ => distributionFunction μ f σ) := by
  intro σ₁ σ₂ hσ
  apply measure_mono
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact lt_of_le_of_lt hσ hx

/-- Unlike `lorentzNorm_zero_le_one` (valid for all `p, q`), this pins the value down to
*exactly* `0` — needs `0 < q` (see the module docstring: the `q = 0` corner has `lorentzNorm = 1`
identically, so this is genuinely false there, not just harder to prove). -/
theorem lorentzNorm_zero_of_pos (p : ℝ≥0∞) {q : ℝ≥0∞} (hq : 0 < q) :
    lorentzNorm μ p q (0 : α → E) = 0 := by
  unfold lorentzNorm
  split
  · simp [decreasingRearrangement_zero]
  · rename_i hqtop
    have hqtoReal : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    have hqinvtoReal : 0 < q⁻¹.toReal :=
      ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hqtop) (ENNReal.inv_ne_top.mpr hq.ne')
    simp_rw [decreasingRearrangement_zero, mul_zero, ENNReal.zero_rpow_of_pos hqtoReal, zero_mul,
      lintegral_zero, ENNReal.zero_rpow_of_pos hqinvtoReal]

/-- If `f*` vanishes on all of `(0,∞)`, so does `ϱ(f,·)` — a near-optimal representative
`σ' < σ` from `f*(ε) = 0`'s defining `sInf` gives `ϱ(f,σ) ≤ ϱ(f,σ') ≤ ε` for every `ε > 0`. -/
theorem distributionFunction_eq_zero_of_forall_pos (f : α → E)
    (h : ∀ t : ℝ≥0∞, 0 < t → decreasingRearrangement μ f t = 0) (σ : ℝ≥0∞) (hσ : 0 < σ) :
    distributionFunction μ f σ = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add ?_) zero_le
  intro ε hε _
  have hεt := h (ε : ℝ≥0∞) (by exact_mod_cast hε)
  unfold decreasingRearrangement at hεt
  obtain ⟨σ', hσ'mem, hσ'lt⟩ := sInf_lt_iff.mp (hεt ▸ hσ)
  simp only [Set.mem_ofPred_eq] at hσ'mem
  calc distributionFunction μ f σ ≤ distributionFunction μ f σ' :=
        distributionFunction_antitone f hσ'lt.le
    _ ≤ (ε : ℝ≥0∞) := hσ'mem
    _ = 0 + ε := by rw [zero_add]

/-- `ϱ(f,σ) = 0` for every `σ > 0` forces `f =ᵐ[μ] 0`: `{x : f x ≠ 0} = ⋃ₙ {x : (n:ℝ≥0∞)⁻¹ <
‖f x‖ₑ}`, a countable union of `ϱ`-null sets. -/
theorem ae_eq_zero_of_distributionFunction_eq_zero (f : α → E)
    (h : ∀ σ : ℝ≥0∞, 0 < σ → distributionFunction μ f σ = 0) : f =ᵐ[μ] 0 := by
  rw [Filter.EventuallyEq, ae_iff]
  have hunion : {x : α | ¬ f x = (0 : α → E) x} ⊆ ⋃ n : ℕ, {x : α | (n : ℝ≥0∞)⁻¹ < ‖f x‖ₑ} := by
    intro x hx
    simp only [Pi.zero_apply] at hx
    have hpos : 0 < ‖f x‖ₑ := by
      rw [enorm_pos]
      exact hx
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine le_antisymm ?_ zero_le
  calc μ {x : α | ¬ f x = (0 : α → E) x}
      ≤ μ (⋃ n : ℕ, {x : α | (n : ℝ≥0∞)⁻¹ < ‖f x‖ₑ}) := measure_mono hunion
    _ ≤ ∑' n : ℕ, μ {x : α | (n : ℝ≥0∞)⁻¹ < ‖f x‖ₑ} := measure_iUnion_le _
    _ = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        intro n
        rcases eq_or_ne n 0 with hn0 | hn0
        · subst hn0
          simp
        · exact h ((n : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n))

/-- The `q = ⊤` case of `lorentzNorm_eq_zero_iff`'s forward direction: `⨆` of nonneg terms `= 0`
forces every term `= 0` directly (no a.e./measure-theoretic argument needed, unlike the finite-`q`
case below). -/
theorem lorentzNorm_top_eq_zero_imp (p : ℝ≥0∞) (f : α → E)
    (h : lorentzNorm μ p ⊤ f = 0) : ∀ t : ℝ≥0∞, 0 < t → decreasingRearrangement μ f t = 0 := by
  unfold lorentzNorm at h
  rw [if_pos rfl] at h
  have hterm : ∀ t : ℝ≥0,
      (t:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ f (t:ℝ≥0∞) = 0 :=
    fun t => le_antisymm (h ▸ le_iSup
      (fun t : ℝ≥0 => (t:ℝ≥0∞) ^ p⁻¹.toReal * decreasingRearrangement μ f (t:ℝ≥0∞)) t)
      zero_le
  have hfin : ∀ t : ℝ≥0, 0 < t → decreasingRearrangement μ f (t:ℝ≥0∞) = 0 := by
    intro t ht
    have hne : (t:ℝ≥0∞) ^ p⁻¹.toReal ≠ 0 :=
      (ENNReal.rpow_pos (by exact_mod_cast ht) (by simp)).ne'
    rcases mul_eq_zero.mp (hterm t) with h1 | h2
    · exact absurd h1 hne
    · exact h2
  intro t ht
  rcases eq_or_ne t ⊤ with rfl | htne
  · exact le_antisymm
      ((decreasingRearrangement_antitone f le_top).trans_eq (hfin 1 one_pos)) zero_le
  · have ht' : 0 < t.toNNReal := ENNReal.toNNReal_pos ht.ne' htne
    have := hfin t.toNNReal ht'
    rwa [ENNReal.coe_toNNReal htne] at this

/-- An antitone `g : ℝ → ℝ≥0∞` that vanishes Lebesgue-a.e. on `(0,∞)` vanishes *everywhere* on
`(0,∞)`: if `g t₀ ≠ 0` for some `t₀ > 0`, antitonicity forces `g ≠ 0` on the whole interval
`Ioc 0 t₀`, which has positive Lebesgue measure — contradicting a.e.-vanishing. The key step
letting `lorentzNorm_finite_eq_zero_imp` upgrade "a.e. `0`" (from `lintegral_eq_zero_iff`) to
"everywhere `0`" (needed to feed `distributionFunction_eq_zero_of_forall_pos`). -/
theorem antitone_eq_zero_of_ae_restrict_eq_zero {g : ℝ → ℝ≥0∞} (hg : Antitone g)
    (h : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g t = 0) (t₀ : ℝ) (ht₀ : 0 < t₀) : g t₀ = 0 := by
  by_contra hne
  have hpos : 0 < g t₀ := zero_le.lt_of_ne (Ne.symm hne)
  rw [ae_restrict_iff' measurableSet_Ioi] at h
  rw [ae_iff] at h
  have hsub : Ioc (0:ℝ) t₀ ⊆ {t | ¬(t ∈ Ioi (0:ℝ) → g t = 0)} := by
    intro t ht
    simp only [mem_ofPred_eq, not_forall]
    refine ⟨ht.1, ?_⟩
    have : g t₀ ≤ g t := hg ht.2
    exact fun hc => absurd (hc ▸ this) (not_le.mpr hpos)
  have hle : volume (Ioc (0:ℝ) t₀) ≤ 0 := h ▸ measure_mono hsub
  rw [Real.volume_Ioc] at hle
  simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
  linarith

/-- Measurability of `lorentzNorm`'s defining integrand at the *unshifted* argument `t` (as
opposed to `lorentzNorm_integrand_measurable`'s `t/2`) — needed to invoke
`lintegral_eq_zero_iff` directly against `lorentzNorm`'s own literal formula. -/
theorem lorentzNorm_integrand_measurable' (p : ℝ≥0∞) (h : α → E) (r : ℝ) :
    Measurable (fun t : ℝ =>
      (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ h (ENNReal.ofReal t)) ^ r *
        ENNReal.ofReal t⁻¹) := by
  have h1 : Measurable (fun t : ℝ => ENNReal.ofReal t ^ p⁻¹.toReal) :=
    ENNReal.continuous_rpow_const.measurable.comp ENNReal.measurable_ofReal
  have h2 : Measurable (fun t : ℝ => decreasingRearrangement μ h (ENNReal.ofReal t)) :=
    (decreasingRearrangement_measurable h).comp ENNReal.measurable_ofReal
  have h3 : Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹) :=
    ENNReal.measurable_ofReal.comp measurable_inv
  exact (ENNReal.continuous_rpow_const.measurable.comp (h1.mul h2)).mul h3

/-- The `0 < q < ⊤` case of `lorentzNorm_eq_zero_iff`'s forward direction. -/
theorem lorentzNorm_finite_eq_zero_imp (p q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ⊤) (f : α → E)
    (h : lorentzNorm μ p q f = 0) :
    ∀ t : ℝ, 0 < t → decreasingRearrangement μ f (ENNReal.ofReal t) = 0 := by
  unfold lorentzNorm at h
  rw [if_neg hqtop] at h
  set F : ℝ → ℝ≥0∞ := fun t =>
    (ENNReal.ofReal t ^ p⁻¹.toReal * decreasingRearrangement μ f (ENNReal.ofReal t)) ^ q.toReal *
      ENNReal.ofReal t⁻¹ with hFdef
  change (∫⁻ t in Ioi (0:ℝ), F t) ^ q⁻¹.toReal = 0 at h
  have hsinv : 0 < q⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hqtop) (ENNReal.inv_ne_top.mpr hq0)
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hint0 : (∫⁻ t in Ioi (0:ℝ), F t) = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hsinv.le)
  have hFmeas : Measurable F := lorentzNorm_integrand_measurable' p f q.toReal
  have hFae : F =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 :=
    (lintegral_eq_zero_iff hFmeas).mp hint0
  have hgae : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))),
      decreasingRearrangement μ f (ENNReal.ofReal t) = 0 := by
    filter_upwards [hFae, ae_restrict_mem measurableSet_Ioi] with t hFt htmem
    simp only [Pi.zero_apply, hFdef] at hFt
    have hweight : ENNReal.ofReal t⁻¹ ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.mpr htmem
    have hbase : (ENNReal.ofReal t ^ p⁻¹.toReal *
        decreasingRearrangement μ f (ENNReal.ofReal t)) ^ q.toReal = 0 :=
      (mul_eq_zero.mp hFt).resolve_right hweight
    have hpow : ENNReal.ofReal t ^ p⁻¹.toReal *
        decreasingRearrangement μ f (ENNReal.ofReal t) = 0 := by
      rcases ENNReal.rpow_eq_zero_iff.mp hbase with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 (not_lt.mpr hr.le)
    have hne : ENNReal.ofReal t ^ p⁻¹.toReal ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr htmem) (by simp)).ne'
    exact (mul_eq_zero.mp hpow).resolve_left hne
  intro t ht
  apply antitone_eq_zero_of_ae_restrict_eq_zero _ hgae t ht
  exact (decreasingRearrangement_antitone f).comp_monotone ENNReal.ofReal_mono

/-- **The full characterization of when `lorentzNorm` vanishes**, for `0 < q` — see the module
docstring for why `0 < q` is genuinely needed, not just a convenience hypothesis. -/
theorem lorentzNorm_eq_zero_iff (p q : ℝ≥0∞) (hq : 0 < q) (f : α → E) :
    lorentzNorm μ p q f = 0 ↔ f =ᵐ[μ] 0 := by
  constructor
  · intro h
    apply ae_eq_zero_of_distributionFunction_eq_zero f
    apply distributionFunction_eq_zero_of_forall_pos f
    rcases eq_or_ne q ⊤ with hqtop | hqtop
    · subst hqtop
      exact lorentzNorm_top_eq_zero_imp p f h
    · intro t ht
      rcases eq_or_ne t ⊤ with rfl | htne
      · have h1 := lorentzNorm_finite_eq_zero_imp p q hq.ne' hqtop f h 1 one_pos
        exact le_antisymm ((decreasingRearrangement_antitone f le_top).trans_eq h1) zero_le
      · have ht' : 0 < t.toReal := ENNReal.toReal_pos ht.ne' htne
        have := lorentzNorm_finite_eq_zero_imp p q hq.ne' hqtop f h t.toReal ht'
        rwa [ENNReal.ofReal_toReal htne] at this
  · intro hf
    rw [lorentzNorm_congr_ae p q hf, lorentzNorm_zero_of_pos p hq]
