/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.Couple
import Mathlib.Analysis.Interpolation.InterpolationCat
import Mathlib.Analysis.Interpolation.TrivialFunctors
import Mathlib.Analysis.Convex.Function
import Mathlib.CategoryTheory.Iso

/-!
# The K-functional

DRAFT — under review.

Triebel §1.3.1: for an interpolation couple `{A₀,A₁}`, `t > 0`, and `a ∈ A₀+A₁`,
`K(t,a) = inf_{a=a₀+a₁} (‖a₀‖ + t‖a₁‖)`. This is the starting point of the K-method (real
interpolation): the spaces `(A₀,A₁)_{θ,q}` (§1.3.2) are defined by prescribing the behavior of
`K(t,a)` as `t → 0` and `t → ∞`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁] [CompleteSpace A₁]
variable (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)

/-- The K-functional: `K(t,a) = inf_{a = a₀+a₁} (‖a₀‖ + t‖a₁‖)`. -/
noncomputable def InterpolationCouple.KFunctional (t : ℝ) (a : InterpolationCouple.sum ι₀ ι₁) :
    ℝ :=
  sInf {r : ℝ | ∃ a₀ : A₀, ∃ a₁ : A₁,
    (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum ι₀ ι₁) = a ∧ ‖a₀‖ + t * ‖a₁‖ = r}

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_set_nonempty (t : ℝ) (a : InterpolationCouple.sum ι₀ ι₁) :
    {r : ℝ | ∃ a₀ : A₀, ∃ a₁ : A₁,
      (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum ι₀ ι₁) = a ∧
        ‖a₀‖ + t * ‖a₁‖ = r}.Nonempty := by
  obtain ⟨⟨a₀, a₁⟩, ha⟩ := Submodule.Quotient.mk_surjective _ a
  exact ⟨‖a₀‖ + t * ‖a₁‖, a₀, a₁, ha, rfl⟩

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_set_boundedBelow (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    BddBelow {r : ℝ | ∃ a₀ : A₀, ∃ a₁ : A₁,
      (Submodule.Quotient.mk (a₀, a₁) : InterpolationCouple.sum ι₀ ι₁) = a ∧
        ‖a₀‖ + t * ‖a₁‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨a₀, a₁, -, rfl⟩
  nlinarith [QuasinormedAddCommGroup.norm_nonneg a₀, QuasinormedAddCommGroup.norm_nonneg a₁]

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.kFunctional_nonneg (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    0 ≤ InterpolationCouple.KFunctional ι₀ ι₁ t a :=
  le_csInf (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a) (by
    rintro r ⟨a₀, a₁, -, rfl⟩
    nlinarith [QuasinormedAddCommGroup.norm_nonneg a₀, QuasinormedAddCommGroup.norm_nonneg a₁])

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K(t,a)` is monotone increasing in `t`, for `t ≥ 0`. -/
theorem InterpolationCouple.kFunctional_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    InterpolationCouple.KFunctional ι₀ ι₁ s a ≤ InterpolationCouple.KFunctional ι₀ ι₁ t a := by
  apply le_csInf (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a)
  rintro r ⟨a₀, a₁, ha, rfl⟩
  have hr' : ‖a₀‖ + s * ‖a₁‖ ∈ {r : ℝ | ∃ a₀' : A₀, ∃ a₁' : A₁,
      (Submodule.Quotient.mk (a₀', a₁') : InterpolationCouple.sum ι₀ ι₁) = a ∧
        ‖a₀'‖ + s * ‖a₁'‖ = r} := ⟨a₀, a₁, ha, rfl⟩
  calc InterpolationCouple.KFunctional ι₀ ι₁ s a
      ≤ ‖a₀‖ + s * ‖a₁‖ :=
        csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ s hs a) hr'
    _ ≤ ‖a₀‖ + t * ‖a₁‖ := by nlinarith [QuasinormedAddCommGroup.norm_nonneg a₁]

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K(t,a) ≥ min(1,t) ‖a‖`, relating `K` back to the couple's own sum-space norm. -/
theorem InterpolationCouple.min_mul_norm_le_kFunctional (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    min 1 t * ‖a‖ ≤ InterpolationCouple.KFunctional ι₀ ι₁ t a := by
  apply le_csInf (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a)
  rintro r ⟨a₀, a₁, ha, rfl⟩
  have h1 : ‖a‖ ≤ max ‖a₀‖ ‖a₁‖ := by
    rw [← ha]
    exact (QuasinormedAddCommGroup.quotientNorm_mk_le
      (InterpolationCouple.plus ι₀ ι₁).ker.toAddSubgroup (a₀, a₁)).trans_eq (Prod.norm_def _)
  have h2 : min 1 t * max ‖a₀‖ ‖a₁‖ ≤ ‖a₀‖ + t * ‖a₁‖ := by
    rcases le_total ‖a₀‖ ‖a₁‖ with h | h
    · rw [max_eq_right h]
      nlinarith [min_le_right (1 : ℝ) t, QuasinormedAddCommGroup.norm_nonneg a₀]
    · rw [max_eq_left h]
      nlinarith [min_le_left (1 : ℝ) t, QuasinormedAddCommGroup.norm_nonneg a₁]
  calc min 1 t * ‖a‖ ≤ min 1 t * max ‖a₀‖ ‖a₁‖ :=
        mul_le_mul_of_nonneg_left h1 (le_min zero_le_one ht)
    _ ≤ ‖a₀‖ + t * ‖a₁‖ := h2

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K(t,a) ≤ 2 max(1,t) ‖a‖` — the extra factor `2` (compared to Triebel's literal
`max(1,t)‖a‖`) comes from our `sum`'s norm being the *max*-based quotient norm, not Triebel's
literal `inf ‖a₀‖+‖a₁‖` sum-norm; the two are equivalent but not equal (documented in
`Couple.lean`). -/
theorem InterpolationCouple.kFunctional_le_two_mul_max_mul_norm (t : ℝ) (ht : 0 ≤ t)
    (a : InterpolationCouple.sum ι₀ ι₁) :
    InterpolationCouple.KFunctional ι₀ ι₁ t a ≤ 2 * max 1 t * ‖a‖ := by
  have hmax : (0 : ℝ) < 2 * max 1 t := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hxlt⟩ := QuasinormedAddCommGroup.exists_norm_lt_quotientNorm_add
    (N := (InterpolationCouple.plus ι₀ ι₁).ker.toAddSubgroup) (x := a) (div_pos hε hmax)
  have hb : InterpolationCouple.KFunctional ι₀ ι₁ t a ≤ ‖x.1‖ + t * ‖x.2‖ :=
    csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht a)
      ⟨x.1, x.2, hx, rfl⟩
  have hc : ‖x.1‖ + t * ‖x.2‖ ≤ 2 * max 1 t * ‖x‖ := by
    rw [Prod.norm_def]
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [le_max_right (1 : ℝ) t, le_max_left (1 : ℝ) t, QuasinormedAddCommGroup.norm_nonneg x.1, QuasinormedAddCommGroup.norm_nonneg x.2]
    · rw [max_eq_left h]
      nlinarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t, QuasinormedAddCommGroup.norm_nonneg x.1, QuasinormedAddCommGroup.norm_nonneg x.2]
  calc InterpolationCouple.KFunctional ι₀ ι₁ t a
      ≤ ‖x.1‖ + t * ‖x.2‖ := hb
    _ ≤ 2 * max 1 t * ‖x‖ := hc
    _ ≤ 2 * max 1 t * (‖a‖ + ε / (2 * max 1 t)) := by
        apply mul_le_mul_of_nonneg_left hxlt.le (by positivity)
    _ = 2 * max 1 t * ‖a‖ + ε := by field_simp

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `K`-functional subadditivity: `K(t,a+b) ≤ Ck·(K(t,a)+K(t,b))`, `Ck := max` of the two legs'
`quasiTriangleConst`s. Combine near-optimal representations of `a` and `b` separately into a
single representation of `a+b`, then bound via each leg's own quasi-triangle inequality. This is
the fact that lets `realInterpolationENorm_add_le` propagate a triangle-type bound through the
`(θ,q)` integral/supremum. -/
theorem InterpolationCouple.kFunctional_add_le (t : ℝ) (ht : 0 ≤ t)
    (a b : InterpolationCouple.sum ι₀ ι₁) :
    InterpolationCouple.KFunctional ι₀ ι₁ t (a + b) ≤
      max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
        (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) *
        (InterpolationCouple.KFunctional ι₀ ι₁ t a +
          InterpolationCouple.KFunctional ι₀ ι₁ t b) := by
  set Ck := max (QuasinormedAddCommGroup.quasiTriangleConst (E := A₀))
    (QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)) with hCkdef
  have hCk_pos : 0 < Ck := lt_of_lt_of_le zero_lt_one
    (le_max_of_le_left QuasinormedAddCommGroup.one_le_quasiTriangleConst)
  have h2Ck_pos : (0:ℝ) < 2 * Ck := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ra, ⟨a₀, a₁, ha, hraeq⟩, hralt⟩ := Real.lt_sInf_add_pos
    (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t a) (div_pos hε h2Ck_pos)
  obtain ⟨rb, ⟨b₀, b₁, hb, hrbeq⟩, hrblt⟩ := Real.lt_sInf_add_pos
    (InterpolationCouple.kFunctional_set_nonempty ι₀ ι₁ t b) (div_pos hε h2Ck_pos)
  subst hraeq
  subst hrbeq
  have hralt' : ‖a₀‖ + t * ‖a₁‖ <
      InterpolationCouple.KFunctional ι₀ ι₁ t a + ε / (2 * Ck) := hralt
  have hrblt' : ‖b₀‖ + t * ‖b₁‖ <
      InterpolationCouple.KFunctional ι₀ ι₁ t b + ε / (2 * Ck) := hrblt
  have hrep : (Submodule.Quotient.mk (a₀ + b₀, a₁ + b₁) : InterpolationCouple.sum ι₀ ι₁) =
      a + b := by
    rw [← ha, ← hb]; rfl
  have hbound : InterpolationCouple.KFunctional ι₀ ι₁ t (a + b) ≤
      ‖a₀ + b₀‖ + t * ‖a₁ + b₁‖ :=
    csInf_le (InterpolationCouple.kFunctional_set_boundedBelow ι₀ ι₁ t ht (a + b))
      ⟨a₀ + b₀, a₁ + b₁, hrep, rfl⟩
  have h0 : ‖a₀ + b₀‖ ≤ Ck * (‖a₀‖ + ‖b₀‖) :=
    (QuasinormedAddCommGroup.norm_add_le a₀ b₀).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg (QuasinormedAddCommGroup.norm_nonneg a₀)
          (QuasinormedAddCommGroup.norm_nonneg b₀)))
  have h1 : ‖a₁ + b₁‖ ≤ Ck * (‖a₁‖ + ‖b₁‖) :=
    (QuasinormedAddCommGroup.norm_add_le a₁ b₁).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg (QuasinormedAddCommGroup.norm_nonneg a₁)
          (QuasinormedAddCommGroup.norm_nonneg b₁)))
  have hcomb : ‖a₀ + b₀‖ + t * ‖a₁ + b₁‖ ≤
      Ck * ((‖a₀‖ + t * ‖a₁‖) + (‖b₀‖ + t * ‖b₁‖)) := by
    have := mul_le_mul_of_nonneg_left h1 ht
    nlinarith [h0]
  have hfin : Ck * ((‖a₀‖ + t * ‖a₁‖) + (‖b₀‖ + t * ‖b₁‖)) ≤
      Ck * (InterpolationCouple.KFunctional ι₀ ι₁ t a +
        InterpolationCouple.KFunctional ι₀ ι₁ t b) + ε := by
    have heps : ε / (2 * Ck) + ε / (2 * Ck) = ε / Ck := by
      field_simp
      ring
    have hsum : (‖a₀‖ + t * ‖a₁‖) + (‖b₀‖ + t * ‖b₁‖) ≤
        (InterpolationCouple.KFunctional ι₀ ι₁ t a +
          InterpolationCouple.KFunctional ι₀ ι₁ t b) + ε / Ck := by
      rw [← heps]; linarith [hralt', hrblt']
    calc Ck * ((‖a₀‖ + t * ‖a₁‖) + (‖b₀‖ + t * ‖b₁‖))
        ≤ Ck * ((InterpolationCouple.KFunctional ι₀ ι₁ t a +
            InterpolationCouple.KFunctional ι₀ ι₁ t b) + ε / Ck) :=
          mul_le_mul_of_nonneg_left hsum hCk_pos.le
      _ = Ck * (InterpolationCouple.KFunctional ι₀ ι₁ t a +
            InterpolationCouple.KFunctional ι₀ ι₁ t b) + ε := by field_simp
  calc InterpolationCouple.KFunctional ι₀ ι₁ t (a + b)
      ≤ ‖a₀ + b₀‖ + t * ‖a₁ + b₁‖ := hbound
    _ ≤ Ck * ((‖a₀‖ + t * ‖a₁‖) + (‖b₀‖ + t * ‖b₁‖)) := hcomb
    _ ≤ Ck * (InterpolationCouple.KFunctional ι₀ ι₁ t a +
          InterpolationCouple.KFunctional ι₀ ι₁ t b) + ε := hfin

/-- Triebel's Lemma (§1.3.1): `K(t,a)` is continuous in `t` (for `t ≥ 0`). STATEMENT ONLY —
proof deferred. -/
theorem InterpolationCouple.kFunctional_continuousOn (a : InterpolationCouple.sum ι₀ ι₁) :
    ContinuousOn (fun t => InterpolationCouple.KFunctional ι₀ ι₁ t a) (Set.Ici 0) := by
  sorry

/-- Triebel's Lemma (§1.3.1): `K(t,a)` is concave in `t` (for `t ≥ 0`). STATEMENT ONLY — proof
deferred (not needed for the `(A₀,A₁)_{θ,q}` Banach/type-θ theorem specifically; needed later
for reiteration / K-L-method equivalence). -/
theorem InterpolationCouple.kFunctional_concaveOn (a : InterpolationCouple.sum ι₀ ι₁) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t => InterpolationCouple.KFunctional ι₀ ι₁ t a) := by
  sorry

/-- The key transformation/naturality property used to show `(A₀,A₁)_{θ,q}` is an exact
interpolation functor of type `θ` (Triebel §1.3.3 proof, step 4): a morphism `T : C ⟶ D` scales
the K-functional by bounds on its operator quasi-norms on each leg.

Stated with arbitrary upper bounds `M₀, M₁` on `opQuasiNorm T.f₀`/`opQuasiNorm T.f₁` (rather than
the exact quasi-norms themselves) precisely to sidestep the `opQuasiNorm T.f₀ = 0` edge case
flagged when this was statement-only: with the exact quasi-norm plugged in, `t * ‖T.f₁‖ / 0`
evaluates to `0` under Lean's `x / 0 = 0` convention, making the RHS `0` and the claimed
inequality false whenever `T.f₀ = 0` and `T.sumMap a ≠ 0`. The proof below only ever uses
`‖T.f₀ a₀‖ ≤ M₀ * ‖a₀‖`/`‖T.f₁ a₁‖ ≤ M₁ * ‖a₁‖`, never that `M₀, M₁` are the *tightest* such
bounds, so this version is strictly more general (recovers the exact-quasi-norm statement by
taking `M₀ := opQuasiNorm T.f₀` whenever that is positive) and avoids the degenerate case by
letting the caller pick `M₀ > 0` freely (e.g. `M₀ := 1` when `T.f₀ = 0`). Signed off by Ryan.

Uses `QuasinormedAddCommGroup.opQuasiNorm` rather than Mathlib's own operator norm, which needs
genuine `SeminormedAddCommGroup` on both ends and so isn't available for merely-quasi-normed legs
(`QuasiNorm.lean`). -/
theorem InterpolationCat.Hom.kFunctional_sumMap_le {C D : InterpolationCat 𝕜}
    (T : InterpolationCat.Hom C D) (t : ℝ) (ht : 0 ≤ t)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm T.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm T.f₁ ≤ M₁)
    (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
      M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a := by
  set s := t * M₁ / M₀ with hs
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, ⟨a₀, a₁, ha, hreq⟩, hrlt⟩ := Real.lt_sInf_add_pos
    (InterpolationCouple.kFunctional_set_nonempty C.ι₀ C.ι₁ s a) (div_pos hε hM₀)
  subst hreq
  have hrlt' : ‖a₀‖ + s * ‖a₁‖ <
      InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a + ε / M₀ := hrlt
  have hb : InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (T.sumMap a) ≤
      ‖T.f₀ a₀‖ + t * ‖T.f₁ a₁‖ := by
    refine csInf_le (InterpolationCouple.kFunctional_set_boundedBelow D.ι₀ D.ι₁ t ht (T.sumMap a))
      ⟨T.f₀ a₀, T.f₁ a₁, ?_, rfl⟩
    rw [← ha, InterpolationCat.Hom.sumMap_mk]
  have h0 : ‖T.f₀ a₀‖ ≤ M₀ * ‖a₀‖ :=
    (QuasinormedAddCommGroup.le_opQuasiNorm T.f₀ a₀).trans
      (mul_le_mul_of_nonneg_right h₀ (QuasinormedAddCommGroup.norm_nonneg a₀))
  have h1 : ‖T.f₁ a₁‖ ≤ M₁ * ‖a₁‖ :=
    (QuasinormedAddCommGroup.le_opQuasiNorm T.f₁ a₁).trans
      (mul_le_mul_of_nonneg_right h₁ (QuasinormedAddCommGroup.norm_nonneg a₁))
  have hcomb : ‖T.f₀ a₀‖ + t * ‖T.f₁ a₁‖ ≤ M₀ * ‖a₀‖ + t * (M₁ * ‖a₁‖) := by
    have := mul_le_mul_of_nonneg_left h1 ht
    linarith
  have heq : M₀ * ‖a₀‖ + t * (M₁ * ‖a₁‖) = M₀ * (‖a₀‖ + s * ‖a₁‖) := by
    rw [hs]; field_simp
  rw [heq] at hcomb
  have hfin : M₀ * (‖a₀‖ + s * ‖a₁‖) <
      M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a + ε := by
    have hmul := mul_lt_mul_of_pos_left hrlt' hM₀
    calc M₀ * (‖a₀‖ + s * ‖a₁‖)
        < M₀ * (InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a + ε / M₀) := hmul
      _ = M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ s a + ε := by field_simp
  linarith [hb, hcomb, hfin]

/-- Unit 5's promised "transport" payoff: a couple-level quasi-norm equivalence (a `Iso` `e : C ≅
D` in `InterpolationCat 𝕜`) bounds `K` in *both* directions, by applying `kFunctional_sumMap_le`
to `e.hom` and separately to `e.inv`. No new "equivalence" structure is needed for this: an `Iso`
already gives `e.inv.sumMap (e.hom.sumMap a) = a` for free, via `Hom.sumMap`'s already-proved
functoriality (`sumMap_id`/`sumMap_comp`, `TrivialFunctors.lean`). STATEMENT ONLY — proof
deferred. -/
theorem InterpolationCat.Hom.kFunctional_iso_le {C D : InterpolationCat 𝕜} (e : C ≅ D)
    (M₀ M₁ N₀ N₁ : ℝ) (hM₀ : 0 < M₀) (hN₀ : 0 < N₀)
    (h₀ : QuasinormedAddCommGroup.opQuasiNorm e.hom.f₀ ≤ M₀)
    (h₁ : QuasinormedAddCommGroup.opQuasiNorm e.hom.f₁ ≤ M₁)
    (g₀ : QuasinormedAddCommGroup.opQuasiNorm e.inv.f₀ ≤ N₀)
    (g₁ : QuasinormedAddCommGroup.opQuasiNorm e.inv.f₁ ≤ N₁)
    (t : ℝ) (ht : 0 ≤ t) (a : InterpolationCouple.sum C.ι₀ C.ι₁) :
    InterpolationCouple.KFunctional D.ι₀ D.ι₁ t (e.hom.sumMap a) ≤
      M₀ * InterpolationCouple.KFunctional C.ι₀ C.ι₁ (t * M₁ / M₀) a ∧
    InterpolationCouple.KFunctional C.ι₀ C.ι₁ t a ≤
      N₀ * InterpolationCouple.KFunctional D.ι₀ D.ι₁ (t * N₁ / N₀) (e.hom.sumMap a) := by
  have hcomp := congrArg InterpolationCat.Hom.sumMap e.hom_inv_id
  rw [InterpolationCat.Hom.sumMap_comp, InterpolationCat.Hom.sumMap_id] at hcomp
  have hinv : e.inv.sumMap (e.hom.sumMap a) = a := by
    have := DFunLike.congr_fun hcomp a
    simpa using this
  refine ⟨InterpolationCat.Hom.kFunctional_sumMap_le e.hom t ht M₀ M₁ hM₀ h₀ h₁ a, ?_⟩
  have hstep := InterpolationCat.Hom.kFunctional_sumMap_le e.inv t ht N₀ N₁ hN₀ g₀ g₁
    (e.hom.sumMap a)
  rwa [hinv] at hstep
