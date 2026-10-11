/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Interpolation.RealInterpolation.JMethod.JFunctional
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Interval

/-!
# The fundamental lemma of interpolation theory

For an interpolation couple `{A₀, A₁}` and `a ∈ A₀ + A₁` with `K(t,a) → 0` as `t → 0⁺` and
`K(t,a)/t → 0` as `t → ∞`, there is a family `u : ℤ → A₀ ∩ A₁` with `a = ∑ᵥ uᵥ` and
`J(2^ν, uᵥ) ≤ γ K(2^ν, a)` for every `ν` (Bergh–Löfström Lemma 3.3.2, with the quasi-normed
constant of their §3.11.3). This is the bridge from the K-method to the J-method: it is the
`K ⊂ J` half of the equivalence theorem. (Triebel has no counterpart: his equivalence theorem
§1.6.1 goes through the integral-based mean methods of §1.5, which need Banach spaces.)

The proof follows Bergh–Löfström's: pick near-optimal decompositions `a = a₀(ν) + a₁(ν)` for
`K(2^ν, a)` and set `uᵥ = a₀(ν) - a₀(ν-1) = a₁(ν-1) - a₁(ν)`, which telescopes.
For quasi-Banach couples the constant picks up the quasi-triangle constants of `A₀`, `A₁`:
`γ = 3 (1 + ε) C` with `C = max C₀ C₁`, recovering Bergh–Löfström's `3 (1 + ε)` for Banach
couples. The argument is purely additive (no scalar multiplication).

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
          KFunctional ι₀ ι₁ (2 ^ ν) a := by
  set C₀ := QuasinormedAddCommGroup.quasiTriangleConst (E := A₀)
  set C₁ := QuasinormedAddCommGroup.quasiTriangleConst (E := A₁)
  have hK (t : ℝ) (ht : 0 ≤ t) : 0 ≤ KFunctional ι₀ ι₁ t a := kFunctional_nonneg ι₀ ι₁ t ht a
  -- B–L (1): for every `ν` there is a decomposition `a = a₀,ᵥ + a₁,ᵥ` with
  -- `‖a₀,ᵥ‖ + 2^ν ‖a₁,ᵥ‖ ≤ (1 + ε) K(2^ν, a)`.
  have hdec (ν : ℤ) : ∃ x : A₀ × A₁, (Submodule.Quotient.mk x : sum ι₀ ι₁) = a ∧
      (‖x.1‖ + 2 ^ ν * ‖x.2‖ : ℝ) ≤ (1 + ε) * KFunctional ι₀ ι₁ (2 ^ ν) a := by
    have h2ν : (0 : ℝ) < 2 ^ ν := zpow_pos two_pos ν
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, rfl, by simpa using mul_nonneg (by linarith) (hK _ h2ν.le)⟩
    have hpos : 0 < KFunctional ι₀ ι₁ (2 ^ ν) a :=
      (mul_pos (lt_min one_pos h2ν) (lt_of_le_of_ne
        (QuasinormedAddCommGroup.norm_nonneg a)
        (Ne.symm ((QuasinormedAddCommGroup.norm_eq_zero_iff a).not.mpr ha)))).trans_le
        (min_mul_norm_le_kFunctional ι₀ ι₁ _ h2ν.le a)
    obtain ⟨r, ⟨a₀, a₁, hmk, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
      (kFunctional_set_nonempty ι₀ ι₁ (2 ^ ν) a)
      (show KFunctional ι₀ ι₁ (2 ^ ν) a < (1 + ε) * KFunctional ι₀ ι₁ (2 ^ ν) a by nlinarith)
    exact ⟨(a₀, a₁), hmk, hr.le⟩
  choose x hxa hxK using hdec
  have hx₀ (ν : ℤ) : ‖(x ν).1‖ ≤ (1 + ε) * KFunctional ι₀ ι₁ (2 ^ ν) a := by
    nlinarith [hxK ν, QuasinormedAddCommGroup.norm_nonneg (x ν).2,
      zpow_pos (two_pos (α := ℝ)) ν]
  have hx₁ (ν : ℤ) : 2 ^ ν * ‖(x ν).2‖ ≤ (1 + ε) * KFunctional ι₀ ι₁ (2 ^ ν) a := by
    nlinarith [hxK ν, QuasinormedAddCommGroup.norm_nonneg (x ν).1]
  -- B–L: thus `‖a₀,ᵥ‖ → 0` as `ν → -∞` and `‖a₁,ᵥ‖ → 0` as `ν → +∞` (along the integers
  -- needed below).
  have hlim₀ : Tendsto (fun N : ℕ => ‖(x (-(N : ℤ) - 1)).1‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ) - 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr
        ⟨?_, .of_forall fun N => Set.mem_Ioi.mpr (zpow_pos two_pos _)⟩
      have : (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ) - 1)) =
          fun N : ℕ => (1 / 2) * (1 / 2 : ℝ) ^ N := by
        funext N
        rw [zpow_sub₀ two_ne_zero, zpow_neg, zpow_natCast, zpow_one, one_div_pow]
        field_simp
      rw [this]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (1 / 2 : ℝ)
    have hK0 := (h0.comp h2).const_mul (1 + ε)
    rw [mul_zero] at hK0
    exact squeeze_zero (fun _ => QuasinormedAddCommGroup.norm_nonneg _) (fun N => hx₀ _) hK0
  have hlim₁ : Tendsto (fun N : ℕ => ‖(x N).2‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (2 : ℝ) ^ (N : ℤ)) atTop atTop := by
      simpa using tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))
    have hK0 := (hT.comp h2).const_mul (1 + ε)
    rw [mul_zero] at hK0
    refine squeeze_zero (fun _ => QuasinormedAddCommGroup.norm_nonneg _) (fun N => ?_) hK0
    have hp : (0 : ℝ) < 2 ^ (N : ℤ) := zpow_pos two_pos _
    rw [Function.comp_apply, mul_div_assoc', le_div_iff₀ hp, mul_comm]
    exact hx₁ N
  -- B–L: write `uᵥ = a₀,ᵥ - a₀,ᵥ₋₁ = a₁,ᵥ₋₁ - a₁,ᵥ`. Then `uᵥ ∈ Δ(A) = A₀ ∩ A₁`.
  have hmem (ν : ℤ) :
      ((x ν).1 - (x (ν - 1)).1, (x (ν - 1)).2 - (x ν).2) ∈ meet ι₀ ι₁ := by
    have h : ((x ν).1 - (x (ν - 1)).1, (x ν).2 - (x (ν - 1)).2) ∈ (plus ι₀ ι₁).ker :=
      (Submodule.Quotient.eq _).mp ((hxa ν).trans (hxa (ν - 1)).symm)
    rw [mem_ker_plus_iff] at h
    rw [mem_meet_iff, h, map_sub, map_sub, neg_sub]
  refine ⟨fun ν => ⟨_, hmem ν⟩, ?_, fun ν => ?_⟩
  · -- B–L: `a - ∑_{-N}^{N} uᵥ = a₀,₋ₙ₋₁ + a₁,ₙ`, so
    -- `K(1, a - ∑_{-N}^{N} uᵥ) ≤ ‖a₀,₋ₙ₋₁‖ + ‖a₁,ₙ‖ → 0`.
    have htel (N : ℕ) : a - ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, meetToSum ι₀ ι₁ ⟨_, hmem ν⟩ =
        Submodule.Quotient.mk ((x (-(N : ℤ) - 1)).1, (x N).2) := by
      have hsum : ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, ((x ν).1 - (x (ν - 1)).1) =
          (x N).1 - (x (-(N : ℤ) - 1)).1 := by
        rw [Finset.sum_nbij' (fun ν : ℤ => (ν + N).toNat) (fun k : ℕ => (k : ℤ) - N)
            (t := Finset.range (2 * N + 1))
            (g := fun k : ℕ => (x ((k + 1 : ℕ) - N - 1)).1 - (x ((k : ℤ) - N - 1)).1)
            (by intro ν hν; rw [Finset.mem_Icc] at hν; rw [Finset.mem_range]; omega)
            (by intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega)
            (by intro ν hν; rw [Finset.mem_Icc] at hν; omega)
            (by intro k hk; omega)
            (by intro ν hν; simp only [Finset.mem_Icc] at hν
                congr 3 <;> push_cast <;> omega),
          Finset.sum_range_sub (fun k : ℕ => (x ((k : ℤ) - N - 1)).1)]
        congr 3 <;> push_cast <;> ring
      have hmeet : ∀ ν, meetToSum ι₀ ι₁ ⟨_, hmem ν⟩ = inl₀ ι₀ ι₁ ((x ν).1 - (x (ν - 1)).1) :=
        fun _ => rfl
      rw [Finset.sum_congr rfl fun ν _ => hmeet ν, ← map_sum, hsum, ← hxa N]
      change (plus ι₀ ι₁ : (A₀ × A₁) →ₗ[𝕜] 𝒜).ker.mkQ (x N) -
          (plus ι₀ ι₁ : (A₀ × A₁) →ₗ[𝕜] 𝒜).ker.mkQ ((x N).1 - (x (-(N : ℤ) - 1)).1, 0) =
        (plus ι₀ ι₁ : (A₀ × A₁) →ₗ[𝕜] 𝒜).ker.mkQ ((x (-(N : ℤ) - 1)).1, (x N).2)
      rw [← map_sub]
      congr 1
      ext <;> simp
    rw [QuasinormedAddCommGroup.tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => QuasinormedAddCommGroup.norm_nonneg _) (fun N => ?_)
      (by simpa using hlim₀.add hlim₁)
    rw [← QuasinormedAddCommGroup.norm_neg, neg_sub, htel]
    -- `‖b‖ ≤ K(1, b)` and `K(1, [(a₀, a₁)]) ≤ ‖a₀‖ + ‖a₁‖`
    refine le_trans ?_ ((min_mul_norm_le_kFunctional ι₀ ι₁ 1 zero_le_one _).trans
      ((csInf_le (kFunctional_set_boundedBelow ι₀ ι₁ 1 zero_le_one _)
        ⟨_, _, rfl, rfl⟩).trans_eq (by rw [one_mul])))
    rw [min_self, one_mul]
  · -- B–L, by (1): `J(2^ν, uᵥ) ≤ C max(‖a₀,ᵥ‖ + ‖a₀,ᵥ₋₁‖, 2^ν (‖a₁,ᵥ₋₁‖ + ‖a₁,ᵥ‖))`
    -- `≤ 3 (1 + ε) C K(2^ν, a)`, using `K(2^{ν-1}, a) ≤ K(2^ν, a)`.
    set F := (1 + ε) * KFunctional ι₀ ι₁ (2 ^ ν) a
    have hF : 0 ≤ F := mul_nonneg (by linarith) (hK _ (zpow_pos two_pos ν).le)
    have hFν : (1 + ε) * KFunctional ι₀ ι₁ (2 ^ (ν - 1)) a ≤ F :=
      mul_le_mul_of_nonneg_left (kFunctional_mono ι₀ ι₁ (zpow_pos two_pos _).le
        (zpow_le_zpow_right₀ one_le_two (by omega)) a) (by linarith)
    have h2 : (2 : ℝ) ^ ν = 2 * 2 ^ (ν - 1) := by
      rw [zpow_sub_one₀ two_ne_zero]
      ring
    have hC : 0 ≤ max C₀ C₁ := QuasinormedAddCommGroup.quasiTriangleConst_pos.le.trans
      (le_max_left _ _)
    rw [show 3 * (1 + ε) * max C₀ C₁ * KFunctional ι₀ ι₁ (2 ^ ν) a = 3 * max C₀ C₁ * F by ring]
    refine max_le ?_ ?_
    · have h : ‖(x ν).1 - (x (ν - 1)).1‖ ≤ C₀ * (‖(x ν).1‖ + ‖(x (ν - 1)).1‖) := by
        simpa [sub_eq_add_neg, QuasinormedAddCommGroup.norm_neg] using
          QuasinormedAddCommGroup.norm_add_le (x ν).1 (-(x (ν - 1)).1)
      have h1 := hx₀ (ν - 1)
      have hC₀ : C₀ ≤ max C₀ C₁ := le_max_left _ _
      nlinarith [hx₀ ν, QuasinormedAddCommGroup.norm_nonneg (x ν).1,
        QuasinormedAddCommGroup.norm_nonneg (x (ν - 1)).1]
    · have h : ‖(x (ν - 1)).2 - (x ν).2‖ ≤ C₁ * (‖(x (ν - 1)).2‖ + ‖(x ν).2‖) := by
        simpa [sub_eq_add_neg, QuasinormedAddCommGroup.norm_neg] using
          QuasinormedAddCommGroup.norm_add_le (x (ν - 1)).2 (-(x ν).2)
      have h1 := hx₁ (ν - 1)
      have hC₁ : C₁ ≤ max C₀ C₁ := le_max_right _ _
      have hC₁0 : 0 ≤ C₁ := QuasinormedAddCommGroup.quasiTriangleConst_pos.le
      change 2 ^ ν * ‖(x (ν - 1)).2 - (x ν).2‖ ≤ _
      calc 2 ^ ν * ‖(x (ν - 1)).2 - (x ν).2‖
          ≤ 2 ^ ν * (C₁ * (‖(x (ν - 1)).2‖ + ‖(x ν).2‖)) :=
            mul_le_mul_of_nonneg_left h (zpow_pos two_pos ν).le
        _ = C₁ * (2 * (2 ^ (ν - 1) * ‖(x (ν - 1)).2‖) + 2 ^ ν * ‖(x ν).2‖ : ℝ) := by
            rw [h2]
            ring
        _ ≤ C₁ * (2 * F + F) :=
            mul_le_mul_of_nonneg_left (add_le_add
              (mul_le_mul_of_nonneg_left (h1.trans hFν) zero_le_two) (hx₁ ν)) hC₁0
        _ ≤ 3 * max C₀ C₁ * F := by nlinarith

end InterpolationCouple
