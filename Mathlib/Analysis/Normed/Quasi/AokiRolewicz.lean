/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Quasi.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The Aoki–Rolewicz theorem

DRAFT — statements only.

Let `E` be a quasi-normed group with quasi-triangle constant `C ≥ 1`, i.e.
`‖x + y‖ ≤ C (‖x‖ + ‖y‖)`. Put `ρ = 1 / (1 + log₂ C) ∈ (0, 1]`, so that `C = 2^{1/ρ - 1}`
(`aokiRolewiczExponent`). The **Aoki–Rolewicz theorem** says that `E` carries an equivalent
`ρ`-norm: a function `N` with `N(x + y)^ρ ≤ N(x)^ρ + N(y)^ρ` and `N ≤ ‖·‖ ≤ 4^{1/ρ} N`. We take
`N(x) = inf (∑ ‖xᵢ‖^ρ)^{1/ρ}` over finite decompositions `x = ∑ xᵢ` (`aokiRolewiczNorm`).

The analytic content is the finite-sum bound `‖∑ xᵢ‖ ≤ 4^{1/ρ} (∑ ‖xᵢ‖^ρ)^{1/ρ}`
(`norm_sum_le_rpow`, Kalton–Peck–Roberts, *An F-space sampler*, Theorem 1.3). The `ρ`-norm
properties follow from it formally. As a consequence, the same bound holds for `‖∑' xᵢ‖` whenever
`∑ ‖xᵢ‖^ρ < ∞` (`norm_tsum_le_rpow`), and in a complete quasi-normed group such a family is
summable (`summable_of_summable_norm_rpow`). A quasi-norm need not be continuous, so
the bound on `‖∑' xᵢ‖` goes through the `ρ`-norm, whose `ρ`-th power is subadditive.

This is what makes the discrete J-method of real interpolation work for quasi-Banach couples
(Bergh–Löfström, *Interpolation Spaces*, Lemma 3.10.1 and §3.11).

## Main definitions
* `QuasinormedAddCommGroup.aokiRolewiczExponent E`: `ρ = 1 / (1 + log₂ C)`.
* `QuasinormedAddCommGroup.aokiRolewiczNorm`: the equivalent `ρ`-norm.

## Main results
* `QuasinormedAddCommGroup.norm_sum_le_rpow`: the finite-sum bound.
* `QuasinormedAddCommGroup.aokiRolewiczNorm_add_rpow_le`, `aokiRolewiczNorm_le_norm`,
  `norm_le_aokiRolewiczNorm`: the `ρ`-norm and its equivalence with `‖·‖`.
* `QuasinormedAddCommGroup.summable_of_summable_norm_rpow`, `norm_tsum_le_rpow`: series.
-/

namespace QuasinormedAddCommGroup

variable (E : Type*) [QuasinormedAddCommGroup E]

/-- The Aoki–Rolewicz exponent `ρ = 1 / (1 + log₂ C)` of a quasi-normed group with
quasi-triangle constant `C`. It satisfies `0 < ρ ≤ 1` and `C = 2^{1/ρ - 1}`. -/
noncomputable def aokiRolewiczExponent : ℝ :=
  (1 + Real.logb 2 (quasiTriangleConst (E := E)))⁻¹

theorem one_le_inv_aokiRolewiczExponent : 1 ≤ (aokiRolewiczExponent E)⁻¹ := by
  rw [aokiRolewiczExponent, inv_inv, le_add_iff_nonneg_right]
  exact Real.logb_nonneg one_lt_two one_le_quasiTriangleConst

theorem aokiRolewiczExponent_pos : 0 < aokiRolewiczExponent E :=
  inv_pos.mp (one_pos.trans_le (one_le_inv_aokiRolewiczExponent E))

theorem aokiRolewiczExponent_le_one : aokiRolewiczExponent E ≤ 1 := by
  simpa using inv_le_one_of_one_le₀ (one_le_inv_aokiRolewiczExponent E)

theorem quasiTriangleConst_eq_two_rpow :
    quasiTriangleConst (E := E) = (2 : ℝ) ^ ((aokiRolewiczExponent E)⁻¹ - 1) := by
  rw [aokiRolewiczExponent, inv_inv, add_sub_cancel_left,
    Real.rpow_logb two_pos (by norm_num) quasiTriangleConst_pos]

variable {E}

/-- Dyadic weights `2^{-kᵢ}` with all `kᵢ ≤ n` that sum to at most `1 - 2^{-(n+1)}` in fact sum
to at most `1 - 2^{-n}`, since their sum is a multiple of `2^{-n}`. -/
private theorem sum_inv_two_pow_add_inv_le {ι : Type*} (t : Finset ι) (k : ι → ℕ) (n : ℕ)
    (hk : ∀ i ∈ t, k i ≤ n)
    (h : ∑ i ∈ t, ((2 : ℝ) ^ k i)⁻¹ + ((2 : ℝ) ^ (n + 1))⁻¹ ≤ 1) :
    ∑ i ∈ t, ((2 : ℝ) ^ k i)⁻¹ + ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
  set N : ℕ := ∑ i ∈ t, 2 ^ (n - k i)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hN : ∑ i ∈ t, ((2 : ℝ) ^ k i)⁻¹ = N / 2 ^ n := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ two_ne_zero (hk i hi)]
    field_simp
  rw [hN] at h ⊢
  have hlt : (N : ℝ) < 2 ^ n := by
    rw [pow_succ] at h
    field_simp at h
    linarith
  have : N + 1 ≤ 2 ^ n := by exact_mod_cast hlt
  rw [show (N : ℝ) / 2 ^ n + (2 ^ n)⁻¹ = (N + 1) / 2 ^ n by ring, div_le_one h2]
  exact_mod_cast this

/-- A dyadic form of the quasi-triangle inequality: if `∑ 2^{-kᵢ} ≤ 1` and
`(2C)^{kᵢ} ‖xᵢ‖ ≤ M` for all `i`, then `‖∑ xᵢ‖ ≤ M`. -/
theorem norm_sum_le_of_sum_inv_two_pow_le {ι : Type*} (s : Finset ι) (x : ι → E) (k : ι → ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hk : ∑ i ∈ s, ((2 : ℝ) ^ k i)⁻¹ ≤ 1)
    (hx : ∀ i ∈ s, (2 * quasiTriangleConst (E := E)) ^ k i * ‖x i‖ ≤ M) :
    ‖∑ i ∈ s, x i‖ ≤ M := by
  classical
  have hK1 : 1 ≤ 2 * quasiTriangleConst (E := E) := by
    linarith [one_le_quasiTriangleConst (E := E)]
  induction h : s.card + ∑ i ∈ s, k i using Nat.strong_induction_on generalizing s x k with
  | _ n ih => ?_
  rcases Nat.lt_or_ge s.card 2 with hs | hs
  · obtain h0 | h1 : s.card = 0 ∨ s.card = 1 := by omega
    · simp [Finset.card_eq_zero.mp h0, hM]
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_singleton]
      calc ‖x a‖ = 1 * ‖x a‖ := (one_mul _).symm
        _ ≤ (2 * quasiTriangleConst (E := E)) ^ k a * ‖x a‖ :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hK1) (norm_nonneg _)
        _ ≤ M := hx a (Finset.mem_singleton_self a)
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image k (Finset.card_pos.mp (by omega))
  obtain ⟨m, hm⟩ : ∃ m, k i₀ = m + 1 := by
    refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun hm0 => ?_)
    have h0 : ∀ i ∈ s, k i = 0 := fun i hi => by have := hmax i hi; omega
    have hsum : ∑ i ∈ s, ((2 : ℝ) ^ k i)⁻¹ = s.card := by
      rw [Finset.sum_congr rfl fun i hi => by rw [h0 i hi]]; simp
    have : (2 : ℝ) ≤ s.card := by exact_mod_cast hs
    linarith
  obtain ⟨k', hk'd⟩ : ∃ k', k' = Function.update k i₀ m := ⟨_, rfl⟩
  by_cases hA : ∃ j ∈ s, j ≠ i₀ ∧ k j = m + 1
  · -- merge `x i₀` and `x j` into a single term at level `m`
    obtain ⟨j, hj, hji, hkj⟩ := hA
    have hi₀' : i₀ ∈ s.erase j := Finset.mem_erase.mpr ⟨hji.symm, hi₀⟩
    set x' := Function.update x i₀ (x i₀ + x j)
    have hrest {f g : ι → ℝ} (hfg : ∀ i ∈ (s.erase j).erase i₀, f i = g i) :
        ∑ i ∈ (s.erase j).erase i₀, f i = ∑ i ∈ (s.erase j).erase i₀, g i :=
      Finset.sum_congr rfl hfg
    have hne {i} (hi : i ∈ (s.erase j).erase i₀) : i ≠ i₀ := Finset.ne_of_mem_erase hi
    have hx' : ∑ i ∈ s.erase j, x' i = ∑ i ∈ s, x i := by
      rw [← Finset.add_sum_erase _ _ hi₀', ← Finset.add_sum_erase _ _ hj,
        ← Finset.add_sum_erase _ _ hi₀',
        Finset.sum_congr rfl fun i hi => Function.update_of_ne (hne hi) _ x]
      simp only [x', Function.update_self]
      abel
    have hk' : ∑ i ∈ s.erase j, ((2 : ℝ) ^ k' i)⁻¹ = ∑ i ∈ s, ((2 : ℝ) ^ k i)⁻¹ := by
      rw [← Finset.add_sum_erase _ _ hi₀', ← Finset.add_sum_erase _ _ hj,
        ← Finset.add_sum_erase _ _ hi₀',
        hrest fun i hi => by rw [hk'd, Function.update_of_ne (hne hi)]]
      simp only [hk'd, Function.update_self, hkj, hm, pow_succ]
      ring
    have hcard : (s.erase j).card + ∑ i ∈ s.erase j, k' i < n := by
      rw [← h, Finset.card_erase_of_mem hj, ← Finset.add_sum_erase _ _ hi₀',
        ← Finset.add_sum_erase _ _ hj, ← Finset.add_sum_erase _ _ hi₀',
        hk'd, Finset.sum_congr rfl fun i hi => Function.update_of_ne (hne hi) _ k]
      simp only [Function.update_self, hkj, hm]
      generalize ((s.erase j).erase i₀).sum k = R at *
      omega
    rw [← hx']
    refine ih _ hcard (s.erase j) x' k' (hk'.le.trans hk) (fun i hi => ?_) rfl
    by_cases hii : i = i₀
    · subst hii
      simp only [hk'd, x', Function.update_self]
      have h₀ := hx i hi₀
      have h₁ := hx j hj
      rw [hm] at h₀
      rw [hkj] at h₁
      rw [pow_succ] at h₀ h₁
      calc (2 * quasiTriangleConst (E := E)) ^ m * ‖x i + x j‖
          ≤ (2 * quasiTriangleConst (E := E)) ^ m *
              (quasiTriangleConst (E := E) * (‖x i‖ + ‖x j‖)) := by
            gcongr; exact norm_add_le _ _
        _ ≤ M := by
            have hC := quasiTriangleConst_pos (E := E)
            have hp : 0 ≤ (2 * quasiTriangleConst (E := E)) ^ m := by positivity
            rcases le_total ‖x i‖ ‖x j‖ with hle | hle
            · nlinarith [norm_nonneg (x i), mul_le_mul_of_nonneg_left hle (mul_nonneg hp hC.le)]
            · nlinarith [norm_nonneg (x j), mul_le_mul_of_nonneg_left hle (mul_nonneg hp hC.le)]
    · simp only [hk'd, x', Function.update_of_ne hii]
      exact hx i (Finset.mem_of_mem_erase hi)
  · -- lower `k i₀` by one; the dyadic weights still sum to at most `1`
    push Not at hA
    have hk' : ∑ i ∈ s, ((2 : ℝ) ^ k' i)⁻¹ ≤ 1 := by
      subst hk'd
      rw [← Finset.add_sum_erase _ _ hi₀, Function.update_self,
        Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      rw [← Finset.add_sum_erase _ _ hi₀, hm] at hk
      rw [add_comm] at hk ⊢
      refine sum_inv_two_pow_add_inv_le _ _ _ (fun i hi => ?_) hk
      have h1 := hmax i (Finset.mem_of_mem_erase hi)
      have h2 := hA i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      omega
    have hcard : s.card + ∑ i ∈ s, k' i < n := by
      rw [← h, ← Finset.add_sum_erase _ _ hi₀, ← Finset.add_sum_erase s k hi₀, hk'd,
        Finset.sum_congr rfl fun i hi =>
          Function.update_of_ne (Finset.ne_of_mem_erase hi) _ k]
      simp only [Function.update_self, hm]
      generalize (s.erase i₀).sum k = R at *
      omega
    refine ih _ hcard s x k' hk' (fun i hi => ?_) rfl
    by_cases hii : i = i₀
    · subst hii
      simp only [hk'd, Function.update_self]
      have h₀ := hx i hi
      rw [hm, pow_succ] at h₀
      have hp : 0 ≤ (2 * quasiTriangleConst (E := E)) ^ m := by positivity
      nlinarith [norm_nonneg (x i),
        mul_le_mul_of_nonneg_left hK1 (mul_nonneg hp (norm_nonneg (x i)))]
    · simp only [hk'd, Function.update_of_ne hii]
      exact hx i hi

/-- **Aoki–Rolewicz**, finite-sum form: `‖∑ xᵢ‖ ≤ 4^{1/ρ} (∑ ‖xᵢ‖^ρ)^{1/ρ}`. -/
theorem norm_sum_le_rpow {ι : Type*} (s : Finset ι) (x : ι → E) :
    ‖∑ i ∈ s, x i‖ ≤ (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ *
      (∑ i ∈ s, ‖x i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ := by
  classical
  set ρ := aokiRolewiczExponent E
  have hρ : 0 < ρ := aokiRolewiczExponent_pos E
  set S := ∑ i ∈ s, ‖x i‖ ^ ρ
  have hp {i} : 0 ≤ ‖x i‖ ^ ρ := Real.rpow_nonneg (norm_nonneg _) _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hp
  -- we prove the sharper bound with `2^{1/ρ}` in place of `4^{1/ρ}`
  refine le_trans ?_ (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by norm_num) (by norm_num : (2 : ℝ) ≤ 4) (inv_pos.mpr hρ).le)
    (by positivity))
  have hnorm_pos {i} (hi : x i ≠ 0) : 0 < ‖x i‖ :=
    (norm_nonneg _).lt_of_ne (Ne.symm fun h => hi ((norm_eq_zero_iff _).mp h))
  rw [← Finset.sum_filter_ne_zero]
  rcases hS0.eq_or_lt with hS | hS
  · have hx0 : ∀ i ∈ s, x i = 0 := fun i hi => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp)).mp hS.symm i hi
      exact (norm_eq_zero_iff _).mp ((Real.rpow_eq_zero (norm_nonneg _) hρ.ne').mp this)
    rw [Finset.filter_false_of_mem fun i hi => not_not.mpr (hx0 i hi), Finset.sum_empty,
      norm_zero]
    positivity
  have hex : ∀ i, i ∈ s ∧ x i ≠ 0 →
      ∃ n : ℕ, (2 : ℝ) ^ n ≤ S / ‖x i‖ ^ ρ ∧ S / ‖x i‖ ^ ρ < 2 ^ (n + 1) := by
    rintro i ⟨his, hi⟩
    refine exists_nat_pow_near ?_ one_lt_two
    rw [le_div_iff₀ (Real.rpow_pos_of_pos (hnorm_pos hi) ρ), one_mul]
    exact Finset.single_le_sum (f := fun j => ‖x j‖ ^ ρ) (fun j _ => hp) his
  choose! n hn using hex
  refine norm_sum_le_of_sum_inv_two_pow_le _ _ (fun i => n i + 1) (by positivity) ?_ ?_
  · calc ∑ i ∈ s with x i ≠ 0, ((2 : ℝ) ^ (n i + 1))⁻¹
        ≤ ∑ i ∈ s with x i ≠ 0, ‖x i‖ ^ ρ / S := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_filter.mp hi
          have ha := Real.rpow_pos_of_pos (hnorm_pos hi'.2) ρ
          rw [inv_le_comm₀ (by positivity) (div_pos ha hS), inv_div]
          exact (hn i hi').2.le
      _ ≤ ∑ i ∈ s, ‖x i‖ ^ ρ / S :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => div_nonneg hp hS.le
      _ = 1 := by rw [← Finset.sum_div, div_self hS.ne']
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    have ha := hnorm_pos hi'.2
    have h2C : 2 * quasiTriangleConst (E := E) = (2 : ℝ) ^ ρ⁻¹ := by
      rw [quasiTriangleConst_eq_two_rpow, Real.rpow_sub two_pos, Real.rpow_one]
      ring
    have hpow : (2 : ℝ) ^ (n i + 1) ≤ 2 * (S / ‖x i‖ ^ ρ) := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_left (hn i hi').1 zero_le_two
    rw [h2C, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, mul_comm ρ⁻¹,
      Real.rpow_mul two_pos.le, Real.rpow_natCast]
    calc ((2 : ℝ) ^ (n i + 1)) ^ ρ⁻¹ * ‖x i‖
        ≤ (2 * (S / ‖x i‖ ^ ρ)) ^ ρ⁻¹ * ‖x i‖ := by gcongr
      _ = 2 ^ ρ⁻¹ * S ^ ρ⁻¹ := by
          rw [Real.mul_rpow zero_le_two (by positivity), Real.div_rpow hS0 (by positivity),
            Real.rpow_rpow_inv (norm_nonneg _) hρ.ne']
          field_simp

/-- The Aoki–Rolewicz `ρ`-norm: `N(x) = inf (∑ ‖yᵢ‖^ρ)^{1/ρ}` over finite decompositions
`x = ∑ yᵢ`. -/
noncomputable def aokiRolewiczNorm (x : E) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (y : Fin n → E), ∑ i, y i = x ∧
    (∑ i, ‖y i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ = r}

theorem aokiRolewiczNorm_nonneg (x : E) : 0 ≤ aokiRolewiczNorm x :=
  Real.sInf_nonneg fun _ ⟨_, _, _, hr⟩ => hr ▸ Real.rpow_nonneg
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

/-- Any finite decomposition `x = ∑ yᵢ` bounds `N(x)` from above. -/
private theorem aokiRolewiczNorm_sum_le {n : ℕ} (y : Fin n → E) :
    aokiRolewiczNorm (∑ i, y i) ≤
      (∑ i, ‖y i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ :=
  csInf_le ⟨0, fun _ ⟨_, _, _, hr⟩ => hr ▸ Real.rpow_nonneg
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _⟩ ⟨n, y, rfl, rfl⟩

theorem aokiRolewiczNorm_le_norm (x : E) : aokiRolewiczNorm x ≤ ‖x‖ := by
  simpa [Real.rpow_rpow_inv (norm_nonneg x) (aokiRolewiczExponent_pos E).ne'] using
    aokiRolewiczNorm_sum_le fun _ : Fin 1 => x

theorem norm_le_aokiRolewiczNorm (x : E) :
    ‖x‖ ≤ (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ * aokiRolewiczNorm x := by
  have h4 : 0 < (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ := by positivity
  rw [← div_le_iff₀' h4]
  refine le_csInf ⟨_, 1, fun _ => x, by simp, rfl⟩ ?_
  rintro _ ⟨n, y, rfl, rfl⟩
  rw [div_le_iff₀' h4]
  exact norm_sum_le_rpow Finset.univ y

/-- Near-optimal decompositions: if `N(x)^ρ < c`, then some decomposition `x = ∑ yᵢ` has
`∑ ‖yᵢ‖^ρ < c`. -/
private theorem exists_sum_eq_of_aokiRolewiczNorm_rpow_lt (x : E) {c : ℝ}
    (hc : aokiRolewiczNorm x ^ aokiRolewiczExponent E < c) :
    ∃ (n : ℕ) (y : Fin n → E), ∑ i, y i = x ∧ ∑ i, ‖y i‖ ^ aokiRolewiczExponent E < c := by
  set ρ := aokiRolewiczExponent E
  have hρ : 0 < ρ := aokiRolewiczExponent_pos E
  have hN := aokiRolewiczNorm_nonneg x
  have hc0 : 0 ≤ c := (Real.rpow_nonneg hN _).trans hc.le
  have hlt : aokiRolewiczNorm x < c ^ ρ⁻¹ :=
    calc aokiRolewiczNorm x = (aokiRolewiczNorm x ^ ρ) ^ ρ⁻¹ :=
          (Real.rpow_rpow_inv hN hρ.ne').symm
      _ < c ^ ρ⁻¹ := Real.rpow_lt_rpow (Real.rpow_nonneg hN _) hc (inv_pos.mpr hρ)
  have hne : {r : ℝ | ∃ (n : ℕ) (y : Fin n → E), ∑ i, y i = x ∧
      (∑ i, ‖y i‖ ^ ρ) ^ ρ⁻¹ = r}.Nonempty := ⟨_, 1, fun _ => x, by simp, rfl⟩
  obtain ⟨_, ⟨n, y, hy, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne hlt
  refine ⟨n, y, hy, ?_⟩
  have hA : 0 ≤ ∑ i, ‖y i‖ ^ ρ :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  exact (Real.rpow_lt_rpow_iff hA hc0 (inv_pos.mpr hρ)).mp hr

/-- The `ρ`-triangle inequality `N(x + y)^ρ ≤ N(x)^ρ + N(y)^ρ`. -/
theorem aokiRolewiczNorm_add_rpow_le (x y : E) :
    aokiRolewiczNorm (x + y) ^ aokiRolewiczExponent E ≤
      aokiRolewiczNorm x ^ aokiRolewiczExponent E +
        aokiRolewiczNorm y ^ aokiRolewiczExponent E := by
  set ρ := aokiRolewiczExponent E
  have hρ : 0 < ρ := aokiRolewiczExponent_pos E
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, a, rfl, ha⟩ := exists_sum_eq_of_aokiRolewiczNorm_rpow_lt x
    (c := aokiRolewiczNorm x ^ ρ + ε / 2) (by linarith)
  obtain ⟨m, b, rfl, hb⟩ := exists_sum_eq_of_aokiRolewiczNorm_rpow_lt y
    (c := aokiRolewiczNorm y ^ ρ + ε / 2) (by linarith)
  have hA : 0 ≤ ∑ i, ‖a i‖ ^ ρ :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hB : 0 ≤ ∑ i, ‖b i‖ ^ ρ :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hsum : ∑ i, Fin.append a b i = ∑ i, a i + ∑ i, b i := by
    rw [Fin.sum_univ_add]; simp
  have hnorm : ∑ i, ‖Fin.append a b i‖ ^ ρ = ∑ i, ‖a i‖ ^ ρ + ∑ i, ‖b i‖ ^ ρ := by
    rw [Fin.sum_univ_add]; simp
  have h := aokiRolewiczNorm_sum_le (Fin.append a b)
  rw [hsum, hnorm] at h
  calc aokiRolewiczNorm (∑ i, a i + ∑ i, b i) ^ ρ
      ≤ ((∑ i, ‖a i‖ ^ ρ + ∑ i, ‖b i‖ ^ ρ) ^ ρ⁻¹) ^ ρ :=
        Real.rpow_le_rpow (aokiRolewiczNorm_nonneg _) h hρ.le
    _ = ∑ i, ‖a i‖ ^ ρ + ∑ i, ‖b i‖ ^ ρ := Real.rpow_inv_rpow (add_nonneg hA hB) hρ.ne'
    _ < _ := by linarith

theorem aokiRolewiczNorm_neg (x : E) : aokiRolewiczNorm (-x) = aokiRolewiczNorm x := by
  sorry

/-- In a complete quasi-normed group, `∑ ‖xᵢ‖^ρ < ∞` implies that `∑ xᵢ` converges. -/
theorem summable_of_summable_norm_rpow [CompleteSpace E] {ι : Type*} {x : ι → E}
    (h : Summable fun i => ‖x i‖ ^ aokiRolewiczExponent E) : Summable x := by
  sorry

/-- The Aoki–Rolewicz bound for infinite sums: `‖∑' xᵢ‖ ≤ 4^{1/ρ} (∑' ‖xᵢ‖^ρ)^{1/ρ}`. Note that we
do not assume that `∑' i, x i` is summable, and it might not be the case if `E` is not complete. -/
theorem norm_tsum_le_rpow {ι : Type*} {x : ι → E}
    (h : Summable fun i => ‖x i‖ ^ aokiRolewiczExponent E) :
    ‖∑' i, x i‖ ≤ (4 : ℝ) ^ (aokiRolewiczExponent E)⁻¹ *
      (∑' i, ‖x i‖ ^ aokiRolewiczExponent E) ^ (aokiRolewiczExponent E)⁻¹ := by
  sorry

end QuasinormedAddCommGroup
