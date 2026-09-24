/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Quasi.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Completeness of quasi-normed groups via controlled Cauchy sequences

Generalizes `Mathlib/Analysis/Normed/Group/Completeness.lean`'s
`NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` (itself Bergh–Löfström, Lemma 2.2.1) —
and, closer in spirit, `MeasureTheory.Lp`'s own
`Lp.completeSpace_lp_of_cauchy_complete_eLpNorm` (`LpSpace/Complete.lean`) — from genuinely-normed
groups to merely-*quasi*-normed ones. The normed-group version reduces to `Metric.
complete_of_cauchySeq_tendsto`, which needs an actual `dist`; a `QuasinormedAddCommGroup` only has
a *quasi*-triangle inequality, so no genuine metric is available in general. The fix: go through
the more primitive `UniformSpace.complete_of_convergent_controlled_sequences` instead, which needs
only a countably-generated uniformity filter — already available for any `QuasinormedAddCommGroup`
via its bundled `IsUniformAddGroup` (`Basic.lean`'s `instFirstCountableTopology`
combines the exact same two facts to get the same instance for a different purpose).

## Main results
* `QuasinormedAddCommGroup.completeSpace_of_cauchy_complete`: if every "controlled" Cauchy sequence
  (one whose steps past index `N` are bounded by some fixed summable `B N`) converges, the whole
  quasi-normed group is complete. Mirrors `Lp`'s own `H`-hypothesis shape exactly, so that a future
  `CompleteSpace (LorentzSpace E p q μ)` proof can follow `Lp`'s own `Complete.lean` structure
  as closely as possible.
-/

open Filter
open scoped Topology QuasinormedAddCommGroup Uniformity

variable {E : Type*} [QuasinormedAddCommGroup E]

/-- A quasi-normed additive group is complete provided every sequence controlled by a fixed
summable `B` (steps past index `N` bounded by `B N`) converges. Mirrors `MeasureTheory.Lp.
completeSpace_lp_of_cauchy_complete_eLpNorm`'s hypothesis shape, generalized from `Lp`'s genuine
norm to a mere quasi-norm — the underlying reduction (`UniformSpace.
complete_of_convergent_controlled_sequences`) needs only a countably-generated uniformity, not an
exact metric, so the quasi-triangle inequality never has to enter this half of the argument at
all. -/
theorem QuasinormedAddCommGroup.completeSpace_of_cauchy_complete
    (H : ∀ (f : ℕ → E) (B : ℕ → ℝ), Summable B →
      (∀ N n m : ℕ, N ≤ n → N ≤ m → ‖f n - f m‖ < B N) →
      ∃ f_lim : E, Tendsto f atTop (𝓝 f_lim)) :
    CompleteSpace E := by
  have hcg : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  apply UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => (fun x : E × E => x.2 - x.1) ⁻¹' {y : E | ‖y‖ < (1 / 2 : ℝ) ^ n})
  · intro n
    rw [uniformity_eq_comap_nhds_zero]
    apply Filter.preimage_mem_comap
    exact (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).mem_iff.mpr
      ⟨(1 / 2 : ℝ) ^ n, by positivity, subset_rfl⟩
  · intro u hu
    apply H u (fun n => (1 / 2 : ℝ) ^ n) summable_geometric_two
    intro N n m hn hm
    exact hu N m n hm hn

/-- A sequence in a quasi-normed group whose tail differences are controlled by a sequence tending
to `0` is Cauchy. -/
theorem QuasinormedAddCommGroup.cauchySeq_of_le_tendsto_zero {f : ℕ → E} (B : ℕ → ℝ)
    (h : ∀ N n m : ℕ, N ≤ n → N ≤ m → ‖f n - f m‖ ≤ B N) (hB : Tendsto B atTop (𝓝 0)) :
    CauchySeq f := by
  have hb : (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε)
      fun ε => (fun x : E × E => x.2 - x.1) ⁻¹' {y : E | ‖y‖ < ε} := by
    rw [uniformity_eq_comap_nhds_zero]
    exact QuasinormedAddCommGroup.nhds_zero_hasBasis.comap _
  rw [hb.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hB).2 ε hε)
  exact ⟨N, fun m hm n hn => (h N n m hn hm).trans_lt (hN N le_rfl)⟩
