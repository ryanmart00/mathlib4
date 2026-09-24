/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Quasi.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Quasi-normed spaces

`QuasiNormedSpace 𝕜 E`: a quasi-normed group `E` that is a `𝕜`-module with
`‖c • x‖ ≤ ‖c‖ * ‖x‖`, the quasi-normed analogue of `NormedSpace`.

## Main definitions
* `QuasiNormedSpace`.

## Main results
* `QuasiNormedSpace.norm_smul`: the homogeneity is exact, `‖c • x‖ = ‖c‖ * ‖x‖`.
* `QuasiNormedSpace.continuousSMul`: scalar multiplication is continuous.
* `NormedSpace.toQuasiNormedSpace`, `QuasiNormedSpace.instProd`.
-/

/-- A `QuasinormedAddCommGroup` that is also a module over `𝕜`, compatibly with the quasi-norm:
`‖c • x‖ ≤ ‖c‖ * ‖x‖` — exactly the axiom `NormedSpace` uses (`NormedSpace.norm_smul_le`), from
which equality follows as a theorem (`norm_smul` below), the same way `NormedSpace` derives it:
apply the bound to both `c` and (for `c ≠ 0`) `c⁻¹ • (c • x)`.

Mirrors `NormedSpace`, not `NormedAddCommGroup`, deliberately: `QuasinormedAddCommGroup` itself
has no scalar field, exactly like `NormedAddCommGroup`. This axiom is what actually lets scalar
multiplication be continuous (`QuasiNormedSpace.continuousSMul` below) — without it, `‖c • x‖`
has no relationship at all to `‖c‖`/`‖x‖`, and there would be no way to derive continuity of `•`
from the quasi-norm. Threading `[Module 𝕜 A] [ContinuousSMul 𝕜 A]` as two independent, unrelated
hypotheses (as earlier versions of this project did) forces `ContinuousSMul` to be re-derived
through generic, ambient-topology-dependent routes (e.g. `SMulMemClass.continuousSMul` for a
submodule) every time a new quasi-normed type is built, which then has to coincide with this
class's own *bundled* topology — a real diamond, caught when it silently failed for a submodule
of an interpolation couple's legs. Deriving `ContinuousSMul` directly from `norm_smul_le` plus
`nhds_zero_hasBasis` (both already tied to *this* class's own bundled topology) sidesteps that
entirely, the same way `NormedSpace.toIsBoundedSMul`/`IsBoundedSMul.continuousSMul` sidestep it
for genuine normed spaces (there, via `dist` instead of norm-balls, since a metric is available). -/
class QuasiNormedSpace (𝕜 E : Type*) [NormedField 𝕜] [QuasinormedAddCommGroup E] extends
    Module 𝕜 E where
  norm_smul_le : ∀ (c : 𝕜) (x : E), ‖c • x‖ ≤ ‖c‖ * ‖x‖

namespace QuasiNormedSpace

variable {𝕜 E : Type*} [NormedField 𝕜] [QuasinormedAddCommGroup E] [QuasiNormedSpace 𝕜 E]

/-- The quasi-norm homogeneity is actually exact, exactly as for `NormedSpace`: the reverse
inequality follows by applying `norm_smul_le` to `c⁻¹ • (c • x)` and using that `𝕜` is a field
(so `c ≠ 0` is invertible). -/
theorem norm_smul (c : 𝕜) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine le_antisymm (norm_smul_le c x) ?_
    calc ‖c‖ * ‖x‖ = ‖c‖ * ‖c⁻¹ • c • x‖ := by rw [inv_smul_smul₀ hc]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • x‖) := by gcongr; exact norm_smul_le c⁻¹ (c • x)
      _ = ‖c • x‖ := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (mt norm_eq_zero.1 hc), one_mul]

/-- Scalar multiplication is continuous, derived directly from `norm_smul_le` and the bundled
`nhds_zero_hasBasis` — no metric/`dist` needed (unlike `IsBoundedSMul.continuousSMul`, which
this otherwise mirrors): continuity at an arbitrary `(c₀, x₀)` reduces, via the identity
`c • x - c₀ • x₀ = c₀ • (x - x₀) + (c - c₀) • x₀ + (c - c₀) • (x - x₀)`, to a direct ε-δ bound
using the quasi-triangle inequality (applied twice, for the three-term sum) and `norm_smul_le`
(applied to each term). -/
theorem continuousAt_smul (c₀ : 𝕜) (x₀ : E) :
    ContinuousAt (fun p : 𝕜 × E => p.1 • p.2) (c₀, x₀) := by
  rw [ContinuousAt, nhds_prod_eq]
  have hb1 : (nhds c₀).HasBasis (0 < ·) (fun δ : ℝ => Metric.ball c₀ δ) := Metric.nhds_basis_ball
  have hb2 : (nhds x₀).HasBasis (0 < ·) (fun δ : ℝ => {x : E | ‖x - x₀‖ < δ}) := by
    have h1 := (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).map (x₀ + ·)
    rw [map_add_left_nhds_zero x₀] at h1
    have himg : ∀ δ : ℝ, (x₀ + ·) '' {y : E | ‖y‖ < δ} = {x : E | ‖x - x₀‖ < δ} := by
      intro δ; ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hx; exact ⟨x - x₀, by simpa using hx, by abel_nf⟩
    simpa only [himg] using h1
  have htarget : (nhds (c₀ • x₀)).HasBasis (0 < ·) (fun ε : ℝ => {z : E | ‖z - c₀ • x₀‖ < ε}) := by
    have h1 := (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := E)).map (c₀ • x₀ + ·)
    rw [map_add_left_nhds_zero (c₀ • x₀)] at h1
    have himg : ∀ ε : ℝ, (c₀ • x₀ + ·) '' {y : E | ‖y‖ < ε} = {z : E | ‖z - c₀ • x₀‖ < ε} := by
      intro ε; ext z
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hz; exact ⟨z - c₀ • x₀, by simpa using hz, by abel_nf⟩
    simpa only [himg] using h1
  rw [(hb1.prod hb2).tendsto_iff htarget]
  intro ε hε
  have hK1 : 1 ≤ QuasinormedAddCommGroup.quasiTriangleConst (E := E) :=
    QuasinormedAddCommGroup.one_le_quasiTriangleConst (E := E)
  set K := QuasinormedAddCommGroup.quasiTriangleConst (E := E) with hKdef
  have hKpos : 0 < K := by linarith
  have hc0 : 0 ≤ ‖c₀‖ := norm_nonneg c₀
  have hx0 : 0 ≤ ‖x₀‖ := QuasinormedAddCommGroup.norm_nonneg x₀
  set M : ℝ := K ^ 2 * (‖c₀‖ + ‖x₀‖) + K + 1 with hMdef
  have hMpos : 0 < M := by
    have : 0 ≤ K ^ 2 * (‖c₀‖ + ‖x₀‖) := mul_nonneg (sq_nonneg K) (add_nonneg hc0 hx0)
    rw [hMdef]; linarith
  have hε2M : 0 < ε / (2 * M) := div_pos hε (by linarith)
  refine ⟨(min 1 (ε / (2 * M)), min 1 (ε / (2 * M))),
    ⟨lt_min one_pos hε2M, lt_min one_pos hε2M⟩, ?_⟩
  rintro ⟨c, x⟩ ⟨hc, hx⟩
  simp only [Metric.mem_ball, dist_eq_norm] at hc
  simp only [Set.mem_ofPred_eq] at hx
  change ‖c • x - c₀ • x₀‖ < ε
  set δ := min 1 (ε / (2 * M)) with hδdef
  set dc := c - c₀ with hdc
  set dx := x - x₀ with hdx
  have hcx : c • x - c₀ • x₀ = c₀ • dx + dc • x₀ + dc • dx := by
    simp only [hdc, hdx, smul_sub, sub_smul]
    abel_nf
  rw [hcx]
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * M) := min_le_right _ _
  have hδpos : 0 < δ := lt_min one_pos hε2M
  have hdcpos : 0 ≤ ‖dc‖ := QuasinormedAddCommGroup.norm_nonneg _
  have hdxpos : 0 ≤ ‖dx‖ := QuasinormedAddCommGroup.norm_nonneg _
  have hltdc : ‖dc‖ < δ := hc
  have hltdx : ‖dx‖ < δ := hx
  have tb1 : ‖c₀ • dx‖ ≤ ‖c₀‖ * δ :=
    (norm_smul_le c₀ dx).trans (mul_le_mul_of_nonneg_left hltdx.le hc0)
  have tb2 : ‖dc • x₀‖ ≤ δ * ‖x₀‖ :=
    (norm_smul_le dc x₀).trans (mul_le_mul_of_nonneg_right hltdc.le hx0)
  have tb3 : ‖dc • dx‖ ≤ δ := by
    have hb : ‖dc • dx‖ ≤ δ * δ :=
      (norm_smul_le dc dx).trans (mul_le_mul hltdc.le hltdx.le hdxpos (by linarith))
    calc ‖dc • dx‖ ≤ δ * δ := hb
      _ ≤ δ * 1 := by gcongr
      _ = δ := mul_one δ
  have htri : ‖c₀ • dx + dc • x₀ + dc • dx‖ ≤
      K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) := by
    calc ‖c₀ • dx + dc • x₀ + dc • dx‖
        ≤ K * (‖c₀ • dx + dc • x₀‖ + ‖dc • dx‖) := QuasinormedAddCommGroup.norm_add_le _ _
      _ ≤ K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) := by
          gcongr
          exact QuasinormedAddCommGroup.norm_add_le _ _
  have hfinal : K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) ≤ δ * M := by
    have step1 : ‖c₀ • dx‖ + ‖dc • x₀‖ ≤ ‖c₀‖ * δ + δ * ‖x₀‖ := by linarith
    have step2 : K * (‖c₀ • dx‖ + ‖dc • x₀‖) ≤ K * (‖c₀‖ * δ + δ * ‖x₀‖) :=
      mul_le_mul_of_nonneg_left step1 hKpos.le
    have step3 : K * (‖c₀‖ * δ + δ * ‖x₀‖) + ‖dc • dx‖ ≤ K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ := by
      linarith
    have step4 : K * (K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖) ≤
        K * (K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ) := by
      have : K * (‖c₀ • dx‖ + ‖dc • x₀‖) + ‖dc • dx‖ ≤ K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ := by
        linarith
      exact mul_le_mul_of_nonneg_left this hKpos.le
    have step5 : K * (K * (‖c₀‖ * δ + δ * ‖x₀‖) + δ) = δ * (M - 1) := by rw [hMdef]; ring
    rw [step5] at step4
    have step6 : δ * (M - 1) ≤ δ * M := by nlinarith
    linarith
  have hδM : δ * M ≤ ε / 2 := by
    calc δ * M ≤ (ε / (2 * M)) * M := mul_le_mul_of_nonneg_right hδ2 hMpos.le
      _ = ε / 2 := by field_simp
  linarith

instance (priority := 100) continuousSMul : ContinuousSMul 𝕜 E where
  continuous_smul := continuous_iff_continuousAt.mpr fun p => continuousAt_smul p.1 p.2

/-- Every `NormedSpace` is a `QuasiNormedSpace` (over the corresponding `NormedAddCommGroup`
bridge instance), with the *same* `norm_smul_le` bound and `Module` structure reused verbatim. -/
instance (priority := 100) _root_.NormedSpace.toQuasiNormedSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] : QuasiNormedSpace 𝕜 F :=
  { ‹NormedSpace 𝕜 F› with norm_smul_le := NormedSpace.norm_smul_le }

/-- The product of two `QuasiNormedSpace`s, via the (already-existing) `Prod` module structure
and max quasi-norm. -/
instance instProd {F : Type*} [QuasinormedAddCommGroup F] [QuasiNormedSpace 𝕜 F] :
    QuasiNormedSpace 𝕜 (E × F) where
  norm_smul_le c p := by
    rw [Prod.norm_def, Prod.norm_def]
    simp only [Prod.smul_fst, Prod.smul_snd]
    rw [norm_smul c p.1, norm_smul c p.2]
    exact (mul_max_of_nonneg _ _ (norm_nonneg c)).ge

end QuasiNormedSpace
