/-
Copyright (c) 2026 Ryan Martinez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Martinez
-/
import Mathlib.Analysis.Normed.Quasi.Quotient
import Mathlib.Analysis.Normed.Quasi.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Tactic.FastInstance

/-!
# Interpolation couples

DRAFT — under review, no proof attempted beyond the completeness of `A₀ ⊓ A₁` and `A₀ + A₁`.

Following Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, §1.2.1:
two Banach spaces `A₀, A₁`, both linearly and continuously embedded in a common Hausdorff
topological vector space `𝒜`, form an *interpolation couple*. `A₀ ⊓ A₁` and `A₀ + A₁` are then
Banach spaces in their own right.

**Unit 2 (2026-09-17): generalized from `NormedAddCommGroup` legs to `QuasinormedAddCommGroup`**
(quasi-norm, with its topology/uniform structure bundled in exactly like `NormedAddCommGroup`,
see `Analysis/Normed/Quasi/Basic.lean`), with completeness kept as a separate `[CompleteSpace _]`
bracket, matching `NormedAddCommGroup`'s own pattern (there is no separate "quasi-Banach"
class). Every genuine `NormedAddCommGroup` still satisfies `QuasinormedAddCommGroup` via the
bridge instance there, so nothing here is a behavior change for existing normed-leg callers.
The parts that never touched a norm at all (`diff`, `plus`, both kernels' closedness, `meet`,
`mem_meet_iff`, `meet.completeSpace`, `sum` as a bare type, `mem_ker_plus_iff`) generalized
with **no proof changes whatsoever** — pure topology/module-map facts. `A₀+A₁`'s norm and
completeness needed real new content, from `Analysis/Normed/Quasi/Quotient.lean` (Unit 1): its
quasi-norm via `QuasinormedAddCommGroup.quotientQuasinormedAddCommGroup` (needing the kernel
closed in the *norm* sense, obtained from the already-proved *topological* closedness via
`AddSubgroup.isNormClosed_of_isClosed`), and its completeness via
`QuasinormedAddCommGroup.quotientNorm_completeSpace`. Its topology, `IsTopologicalAddGroup`
instance, and module/`ContinuousSMul` structure all turned out to **already be automatic**
Mathlib instances for `Submodule.Quotient` (`Submodule.isTopologicalAddGroup_quotient`,
`Submodule.continuousSMul_quotient`, `QuotientModule.Quotient.topologicalSpace`) — no new proof
needed for any of those either. `FirstCountableTopology` needed no bridging at all once
`QuasinormedAddCommGroup` grew its own generic `instFirstCountableTopology`
(`Analysis/Normed/Quasi/Basic.lean`) — free for *any* quasi-normed leg from the quasi-norm's own
neighborhood basis, no Aoki–Rolewicz needed, so `A₀+A₁` picks it up automatically the same way
`A₀`, `A₁` themselves do. Only the quasi-norm and completeness needed real work; everything else
was already there.

Realized here as: `A₀ ⊓ A₁` (the "meet") is the kernel of `diff (a₀,a₁) = ι₀ a₀ - ι₁ a₁` on
`A₀ × A₁` — the pullback/equalizer, matching Triebel's `A₀ ∩ A₁` as the set of points reachable
from both legs. `A₀ + A₁` (the "sum") is the quotient of `A₀ × A₁` by the kernel of the *different*
map `plus (a₀,a₁) = ι₀ a₀ + ι₁ a₁` — matching Triebel's `A₀+A₁` as the image of `plus` via the
first isomorphism theorem (`(A₀×A₁)/ker(plus) ≅ image(plus)`). Both kernels are closed (the maps
are continuous into a `T2Space`), so both quotient/submodule constructions are Banach (resp.
quasi-Banach) spaces via existing Mathlib instances plus `Analysis/Normed/Quasi/Quotient.lean`,
with no
from-scratch Cauchy-sequence argument needed.

Both `diff`'s kernel and `plus`'s kernel are needed — they are genuinely different submodules
(related by the sign-flip automorphism `(a₀,a₁) ↦ (a₀,-a₁)` on `A₁`, not literally equal). An
earlier version of this file mistakenly quotiented by the *same* kernel (`diff`'s) for both,
which made the canonical `meet → sum` map identically zero (every element of the kernel you
quotient by is trivially killed by that same quotient) — a real bug, only caught once we tried
to actually construct the interpolation functors `∩`/`+` themselves and needed that map to be
meaningful. The norms obtained this way (`Prod`'s max-norm, restricted resp. quotiented) are
equivalent to, but not literally equal to, Triebel's `max(‖a₀‖,‖a₁‖)` and `inf ‖a₀‖+‖a₁‖` — an
acceptable trade since interpolation theory works up to norm equivalence throughout.
-/

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module 𝕜 𝒜] [TopologicalSpace 𝒜]
  [IsTopologicalAddGroup 𝒜] [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜]
variable {A₀ A₁ : Type*}
  [QuasinormedAddCommGroup A₀] [QuasiNormedSpace 𝕜 A₀] [CompleteSpace A₀]
  [QuasinormedAddCommGroup A₁] [QuasiNormedSpace 𝕜 A₁] [CompleteSpace A₁]

/-- The continuous linear map `(a₀, a₁) ↦ ι₀ a₀ - ι₁ a₁` on the product. Its kernel realizes
`A₀ ∩ A₁` and its induced quotient realizes `A₀ + A₁`. -/
noncomputable def InterpolationCouple.diff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    (A₀ × A₁) →L[𝕜] 𝒜 :=
  ι₀.comp (ContinuousLinearMap.fst 𝕜 A₀ A₁) - ι₁.comp (ContinuousLinearMap.snd 𝕜 A₀ A₁)

/-- The continuous linear map `(a₀, a₁) ↦ ι₀ a₀ + ι₁ a₁` on the product. Its kernel is what
`A₀ + A₁` is the quotient by (via the first isomorphism theorem, `(A₀×A₁)/ker(plus) ≅
image(plus) = A₀+A₁`). -/
noncomputable def InterpolationCouple.plus (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    (A₀ × A₁) →L[𝕜] 𝒜 :=
  ι₀.comp (ContinuousLinearMap.fst 𝕜 A₀ A₁) + ι₁.comp (ContinuousLinearMap.snd 𝕜 A₀ A₁)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The kernel of `diff` is closed, since `diff` is continuous into a Hausdorff space. -/
theorem InterpolationCouple.isClosed_ker_diff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    IsClosed ((InterpolationCouple.diff ι₀ ι₁).ker : Set (A₀ × A₁)) :=
  isClosed_singleton.preimage (InterpolationCouple.diff ι₀ ι₁).continuous

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- The kernel of `plus` is closed, since `plus` is continuous into a Hausdorff space. -/
theorem InterpolationCouple.isClosed_ker_plus (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    IsClosed ((InterpolationCouple.plus ι₀ ι₁).ker : Set (A₀ × A₁)) :=
  isClosed_singleton.preimage (InterpolationCouple.plus ι₀ ι₁).continuous

/-- `A₀ ∩ A₁`, realized as the (closed) kernel submodule of `diff` inside `A₀ × A₁`. -/
noncomputable def InterpolationCouple.meet (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    Submodule 𝕜 (A₀ × A₁) :=
  (InterpolationCouple.diff ι₀ ι₁).ker

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.mem_meet_iff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a₀ : A₀) (a₁ : A₁) :
    (a₀, a₁) ∈ InterpolationCouple.meet ι₀ ι₁ ↔ ι₀ a₀ = ι₁ a₁ := by
  simp [InterpolationCouple.meet, InterpolationCouple.diff, LinearMap.mem_ker, sub_eq_zero]

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `A₀ ∩ A₁`'s quasi-norm: the restriction of `A₀ × A₁`'s own (max) quasi-norm to the (closed)
submodule `meet ι₀ ι₁`, with the same triangle constant. The topology/uniform structure are the
submodule's own already-automatic ones (`Submodule`'s generic subtype instances, from `A₀ × A₁`'s
own topology), reused rather than recomputed — `toIsUniformAddGroup` specifically via
`AddSubgroup.isUniformAddGroup` applied to `(diff ι₀ ι₁).ker.toAddSubgroup` (whose carrier type
is definitionally `meet ι₀ ι₁`'s own, so this gives the *same* ambient uniform space, not a
second one). Same "reuse ambient, don't recompute" principle as `sum.quasinormedAddCommGroup`'s
topology fields, for the same reason: a second, only-propositionally-equal instance here would
create the same kind of diamond that surfaced for `A₀+A₁` (see `QuotientQuasinormedAddCommGroup`'s
docstring in `Analysis/Normed/Quasi/Quotient.lean`). -/
@[instance_reducible]
noncomputable instance InterpolationCouple.meet.quasinormedAddCommGroup
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    QuasinormedAddCommGroup (InterpolationCouple.meet ι₀ ι₁) :=
  fast_instance% show QuasinormedAddCommGroup (InterpolationCouple.diff ι₀ ι₁).ker from
  { norm := fun x => ‖(x : A₀ × A₁)‖
    quasiTriangleConst := QuasinormedAddCommGroup.quasiTriangleConst (E := A₀ × A₁)
    one_le_quasiTriangleConst := QuasinormedAddCommGroup.one_le_quasiTriangleConst (E := A₀ × A₁)
    norm_add_le := fun x y => QuasinormedAddCommGroup.norm_add_le (x : A₀ × A₁) (y : A₀ × A₁)
    norm_neg := fun x => by simp [QuasinormedAddCommGroup.norm_neg]
    norm_eq_zero_iff := fun x => by simp [QuasinormedAddCommGroup.norm_eq_zero_iff]
    toUniformSpace := inferInstance
    toIsTopologicalAddGroup := inferInstance
    toIsUniformAddGroup :=
      AddSubgroup.isUniformAddGroup (InterpolationCouple.diff ι₀ ι₁).ker.toAddSubgroup
    nhds_zero_hasBasis := by
      rw [nhds_subtype]
      exact (QuasinormedAddCommGroup.nhds_zero_hasBasis (E := A₀ × A₁)).comap _ }

/-- `A₀ ∩ A₁` is a `QuasiNormedSpace`: the norm-scalar bound is just the restriction of
`A₀ × A₁`'s own. Gives `Module`/`ContinuousSMul` for free via `QuasiNormedSpace.toModule`/
`.continuousSMul`, superseding what used to be two separate, ambient-topology-dependent
instances (`meet.module`, `meet.continuousSMul`, via the generic `Submodule.module`/
`SMulMemClass.continuousSMul` routes) — those turned out to create exactly the same kind of
diamond as `sum.uniformSpace` once did, since `ContinuousSMul` traces back to needing
`meet.quasinormedAddCommGroup`'s *own* bundled topology to match the generic ambient one, and
that match is not obvious to instance search. Deriving `ContinuousSMul` directly from the
quasi-norm bound (`QuasiNormedSpace.continuousSMul`) sidesteps the ambient
topology entirely, the same way it does for `sum` below. -/
noncomputable instance InterpolationCouple.meet.quasiNormedSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    QuasiNormedSpace 𝕜 (InterpolationCouple.meet ι₀ ι₁) where
  norm_smul_le c a := by
    change ‖(↑(c • a) : A₀ × A₁)‖ ≤ ‖c‖ * ‖(↑a : A₀ × A₁)‖
    rw [Submodule.coe_smul]
    exact QuasiNormedSpace.norm_smul_le c (a : A₀ × A₁)

noncomputable instance InterpolationCouple.meet.completeSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    @CompleteSpace (InterpolationCouple.meet ι₀ ι₁)
      (InterpolationCouple.meet.quasinormedAddCommGroup ι₀ ι₁).toUniformSpace :=
  (InterpolationCouple.isClosed_ker_diff ι₀ ι₁).completeSpace_coe

/-- `A₀ + A₁`, realized as the quotient of `A₀ × A₁` by the (closed) kernel of `plus`. -/
def InterpolationCouple.sum (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) : Type _ :=
  (A₀ × A₁) ⧸ (InterpolationCouple.plus ι₀ ι₁).ker

omit [ContinuousSMul 𝕜 𝒜] [T2Space 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.mem_ker_plus_iff
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a₀ : A₀) (a₁ : A₁) :
    (a₀, a₁) ∈ (InterpolationCouple.plus ι₀ ι₁).ker ↔ ι₀ a₀ = -ι₁ a₁ := by
  simp [InterpolationCouple.plus, LinearMap.mem_ker, eq_neg_iff_add_eq_zero]

/-- `A₀+A₁`'s quasi-norm, from the quotient construction of `Analysis/Normed/Quasi/Quotient.lean`;
the kernel's
already-proved *topological* closedness (`isClosed_ker_plus`) bridges to the *norm* closedness
this needs via `AddSubgroup.isNormClosed_of_isClosed`. -/
noncomputable instance InterpolationCouple.sum.quasinormedAddCommGroup
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    QuasinormedAddCommGroup (InterpolationCouple.sum ι₀ ι₁) :=
  QuasinormedAddCommGroup.quotientQuasinormedAddCommGroup
    (InterpolationCouple.plus ι₀ ι₁).ker.toAddSubgroup
    (AddSubgroup.isNormClosed_of_isClosed _ (InterpolationCouple.isClosed_ker_plus ι₀ ι₁))

/-- Completeness of `A₀+A₁`, from `QuasinormedAddCommGroup.quotientNorm_completeSpace` (the
purely topological `QuotientAddGroup.completeSpace_right`) — matches `sum.quasinormedAddCommGroup`
above exactly, since `QuasinormedAddCommGroup.quotientQuasinormedAddCommGroup`'s own
`toUniformSpace` field *is* `IsTopologicalAddGroup.rightUniformSpace` (reusing the quotient's
already-automatic ambient topology, not a fresh one — see that definition's docstring). No
separate `sum.uniformSpace` instance is needed (an earlier version of this file had one,
built the same way, but as a *second*, only-propositionally-equal term for the same class —
a real diamond, caught once `QuasiBanachCat.ofHom` needed to compare a term built through each
path). -/
noncomputable instance InterpolationCouple.sum.completeSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    @CompleteSpace (InterpolationCouple.sum ι₀ ι₁)
      (InterpolationCouple.sum.quasinormedAddCommGroup ι₀ ι₁).toUniformSpace :=
  QuasinormedAddCommGroup.quotientNorm_completeSpace
    (E := A₀ × A₁) (N := (InterpolationCouple.plus ι₀ ι₁).ker.toAddSubgroup)

/-- `A₀+A₁` is a `QuasiNormedSpace`: the norm-scalar bound for the quotient norm, proved the same
way `quotientNorm_add_le` proves its own triangle inequality — for any `ε > 0`, pick a
representative `y` of `a` with `‖y‖` within `ε` of the infimum, then bound
`‖c • a‖ ≤ ‖c • y‖ ≤ ‖c‖ * ‖y‖ < ‖c‖ * quotientNorm a + ‖c‖ * ε'` for `ε' := ε/(‖c‖+1)` (chosen to
avoid dividing by `‖c‖` itself, so the same argument covers `c = 0` too). Gives
`Module`/`ContinuousSMul` for free via `QuasiNormedSpace.toModule`/`.continuousSMul`, superseding
what used to be two separate instances (`sum.module`, `sum.continuousSMul`) — for the same reason
`meet.quasiNormedSpace` above supersedes its own pair: deriving `ContinuousSMul` directly from
the quasi-norm bound sidesteps ever needing to match this class's bundled topology against a
generic ambient one. -/
noncomputable instance InterpolationCouple.sum.quasiNormedSpace
    (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    QuasiNormedSpace 𝕜 (InterpolationCouple.sum ι₀ ι₁) :=
  letI : Module 𝕜 (InterpolationCouple.sum ι₀ ι₁) :=
    (show Module 𝕜 ((A₀ × A₁) ⧸ (InterpolationCouple.plus ι₀ ι₁).ker) from inferInstance)
  { norm_smul_le := fun c a => by
      induction a using Submodule.Quotient.induction_on with
      | _ x =>
        set P := (InterpolationCouple.plus ι₀ ι₁).ker with hP
        let a : InterpolationCouple.sum ι₀ ι₁ := Submodule.Quotient.mk (p := P) x
        change ‖c • a‖ ≤ ‖c‖ * ‖a‖
        apply le_of_forall_pos_le_add
        intro ε hε
        have hcpos : (0:ℝ) < ‖c‖ + 1 := by positivity
        obtain ⟨y, hy, hy'⟩ := QuasinormedAddCommGroup.exists_norm_lt_quotientNorm_add
          (N := P.toAddSubgroup) (x := a) (div_pos hε hcpos)
        have hbound : ‖c‖ * (ε / (‖c‖ + 1)) ≤ ε := by
          rw [← mul_div_assoc, div_le_iff₀ hcpos]
          nlinarith [norm_nonneg c, hε.le]
        let b : InterpolationCouple.sum ι₀ ι₁ := Submodule.Quotient.mk (p := P) (c • y)
        have hcx : c • a = b := by
          rw [← hy]
          exact (Submodule.Quotient.mk_smul (S := 𝕜) P c y).symm
        calc ‖c • a‖ = ‖b‖ := by rw [hcx]
          _ ≤ ‖c • y‖ := QuasinormedAddCommGroup.quotientNorm_mk_le _ (c • y)
          _ ≤ ‖c‖ * ‖y‖ := QuasiNormedSpace.norm_smul_le c y
          _ ≤ ‖c‖ * (QuasinormedAddCommGroup.quotientNorm P.toAddSubgroup a
                + ε / (‖c‖ + 1)) :=
              mul_le_mul_of_nonneg_left hy'.le (norm_nonneg c)
          _ = ‖c‖ * QuasinormedAddCommGroup.quotientNorm P.toAddSubgroup a
                + ‖c‖ * (ε / (‖c‖ + 1)) := by ring
          _ ≤ ‖c‖ * QuasinormedAddCommGroup.quotientNorm P.toAddSubgroup a + ε := by linarith }

/-- The canonical continuous linear map `A₀ →L[𝕜] A₀ + A₁`, `a₀ ↦ [(a₀, 0)]`. -/
noncomputable def InterpolationCouple.inl₀ (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    A₀ →L[𝕜] InterpolationCouple.sum ι₀ ι₁ :=
  (InterpolationCouple.plus ι₀ ι₁).ker.mkQL.comp (ContinuousLinearMap.inl 𝕜 A₀ A₁)

/-- The canonical continuous linear map `A₁ →L[𝕜] A₀ + A₁`, `a₁ ↦ [(0, a₁)]`. -/
noncomputable def InterpolationCouple.inl₁ (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    A₁ →L[𝕜] InterpolationCouple.sum ι₀ ι₁ :=
  (InterpolationCouple.plus ι₀ ι₁).ker.mkQL.comp (ContinuousLinearMap.inr 𝕜 A₀ A₁)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
@[simp]
theorem InterpolationCouple.inl₀_eq_mk (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₀) :
    InterpolationCouple.inl₀ ι₀ ι₁ a = Submodule.Quotient.mk (a, 0) := rfl

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
@[simp]
theorem InterpolationCouple.inl₁_eq_mk (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₁) :
    InterpolationCouple.inl₁ ι₀ ι₁ a = Submodule.Quotient.mk (0, a) := rfl

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₀_eq_zero_iff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₀) :
    InterpolationCouple.inl₀ ι₀ ι₁ a = 0 ↔ ι₀ a = 0 := by
  change (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (a, 0) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, InterpolationCouple.mem_ker_plus_iff]
  simp

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₁_eq_zero_iff (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₁) :
    InterpolationCouple.inl₁ ι₀ ι₁ a = 0 ↔ ι₁ a = 0 := by
  change (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (0, a) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, InterpolationCouple.mem_ker_plus_iff]
  simp

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₀_injective (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    (hι₀ : Function.Injective ι₀) :
    Function.Injective (InterpolationCouple.inl₀ ι₀ ι₁) := by
  intro a b hab
  have h0 : InterpolationCouple.inl₀ ι₀ ι₁ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [InterpolationCouple.inl₀_eq_zero_iff, map_sub] at h0
  exact hι₀ (sub_eq_zero.mp h0)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.inl₁_injective (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    (hι₁ : Function.Injective ι₁) :
    Function.Injective (InterpolationCouple.inl₁ ι₀ ι₁) := by
  intro a b hab
  have h0 : InterpolationCouple.inl₁ ι₀ ι₁ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [InterpolationCouple.inl₁_eq_zero_iff, map_sub] at h0
  exact hι₁ (sub_eq_zero.mp h0)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- For `(a₀,a₁)` in the meet (so `ι₀ a₀ = ι₁ a₁`, a single point of the ambient space reachable
from both legs), its images in the sum space via either leg agree: `[(a₀,0)] = [(0,a₁)]`. This is
what makes `meetToSum` (using only the `A₀` leg) the right, symmetric notion of "the meet, viewed
inside the sum". -/
theorem InterpolationCouple.inl₀_fst_eq_inl₁_snd (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    {a₀ : A₀} {a₁ : A₁} (h : ι₀ a₀ = ι₁ a₁) :
    InterpolationCouple.inl₀ ι₀ ι₁ a₀ = InterpolationCouple.inl₁ ι₀ ι₁ a₁ := by
  change (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (a₀, 0) =
    (InterpolationCouple.plus ι₀ ι₁).ker.mkQ (0, a₁)
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    InterpolationCouple.mem_ker_plus_iff]
  simpa using h

/-- The canonical continuous linear map `A₀ ∩ A₁ →L[𝕜] A₀ + A₁`: `(a₀,a₁) ↦ [(a₀,0)]` (which,
by `inl₀_fst_eq_inl₁_snd`, agrees with `[(0,a₁)]` — the meet, viewed inside the sum).

The domain's `TopologicalSpace`/`AddCommMonoid` are `@`-pinned to `meet.quasinormedAddCommGroup`'s
own bundled ones rather than left to ordinary instance search: since `meet ι₀ ι₁` is a *visible*
`Submodule` (unlike the opaque `sum`), the generic `Submodule`-subtype instances are always a
competing candidate and win by default — but `QuasiBanachCat.of`/`.ofHom` (via their
`[QuasinormedAddCommGroup _]` bracket) expect the bundled ones. Pinning here keeps this
declaration consistent with those. Do **not** unfold this definition by name in a later `simp`;
that discards the pinning and reverts to the generic route — use `meetToSum_apply` instead. -/
noncomputable def InterpolationCouple.meetToSum (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    @ContinuousLinearMap 𝕜 𝕜 _ _ (RingHom.id 𝕜)
      (InterpolationCouple.meet ι₀ ι₁)
      (InterpolationCouple.meet.quasinormedAddCommGroup ι₀ ι₁).toUniformSpace.toTopologicalSpace
      (InterpolationCouple.meet.quasinormedAddCommGroup ι₀ ι₁).toAddCommMonoid
      (InterpolationCouple.sum ι₀ ι₁) _ _ _ _ :=
  (InterpolationCouple.inl₀ ι₀ ι₁).comp
    ((ContinuousLinearMap.fst 𝕜 A₀ A₁).comp (InterpolationCouple.meet ι₀ ι₁).subtypeL)

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.meetToSum_apply (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    (a₀ : A₀) (a₁ : A₁) (ha) :
    InterpolationCouple.meetToSum ι₀ ι₁ ⟨(a₀, a₁), ha⟩ = InterpolationCouple.inl₀ ι₀ ι₁ a₀ := rfl

/-- The canonical continuous linear map `A₀ + A₁ →L[𝕜] 𝒜`, `[(a₀, a₁)] ↦ ι₀ a₀ + ι₁ a₁`: `plus`
descended to the quotient. It is injective (`sumToAmbient_injective`), since the quotient is by
exactly `ker plus`, so it identifies `A₀ + A₁` with the subspace `ι₀(A₀) + ι₁(A₁)` of `𝒜`. -/
noncomputable def InterpolationCouple.sumToAmbient (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    InterpolationCouple.sum ι₀ ι₁ →L[𝕜] 𝒜 :=
  (InterpolationCouple.plus ι₀ ι₁).ker.liftQL (InterpolationCouple.plus ι₀ ι₁) le_rfl

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
@[simp]
theorem InterpolationCouple.sumToAmbient_mk (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜)
    (a₀ : A₀) (a₁ : A₁) :
    InterpolationCouple.sumToAmbient ι₀ ι₁ (Submodule.Quotient.mk (a₀, a₁)) = ι₀ a₀ + ι₁ a₁ :=
  rfl

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.sumToAmbient_inl₀ (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₀) :
    InterpolationCouple.sumToAmbient ι₀ ι₁ (InterpolationCouple.inl₀ ι₀ ι₁ a) = ι₀ a := by
  rw [InterpolationCouple.inl₀_eq_mk, InterpolationCouple.sumToAmbient_mk, map_zero, add_zero]

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
theorem InterpolationCouple.sumToAmbient_inl₁ (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) (a : A₁) :
    InterpolationCouple.sumToAmbient ι₀ ι₁ (InterpolationCouple.inl₁ ι₀ ι₁ a) = ι₁ a := by
  rw [InterpolationCouple.inl₁_eq_mk, InterpolationCouple.sumToAmbient_mk, map_zero, zero_add]

omit [ContinuousSMul 𝕜 𝒜] [CompleteSpace A₀] [CompleteSpace A₁] in
/-- `A₀ + A₁ → 𝒜` is injective, with no hypothesis on `ι₀, ι₁`: the quotient defining the sum is
by exactly the kernel of `plus`. -/
theorem InterpolationCouple.sumToAmbient_injective (ι₀ : A₀ →L[𝕜] 𝒜) (ι₁ : A₁ →L[𝕜] 𝒜) :
    Function.Injective (InterpolationCouple.sumToAmbient ι₀ ι₁) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- Scoped notation `ι₀ ∩ᵢ ι₁` for `InterpolationCouple.meet` and `ι₀ +ᵢ ι₁` for
`InterpolationCouple.sum`, after Triebel's `A₀ ∩ A₁` / `A₀ + A₁` (Bergh–Löfström's `Δ(Ā)`,
`Σ(Ā)`). The subscript `ᵢ` ("interpolation") keeps the tokens distinct from the core `∩` and `+`:
an overloaded `+` makes plain arithmetic such as `1 + 1` ambiguous wherever the notation is open.
(Mathlib's sum of two submodules of one module is `p ⊔ q`; ours is a separate quotient type with
its own quasi-norm, merely isomorphic to `range ι₀ ⊔ range ι₁ ≤ 𝒜`.)

NOTE for later: this notation currently takes the *embedding maps* `ι₀, ι₁` as arguments, not the
Banach spaces `A₀, A₁` themselves, since nothing yet determines a canonical embedding from a type
alone. Once canonical embeddings exist for concrete spaces (e.g. `Lp` spaces embedding into `𝒟'`
or `𝒮'`), it will likely read better for this notation to apply directly to `A₀, A₁` (with the
embedding found automatically) rather than to `ι₀, ι₁` explicitly — deliberately not acted on
yet, flagged here for when that machinery exists. -/
scoped[InterpolationCouple] infixl:70 " ∩ᵢ " => InterpolationCouple.meet

/-- Scoped notation `ι₀ +ᵢ ι₁` for the sum space `InterpolationCouple.sum ι₀ ι₁`; see the
`ι₀ ∩ᵢ ι₁` notation above. -/
scoped[InterpolationCouple] infixl:65 " +ᵢ " => InterpolationCouple.sum
