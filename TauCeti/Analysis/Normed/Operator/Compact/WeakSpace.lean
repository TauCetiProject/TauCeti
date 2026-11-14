/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.WeakSpace.Closure
public import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Compact operators on bounded sets in the weak topology

A compact linear operator `J : V →L[𝕜] F` maps norm-bounded subsets of `V` into relatively compact
subsets of `F`, on which the weak topology and the original topology agree whenever `WeakSpace 𝕜 F`
is Hausdorff (`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`). Consequently, `J` is
continuous from the weak topology on any norm-bounded subset of `V` to the topology of `F`
(`IsCompactOperator.continuousOn_toWeakSpace_symm`), even for net/filter convergence without
metrizability or reflexivity assumptions on `V`.

This bounded-set weak-to-norm continuity yields:
* weak continuity and weak lower semicontinuity of nonlinear functionals `g ∘ J` on norm-bounded
  sets (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm`,
  `IsCompactOperator.lowerSemicontinuousOn_comp_toWeakSpace_symm`);
* weak closedness — and, in reflexive spaces, weak compactness — of `S ∩ J ⁻¹' C` whenever `S` is
  norm-bounded and weakly closed and `C ⊆ F` is closed
  (`IsCompactOperator.isClosed_toWeakSpace_inter_preimage`,
  `IsCompactOperator.isCompact_toWeakSpace_inter_preimage`);
* sequential weak closedness of `J ⁻¹' C` for every closed `C ⊆ F` over `ℝ` or `ℂ`
  (`IsCompactOperator.isSeqClosed_toWeakSpace_preimage`), because weakly convergent sequences are
  norm-bounded (`IsCompactOperator.isDunfordPettis`).

In contrast, on an infinite-dimensional domain `V` an injective compact operator is never globally
weak-to-norm continuous, and its unbounded level spheres `{u : V | ‖J u‖ = r}` (`0 < r`) are weakly
sequentially closed yet contain `0` in their weak closure and hence fail to be weakly closed. We
instantiate this sharp topological-versus-sequential dichotomy on `ℓ^2(ℕ, 𝕜)` using the harmonic
diagonal multiplier `lp.diagonalCLM (lp.invNatSucc 𝕜)`.

## Main results

* `IsCompactOperator.continuousOn_toWeakSpace_symm`: weak-to-norm continuity of a compact operator
  on any norm-bounded set.
* `IsCompactOperator.isCompact_toWeakSpace_inter_preimage`: weak compactness of `S ∩ J ⁻¹' C` for a
  bounded weakly closed set `S` in a reflexive space and a closed set `C`.
* `IsCompactOperator.isSeqClosed_toWeakSpace_preimage`: sequential weak closedness of `J ⁻¹' C` for
  a compact operator `J` and a norm-closed set `C`.
* `lp.isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq` and
  `lp.not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq`: for `0 < r`,
  `{u ∈ ℓ² | ‖J u‖ = r}` for the harmonic diagonal operator `J` is weakly sequentially closed yet
  not weakly closed.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Springer, 2016, §5.4.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Section 6.1 and Chapter 3.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications, II/B: Nonlinear Monotone
  Operators*, Springer, 1990, Proposition 38.2 and §38.3.
-/

public section

open Bornology Filter Function Metric NormedSpace Set Topology
open scoped lp ENNReal

namespace IsCompactOperator

section BoundedContinuity

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- If a family in `V` eventually stays in a norm-bounded set and converges weakly to `a`, then its
image under a compact operator `J` converges to `J a` in the topology of `F`. -/
theorem tendsto_of_tendsto_toWeakSpace_of_isBounded (hJ : IsCompactOperator J) {α : Type*}
    {l : Filter α} {B : Set V} (hB : IsBounded B) {u : α → V} (hu : ∀ᶠ n in l, u n ∈ B) {a : V}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) l (𝓝 (toWeakSpace 𝕜 V a))) :
    Tendsto (fun n ↦ J (u n)) l (𝓝 (J a)) := by
  obtain ⟨K, hK, hJK⟩ := hJ.image_subset_compact_of_bounded hB
  refine TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact (𝕜 := 𝕜) hK
    (hu.mono fun n hn ↦ hJK (mem_image_of_mem J hn)) ?_
  simpa only [Function.comp_def, WeakSpace.map_toWeakSpace] using
    ((WeakSpace.map J).continuous.tendsto (toWeakSpace 𝕜 V a)).comp h

/-- A compact operator `J : V →L[𝕜] F` is continuous within any subset `T ⊆ WeakSpace 𝕜 V` whose
preimage in `V` is norm-bounded, at every point `w : WeakSpace 𝕜 V`. -/
theorem continuousWithinAt_toWeakSpace_symm_of_isBounded_preimage (hJ : IsCompactOperator J)
    {T : Set (WeakSpace 𝕜 V)} (hT : IsBounded ((toWeakSpace 𝕜 V) ⁻¹' T)) (w : WeakSpace 𝕜 V) :
    ContinuousWithinAt (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z)) T w := by
  refine hJ.tendsto_of_tendsto_toWeakSpace_of_isBounded hT ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [mem_preimage, LinearEquiv.apply_symm_apply] using hz
  · have hid : (fun z : WeakSpace 𝕜 V ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm z)) = id :=
      funext (toWeakSpace 𝕜 V).apply_symm_apply
    rw [hid, LinearEquiv.apply_symm_apply]
    exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- A compact operator `J : V →L[𝕜] F` is weak-to-norm continuous on any subset of `WeakSpace 𝕜 V`
whose preimage in `V` is norm-bounded. -/
theorem continuousOn_toWeakSpace_symm_of_isBounded_preimage (hJ : IsCompactOperator J)
    {T : Set (WeakSpace 𝕜 V)} (hT : IsBounded ((toWeakSpace 𝕜 V) ⁻¹' T)) :
    ContinuousOn (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z)) T :=
  fun w _ ↦ hJ.continuousWithinAt_toWeakSpace_symm_of_isBounded_preimage hT w

/-- A compact operator `J : V →L[𝕜] F` is continuous within the weak image of any norm-bounded set
`B ⊆ V` at every point `w : WeakSpace 𝕜 V`. -/
theorem continuousWithinAt_toWeakSpace_symm (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) (w : WeakSpace 𝕜 V) :
    ContinuousWithinAt (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      (toWeakSpace 𝕜 V '' B) w :=
  hJ.continuousWithinAt_toWeakSpace_symm_of_isBounded_preimage
    (by simpa only [preimage_image_eq _ (toWeakSpace 𝕜 V).injective] using hB) w

/-- **Weak-to-norm continuity of compact operators on bounded sets.** A compact operator
`J : V →L[𝕜] F` is continuous from the weak topology on any norm-bounded set `B ⊆ V` to the
topology of `F`. -/
theorem continuousOn_toWeakSpace_symm (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B) :
    ContinuousOn (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      (toWeakSpace 𝕜 V '' B) :=
  fun w _ ↦ hJ.continuousWithinAt_toWeakSpace_symm hB w

/-- Composing a continuous map `g : F → α` on `J '' B` with a compact operator `J` gives a weakly
continuous map on any norm-bounded set `B ⊆ V`. -/
theorem continuousOn_comp_toWeakSpace_symm {α : Type*} [TopologicalSpace α]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B) {g : F → α}
    (hg : ContinuousOn g (J '' B)) :
    ContinuousOn (fun z : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm z)))
      (toWeakSpace 𝕜 V '' B) := by
  refine hg.comp (hJ.continuousOn_toWeakSpace_symm hB) ?_
  rintro _ ⟨u, hu, rfl⟩
  simpa only [LinearEquiv.symm_apply_apply] using mem_image_of_mem J hu

/-- Composing a lower semicontinuous map `g : F → β` on `J '' B` with a compact operator `J` gives a
weakly lower semicontinuous functional on any norm-bounded set `B ⊆ V`. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm {β : Type*} [Preorder β]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B) {g : F → β}
    (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn (fun z : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm z)))
      (toWeakSpace 𝕜 V '' B) := by
  refine hg.comp (hJ.continuousOn_toWeakSpace_symm hB) ?_
  rintro _ ⟨u, hu, rfl⟩
  simpa only [LinearEquiv.symm_apply_apply] using mem_image_of_mem J hu

/-- If `S ⊆ V` is norm-bounded and weakly closed, `J : V →L[𝕜] F` is compact, and `C ⊆ F` is closed,
then `S ∩ J ⁻¹' C` is closed in the weak topology. -/
theorem isClosed_toWeakSpace_inter_preimage (hJ : IsCompactOperator J) {S : Set V}
    (hS_bdd : IsBounded S) (hS_closed : IsClosed (toWeakSpace 𝕜 V '' S)) {C : Set F}
    (hC : IsClosed C) :
    IsClosed (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)) := by
  have heq : toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C) =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z)) ⁻¹' C := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_inter_iff, mem_preimage]
  rw [heq]
  exact (hJ.continuousOn_toWeakSpace_symm hS_bdd).preimage_isClosed_of_isClosed hS_closed hC

/-- In a reflexive seminormed space over a proper nontrivially normed field, if `S ⊆ V` is
norm-bounded and weakly closed, `J : V →L[𝕜] F` is compact, and `C ⊆ F` is closed, then
`S ∩ J ⁻¹' C` is weakly compact. -/
theorem isCompact_toWeakSpace_inter_preimage [ProperSpace 𝕜]
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J) {S : Set V}
    (hS_bdd : IsBounded S) (hS_closed : IsClosed (toWeakSpace 𝕜 V '' S)) {C : Set F}
    (hC : IsClosed C) :
    IsCompact (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)) := by
  have hclosed := hJ.isClosed_toWeakSpace_inter_preimage hS_bdd hS_closed hC
  have hcpt := TauCeti.isCompact_closure_toWeakSpace hV
    (hS_bdd.subset (inter_subset_left (t := J ⁻¹' C)))
  rwa [hclosed.closure_eq] at hcpt

end BoundedContinuity

section RCLikeClosedBall

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- Intersecting the preimage of a closed set `C ⊆ F` under a compact operator `J` with any closed
norm ball in `V` yields a weakly closed set. -/
theorem isClosed_toWeakSpace_closedBall_inter_preimage (hJ : IsCompactOperator J) (x : V) (r : ℝ)
    {C : Set F} (hC : IsClosed C) :
    IsClosed (toWeakSpace 𝕜 V '' (closedBall x r ∩ J ⁻¹' C)) :=
  hJ.isClosed_toWeakSpace_inter_preimage isBounded_closedBall
    (TauCeti.isClosed_toWeakSpace_closedBall x r) hC

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, intersecting the preimage of a closed set
`C ⊆ F` under a compact operator `J` with any closed norm ball in `V` yields a weakly compact set.
-/
theorem isCompact_toWeakSpace_closedBall_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J) (x : V) (r : ℝ)
    {C : Set F} (hC : IsClosed C) :
    IsCompact (toWeakSpace 𝕜 V '' (closedBall x r ∩ J ⁻¹' C)) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact hJ.isCompact_toWeakSpace_inter_preimage hV isBounded_closedBall
    (TauCeti.isClosed_toWeakSpace_closedBall x r) hC

end RCLikeClosedBall

section RCLike

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {J : V →L[𝕜] F}

/-- Along any weakly convergent sequence in `V`, a compact operator `J : V →L[𝕜] F` composed with a
map `g : F → α` continuous at `J a` converges to `g (J a)`. -/
theorem tendsto_comp_of_tendsto_toWeakSpace {α : Type*} [TopologicalSpace α]
    (hJ : IsCompactOperator J) {u : ℕ → V} {a : V}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V a)))
    {g : F → α} (hg : ContinuousAt g (J a)) :
    Tendsto (fun n ↦ g (J (u n))) atTop (𝓝 (g (J a))) :=
  hg.tendsto.comp (ContinuousLinearMap.isDunfordPettis_def.1 hJ.isDunfordPettis hu)

/-- **Sequential weak closedness of compact constraints.** For a compact operator `J : V →L[𝕜] F`
and any closed set `C ⊆ F`, `J ⁻¹' C` is sequentially closed in the weak topology on `V`, even when
`J ⁻¹' C` is unbounded and not weakly closed. -/
theorem isSeqClosed_toWeakSpace_preimage (hJ : IsCompactOperator J) {C : Set F} (hC : IsClosed C) :
    IsSeqClosed (toWeakSpace 𝕜 V '' (J ⁻¹' C)) := by
  intro w x hw hwx
  have hmem : ∀ n, J ((toWeakSpace 𝕜 V).symm (w n)) ∈ C := fun n ↦ by
    simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw n
  have hconv : Tendsto (fun n ↦ J ((toWeakSpace 𝕜 V).symm (w n))) atTop
      (𝓝 (J ((toWeakSpace 𝕜 V).symm x))) :=
    ContinuousLinearMap.isDunfordPettis_def.1 hJ.isDunfordPettis
      (by simpa only [LinearEquiv.apply_symm_apply] using hwx)
  simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using
    hC.mem_of_tendsto hconv (Eventually.of_forall hmem)

/-- For a compact operator `J : V →L[𝕜] F` over `ℝ` or `ℂ`, every level sphere
`{u : V | ‖J u‖ = r}` is sequentially closed in the weak topology. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_eq (hJ : IsCompactOperator J) (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) := by
  have hsphere : {u : V | ‖J u‖ = r} = J ⁻¹' sphere (0 : F) r := by
    ext u
    simp
  rw [hsphere]
  exact hJ.isSeqClosed_toWeakSpace_preimage isClosed_sphere

end RCLike

end IsCompactOperator

namespace lp

section HarmonicDiagonalCounterexample

variable (𝕜 : Type*) [RCLike 𝕜]

/-- On `ℓ^2(ℕ, 𝕜)`, the level sphere `{u | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}` of the compact
harmonic diagonal multiplier `n ↦ (n + 1)⁻¹` is sequentially closed in the weak topology. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq (r : ℝ) :
    IsSeqClosed
      (toWeakSpace 𝕜 ℓ^2(ℕ, 𝕜) '' {u : ℓ^2(ℕ, 𝕜) | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}) :=
  (isCompactOperator_diagonalCLM_invNatSucc 𝕜 (p := 2)).isSeqClosed_toWeakSpace_setOf_norm_eq r

/-- On `ℓ^2(ℕ, 𝕜)`, `0` belongs to the weak closure of `{u | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}`
for every `0 ≤ r`, witnessing the failure of weak topological closedness on unbounded sets. -/
theorem mem_closure_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq_zero {r : ℝ} (hr : 0 ≤ r) :
    toWeakSpace 𝕜 ℓ^2(ℕ, 𝕜) 0 ∈
      closure (toWeakSpace 𝕜 ℓ^2(ℕ, 𝕜) ''
        {u : ℓ^2(ℕ, 𝕜) | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}) :=
  (diagonalCLM (p := 2) (invNatSucc 𝕜)).mem_closure_toWeakSpace_setOf_norm_eq_zero
    (not_finite (ι := ℕ) (𝕜 := 𝕜) (p := 2)) (injective_diagonalCLM_invNatSucc 𝕜 (p := 2)) hr

/-- **Sequential weak closedness does not imply weak closedness for compact constraints.** On
`ℓ^2(ℕ, 𝕜)` for `0 < r`, `{u | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}` is weakly sequentially closed
yet not closed in the weak topology. -/
theorem not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_invNatSucc_eq {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed
        (toWeakSpace 𝕜 ℓ^2(ℕ, 𝕜) '' {u : ℓ^2(ℕ, 𝕜) | ‖diagonalCLM (invNatSucc 𝕜) u‖ = r}) :=
  (diagonalCLM (p := 2) (invNatSucc 𝕜)).not_isClosed_toWeakSpace_setOf_norm_eq
    (not_finite (ι := ℕ) (𝕜 := 𝕜) (p := 2)) (injective_diagonalCLM_invNatSucc 𝕜 (p := 2)) hr

/-- **Compact operators need not be globally weak-to-norm continuous.** On `ℓ^2(ℕ, 𝕜)`, the compact
harmonic diagonal operator `diagonalCLM (invNatSucc 𝕜)` is weak-to-norm continuous on every bounded
set (`IsCompactOperator.continuousOn_toWeakSpace_symm`) but is not globally continuous from the weak
topology to the norm topology. -/
theorem not_continuous_diagonalCLM_invNatSucc_toWeakSpace_symm :
    ¬ Continuous (fun w : WeakSpace 𝕜 ℓ^2(ℕ, 𝕜) ↦
        diagonalCLM (p := 2) (invNatSucc 𝕜) ((toWeakSpace 𝕜 ℓ^2(ℕ, 𝕜)).symm w)) :=
  (diagonalCLM (p := 2) (invNatSucc 𝕜)).not_continuous_toWeakSpace_symm
    (not_finite (ι := ℕ) (𝕜 := 𝕜) (p := 2)) (injective_diagonalCLM_invNatSucc 𝕜 (p := 2))

end HarmonicDiagonalCounterexample

end lp
