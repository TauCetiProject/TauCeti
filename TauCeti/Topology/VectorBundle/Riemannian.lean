/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Compactness of norm-bounded parts of a Riemannian vector bundle

In a vector bundle whose fibers carry inner products depending continuously on the base point,
the fiber norm is a continuous function on the total space.  When the model fiber is
finite-dimensional, this file proves that the vectors of norm at most `r` lying over a compact
subset of the base form a compact subset of the total space.

This is the properness statement that turns a bound on the speed of a curve in the base together
with relative compactness of its image into relative compactness of its velocity lift.  The
fibers of a bundle over a noncompact base are themselves noncompact, so the norm bound is what
makes the statement true, and the proof is local: over a compact set inside the base set of one
trivialization, the fiber norm and the model norm are comparable by
`eventually_norm_trivializationAt_lt`, and the general case follows by a finite cover.

## Main results

* `Continuous.norm_bundle`: the fiber norm of a continuous map into the fibers of a continuous
  Riemannian bundle is continuous, with `continuous_norm_bundle` its tautological case.
* `IsCompact.norm_le_bundle`: the vectors of norm at most `r` over a compact set form a compact
  subset of the total space.
-/

public section

open Bundle Filter Set
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

section Norm

variable {X : Type*} [TopologicalSpace X] {b : X → B} {v : ∀ x, E (b x)}

/-- Given a continuous map into the fibers of a continuous Riemannian bundle, its fiber norm is
a continuous function. -/
theorem Continuous.norm_bundle (hv : Continuous fun x ↦ (v x : TotalSpace F E)) :
    Continuous fun x ↦ ‖v x‖ := by
  simp only [norm_eq_sqrt_real_inner]
  exact (hv.inner_bundle hv).sqrt

variable (F E) in
/-- In a continuous Riemannian bundle, the fiber norm is a continuous function on the total
space. -/
theorem continuous_norm_bundle : Continuous fun z : TotalSpace F E ↦ ‖z.2‖ :=
  Continuous.norm_bundle (b := TotalSpace.proj) (v := fun z ↦ z.2)
    (continuous_id.congr fun z ↦ (TotalSpace.eta z).symm)

end Norm

section Compact

variable (F E) in
/-- Over a suitable neighbourhood of any point of the base, the trivialization at that point
distorts the fiber norm by at most a fixed factor. This is the local ingredient in
`IsCompact.norm_le_bundle`. -/
private theorem exists_isOpen_forall_norm_continuousLinearMapAt_le (x : B) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ (trivializationAt F E x).baseSet ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ U, ∀ w : E y, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y w‖ ≤ C * ‖w‖ := by
  obtain ⟨C, hCpos, hC⟩ := eventually_norm_trivializationAt_lt F E x
  have hbase : (trivializationAt F E x).baseSet ∈ 𝓝 x :=
    (trivializationAt F E x).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.1 (hC.and hbase)
  exact ⟨U, hUopen, hxU, fun y hy ↦ (hUsub hy).2, C, hCpos.le,
    fun y hy w ↦ ((trivializationAt F E x).continuousLinearMapAt ℝ y).le_of_opNorm_le
      (hUsub hy).1.le w⟩

variable [FiniteDimensional ℝ F]

/-- Over a compact subset of the base set of a single trivialization, the vectors of norm at most
`r` form a compact subset of the total space. -/
private theorem isCompact_norm_le_bundle_of_subset_baseSet [T2Space B] {x : B} {K : Set B}
    (hK : IsCompact K) (hKU : K ⊆ (trivializationAt F E x).baseSet) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ K, ∀ w : E y, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y w‖ ≤ C * ‖w‖)
    (r : ℝ) : IsCompact {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.2‖ ≤ r} := by
  set e := trivializationAt F E x
  have hclosed : IsClosed {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.2‖ ≤ r} :=
    (hK.isClosed.preimage (FiberBundle.continuous_proj F E)).inter
      (isClosed_le (continuous_norm_bundle F E) continuous_const)
  have hprod : IsCompact ((K ×ˢ Metric.closedBall (0 : F) (C * r))) :=
    hK.prod (isCompact_closedBall (0 : F) (C * r))
  have hsubset : K ×ˢ Metric.closedBall (0 : F) (C * r) ⊆ e.baseSet ×ˢ (univ : Set F) :=
    fun q hq ↦ ⟨hKU hq.1, mem_univ _⟩
  have himage : IsCompact ((fun q : B × F ↦ TotalSpace.mk' F q.1 (e.symm q.1 q.2)) ''
      (K ×ˢ Metric.closedBall (0 : F) (C * r))) :=
    hprod.image_of_continuousOn (e.continuousOn_symm.mono hsubset)
  refine himage.of_isClosed_subset hclosed ?_
  rintro z ⟨hz1, hz2⟩
  have hsymm : e.symm z.proj (e.continuousLinearMapAt ℝ z.proj z.2) = z.2 :=
    (e.symmL_apply (R := ℝ) (hKU hz1) (e.continuousLinearMapAt ℝ z.proj z.2)).symm.trans
      (e.symmL_continuousLinearMapAt (hKU hz1) z.2)
  refine ⟨(z.proj, e.continuousLinearMapAt ℝ z.proj z.2), ⟨hz1, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC z.proj hz1 z.2).trans (by gcongr)
  · simp only [hsymm]

/-- **The norm-bounded part of a Riemannian bundle over a compact set is compact.** In a
continuous Riemannian vector bundle with finite-dimensional model fiber, the vectors of norm at
most `r` lying over a compact subset of the base form a compact subset of the total space. -/
theorem IsCompact.norm_le_bundle [T2Space B] {K : Set B} (hK : IsCompact K) (r : ℝ) :
    IsCompact {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.2‖ ≤ r} := by
  choose U hUopen hxU hUsub C hC0 hC using exists_isOpen_forall_norm_continuousLinearMapAt_le F E
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen fun y _ ↦ mem_iUnion.2 ⟨y, hxU y⟩
  obtain ⟨K', hK'compact, hK'sub, hK'eq⟩ :=
    hK.finite_compact_cover t U (fun i _ ↦ hUopen i) ht
  have hsplit : {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.2‖ ≤ r} =
      ⋃ i ∈ t, {z : TotalSpace F E | z.proj ∈ K' i ∧ ‖z.2‖ ≤ r} := by
    ext z
    simp only [Set.mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz1, hz2⟩
      rw [hK'eq] at hz1
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz1
      exact ⟨i, hi, hzi, hz2⟩
    · rintro ⟨i, hi, hzi, hz2⟩
      exact ⟨hK'eq ▸ mem_biUnion hi hzi, hz2⟩
  rw [hsplit]
  exact t.isCompact_biUnion fun i _ ↦
    isCompact_norm_le_bundle_of_subset_baseSet (hK'compact i) ((hK'sub i).trans (hUsub i)) (hC0 i)
      (fun y hy w ↦ hC i y (hK'sub i hy) w) r

end Compact
