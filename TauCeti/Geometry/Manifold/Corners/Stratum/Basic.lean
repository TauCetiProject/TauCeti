/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Corners.Stratum

import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Depth strata of a manifold with corners: topology and coordinate-region properties

For a manifold `M` modelled on a real model with corners `I`,
`TauCeti.Geometry.Manifold.Corners.Stratum` defines the *depth-`k` stratum*
`I.depthStratum M k := {x : M | I.depth x = k}` and establishes its basic partition properties
(`ModelWithCorners.iUnion_depthStratum`, `ModelWithCorners.pairwise_disjoint_depthStratum`,
`ModelWithCorners.depthStratum_zero`) together with the quadrant manifold structure. This file
develops general topological, functorial, and product properties of `ModelWithCorners.depthStratum`,
and establishes upper semicontinuity of the depth on arbitrary coordinate-region models.

When `I` is a coordinate-region model `range I = {z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}`
(such as the quadrant `𝓡c n` with `S = univ`, the half-space `𝓡∂ n` with `S = {0}`, or via a
continuous linear equivalence any finite product of such models), the depth is upper semicontinuous
on any `C^1` manifold: near a point `x`, coordinates in `S` that are positive in a chart remain
positive, so points near `x` have depth at most `I.depth x`
(`ModelWithCorners.isOpen_setOf_depth_le_of_range_eq`). Consequently `{x | k ≤ I.depth x}` is
closed and each depth stratum `I.depthStratum M k` is locally closed
(`ModelWithCorners.isLocallyClosed_depthStratum_of_range_eq`).

For the boundaryless smooth manifold structure on each depth stratum `↥(J.depthStratum M k)` of any
coordinate-region model `J`, see `TauCeti.Geometry.Manifold.Corners.Stratum.Manifold`.

## Main results

* `ModelWithCorners.depthStratum_eq_empty_of_boundaryless`,
  `ModelWithCorners.depthStratum_zero_of_boundaryless`,
  `ModelWithCorners.iUnion_depthStratum_eq_univ`: boundaryless strata and the finite cover indexed
  by `Fin (finrank ℝ E + 1)`.
* `ModelWithCorners.depthStratum_transContinuousLinearEquiv`,
  `ModelWithCorners.depthStratum_prod`, `Diffeomorph.image_depthStratum`: invariance under linear
  coordinate changes and diffeomorphisms, and the product decomposition.
* `ModelWithCorners.secondCountableTopology_depthStratum`,
  `ModelWithCorners.lindelofSpace_depthStratum`: second-countability and Lindelöfness of every
  depth stratum of a Lindelöf manifold over a second-countable model space.
* `ModelWithCorners.depthAt_le_of_forall_pos`, `ModelWithCorners.depthAt_eq_iff_of_forall_pos`:
  monotone behaviour and equality criterion for `depthAt` under positivity preservation.
* `ModelWithCorners.isOpen_setOf_depth_le_of_range_eq`,
  `ModelWithCorners.isClosed_setOf_le_depth_of_range_eq`,
  `ModelWithCorners.isLocallyClosed_depthStratum_of_range_eq`: upper semicontinuity of `depth` and
  local closedness of depth strata (with linear-equivalence transfers `*_of_image_range_eq`).
* Concrete coordinate characterizations for `EuclideanHalfSpace n` and `EuclideanQuadrant n`
  (`n : ℕ`).

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (depth strata `S^k(X)`).
  [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
* Formal foundations in this library: `TauCeti.Geometry.Manifold.Corners.Depth` (intrinsic `depth`
  and `depthAt`) and `TauCeti.Geometry.Manifold.Corners.Stratum` (`ModelWithCorners.depthStratum`).
-/

public section

noncomputable section

open Set Function Module Topology
open scoped Manifold ContDiff

namespace ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners ℝ E' H')

/-! ### Functorial, product, and countability properties of depth strata -/

section Basic

variable {I I'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- On a boundaryless finite-dimensional manifold, every stratum of positive depth is empty. -/
theorem depthStratum_eq_empty_of_boundaryless [BoundarylessManifold I M] [FiniteDimensional ℝ E]
    {k : ℕ} (hk : k ≠ 0) : I.depthStratum M k = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ hk ?_
  rw [mem_depthStratum] at hx
  rw [← hx, depth_eq_zero_iff]
  exact BoundarylessManifold.isInteriorPoint

/-- On a boundaryless finite-dimensional manifold, the depth-`0` stratum is the whole manifold. -/
theorem depthStratum_zero_of_boundaryless [BoundarylessManifold I M] [FiniteDimensional ℝ E] :
    I.depthStratum M 0 = univ := by
  rw [depthStratum_zero]
  exact I.interior_eq_univ

/-- The depth strata of depths `0, …, dim E` cover the manifold. -/
theorem iUnion_depthStratum_eq_univ :
    ⋃ k : Fin (finrank ℝ E + 1), I.depthStratum M k = univ := by
  refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
  exact ⟨⟨I.depth x, Nat.lt_succ_of_le (I.depth_le_finrank x)⟩, mem_depthStratum.2 rfl⟩

/-- A continuous linear change of model coordinates leaves every depth stratum unchanged. -/
@[simp]
theorem depthStratum_transContinuousLinearEquiv [FiniteDimensional ℝ E] (e : E ≃L[ℝ] E')
    (k : ℕ) : (I.transContinuousLinearEquiv e).depthStratum M k = I.depthStratum M k := by
  ext x
  simp

/-- A point of a product manifold lies in the depth-`k` stratum iff the depths of its coordinates
sum to `k`. -/
theorem mem_depthStratum_prod_iff [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    {k : ℕ} {x : M} {x' : N} :
    (x, x') ∈ (I.prod I').depthStratum (M × N) k ↔ I.depth x + I'.depth x' = k := by
  simp

/-- The depth-`k` stratum of a product manifold is the union of products of strata whose depths sum
to `k`. -/
theorem depthStratum_prod [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] (k : ℕ) :
    (I.prod I').depthStratum (M × N) k =
      ⋃ (a : ℕ) (b : ℕ) (_ : a + b = k), I.depthStratum M a ×ˢ I'.depthStratum N b := by
  ext ⟨x, x'⟩
  simp only [mem_depthStratum, depth_prod, mem_iUnion, mem_prod]
  constructor
  · intro h
    exact ⟨I.depth x, I'.depth x', h, rfl, rfl⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact hab

/-- The depth-`0` stratum of a product manifold is the product of the depth-`0` strata. -/
theorem depthStratum_prod_zero [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] :
    (I.prod I').depthStratum (M × N) 0 = I.depthStratum M 0 ×ˢ I'.depthStratum N 0 := by
  ext ⟨x, x'⟩
  simp only [mem_depthStratum, mem_prod, depth_prod, add_eq_zero]

variable (I) in
/-- Every depth stratum of a Lindelöf manifold over a second-countable model space is second
countable. -/
theorem secondCountableTopology_depthStratum [SecondCountableTopology E] [LindelofSpace M]
    (k : ℕ) : SecondCountableTopology ↥(I.depthStratum M k) := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof H M
  infer_instance

variable (I) in
/-- Every depth stratum of a Lindelöf manifold over a second-countable model space is Lindelöf. -/
theorem lindelofSpace_depthStratum [SecondCountableTopology E] [LindelofSpace M] (k : ℕ) :
    LindelofSpace ↥(I.depthStratum M k) := by
  have : SecondCountableTopology ↥(I.depthStratum M k) :=
    I.secondCountableTopology_depthStratum (M := M) k
  infer_instance

end Basic

/-! ### Coordinate-region depth inequalities and upper semicontinuity -/

section Topology

variable {ι : Type*} [Fintype ι] {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}

/-- At a point `z` of `{w | ∀ i ∈ S, 0 ≤ w i}` where every coordinate of `S` positive at `y`
remains positive, the depth at `z` is at most the depth at `y`. -/
theorem depthAt_le_of_forall_pos (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {y z : EuclideanSpace ℝ ι} (hy : y ∈ range J) (hz : z ∈ range J)
    (hpos : ∀ i ∈ S, y i ≠ 0 → 0 < z i) :
    J.depthAt z ≤ J.depthAt y := by
  rw [depthAt_eq_natCard_of_range_eq hJ hy, depthAt_eq_natCard_of_range_eq hJ hz]
  refine Nat.card_le_card_of_injective
    (fun j : {i // i ∈ S ∧ z i = 0} ↦
      (⟨j.val, j.property.1, by_contra fun hy0 ↦ (hpos j.val j.property.1 hy0).ne' j.property.2⟩ :
        {i // i ∈ S ∧ y i = 0}))
    (fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : {i // i ∈ S ∧ y i = 0} → ι) h))

/-- Under the positivity condition of `depthAt_le_of_forall_pos`, equality of depths holds exactly
when every coordinate of `S` vanishing at `y` also vanishes at `z`. -/
theorem depthAt_eq_iff_of_forall_pos (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {y z : EuclideanSpace ℝ ι} (hy : y ∈ range J) (hz : z ∈ range J)
    (hpos : ∀ i ∈ S, y i ≠ 0 → 0 < z i) :
    J.depthAt z = J.depthAt y ↔ ∀ i ∈ S, y i = 0 → z i = 0 := by
  classical
  let A : Finset ι := Finset.univ.filter fun i ↦ i ∈ S ∧ z i = 0
  let B : Finset ι := Finset.univ.filter fun i ↦ i ∈ S ∧ y i = 0
  have hAB : A ⊆ B := fun i hi ↦ by
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, by_contra fun hy0 ↦ (hpos i hi.1 hy0).ne' hi.2⟩
  have hcardA : J.depthAt z = A.card := by
    rw [depthAt_eq_natCard_of_range_eq hJ hz, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardB : J.depthAt y = B.card := by
    rw [depthAt_eq_natCard_of_range_eq hJ hy, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcardA, hcardB]
  constructor
  · intro h i hiS hyi
    have hBA : A = B := Finset.eq_of_subset_of_card_le hAB h.ge
    have hiA : i ∈ A := hBA ▸ (by simp [B, hiS, hyi])
    exact (Finset.mem_filter.1 hiA).2.2
  · intro h
    refine congrArg Finset.card (Finset.Subset.antisymm hAB fun i hi ↦ ?_)
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, h i hi.1 hi.2⟩

variable {M : Type*} [TopologicalSpace M]

/-- Inside the source of an open partial homeomorphism `e : OpenPartialHomeomorph M H`, the subset
where every coordinate in `S` nonzero at `e.extend J x` stays strictly positive is open in `M`. -/
theorem isOpen_setOf_forall_extend_pos (J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H)
    (S : Set ι) (e : OpenPartialHomeomorph M H) (x : M) :
    IsOpen {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} := by
  have hset : {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} =
      e.source ∩ ⋂ j : {j : ι // j ∈ S ∧ e.extend J x j ≠ 0},
        (fun q ↦ e.extend J q j.val) ⁻¹' Ioi 0 := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_Ioi, Subtype.forall]
    exact ⟨fun ⟨hq, h⟩ ↦ ⟨hq, fun j hj ↦ h j hj.1 hj.2⟩,
      fun ⟨hq, h⟩ ↦ ⟨hq, fun j hj hx0 ↦ h j ⟨hj, hx0⟩⟩⟩
  rw [hset]
  refine isOpen_iff_mem_nhds.2 fun q ⟨hq, hpos⟩ ↦ ?_
  have hcont (j : {j : ι // j ∈ S ∧ e.extend J x j ≠ 0}) :
      ContinuousAt (fun p ↦ e.extend J p j.val) q :=
    (EuclideanSpace.proj j.val : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.continuousAt.comp
      (J.continuous.continuousAt.comp (e.continuousAt hq))
  refine Filter.inter_mem (e.open_source.mem_nhds hq) ?_
  rw [Filter.iInter_mem]
  intro j
  exact (hcont j).preimage_mem_nhds (isOpen_Ioi.mem_nhds (mem_iInter.1 hpos j))

/-- A point `x ∈ e.source` belongs to the positive slice of `e` defined at `x`. -/
theorem mem_setOf_forall_extend_pos_self (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    x ∈ {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j} := by
  refine ⟨hx, fun j hj hne ↦ ?_⟩
  have hmem : e.extend J x ∈ range J := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  rw [hJ] at hmem
  exact lt_of_le_of_ne (hmem j hj) hne.symm

variable [ChartedSpace H M]

/-- On a manifold modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, every depth stratum beyond `Nat.card S` is
empty. -/
theorem depthStratum_eq_empty_of_natCard_lt_of_range_eq
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (hk : Nat.card S < k) :
    J.depthStratum M k = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  have := depth_le_natCard_of_range_eq hJ x
  rw [mem_depthStratum] at hx
  omega

variable {n : WithTop ℕ∞}

/-- **Upper semicontinuity of depth** for coordinate-region models: on a `C^n` manifold (`n ≠ 0`)
modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, the points of depth at most `k` form an open set. -/
theorem isOpen_setOf_depth_le_of_range_eq [IsManifold J n M] (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsOpen {x : M | J.depth x ≤ k} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  let e := chartAt H x
  let U := {q ∈ e.source | ∀ j ∈ S, e.extend J x j ≠ 0 → 0 < e.extend J q j}
  refine ⟨U, ?_, isOpen_setOf_forall_extend_pos J S e x,
    mem_setOf_forall_extend_pos_self hJ (mem_chart_source H x)⟩
  intro q ⟨hq, hpos⟩
  have hxe : x ∈ e.source := mem_chart_source H x
  have he : e ∈ IsManifold.maximalAtlas J n M := IsManifold.chart_mem_maximalAtlas x
  rw [mem_ofPred_eq, ← depthAt_extend_eq_depth hn he hq]
  have hle := depthAt_le_of_forall_pos hJ
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
    (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _) hpos
  rw [depthAt_extend_eq_depth hn he hxe] at hle
  exact hle.trans hx

/-- On a `C^n` manifold (`n ≠ 0`) modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, the points of depth at
least `k` form a closed set. -/
theorem isClosed_setOf_le_depth_of_range_eq [IsManifold J n M] (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsClosed {x : M | k ≤ J.depth x} := by
  cases k with
  | zero =>
    have : {x : M | 0 ≤ J.depth x} = univ := eq_univ_of_forall fun _ ↦ Nat.zero_le _
    rw [this]
    exact isClosed_univ
  | succ m =>
    have : {x : M | m + 1 ≤ J.depth x} = {x : M | J.depth x ≤ m}ᶜ := by
      ext x
      simp
    rw [this]
    exact (isOpen_setOf_depth_le_of_range_eq hn hJ m).isClosed_compl

/-- Every depth stratum of a `C^n` manifold (`n ≠ 0`) modelled on `{z | ∀ i ∈ S, 0 ≤ z i}` is
locally closed (an intersection of an open set and a closed set). -/
theorem isLocallyClosed_depthStratum_of_range_eq [IsManifold J n M] (hn : n ≠ 0)
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsLocallyClosed (J.depthStratum M k) := by
  have hEq : J.depthStratum M k = {x : M | J.depth x ≤ k} ∩ {x : M | k ≤ J.depth x} := by
    ext x
    simp [le_antisymm_iff]
  rw [hEq]
  exact (isOpen_setOf_depth_le_of_range_eq hn hJ k).isLocallyClosed.inter
    (isClosed_setOf_le_depth_of_range_eq hn hJ k).isLocallyClosed

end Topology

section TopologyEquiv

variable {ι : Type*} [Finite ι] {S : Set ι}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- **Upper semicontinuity of depth** for any model linearly equivalent to a coordinate region
`{z | ∀ i ∈ S, 0 ≤ z i}`. -/
theorem isOpen_setOf_depth_le_of_image_range_eq {I : ModelWithCorners ℝ E H} [IsManifold I n M]
    (hn : n ≠ 0) (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsOpen {x : M | I.depth x ≤ k} := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have heq : {x : M | I.depth x ≤ k} =
      {x : M | (I.transContinuousLinearEquiv e).depth x ≤ k} := by
    ext x
    simp
  rw [heq]
  exact isOpen_setOf_depth_le_of_range_eq hn
    (by rwa [I.transContinuousLinearEquiv_range]) k

/-- For any model linearly equivalent to a coordinate region, `{x | k ≤ I.depth x}` is closed. -/
theorem isClosed_setOf_le_depth_of_image_range_eq {I : ModelWithCorners ℝ E H} [IsManifold I n M]
    (hn : n ≠ 0) (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsClosed {x : M | k ≤ I.depth x} := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have heq : {x : M | k ≤ I.depth x} =
      {x : M | k ≤ (I.transContinuousLinearEquiv e).depth x} := by
    ext x
    simp
  rw [heq]
  exact isClosed_setOf_le_depth_of_range_eq hn
    (by rwa [I.transContinuousLinearEquiv_range]) k

/-- For any model linearly equivalent to a coordinate region, every depth stratum is locally
closed. -/
theorem isLocallyClosed_depthStratum_of_image_range_eq {I : ModelWithCorners ℝ E H}
    [IsManifold I n M] (hn : n ≠ 0) (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) (k : ℕ) :
    IsLocallyClosed (I.depthStratum M k) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  rw [← depthStratum_transContinuousLinearEquiv (I := I) e k]
  exact isLocallyClosed_depthStratum_of_range_eq hn
    (by rwa [I.transContinuousLinearEquiv_range]) k

end TopologyEquiv

/-! ### Concrete half-space and quadrant characterizations -/

section ConcreteModels

variable {n : ℕ}

section HalfSpace

variable [NeZero n]

/-- A point of `EuclideanHalfSpace n` has depth `0` iff its zeroth coordinate is positive. -/
theorem mem_depthStratum_euclideanHalfSpace_zero_iff {x : EuclideanHalfSpace n} :
    x ∈ (𝓡∂ n).depthStratum (EuclideanHalfSpace n) 0 ↔ 0 < x.val 0 := by
  rw [mem_depthStratum, depth_def, extChartAt_self_apply,
    depthAt_modelWithCornersEuclideanHalfSpace (mem_range_self x)]
  by_cases h : x.val 0 = 0
  · simp [h]
  · simpa [h] using lt_of_le_of_ne x.property (Ne.symm h)

/-- A point of `EuclideanHalfSpace n` has depth `1` iff its zeroth coordinate vanishes. -/
theorem mem_depthStratum_euclideanHalfSpace_one_iff {x : EuclideanHalfSpace n} :
    x ∈ (𝓡∂ n).depthStratum (EuclideanHalfSpace n) 1 ↔ x.val 0 = 0 := by
  rw [mem_depthStratum, depth_def, extChartAt_self_apply,
    depthAt_modelWithCornersEuclideanHalfSpace (mem_range_self x)]
  by_cases h : x.val 0 = 0 <;> simp [h]

end HalfSpace

section Quadrant

/-- A point of `EuclideanQuadrant n` lies in the depth-`k` stratum iff exactly `k` of its
coordinates vanish. -/
theorem mem_depthStratum_euclideanQuadrant_iff {k : ℕ} {x : EuclideanQuadrant n} :
    x ∈ (𝓡c n).depthStratum (EuclideanQuadrant n) k ↔ Nat.card {i : Fin n // x.val i = 0} = k := by
  rw [mem_depthStratum, depth_def, extChartAt_self_apply,
    depthAt_modelWithCornersEuclideanQuadrant (mem_range_self x)]
  rfl

/-- A point of `EuclideanQuadrant n` has depth `0` iff all of its coordinates are strictly
positive. -/
theorem mem_depthStratum_euclideanQuadrant_zero_iff {x : EuclideanQuadrant n} :
    x ∈ (𝓡c n).depthStratum (EuclideanQuadrant n) 0 ↔ ∀ i : Fin n, 0 < x.val i := by
  rw [mem_depthStratum_euclideanQuadrant_iff, Nat.card_eq_zero]
  have hfin : ¬ Infinite {i : Fin n // x.val i = 0} := not_infinite_iff_finite.2 inferInstance
  rw [or_iff_left hfin]
  constructor
  · intro hempty i
    exact lt_of_le_of_ne (x.property i) fun h ↦ hempty.false ⟨i, h.symm⟩
  · intro hpos
    exact ⟨fun ⟨i, hi⟩ ↦ (hpos i).ne' hi⟩

/-- A point of `EuclideanQuadrant n` has depth `1` iff exactly one of its coordinates vanishes. -/
theorem mem_depthStratum_euclideanQuadrant_one_iff {x : EuclideanQuadrant n} :
    x ∈ (𝓡c n).depthStratum (EuclideanQuadrant n) 1 ↔ ∃! i : Fin n, x.val i = 0 := by
  rw [mem_depthStratum_euclideanQuadrant_iff, Nat.card_eq_one_iff_exists]
  constructor
  · rintro ⟨⟨i, hi⟩, huniq⟩
    exact ⟨i, hi, fun j hj ↦ congrArg Subtype.val (huniq ⟨j, hj⟩)⟩
  · rintro ⟨i, hi, huniq⟩
    exact ⟨⟨i, hi⟩, fun ⟨j, hj⟩ ↦ Subtype.ext (huniq j hj)⟩

/-- A point of `EuclideanQuadrant n` has depth `n` iff all of its coordinates vanish. -/
theorem mem_depthStratum_euclideanQuadrant_self_iff {x : EuclideanQuadrant n} :
    x ∈ (𝓡c n).depthStratum (EuclideanQuadrant n) n ↔ ∀ i : Fin n, x.val i = 0 := by
  classical
  rw [mem_depthStratum_euclideanQuadrant_iff, Nat.card_eq_fintype_card, Fintype.card_subtype]
  constructor
  · intro hcard i
    have hall : Finset.univ.filter (fun j : Fin n ↦ x.val j = 0) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hcard)
    have hi : i ∈ Finset.univ.filter (fun j : Fin n ↦ x.val j = 0) := by
      rw [hall]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.1 hi).2
  · intro hzero
    have hall : Finset.univ.filter (fun j : Fin n ↦ x.val j = 0) = Finset.univ := by
      ext i
      simp [hzero i]
    simp [hall]

end Quadrant

end ConcreteModels

end ModelWithCorners

section Maps

open ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

/-- The preimage of a depth stratum under a `C^n` diffeomorphism (`n ≠ 0`) is the corresponding
depth stratum. -/
@[simp]
theorem Diffeomorph.preimage_depthStratum (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) (k : ℕ) :
    Φ ⁻¹' I'.depthStratum N k = I.depthStratum M k := by
  ext x
  simp [Φ.depth_eq hn]

/-- A `C^n` diffeomorphism (`n ≠ 0`) carries each depth stratum onto the corresponding depth
stratum. -/
@[simp]
theorem Diffeomorph.image_depthStratum (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) (k : ℕ) :
    Φ '' I.depthStratum M k = I'.depthStratum N k := by
  ext y
  simp only [mem_image, mem_depthStratum]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ (Φ.depth_eq hn x).trans hx,
    fun hy ↦ ⟨Φ.symm y, (Φ.symm.depth_eq hn y).trans hy, Φ.apply_symm_apply y⟩⟩

end Maps
