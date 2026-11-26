/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Corners.Depth

import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# The depth strata of a manifold with corners

A manifold with corners `M` modelled on a real model `I` is partitioned by the depth of its points
(`ModelWithCorners.depth`): its *depth-`k` stratum* `I.depthStratum M k := {x : M | I.depth x = k}`
is the set of points of depth `k`. The depth-zero stratum is the interior and is open; on a manifold
with boundary modelled on the half-space the depth-one stratum is the boundary, and there are no
strata of depth greater than one. The strata of higher depth are the edges and vertices of the
corners: on the cube `[0, 1]³` the strata of depth `0, 1, 2, 3` are the open cube, the six open
faces, the twelve open edges and the eight vertices.

This file defines `ModelWithCorners.depthStratum` and establishes its partition, functorial,
product, countability, and local-closedness properties, together with concrete characterizations on
the half-space and quadrant models. When `I` is (up to a continuous linear equivalence) a
coordinate-region model `{z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}`, upper semicontinuity of the
depth (`ModelWithCorners.isOpen_setOf_depth_le_of_range_eq`) implies that each depth stratum is
locally closed (`ModelWithCorners.isLocallyClosed_depthStratum_of_range_eq`).

For the boundaryless smooth manifold structure on each depth stratum `↥(J.depthStratum M k)` of any
coordinate-region model `J`, see `TauCeti.Geometry.Manifold.Corners.Stratum.Manifold`.

## Main definitions

* `ModelWithCorners.depthStratum`: the depth-`k` stratum `{x : M | I.depth x = k}` of a manifold
  with corners.

## Main results

* `ModelWithCorners.iUnion_depthStratum`, `ModelWithCorners.pairwise_disjoint_depthStratum`,
  `ModelWithCorners.depthStratum_eq_empty_of_finrank_lt`: the strata partition the manifold, and
  only the strata of depth at most its dimension are nonempty.
* `ModelWithCorners.depthStratum_zero`, `ModelWithCorners.isOpen_depthStratum_zero`,
  `ModelWithCorners.depthStratum_eq_empty_of_boundaryless`,
  `ModelWithCorners.depthStratum_zero_of_boundaryless`: the depth-zero stratum is the interior (open
  on any `C^r` manifold with `r ≠ 0`), and boundaryless manifolds have only the depth-zero stratum.
* `ModelWithCorners.depthStratum_transContinuousLinearEquiv`,
  `ModelWithCorners.depthStratum_prod`, `Diffeomorph.preimage_depthStratum`,
  `Diffeomorph.image_depthStratum`: invariance under linear coordinate changes and diffeomorphisms,
  and the product decomposition.
* `ModelWithCorners.secondCountableTopology_depthStratum`,
  `ModelWithCorners.lindelofSpace_depthStratum`: second-countability and Lindelöfness of every
  depth stratum of a Lindelöf manifold over a second-countable model space.
* `ModelWithCorners.isLocallyClosed_depthStratum_of_range_eq`,
  `ModelWithCorners.isLocallyClosed_depthStratum_of_image_range_eq`: local closedness of depth
  strata on coordinate-region models and models linearly equivalent to them.
* Concrete characterizations for manifolds modelled on `EuclideanHalfSpace n` and points of
  `EuclideanHalfSpace n` and `EuclideanQuadrant n` (`n : ℕ`).

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (depth strata `S^k(X)`).
  [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
* Formal foundations in this library: `TauCeti.Geometry.Manifold.Corners.Depth` (intrinsic `depth`,
  `depthAt`, and upper semicontinuity of depth).
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

/-! ### Definition, partition, functorial, product, and countability properties -/

section Basic

variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The **depth-`k` stratum** of a manifold with corners `M`: the set of its points of depth `k`
(`ModelWithCorners.depth`). -/
def depthStratum (k : ℕ) : Set M :=
  {x | I.depth x = k}

variable {I I' M}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Explicit set description of `depthStratum`. -/
theorem depthStratum_def (k : ℕ) : I.depthStratum M k = {x | I.depth x = k} :=
  (rfl)

/-- A point belongs to the depth-`k` stratum iff its depth is `k`. -/
@[simp, grind =]
theorem mem_depthStratum {k : ℕ} {x : M} : x ∈ I.depthStratum M k ↔ I.depth x = k :=
  (Iff.rfl)

/-- A point of the depth-`k` stratum has depth `k`. -/
@[simp, grind =]
theorem depth_subtypeVal_depthStratum {k : ℕ} (p : I.depthStratum M k) : I.depth (p : M) = k :=
  p.prop

/-- Every point lies in the stratum of its depth. -/
@[simp]
theorem iUnion_depthStratum : ⋃ k, I.depthStratum M k = univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨I.depth x, rfl⟩

/-- Distinct depth strata are disjoint. -/
theorem pairwise_disjoint_depthStratum : Pairwise (Disjoint on I.depthStratum M) :=
  fun _ _ hkl ↦ disjoint_left.2 fun _ hk hl ↦ hkl (hk.symm.trans hl)

/-- There are no points of depth larger than the dimension of the model. -/
theorem depthStratum_eq_empty_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    I.depthStratum M k = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := depth_le_finrank (I := I) x
    rw [mem_depthStratum] at hx
    omega

/-- The depth-zero stratum is the interior. -/
@[simp]
theorem depthStratum_zero [FiniteDimensional ℝ E] : I.depthStratum M 0 = I.interior M := by
  ext x
  simp [ModelWithCorners.interior]

/-- The depth-zero stratum of a `C^r` manifold, `r ≠ 0`, is open. -/
theorem isOpen_depthStratum_zero [FiniteDimensional ℝ E] {r : WithTop ℕ∞} [IsManifold I r M]
    (hr : r ≠ 0) : IsOpen (I.depthStratum M 0) :=
  depthStratum_zero (I := I) (M := M) ▸ I.isOpen_interior hr

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

/-! ### Local closedness on coordinate-region models -/

section Topology

variable {ι : Type*} [Fintype ι] {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On a manifold modelled on `{z | ∀ i ∈ S, 0 ≤ z i}`, every depth stratum beyond `Nat.card S` is
empty. -/
theorem depthStratum_eq_empty_of_natCard_lt_of_range_eq
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) {k : ℕ} (hk : Nat.card S < k) :
    J.depthStratum M k = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  have := depth_le_natCard_of_range_eq hJ x
  rw [mem_depthStratum] at hx
  omega

/-- Every depth stratum of a `C^n` manifold (`n ≠ 0`) modelled on `{z | ∀ i ∈ S, 0 ≤ z i}` is
locally closed (an intersection of an open set and a closed set). -/
theorem isLocallyClosed_depthStratum_of_range_eq {n : WithTop ℕ∞} [IsManifold J n M] (hn : n ≠ 0)
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

/-- On a manifold modelled on the half-space, the depth-one stratum is the boundary. -/
@[simp]
theorem depthStratum_modelWithCornersEuclideanHalfSpace_one {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] :
    (𝓡∂ n).depthStratum M 1 = (𝓡∂ n).boundary M := by
  ext x
  simp [ModelWithCorners.boundary]

/-- On a manifold modelled on the half-space, there are no strata of depth larger than one. -/
theorem depthStratum_modelWithCornersEuclideanHalfSpace_eq_empty_of_one_lt {k : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] (hk : 1 < k) :
    (𝓡∂ n).depthStratum M k = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := depth_modelWithCornersEuclideanHalfSpace_le_one (n := n) x
    rw [mem_depthStratum] at hx
    omega

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
