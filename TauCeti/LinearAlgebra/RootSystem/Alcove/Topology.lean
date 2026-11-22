/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.LocallyFinite
public import TauCeti.LinearAlgebra.RootSystem.Alcove.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Topology of the fundamental alcove and the affine root hyperplanes

Let `b` be a base of a finite root pairing `P` over an ordered topological ring or field `R`, with
coweight space `N`, open fundamental alcove `A` (`RootPairing.fundamentalAlcove`), and closed
fundamental alcove `Ā` (`RootPairing.closedFundamentalAlcove`). This file establishes the basic
topological properties of `A`, `Ā`, its closed faces, and the affine root-hyperplane arrangement
`H_{αⱼ,k} = {x : N | αⱼ(x) = k}` (`(j, k) : ι × ℤ`).

In the first half of the file, continuity of the root functionals (`∀ i, Continuous (P.root' i)`) is
taken as an explicit hypothesis so that the theorems apply over any ordered topological ring or
field (including `ℚ` or number fields embedded in `ℝ`, as well as arbitrary modules carrying the
module topology):
* under `[OrderClosedTopology R]`, `A` is open (for a linear order), `Ā` is closed (for any
  preorder), and every closed face `b.closedAlcoveFace J` is closed (for any partial order);
* over any linearly ordered ring with `[OrderClosedTopology R]`, the family of affine root
  hyperplanes `H_{αⱼ,k}` is locally finite, so their union is closed and its complement — the set
  of points lying on no affine root hyperplane — is open;
* over a linearly ordered topological field with `[OrderTopology R]` and continuous addition and
  scalar multiplication on `N` (`[ContinuousAdd N] [ContinuousSMul R N]`), `Ā` is the topological
  closure of `A` (by shrinking segments toward an interior point `x₀ ∈ A`), and `A` is the
  topological interior of `Ā` (by moving across any wall `aₖ(x) = 0` in the direction `-αₖ^∨`).

In the second half of the file, all of these results are specialized to a finite-dimensional
Hausdorff real topological vector space `N`, where `LinearMap.continuous_of_finiteDimensional`
discharges continuity of every root functional automatically.

## Main results

* `RootPairing.Base.continuous_affineSimpleRoot_of_continuous` and
  `RootPairing.Base.continuous_affineSimpleRoot`: every affine simple root is continuous.
* `RootPairing.isOpen_fundamentalAlcove_of_continuous` and `RootPairing.isOpen_fundamentalAlcove`:
  the open fundamental alcove is open.
* `RootPairing.isClosed_closedFundamentalAlcove_of_continuous`,
  `RootPairing.isClosed_closedFundamentalAlcove`, and `RootPairing.Base.isClosed_closedAlcoveFace`:
  the closed fundamental alcove and all of its closed faces are closed.
* `RootPairing.closure_fundamentalAlcove_of_continuous` and
  `RootPairing.closure_fundamentalAlcove`: **the closed fundamental alcove is the topological
  closure of the open fundamental alcove.**
* `RootPairing.interior_closedFundamentalAlcove_of_continuous` and
  `RootPairing.interior_closedFundamentalAlcove`: **the open fundamental alcove is the topological
  interior of the closed fundamental alcove.**
* `RootPairing.locallyFinite_setOf_root'_eq_intCast_of_continuous` and
  `RootPairing.locallyFinite_setOf_root'_eq_intCast`: **the family of affine root hyperplanes
  `{x | αⱼ(x) = k}` indexed by `ι × ℤ` is locally finite.**
* `RootPairing.isClosed_iUnion_setOf_root'_eq_intCast` and
  `RootPairing.isOpen_setOf_forall_root'_ne_intCast`: the union of the affine root hyperplanes is
  closed, and the set of points lying on no affine root hyperplane is open.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §1.1–§1.2 and Ch. VI, §2.1.
* A. Garnier, *Fundamental domains for extended affine Weyl groups* (2020), §1.3.
-/

public section

open Set Filter Topology

namespace RootPairing

/-! ### Topological properties from continuity of root functionals -/

section OrderedCommRing

variable {ι R M N : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

section Base

variable {P : RootPairing ι R M N} [CharZero R] [Finite ι] [Nonempty ι] (b : P.Base)

/-- Every affine simple root is continuous whenever `R` has characteristic zero, addition on `R` is
continuous, and the root functionals are continuous. -/
theorem Base.continuous_affineSimpleRoot_of_continuous [ContinuousAdd R]
    (hcont : ∀ i, Continuous (P.root' i)) (k : Option b.support) :
    Continuous (b.affineSimpleRoot k) := by
  have h : b.affineSimpleRoot k = fun x ↦
      P.root' (b.affineSimpleRootIndex k) x + b.affineSimpleRoot k 0 :=
    funext (b.affineSimpleRoot_eq_root'_add k)
  rw [h]
  exact (hcont _).add continuous_const

/-- The open fundamental alcove is open when every root functional is continuous. -/
theorem isOpen_fundamentalAlcove_of_continuous [LinearOrder R] [OrderClosedTopology R]
    (hcont : ∀ i, Continuous (P.root' i)) : IsOpen (fundamentalAlcove P b) := by
  rw [fundamentalAlcove_eq_biInter_inter]
  exact (isOpen_biInter_finset fun i _ ↦ isOpen_Ioi.preimage (hcont i)).inter
    (isOpen_Iio.preimage (hcont _))

/-- The closed fundamental alcove is closed when every root functional is continuous. -/
theorem isClosed_closedFundamentalAlcove_of_continuous [Preorder R] [OrderClosedTopology R]
    (hcont : ∀ i, Continuous (P.root' i)) : IsClosed (closedFundamentalAlcove P b) := by
  rw [closedFundamentalAlcove_eq_biInter_inter]
  exact (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ isClosed_Ici.preimage (hcont i)).inter
    (isClosed_Iic.preimage (hcont _))

/-- Every closed face `b.closedAlcoveFace J` of the fundamental alcove is closed when every root
functional is continuous. -/
theorem Base.isClosed_closedAlcoveFace_of_continuous [PartialOrder R] [OrderClosedTopology R]
    (hcont : ∀ i, Continuous (P.root' i)) (J : Set (Option b.support)) :
    IsClosed (b.closedAlcoveFace J) := by
  have h : b.closedAlcoveFace J =
      closedFundamentalAlcove P b ∩ ⋂ k ∈ J, b.affineSimpleRoot k ⁻¹' {0} := by
    ext x
    simp [Base.mem_closedAlcoveFace]
  rw [h]
  refine (isClosed_closedFundamentalAlcove_of_continuous b hcont).inter
    (isClosed_biInter fun k _ ↦ ?_)
  rcases k with _ | i
  · have hpre : b.affineSimpleRoot none ⁻¹' {0} = P.root' b.highestRoot ⁻¹' {1} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, Base.affineSimpleRoot_none, sub_eq_zero]
      exact eq_comm
    rw [hpre]
    exact isClosed_singleton.preimage (hcont _)
  · have hpre : b.affineSimpleRoot (some i) ⁻¹' {0} = P.root' i ⁻¹' {0} := by
      ext x
      simp
    rw [hpre]
    exact isClosed_singleton.preimage (hcont i)

end Base

section Hyperplanes

variable [LinearOrder R] [IsStrictOrderedRing R] [OrderClosedTopology R] [Finite ι]
  (P : RootPairing ι R M N)

/-- **Local finiteness of the affine root hyperplanes**: over a linearly ordered ring with an
order-closed topology, when `ι` is finite and each root functional `P.root' i` is continuous, every
point of `N` has a neighborhood meeting only finitely many affine root hyperplanes
`{x | αⱼ(x) = k}` (`(j, k) : ι × ℤ`). -/
theorem locallyFinite_setOf_root'_eq_intCast_of_continuous
    (hcont : ∀ i, Continuous (P.root' i)) :
    LocallyFinite fun p : ι × ℤ ↦ {x : N | P.root' p.1 x = p.2} := by
  let _ := Fintype.ofFinite ι
  intro x
  let U : Set N := ⋂ j : ι, P.root' j ⁻¹' Ioo (P.root' j x - 1) (P.root' j x + 1)
  have hU : U ∈ 𝓝 x := iInter_mem.mpr fun j ↦
    (isOpen_Ioo.preimage (hcont j)).mem_nhds ⟨sub_lt_self _ one_pos, lt_add_one _⟩
  refine ⟨U, hU, ?_⟩
  -- In each root direction `j`, any two integers in `(αⱼ(x) - 1, αⱼ(x) + 1)` differ by `< 2`.
  have hfin (j : ι) : {k : ℤ | (k : R) ∈ Ioo (P.root' j x - 1) (P.root' j x + 1)}.Finite := by
    by_cases hne : {k : ℤ | (k : R) ∈ Ioo (P.root' j x - 1) (P.root' j x + 1)}.Nonempty
    · obtain ⟨k₀, hk₀₁, hk₀₂⟩ := hne
      refine (Set.finite_Icc (k₀ - 1) (k₀ + 1)).subset fun k ⟨hk₁, hk₂⟩ ↦ ⟨?_, ?_⟩
      · have hlt : ((-2 : ℤ) : R) < ((k - k₀ : ℤ) : R) := by push_cast; linarith
        have := Int.cast_lt.mp hlt
        omega
      · have hlt : ((k - k₀ : ℤ) : R) < ((2 : ℤ) : R) := by push_cast; linarith
        have := Int.cast_lt.mp hlt
        omega
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  refine (Set.finite_iUnion fun j : ι ↦ (Set.finite_singleton j).prod (hfin j)).subset ?_
  rintro ⟨j, k⟩ ⟨y, hyk : P.root' j y = k, hyU⟩
  have hyj := mem_iInter.mp hyU j
  simp only [mem_preimage, hyk] at hyj
  exact mem_iUnion.mpr ⟨j, mem_prod.mpr ⟨rfl, hyj⟩⟩

/-- The union of all affine root hyperplanes is closed when the root functionals are continuous. -/
theorem isClosed_iUnion_setOf_root'_eq_intCast_of_continuous
    (hcont : ∀ i, Continuous (P.root' i)) :
    IsClosed (⋃ p : ι × ℤ, {x : N | P.root' p.1 x = p.2}) :=
  (P.locallyFinite_setOf_root'_eq_intCast_of_continuous hcont).isClosed_iUnion fun p ↦
    isClosed_singleton.preimage (hcont p.1)

/-- The set of points lying on no affine root hyperplane is open when the root functionals are
continuous. -/
theorem isOpen_setOf_forall_root'_ne_intCast_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    IsOpen {x : N | ∀ (j : ι) (k : ℤ), P.root' j x ≠ k} := by
  have h : {x : N | ∀ (j : ι) (k : ℤ), P.root' j x ≠ k} =
      (⋃ p : ι × ℤ, {x : N | P.root' p.1 x = p.2})ᶜ := by
    ext x
    simp [Prod.forall]
  rw [h]
  exact (P.isClosed_iUnion_setOf_root'_eq_intCast_of_continuous hcont).isOpen_compl

end Hyperplanes

end OrderedCommRing

section OrderedField

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [TopologicalSpace R] [OrderTopology R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] (b : P.Base)

/-- Every point of the closed fundamental alcove is a limit of points on an open segment in the
fundamental alcove; no continuity of the root functionals is required for this inclusion. -/
theorem closedFundamentalAlcove_subset_closure_fundamentalAlcove :
    closedFundamentalAlcove P b ⊆ closure (fundamentalAlcove P b) := by
  intro x hx
  obtain ⟨x₀, hx₀⟩ := fundamentalAlcove_nonempty b
  refine closure_mono ?_ (segment_subset_closure_openSegment (left_mem_segment R x x₀))
  rw [openSegment_eq_image_lineMap]
  rintro _ ⟨t, ht, rfl⟩
  exact lineMap_mem_fundamentalAlcove hx hx₀ ht.1 ht.2.le

/-- **The closed fundamental alcove is the topological closure of the open fundamental alcove.** -/
theorem closure_fundamentalAlcove_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    closure (fundamentalAlcove P b) = closedFundamentalAlcove P b :=
  Subset.antisymm
    (closure_minimal (fundamentalAlcove_subset_closedFundamentalAlcove P b)
      (isClosed_closedFundamentalAlcove_of_continuous b hcont))
    (closedFundamentalAlcove_subset_closure_fundamentalAlcove b)

/-- **The open fundamental alcove is the topological interior of the closed fundamental alcove.** -/
theorem interior_closedFundamentalAlcove_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    interior (closedFundamentalAlcove P b) = fundamentalAlcove P b := by
  refine Subset.antisymm (fun x hx ↦ ?_)
    (interior_maximal (fundamentalAlcove_subset_closedFundamentalAlcove P b)
      (isOpen_fundamentalAlcove_of_continuous b hcont))
  have hxbar : x ∈ closedFundamentalAlcove P b := interior_subset hx
  refine (mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos b).mpr fun k ↦ ?_
  have hnn := (mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg b).mp hxbar k
  refine hnn.lt_of_ne' fun hk0 ↦ ?_
  let ψ : R → N := fun t ↦ t • (-P.coroot (b.affineSimpleRootIndex k)) + x
  have hψ : Continuous ψ := (continuous_id.smul continuous_const).add continuous_const
  have h0 : (0 : R) ∈ closure (Ioi (0 : R)) := by
    rw [closure_Ioi (0 : R)]
    exact le_rfl
  have hnhds : ψ ⁻¹' interior (closedFundamentalAlcove P b) ∈ 𝓝 (0 : R) :=
    (isOpen_interior.preimage hψ).mem_nhds (by simpa [ψ] using hx)
  obtain ⟨t, htu, htpos : 0 < t⟩ := mem_closure_iff_nhds.mp h0 _ hnhds
  have htbar : ψ t ∈ closedFundamentalAlcove P b := interior_subset htu
  have hge : 0 ≤ b.affineSimpleRoot k (ψ t) :=
    (mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg b).mp htbar k
  have hval : b.affineSimpleRoot k (ψ t) = -2 * t := by
    have hx0 := (b.affineSimpleRoot_eq_root'_add k x).symm.trans hk0
    rw [b.affineSimpleRoot_eq_root'_add k (ψ t)]
    simp only [ψ, map_add, map_smul, map_neg, root'_coroot_eq_pairing, pairing_same, smul_eq_mul]
    linear_combination hx0
  linarith

end OrderedField

/-! ### Specialization over `ℝ` -/

section Real

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul ℝ N] [T2Space N]
  [FiniteDimensional ℝ N]

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, every root functional is
continuous. -/
@[fun_prop]
theorem continuous_root' (P : RootPairing ι ℝ M N) (i : ι) : Continuous (P.root' i) :=
  (P.root' i).continuous_of_finiteDimensional

section Base

variable {P : RootPairing ι ℝ M N} [Finite ι] [Nonempty ι] (b : P.Base)

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, every affine simple root
is continuous. -/
@[fun_prop]
theorem Base.continuous_affineSimpleRoot (k : Option b.support) :
    Continuous (b.affineSimpleRoot k) :=
  b.continuous_affineSimpleRoot_of_continuous P.continuous_root' k

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, the open fundamental
alcove is open. -/
theorem isOpen_fundamentalAlcove : IsOpen (fundamentalAlcove P b) :=
  isOpen_fundamentalAlcove_of_continuous b P.continuous_root'

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, the closed fundamental
alcove is closed. -/
theorem isClosed_closedFundamentalAlcove : IsClosed (closedFundamentalAlcove P b) :=
  isClosed_closedFundamentalAlcove_of_continuous b P.continuous_root'

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, every closed face of the
fundamental alcove is closed. -/
theorem Base.isClosed_closedAlcoveFace (J : Set (Option b.support)) :
    IsClosed (b.closedAlcoveFace J) :=
  b.isClosed_closedAlcoveFace_of_continuous P.continuous_root' J

/-- **Over `ℝ`, the closed fundamental alcove is the topological closure of the open fundamental
alcove.** -/
@[simp]
theorem closure_fundamentalAlcove :
    closure (fundamentalAlcove P b) = closedFundamentalAlcove P b :=
  closure_fundamentalAlcove_of_continuous b P.continuous_root'

/-- **Over `ℝ`, the open fundamental alcove is the topological interior of the closed fundamental
alcove.** -/
@[simp]
theorem interior_closedFundamentalAlcove :
    interior (closedFundamentalAlcove P b) = fundamentalAlcove P b :=
  interior_closedFundamentalAlcove_of_continuous b P.continuous_root'

end Base

/-- **Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, the family of affine
root hyperplanes `{x | αⱼ(x) = k}` (`(j, k) : ι × ℤ`) is locally finite.** -/
theorem locallyFinite_setOf_root'_eq_intCast [Finite ι] (P : RootPairing ι ℝ M N) :
    LocallyFinite fun p : ι × ℤ ↦ {x : N | P.root' p.1 x = p.2} :=
  P.locallyFinite_setOf_root'_eq_intCast_of_continuous P.continuous_root'

/-- Over `ℝ`, the union of all affine root hyperplanes is closed. -/
theorem isClosed_iUnion_setOf_root'_eq_intCast [Finite ι] (P : RootPairing ι ℝ M N) :
    IsClosed (⋃ p : ι × ℤ, {x : N | P.root' p.1 x = p.2}) :=
  P.isClosed_iUnion_setOf_root'_eq_intCast_of_continuous P.continuous_root'

/-- Over `ℝ`, the set of points lying on no affine root hyperplane is open. -/
theorem isOpen_setOf_forall_root'_ne_intCast [Finite ι] (P : RootPairing ι ℝ M N) :
    IsOpen {x : N | ∀ (j : ι) (k : ℤ), P.root' j x ≠ k} :=
  P.isOpen_setOf_forall_root'_ne_intCast_of_continuous P.continuous_root'

end Real

end RootPairing
