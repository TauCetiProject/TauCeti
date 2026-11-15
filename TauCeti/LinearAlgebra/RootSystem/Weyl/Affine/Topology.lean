/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.LocallyFinite
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.FundamentalDomain
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
* `A` is open, `Ā` and every closed face `b.closedAlcoveFace J` are closed;
* over a linearly ordered topological field, `Ā` is the topological closure of `A` (by shrinking
  segments toward an interior point `x₀ ∈ A`), and `A` is the topological interior of `Ā` (by
  moving across any wall `aₖ(x) = 0` in the direction `-αₖ^∨`);
* over an archimedean linearly ordered topological ring, the family of affine root hyperplanes
  `H_{αⱼ,k}` is locally finite, so their union is closed and the complement — the set of alcove
  interior points — is open.

In the second half of the file, all of these results are specialized to a finite-dimensional
Hausdorff real topological vector space `N`, where `LinearMap.continuous_of_finiteDimensional`
discharges continuity of every root functional automatically; for a root system
(`[P.IsRootSystem]`), `RootPairing.moduleFinite_coweight_of_isRootSystem` also supplies
finite-dimensionality of `N`.

## Main results

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
* `RootPairing.locallyFinite_affineRootHyperplane_of_continuous` and
  `RootPairing.locallyFinite_affineRootHyperplane`: **the family of affine root hyperplanes
  `{x | αⱼ(x) = k}` indexed by `ι × ℤ` is locally finite.**
* `RootPairing.isClosed_iUnion_affineRootHyperplane` and
  `RootPairing.isOpen_setOf_forall_root'_ne_intCast`: the union of the affine root hyperplanes is
  closed, and the set of regular coweights avoiding all affine root hyperplanes is open.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §1.1–§1.2 and Ch. VI, §2.1.
* L. Garnier, *Affine Weyl groups and compact Lie groups*, §1.3.
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

section Order

variable [LinearOrder R] [OrderTopology R]

/-- The open fundamental alcove is open when every root functional is continuous. -/
theorem isOpen_fundamentalAlcove_of_continuous
    (hcont : ∀ i, Continuous (P.root' i)) : IsOpen (fundamentalAlcove P b) := by
  have h : fundamentalAlcove P b =
      (⋂ i ∈ b.support, P.root' i ⁻¹' Ioi 0) ∩ P.root' b.highestRoot ⁻¹' Iio 1 := by
    ext x
    simp [mem_fundamentalAlcove]
  rw [h]
  exact (isOpen_biInter_finset fun i _ ↦ isOpen_Ioi.preimage (hcont i)).inter
    (isOpen_Iio.preimage (hcont _))

/-- The closed fundamental alcove is closed when every root functional is continuous. -/
theorem isClosed_closedFundamentalAlcove_of_continuous
    (hcont : ∀ i, Continuous (P.root' i)) : IsClosed (closedFundamentalAlcove P b) := by
  have h : closedFundamentalAlcove P b =
      (⋂ i ∈ (b.support : Set ι), P.root' i ⁻¹' Ici 0) ∩ P.root' b.highestRoot ⁻¹' Iic 1 := by
    ext x
    simp [mem_closedFundamentalAlcove]
  rw [h]
  exact (isClosed_biInter fun i _ ↦ isClosed_Ici.preimage (hcont i)).inter
    (isClosed_Iic.preimage (hcont _))

/-- Every closed face `b.closedAlcoveFace J` of the fundamental alcove is closed when the root
functionals and addition on `R` are continuous. -/
theorem Base.isClosed_closedAlcoveFace_of_continuous [ContinuousAdd R]
    (hcont : ∀ i, Continuous (P.root' i)) (J : Set (Option b.support)) :
    IsClosed (b.closedAlcoveFace J) := by
  have h : b.closedAlcoveFace J =
      closedFundamentalAlcove P b ∩ ⋂ k ∈ J, b.affineSimpleRoot k ⁻¹' {0} := by
    ext x
    simp [Base.mem_closedAlcoveFace]
  rw [h]
  exact (isClosed_closedFundamentalAlcove_of_continuous b hcont).inter
    (isClosed_biInter fun k _ ↦ isClosed_singleton.preimage
      (b.continuous_affineSimpleRoot_of_continuous hcont k))

end Order

end Base

section Hyperplanes

variable [LinearOrder R] [IsStrictOrderedRing R] [OrderTopology R] [Archimedean R] [Finite ι]
  (P : RootPairing ι R M N)

/-- **Local finiteness of the affine root hyperplanes**: over an archimedean linearly ordered
topological ring, when `ι` is finite and each root functional `P.root' i` is continuous, every
point of `N` has a neighborhood meeting only finitely many affine root hyperplanes
`{x | αⱼ(x) = k}` (`(j, k) : ι × ℤ`). -/
theorem locallyFinite_affineRootHyperplane_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    LocallyFinite fun p : ι × ℤ ↦ {x : N | P.root' p.1 x = p.2} := by
  let _ := Fintype.ofFinite ι
  intro x
  choose a ha using fun j : ι ↦ exists_int_lt (P.root' j x)
  choose c hc using fun j : ι ↦ exists_int_gt (P.root' j x)
  refine ⟨⋂ j : ι, P.root' j ⁻¹' Ioo (a j : R) (c j : R),
    iInter_mem.mpr fun j ↦ (isOpen_Ioo.preimage (hcont j)).mem_nhds ⟨ha j, hc j⟩, ?_⟩
  refine (Set.finite_iUnion fun j : ι ↦
    (Set.finite_singleton j).prod (Set.finite_Icc (a j) (c j))).subset ?_
  rintro ⟨j, k⟩ ⟨y, hyk, hyU⟩
  have hyj := mem_iInter.mp hyU j
  simp only [mem_preimage, mem_Ioo] at hyj
  rw [mem_ofPred.mp hyk] at hyj
  exact mem_iUnion.mpr ⟨j, mem_prod.mpr ⟨rfl, (Int.cast_lt.mp hyj.1).le,
    (Int.cast_lt.mp hyj.2).le⟩⟩

/-- The union of all affine root hyperplanes is closed when `R` is archimedean and the root
functionals are continuous. -/
theorem isClosed_iUnion_affineRootHyperplane_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    IsClosed (⋃ p : ι × ℤ, {x : N | P.root' p.1 x = p.2}) :=
  (P.locallyFinite_affineRootHyperplane_of_continuous hcont).isClosed_iUnion fun p ↦
    isClosed_singleton.preimage (hcont p.1)

/-- The set of regular coweights — points avoiding every affine root hyperplane — is open when `R`
is archimedean and the root functionals are continuous. -/
theorem isOpen_setOf_forall_root'_ne_intCast_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    IsOpen {x : N | ∀ (j : ι) (k : ℤ), P.root' j x ≠ k} := by
  have h : {x : N | ∀ (j : ι) (k : ℤ), P.root' j x ≠ k} =
      (⋃ p : ι × ℤ, {x : N | P.root' p.1 x = p.2})ᶜ := by
    ext x
    simp [Prod.forall]
  rw [h]
  exact (P.isClosed_iUnion_affineRootHyperplane_of_continuous hcont).isOpen_compl

end Hyperplanes

end OrderedCommRing

section OrderedField

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [TopologicalSpace R] [OrderTopology R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] (b : P.Base)

/-- Every point of the closed fundamental alcove is a limit of points on an open segment in the
fundamental alcove; no continuity of the root functionals is required for this inclusion. -/
theorem subset_closure_fundamentalAlcove :
    closedFundamentalAlcove P b ⊆ closure (fundamentalAlcove P b) := by
  intro x hx
  obtain ⟨x₀, hx₀⟩ := fundamentalAlcove_nonempty b
  let φ : R → N := fun t ↦ AffineMap.lineMap x x₀ t
  have hφ : Continuous φ := by
    have h : φ = fun t ↦ t • (x₀ - x) + x := funext (AffineMap.lineMap_apply_module' x x₀)
    rw [h]
    exact (continuous_id.smul continuous_const).add continuous_const
  have h0 : (0 : R) ∈ closure (Ioo (0 : R) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hxφ : x ∈ φ '' closure (Ioo (0 : R) 1) := ⟨0, h0, by simp [φ]⟩
  exact closure_mono
    (by rintro _ ⟨t, ht, rfl⟩; exact lineMap_mem_fundamentalAlcove b hx hx₀ ht.1 ht.2)
    (image_closure_subset_closure_image hφ hxφ)

/-- **The closed fundamental alcove is the topological closure of the open fundamental alcove.** -/
theorem closure_fundamentalAlcove_of_continuous (hcont : ∀ i, Continuous (P.root' i)) :
    closure (fundamentalAlcove P b) = closedFundamentalAlcove P b :=
  Subset.antisymm
    (closure_minimal (fundamentalAlcove_subset_closedFundamentalAlcove P b)
      (isClosed_closedFundamentalAlcove_of_continuous b hcont))
    (subset_closure_fundamentalAlcove b)

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
    rw [b.affineSimpleRoot_eq_root'_add, map_add, map_smul, map_neg, root'_coroot_eq_pairing,
      pairing_same, smul_eq_mul, add_assoc, ← b.affineSimpleRoot_eq_root'_add k x, hk0]
    ring
  linarith

end OrderedField

/-! ### Finite generation of coweights for root systems and specialization over `ℝ` -/

/-- For a finite root system over a commutative ring, the coweight module `N` is finitely generated
(in particular `FiniteDimensional R N` when `R` is a field), since it is spanned by the finitely
many coroots. -/
theorem moduleFinite_coweight_of_isRootSystem {ι R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] : Module.Finite R N :=
  Module.Finite.equiv (LinearEquiv.ofTop (P.corootSpan R) IsRootSystem.span_coroot_eq_top)

section Real

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul ℝ N] [T2Space N]
  [FiniteDimensional ℝ N]

section Base

variable {P : RootPairing ι ℝ M N} [Finite ι] [Nonempty ι] (b : P.Base)

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, the open fundamental
alcove is open. -/
theorem isOpen_fundamentalAlcove : IsOpen (fundamentalAlcove P b) :=
  isOpen_fundamentalAlcove_of_continuous b fun i ↦ (P.root' i).continuous_of_finiteDimensional

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, the closed fundamental
alcove is closed. -/
theorem isClosed_closedFundamentalAlcove : IsClosed (closedFundamentalAlcove P b) :=
  isClosed_closedFundamentalAlcove_of_continuous b
    fun i ↦ (P.root' i).continuous_of_finiteDimensional

/-- Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, every closed face of the
fundamental alcove is closed. -/
theorem Base.isClosed_closedAlcoveFace (J : Set (Option b.support)) :
    IsClosed (b.closedAlcoveFace J) :=
  b.isClosed_closedAlcoveFace_of_continuous
    (fun i ↦ (P.root' i).continuous_of_finiteDimensional) J

/-- **Over `ℝ`, the closed fundamental alcove is the topological closure of the open fundamental
alcove.** -/
@[simp]
theorem closure_fundamentalAlcove :
    closure (fundamentalAlcove P b) = closedFundamentalAlcove P b :=
  closure_fundamentalAlcove_of_continuous b fun i ↦ (P.root' i).continuous_of_finiteDimensional

/-- **Over `ℝ`, the open fundamental alcove is the topological interior of the closed fundamental
alcove.** -/
@[simp]
theorem interior_closedFundamentalAlcove :
    interior (closedFundamentalAlcove P b) = fundamentalAlcove P b :=
  interior_closedFundamentalAlcove_of_continuous b
    fun i ↦ (P.root' i).continuous_of_finiteDimensional

end Base

/-- **Over `ℝ`, on a finite-dimensional Hausdorff topological vector space, the family of affine
root hyperplanes `{x | αⱼ(x) = k}` (`(j, k) : ι × ℤ`) is locally finite.** -/
theorem locallyFinite_affineRootHyperplane [Finite ι] (P : RootPairing ι ℝ M N) :
    LocallyFinite fun p : ι × ℤ ↦ {x : N | P.root' p.1 x = p.2} :=
  P.locallyFinite_affineRootHyperplane_of_continuous
    fun i ↦ (P.root' i).continuous_of_finiteDimensional

/-- Over `ℝ`, the union of all affine root hyperplanes is closed. -/
theorem isClosed_iUnion_affineRootHyperplane [Finite ι] (P : RootPairing ι ℝ M N) :
    IsClosed (⋃ p : ι × ℤ, {x : N | P.root' p.1 x = p.2}) :=
  P.isClosed_iUnion_affineRootHyperplane_of_continuous
    fun i ↦ (P.root' i).continuous_of_finiteDimensional

/-- Over `ℝ`, the set of regular coweights avoiding all affine root hyperplanes is open. -/
theorem isOpen_setOf_forall_root'_ne_intCast [Finite ι] (P : RootPairing ι ℝ M N) :
    IsOpen {x : N | ∀ (j : ι) (k : ℤ), P.root' j x ≠ k} :=
  P.isOpen_setOf_forall_root'_ne_intCast_of_continuous
    fun i ↦ (P.root' i).continuous_of_finiteDimensional

end Real

end RootPairing
