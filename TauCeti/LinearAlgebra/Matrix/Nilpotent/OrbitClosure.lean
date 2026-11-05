/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.OrbitClosure
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation

/-!
# Regular and subregular nilpotent orbit closures in type A

The conjugacy class of a nilpotent matrix of Jordan type `(n)` is dense in the
nilpotent matrices. For `n ≥ 2`, the closure of the class of type `(n - 1, 1)`
is exactly the nilpotent matrices outside that regular class. These are equalities
of sets of matrix points, both in the usual topology and in the Zariski closure
defined by polynomial vanishing. They make no assertion about scheme structures.

The representatives are arbitrary matrices with the specified Jordan types, so
the statements do not depend on choices of Jordan bases. The regular statement
includes the empty matrix and size one; a subregular type requires size at least two,
as follows already from positivity of the two prescribed parts.

The proof uses Gerstenhaber's orbit-closure criterion and the fact that `(n - 1, 1)`
is the greatest partition other than `(n)` in dominance order.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §§6.1–6.2.
* M. Gerstenhaber, *On dominance and varieties of commuting matrices*,
  Ann. of Math. **73** (1961), 324–348.
-/

public section

open MvPolynomial Topology Module.End

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- Two nilpotent square matrices are conjugate exactly when their Jordan partitions agree. -/
theorem mem_orbit_conjAct_iff_jordanPartition_eq {X Y : Matrix n n K}
    (hX : IsNilpotent X) (hY : IsNilpotent Y) :
    Y ∈ MulAction.orbit (ConjAct (GL n K)) X ↔
      jordanPartition (toLin' X) ((isNilpotent_toLin'_iff X).2 hX) =
        jordanPartition (toLin' Y) ((isNilpotent_toLin'_iff Y).2 hY) := by
  rw [mem_orbit_conjAct_iff_exists_linearEquiv_conj,
    exists_linearEquiv_conj_eq_iff_jordanPartition_parts_eq _ _
      ((isNilpotent_toLin'_iff X).2 hX) ((isNilpotent_toLin'_iff Y).2 hY)]
  exact ⟨Nat.Partition.ext, congrArg Nat.Partition.parts⟩

section Topological

variable [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
  [(𝓝[≠] (0 : K)).NeBot]

/-- The usual closure of a regular nilpotent conjugacy class is the nilpotent locus,
including sizes zero and one. -/
theorem closure_orbit_eq_setOf_isNilpotent_of_jordanPartition_eq_indiscrete
    {R : Matrix n n K} (hR : IsNilpotent R)
    (hreg : jordanPartition (toLin' R) ((isNilpotent_toLin'_iff R).2 hR) =
      Nat.Partition.indiscrete _) :
    closure (MulAction.orbit (ConjAct (GL n K)) R) = {Y | IsNilpotent Y} := by
  ext Y
  constructor
  · intro hY
    exact isNilpotent_of_forall_rank_pow_le hR (rank_pow_le_of_mem_closure_orbit hY)
  · intro hY
    rw [mem_closure_orbit_iff_jordanPartition_dominates hR hY, hreg]
    exact Nat.Partition.indiscrete_dominates _

/-- The usual closure of a subregular nilpotent class is the complement of the regular
class inside the nilpotent locus. -/
theorem closure_orbit_eq_setOf_isNilpotent_diff_orbit_of_jordanPartition_parts_eq_pair
    {R S : Matrix n n K} (hR : IsNilpotent R) (hS : IsNilpotent S)
    (hreg : jordanPartition (toLin' R) ((isNilpotent_toLin'_iff R).2 hR) =
      Nat.Partition.indiscrete _)
    (hsub : (jordanPartition (toLin' S) ((isNilpotent_toLin'_iff S).2 hS)).parts =
      {Module.finrank K (n → K) - 1, 1}) :
    closure (MulAction.orbit (ConjAct (GL n K)) S) =
      {Y | IsNilpotent Y} \ MulAction.orbit (ConjAct (GL n K)) R := by
  ext Y
  by_cases hY : IsNilpotent Y
  · simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hY, true_and]
    rw [mem_closure_orbit_iff_jordanPartition_dominates hS hY,
      Nat.Partition.dominates_iff_ne_indiscrete_of_parts_eq_pair hsub,
      mem_orbit_conjAct_iff_jordanPartition_eq hR hY, hreg, ne_comm]
  · have hout : Y ∉ closure (MulAction.orbit (ConjAct (GL n K)) S) := fun h =>
      hY (isNilpotent_of_forall_rank_pow_le hS (rank_pow_le_of_mem_closure_orbit h))
    simp [hout, hY]

end Topological

section Zariski

variable {k : Type*} [Field k] [Algebra k K] [Infinite K]

/-- The Zariski closure of a regular nilpotent conjugacy class is the nilpotent locus.
Polynomials may have coefficients in any subfield of the infinite field of points. -/
theorem zeroLocus_vanishingIdeal_orbit_eq_image_setOf_isNilpotent_of_jordanPartition_eq_indiscrete
    {R : Matrix n n K} (hR : IsNilpotent R)
    (hreg : jordanPartition (toLin' R) ((isNilpotent_toLin'_iff R).2 hR) =
      Nat.Partition.indiscrete _) :
    zeroLocus K (vanishingIdeal k
        (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) R : Set (Matrix n n K)))) =
      Function.uncurry '' {Y : Matrix n n K | IsNilpotent Y} := by
  ext y
  let Y : Matrix n n K := Function.curry y
  have hy : Function.uncurry Y = y := Function.uncurry_curry y
  constructor
  · intro hY
    exact ⟨Y, isNilpotent_of_forall_rank_pow_le hR
      (rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit (hy ▸ hY)), hy⟩
  · rintro ⟨Z, hZ, rfl⟩
    rw [mem_zeroLocus_vanishingIdeal_orbit_iff_jordanPartition_dominates hR hZ, hreg]
    exact Nat.Partition.indiscrete_dominates _

/-- The Zariski closure of a subregular nilpotent class is the complement of the regular
class inside the nilpotent locus, as an equality of sets of matrix points. -/
theorem zeroLocus_vanishingIdeal_orbit_eq_image_setOf_isNilpotent_diff_orbit_of_parts_eq_pair
    {R S : Matrix n n K} (hR : IsNilpotent R) (hS : IsNilpotent S)
    (hreg : jordanPartition (toLin' R) ((isNilpotent_toLin'_iff R).2 hR) =
      Nat.Partition.indiscrete _)
    (hsub : (jordanPartition (toLin' S) ((isNilpotent_toLin'_iff S).2 hS)).parts =
      {Module.finrank K (n → K) - 1, 1}) :
    zeroLocus K (vanishingIdeal k
        (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) S : Set (Matrix n n K)))) =
      Function.uncurry ''
        ({Y : Matrix n n K | IsNilpotent Y} \ (MulAction.orbit (ConjAct (GL n K)) R :
          Set (Matrix n n K))) := by
  ext y
  let Y : Matrix n n K := Function.curry y
  have hy : Function.uncurry Y = y := Function.uncurry_curry y
  constructor
  · intro h
    have hY := isNilpotent_of_forall_rank_pow_le hS
      (rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit (hy ▸ h))
    refine ⟨Y, ⟨hY, ?_⟩, hy⟩
    have hdom := (mem_zeroLocus_vanishingIdeal_orbit_iff_jordanPartition_dominates hS hY).mp
      (hy ▸ h)
    intro hmem
    have heq := (mem_orbit_conjAct_iff_jordanPartition_eq hR hY).mp hmem
    exact ((Nat.Partition.dominates_iff_ne_indiscrete_of_parts_eq_pair hsub).mp hdom)
      (heq.symm.trans hreg)
  · rintro ⟨Z, ⟨hZ, hnot⟩, rfl⟩
    rw [mem_zeroLocus_vanishingIdeal_orbit_iff_jordanPartition_dominates hS hZ,
      Nat.Partition.dominates_iff_ne_indiscrete_of_parts_eq_pair hsub]
    intro heq
    exact hnot ((mem_orbit_conjAct_iff_jordanPartition_eq hR hZ).mpr (hreg.trans heq.symm))

end Zariski

end Matrix
