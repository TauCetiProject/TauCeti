/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Pi
import Mathlib.Order.WellFoundedSet

/-!
# Finiteness of nonnegative integer vectors in subgroup cosets

Dickson's lemma shows that each coset of a subgroup of `ι → ℤ` has finitely many nonnegative
vectors exactly when the subgroup has no nonzero nonnegative vector, which in turn says that each
of its nonzero vectors has both a positive and a negative coordinate. For periodic domains of a
pointed Heegaard diagram, this is the algebraic finiteness result used in the admissibility
argument of Ozsváth–Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Lemma 4.13. Applying it to Whitney disk classes also requires a geometric
correspondence with domain vectors and control of its fibers.

## Main results

* `AddSubgroup.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero`: every nonzero vector has
  coordinates of both signs exactly when `0` is the only nonnegative vector.
* `AddSubgroup.finite_setOf_mem_nonneg_iff`: the subgroup has finitely many nonnegative vectors
  exactly when `0` is the only one.
* `AddSubgroup.finite_setOf_nonneg_sub_mem_iff`: the same holds for each coset.
* `AddSubgroup.finite_of_forall_sub_mem`: a set of nonnegative vectors whose differences lie in
  such a subgroup is finite.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- Every nonzero vector of a subgroup `P` of `ι → G` has both a positive and a negative
coordinate exactly when `0` is the only nonnegative vector of `P`. -/
theorem _root_.AddSubgroup.forall_exists_pos_and_neg_iff_forall_nonneg_eq_zero {G : Type*}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (P : AddSubgroup (ι → G)) :
    (∀ p ∈ P, p ≠ 0 → (∃ i, 0 < p i) ∧ ∃ i, p i < 0) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  constructor
  · intro h p hp hp₀
    by_contra hne
    obtain ⟨i, hi⟩ := (h p hp hne).2
    exact (hp₀ i).not_gt hi
  · intro h p hp hne
    refine ⟨?_, ?_⟩
    · by_contra hpos
      push Not at hpos
      refine hne (neg_eq_zero.mp (h (-p) (neg_mem hp) fun i => ?_))
      simpa using hpos i
    · by_contra hneg
      push Not at hneg
      exact hne (h p hp hneg)

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when it contains
only finitely many nonnegative vectors: the multiples of a nonzero one are infinitely many. -/
theorem _root_.AddSubgroup.finite_setOf_mem_nonneg_iff (P : AddSubgroup (ι → ℤ)) :
    {p | p ∈ P ∧ 0 ≤ p}.Finite ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  refine ⟨fun hfin p hp hp0 => by_contra fun hne => ?_,
    fun h => (Set.finite_singleton 0).subset fun p hp => h p hp.1 hp.2⟩
  exact Set.infinite_of_injective_forall_mem (s := {p | p ∈ P ∧ 0 ≤ p})
    (nsmul_left_strictMono (hp0.lt_of_ne' hne)).injective
    (fun n => ⟨nsmul_mem hp n, nsmul_nonneg hp0 n⟩) hfin

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when each coset
`D₀ + P` contains only finitely many nonnegative vectors. -/
theorem _root_.AddSubgroup.finite_setOf_nonneg_sub_mem_iff [Finite ι]
    (P : AddSubgroup (ι → ℤ)) :
    (∀ D₀ : ι → ℤ, {D | 0 ≤ D ∧ D - D₀ ∈ P}.Finite) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  refine ⟨fun hfin => P.finite_setOf_mem_nonneg_iff.mp
    ((hfin 0).subset fun p hp => ⟨hp.2, by simpa using hp.1⟩), fun h D₀ => ?_⟩
  -- Dickson's lemma: the nonnegative vectors of `ι → ℤ` are partially well-ordered.
  have hpwo : (Set.univ.pi fun _ : ι => Set.Ici (0 : ℤ)).IsPWO :=
    Set.IsPWO.pi fun _ => Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt bddBelow_Ici)
  -- Two comparable vectors in the coset differ by a nonnegative vector of `P`.
  refine IsAntichain.finite_of_partiallyWellOrderedOn (fun D hD D' hD' hne hle => hne ?_)
    (hpwo.mono fun D hD i _ => hD.1 i)
  exact (sub_eq_zero.1 (h _ (by simpa using sub_mem hD'.2 hD.2) (sub_nonneg.2 hle))).symm

/-- If `0` is the only nonnegative vector of a subgroup `P` of `ι → ℤ`, then a set of
nonnegative vectors any two of which differ by an element of `P` is finite: it lies in the
nonnegative part of a single coset of `P`. -/
theorem _root_.AddSubgroup.finite_of_forall_sub_mem [Finite ι] {P : AddSubgroup (ι → ℤ)}
    (hP : ∀ p ∈ P, 0 ≤ p → p = 0) {s : Set (ι → ℤ)} (hs : ∀ D ∈ s, 0 ≤ D)
    (hsub : ∀ D ∈ s, ∀ D' ∈ s, D' - D ∈ P) : s.Finite := by
  obtain rfl | ⟨D₀, hD₀⟩ := s.eq_empty_or_nonempty
  · exact Set.finite_empty
  exact (P.finite_setOf_nonneg_sub_mem_iff.mpr hP D₀).subset fun D hD =>
    ⟨hs D hD, hsub D₀ hD₀ D hD⟩

end TauCeti
