/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.ColumnReflection

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Truncated reflections on coefficient columns

Truncated simple reflections replace the other coefficients in a Cartan reflection by their
positive parts. They are involutions on the entire integer coefficient lattice; this does not
assert that an arbitrary matrix preserves a root system. Reflections at nonadjacent vertices
commute, and an independent finite colour class has an involutive simultaneous update.

The convention is that `A j i` pairs the root at `j` with the coroot at `i`, as in
`Matrix.columnReflection`. Consequently the matrix in Fomin--Zelevinsky's coordinate formula
is the transpose of `A`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §3, equation (3.2).
-/

public section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)

/-- A truncated simple reflection changes one coordinate, using the positive parts of the
other coefficients. No assumption on the diagonal or signs of the matrix is required. -/
def truncatedColumnReflection (i : ι) (c : ι → ℤ) : ι → ℤ :=
  Function.update c i (-c i - ∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0)

/-- The coordinate changed by a truncated reflection. -/
@[simp]
theorem truncatedColumnReflection_apply_same (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflection i c i =
      -c i - ∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0 := by
  simp [truncatedColumnReflection]

/-- Every coordinate other than the selected one is unchanged. -/
@[simp]
theorem truncatedColumnReflection_apply_of_ne {i k : ι} (hki : k ≠ i) (c : ι → ℤ) :
    A.truncatedColumnReflection i c k = c k := by
  simp [truncatedColumnReflection, hki]

/-- Truncated reflection is an involution on all integer coefficient columns. -/
theorem truncatedColumnReflection_involutive (i : ι) :
    Function.Involutive (A.truncatedColumnReflection i) := by
  intro c
  ext k
  by_cases hki : k = i
  · subst k
    simp only [truncatedColumnReflection_apply_same]
    have hs : (∑ j ∈ Finset.univ.erase i,
        A j i * max (A.truncatedColumnReflection i c j) 0) =
        ∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [truncatedColumnReflection_apply_of_ne A (Finset.ne_of_mem_erase hj)]
    rw [hs]
    omega
  · simp [hki]

/-- Applying the same truncated reflection twice restores the column. -/
@[simp]
theorem truncatedColumnReflection_truncatedColumnReflection (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflection i (A.truncatedColumnReflection i c) = c :=
  A.truncatedColumnReflection_involutive i c

/-- On columns whose other coordinates are nonnegative, truncation agrees with the usual
Cartan reflection. The diagonal hypothesis also supplies the existing linear reflection. -/
theorem truncatedColumnReflection_eq_columnReflection (hA : ∀ i, A i i = 2)
    (i : ι) (c : ι → ℤ) (hc : ∀ j, j ≠ i → 0 ≤ c j) :
    A.truncatedColumnReflection i c = A.columnReflection hA i c := by
  ext k
  by_cases hki : k = i
  · subst k
    rw [truncatedColumnReflection_apply_same, columnReflection_apply_same,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hs : (∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0) =
        ∑ j ∈ Finset.univ.erase i, A j i * c j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [max_eq_left (hc j (Finset.ne_of_mem_erase hj))]
    rw [hs, hA]
    ring
  · simp [hki]

/-- When all other coefficients are nonpositive, a truncated reflection simply negates
the selected coordinate, independently of the matrix entries. -/
theorem truncatedColumnReflection_eq_update_of_nonpos (i : ι) (c : ι → ℤ)
    (hc : ∀ j, j ≠ i → c j ≤ 0) :
    A.truncatedColumnReflection i c = Function.update c i (-c i) := by
  have hs : (∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [max_eq_right (hc j (Finset.ne_of_mem_erase hj)), mul_zero]
  unfold truncatedColumnReflection
  rw [hs, sub_zero]

/-- A truncated reflection swaps a negative simple column with its positive simple column. -/
@[simp]
theorem truncatedColumnReflection_neg_single (i : ι) :
    A.truncatedColumnReflection i (-Pi.single i 1) = Pi.single i 1 := by
  rw [A.truncatedColumnReflection_eq_update_of_nonpos i _ (by
    intro j hj
    simp [hj])]
  ext k
  by_cases hki : k = i <;> simp [hki]

/-- Truncated reflection fixes a negative simple column at any other vertex. -/
@[simp]
theorem truncatedColumnReflection_neg_single_of_ne {i j : ι} (hji : j ≠ i) :
    A.truncatedColumnReflection i (-Pi.single j 1) = -Pi.single j 1 := by
  rw [A.truncatedColumnReflection_eq_update_of_nonpos i _ (by
    intro k _
    by_cases hkj : k = j <;> simp [hkj])]
  ext k
  by_cases hki : k = i <;> simp [hki, Ne.symm hji]

private theorem sum_truncatedColumnReflection {i j : ι} (hji : A j i = 0) (c : ι → ℤ) :
    (∑ k ∈ Finset.univ.erase i, A k i * max (A.truncatedColumnReflection j c k) 0) =
      ∑ k ∈ Finset.univ.erase i, A k i * max (c k) 0 := by
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp [hji]
  · rw [truncatedColumnReflection_apply_of_ne A hkj]

/-- Truncated reflections at nonadjacent vertices commute. Both oriented matrix entries
are required; the matrix itself need not be a generalized Cartan matrix. -/
theorem commute_truncatedColumnReflection {i j : ι}
    (hijA : A i j = 0) (hjiA : A j i = 0) :
    Function.Commute (A.truncatedColumnReflection i) (A.truncatedColumnReflection j) := by
  by_cases hij : i = j
  · subst j
    intro c
    rfl
  intro c
  ext k
  by_cases hki : k = i
  · subst k
    simp only [truncatedColumnReflection_apply_same,
      truncatedColumnReflection_apply_of_ne A hij]
    rw [sum_truncatedColumnReflection A hjiA]
  · by_cases hkj : k = j
    · subst k
      simp only [truncatedColumnReflection_apply_same,
        truncatedColumnReflection_apply_of_ne A hki]
      rw [sum_truncatedColumnReflection A hijA]
    · simp [hki, hkj]

/-- Independent coordinates can be reflected simultaneously. This is the integer-lattice
formula for a colour-class transformation, before restricting to almost-positive roots. -/
def truncatedColumnReflections (s : Finset ι) (c : ι → ℤ) : ι → ℤ :=
  fun i ↦ if i ∈ s then A.truncatedColumnReflection i c i else c i

/-- The selected coordinate formula for a simultaneous truncated reflection. -/
@[simp]
theorem truncatedColumnReflections_apply_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s)
    (c : ι → ℤ) : A.truncatedColumnReflections s c i = A.truncatedColumnReflection i c i := by
  simp [truncatedColumnReflections, hi]

/-- Unselected coordinates remain unchanged in a simultaneous reflection. -/
@[simp]
theorem truncatedColumnReflections_apply_of_notMem {s : Finset ι} {i : ι} (hi : i ∉ s)
    (c : ι → ℤ) : A.truncatedColumnReflections s c i = c i := by
  simp [truncatedColumnReflections, hi]

/-- The empty colour class does nothing. -/
@[simp]
theorem truncatedColumnReflections_empty (c : ι → ℤ) :
    A.truncatedColumnReflections ∅ c = c := by
  ext i
  simp [truncatedColumnReflections]

/-- A singleton colour class is one truncated simple reflection. -/
@[simp]
theorem truncatedColumnReflections_singleton (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflections {i} c = A.truncatedColumnReflection i c := by
  ext k
  by_cases hki : k = i <;> simp [truncatedColumnReflections, hki]

/-- Adding a selected vertex not joined to the previous colour class composes its simple
reflection with the simultaneous update. Iteration identifies the update with any ordering
of a finite independent colour class. -/
theorem truncatedColumnReflections_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (hs : ∀ j ∈ s, A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections (insert i s) c =
      A.truncatedColumnReflection i (A.truncatedColumnReflections s c) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp only [truncatedColumnReflections_apply_of_mem A (Finset.mem_insert_self i s),
      truncatedColumnReflection_apply_same, truncatedColumnReflections_apply_of_notMem A hi]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjs : j ∈ s
    · rw [hs j hjs]
      simp
    · rw [truncatedColumnReflections_apply_of_notMem A hjs]
  · simp [truncatedColumnReflections, hki]

/-- A finite independent colour class gives an involution. The condition only concerns
entries between distinct selected indices; the matrix need not be Cartan or symmetrizable. -/
theorem truncatedColumnReflections_involutive (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ A j i = 0) :
    Function.Involutive (A.truncatedColumnReflections s) := by
  intro c
  ext i
  by_cases hi : i ∈ s
  · simp only [truncatedColumnReflections_apply_of_mem A hi,
      truncatedColumnReflection_apply_same]
    have he : (∑ j ∈ Finset.univ.erase i,
        A j i * max (A.truncatedColumnReflections s c j) 0) =
        ∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjs : j ∈ s
      · rw [hs hi hjs (Ne.symm (Finset.ne_of_mem_erase hj))]
        simp
      · rw [truncatedColumnReflections_apply_of_notMem A hjs]
    rw [he]
    omega
  · simp [hi]

/-- Applying an independent colour-class transformation twice restores the column. -/
@[simp]
theorem truncatedColumnReflections_truncatedColumnReflections (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections s (A.truncatedColumnReflections s c) = c :=
  A.truncatedColumnReflections_involutive s hs c

end Matrix
