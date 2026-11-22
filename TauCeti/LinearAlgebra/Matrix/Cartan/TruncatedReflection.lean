/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.ColumnReflection

import Mathlib.Data.Finset.Piecewise

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

/-- The whole-column update formula for a truncated reflection. -/
theorem truncatedColumnReflection_def (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflection i c =
      Function.update c i (-c i - ∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0) := by rfl

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

private theorem sum_positivePart_congr (i : ι) (c d : ι → ℤ)
    (h : ∀ j, j ≠ i → A j i ≠ 0 → c j = d j) :
    (∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0) =
      ∑ j ∈ Finset.univ.erase i, A j i * max (d j) 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : A j i = 0
  · simp [hji]
  · rw [h j (Finset.ne_of_mem_erase hj) hji]

/-- On columns whose nonzero-weight other coordinates are nonnegative, truncation agrees with the
usual
Cartan reflection. The diagonal hypothesis also supplies the existing linear reflection. -/
theorem truncatedColumnReflection_eq_columnReflection (hA : ∀ i, A i i = 2)
    (i : ι) (c : ι → ℤ) (hc : ∀ j, j ≠ i → A j i ≠ 0 → 0 ≤ c j) :
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
      by_cases hji : A j i = 0
      · simp [hji]
      · rw [max_eq_left (hc j (Finset.ne_of_mem_erase hj) hji)]
    rw [hs, hA]
    ring
  · simp [hki]

/-- When all nonzero-weight other coefficients are nonpositive, a truncated reflection negates
the selected coordinate, independently of the matrix entries. -/
theorem truncatedColumnReflection_eq_update_of_nonpos (i : ι) (c : ι → ℤ)
    (hc : ∀ j, j ≠ i → A j i ≠ 0 → c j ≤ 0) :
    A.truncatedColumnReflection i c = Function.update c i (-c i) := by
  have hs : (∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : A j i = 0
    · simp [hji]
    · rw [max_eq_right (hc j (Finset.ne_of_mem_erase hj) hji), mul_zero]
  unfold truncatedColumnReflection
  rw [hs, sub_zero]

/-- The simultaneous update on any finite set computes each selected coordinate from the
original column. Independence is needed for involutivity, not for this definition. -/
def truncatedColumnReflections (s : Finset ι) (c : ι → ℤ) : ι → ℤ :=
  s.piecewise (fun i ↦ A.truncatedColumnReflection i c i) c

/-- The unconditional coordinate formula for a simultaneous update. -/
theorem truncatedColumnReflections_apply (s : Finset ι) (c : ι → ℤ) (i : ι) :
    A.truncatedColumnReflections s c i =
      if i ∈ s then A.truncatedColumnReflection i c i else c i := by rfl

/-- The selected coordinate formula for a simultaneous truncated reflection. -/
@[simp]
theorem truncatedColumnReflections_apply_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s)
    (c : ι → ℤ) : A.truncatedColumnReflections s c i = A.truncatedColumnReflection i c i :=
  Finset.piecewise_eq_of_mem _ _ _ hi

/-- Unselected coordinates remain unchanged in a simultaneous reflection. -/
@[simp]
theorem truncatedColumnReflections_apply_of_notMem {s : Finset ι} {i : ι} (hi : i ∉ s)
    (c : ι → ℤ) : A.truncatedColumnReflections s c i = c i :=
  Finset.piecewise_eq_of_notMem _ _ _ hi

/-- The empty colour class does nothing. -/
@[simp]
theorem truncatedColumnReflections_empty (c : ι → ℤ) :
    A.truncatedColumnReflections ∅ c = c := Finset.piecewise_empty _ _

/-- Inserting a fresh index composes its reflection with the previous update when only the
incoming entries `A j i` for previously selected `j` vanish. The opposite entries are unused. -/
theorem truncatedColumnReflections_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (hs : ∀ j ∈ s, A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections (insert i s) c =
      A.truncatedColumnReflection i (A.truncatedColumnReflections s c) := by
  rw [truncatedColumnReflections, Finset.piecewise_insert]
  ext k
  by_cases hki : k = i
  · subst k
    simp only [Function.update_self, truncatedColumnReflection_apply_same,
      truncatedColumnReflections_apply_of_notMem A hi]
    congr 1
    apply A.sum_positivePart_congr
    intro j _ hji
    have hjs : j ∉ s := fun hj ↦ hji (hs j hj)
    exact (A.truncatedColumnReflections_apply_of_notMem hjs c).symm
  · simp [Function.update_of_ne hki, truncatedColumnReflection_apply_of_ne A hki,
      truncatedColumnReflections]

/-- A singleton colour class is one truncated simple reflection. -/
@[simp]
theorem truncatedColumnReflections_singleton (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflections {i} c = A.truncatedColumnReflection i c := by
  simpa using A.truncatedColumnReflections_insert ∅ i (by simp) (by simp) c

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
    have he := A.sum_positivePart_congr i (A.truncatedColumnReflections s c) c (by
      intro j hji hAji
      have hjs : j ∉ s := fun hj ↦ hAji (hs hi hj hji.symm)
      exact A.truncatedColumnReflections_apply_of_notMem hjs c)
    rw [he]
    omega
  · simp [hi]

/-- Applying an independent colour-class transformation twice restores the column. -/
@[simp]
theorem truncatedColumnReflections_truncatedColumnReflections (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections s (A.truncatedColumnReflections s c) = c :=
  A.truncatedColumnReflections_involutive s hs c

/-- Truncated reflection is the singleton case of the colour-class involution. -/
theorem truncatedColumnReflection_involutive (i : ι) :
    Function.Involutive (A.truncatedColumnReflection i) := by
  have h := A.truncatedColumnReflections_involutive {i} (by simp)
  intro c
  simpa only [truncatedColumnReflections_singleton] using h c

/-- Applying the same truncated reflection twice restores the column. -/
@[simp]
theorem truncatedColumnReflection_truncatedColumnReflection (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflection i (A.truncatedColumnReflection i c) = c :=
  A.truncatedColumnReflection_involutive i c

private theorem truncatedColumnReflection_neg_single_apply (i j : ι) :
    A.truncatedColumnReflection i (-Pi.single j 1) i = (Pi.single j 1 : ι → ℤ) i := by
  rw [A.truncatedColumnReflection_eq_update_of_nonpos i _ (by
    intro k _ _
    by_cases hkj : k = j <;> simp [hkj])]
  simp

/-- A selected negative simple column is sent to the corresponding positive simple column. -/
@[simp]
theorem truncatedColumnReflections_neg_single_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s) :
    A.truncatedColumnReflections s (-Pi.single i 1) = Pi.single i 1 := by
  ext k
  by_cases hk : k ∈ s
  · rw [truncatedColumnReflections_apply_of_mem A hk,
      truncatedColumnReflection_neg_single_apply]
  · have hki : k ≠ i := fun h ↦ hk (h.symm ▸ hi)
    simp [truncatedColumnReflections_apply_of_notMem A hk, hki]

/-- An unselected negative simple column is fixed by the simultaneous update. -/
@[simp]
theorem truncatedColumnReflections_neg_single_of_notMem {s : Finset ι} {i : ι} (hi : i ∉ s) :
    A.truncatedColumnReflections s (-Pi.single i 1) = -Pi.single i 1 := by
  ext k
  by_cases hk : k ∈ s
  · have hki : k ≠ i := fun h ↦ hi (h ▸ hk)
    rw [truncatedColumnReflections_apply_of_mem A hk,
      truncatedColumnReflection_neg_single_apply]
    simp [hki]
  · rw [truncatedColumnReflections_apply_of_notMem A hk]

/-- Reflection at `i` sends its negative simple column to its positive simple column. -/
@[simp]
theorem truncatedColumnReflection_neg_single (i : ι) :
    A.truncatedColumnReflection i (-Pi.single i 1) = Pi.single i 1 := by
  simpa only [truncatedColumnReflections_singleton] using
    A.truncatedColumnReflections_neg_single_of_mem (Finset.mem_singleton_self i)

/-- Truncated reflection fixes a negative simple column at any other vertex. -/
@[simp]
theorem truncatedColumnReflection_neg_single_of_ne {i j : ι} (hji : j ≠ i) :
    A.truncatedColumnReflection i (-Pi.single j 1) = -Pi.single j 1 := by
  simpa only [truncatedColumnReflections_singleton] using
    A.truncatedColumnReflections_neg_single_of_notMem (by simpa using hji : j ∉ ({i} : Finset ι))

/-- Truncated reflections at nonadjacent vertices commute. Vanishing of both oriented entries
is sufficient; a reflection also commutes with itself without a diagonal condition. -/
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
    congr 1
    apply A.sum_positivePart_congr
    intro k _ hk
    have hkj : k ≠ j := by
      intro h
      subst k
      exact hk hjiA
    exact A.truncatedColumnReflection_apply_of_ne hkj c
  · by_cases hkj : k = j
    · subst k
      simp only [truncatedColumnReflection_apply_same,
        truncatedColumnReflection_apply_of_ne A hki]
      congr 1
      symm
      apply A.sum_positivePart_congr
      intro k _ hk
      have hki : k ≠ i := by
        intro h
        subst k
        exact hk hijA
      exact A.truncatedColumnReflection_apply_of_ne hki c
    · simp [hki, hkj]

/-- If coordinates seen with nonzero weight by the selected vertices are nonnegative,
an independent simultaneous update equals the ordinary Cartan reflections in any
duplicate-free enumeration. In particular this applies to every nonnegative column. -/
theorem truncatedColumnReflections_eq_foldr_columnReflection (hA : ∀ i, A i i = 2)
    (w : List ι) (hw : w.Nodup)
    (hs : (w.toFinset : Set ι).Pairwise fun i j ↦ A j i = 0)
    (c : ι → ℤ) (hc : ∀ i ∈ w, ∀ j, j ≠ i → A j i ≠ 0 → 0 ≤ c j) :
    A.truncatedColumnReflections w.toFinset c =
      w.foldr (fun i d ↦ A.columnReflection hA i d) c := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hi : i ∉ w.toFinset := by simpa using (List.nodup_cons.mp hw).1
    have ht : (w.toFinset : Set ι).Pairwise fun i j ↦ A j i = 0 :=
      hs.mono (by intro j hj; simpa using Or.inr hj)
    have he : ∀ j ∈ w.toFinset, A j i = 0 := by
      intro j hj
      exact hs (by simp) (by simpa using Or.inr hj) (fun h ↦ hi (h.symm ▸ hj))
    rw [List.toFinset_cons, A.truncatedColumnReflections_insert w.toFinset i hi he,
      A.truncatedColumnReflection_eq_columnReflection hA]
    · rw [ih (List.nodup_cons.mp hw).2 ht (fun k hk ↦ hc k (List.mem_cons_of_mem i hk))]
      rfl
    · intro j hji hAji
      have hj : j ∉ w.toFinset := fun hj ↦ hAji (he j hj)
      rw [A.truncatedColumnReflections_apply_of_notMem hj]
      exact hc i (by simp) j hji hAji

end Matrix
