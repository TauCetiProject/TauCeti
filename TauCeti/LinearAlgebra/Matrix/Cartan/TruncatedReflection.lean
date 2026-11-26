/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.ColumnReflection

public import TauCeti.Algebra.BigOperators.GroupWithZero.Action

/-!
# Truncated reflections on coefficient columns

Truncated simple reflections replace the other coefficients in a Cartan reflection by their
positive parts. They are involutions on the entire integer coefficient lattice; this does not
assert that an arbitrary matrix preserves a root system. Reflections at nonadjacent vertices
commute, and an independent finite colour class has an involutive simultaneous update.
These updates give the coefficient-lattice formulas underlying the bipartite involutions
τ₊ and τ₋, before any restriction to almost-positive roots.

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

/-- Every truncated simple reflection fixes the zero column. -/
@[simp]
theorem truncatedColumnReflection_zero (i : ι) :
    A.truncatedColumnReflection i 0 = 0 := by
  ext j
  by_cases hji : j = i <;> simp [hji]

/-- On columns whose nonzero-weight other coordinates are nonnegative, truncation agrees with the
usual Cartan reflection. The diagonal hypothesis also supplies the existing linear reflection. -/
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
      simpa only [smul_eq_mul] using
        Finset.sum_smul_congr_of_ne_zero (Finset.univ.erase i) (fun j ↦ A j i)
          (fun j ↦ max (c j) 0) c
          (fun j hj hji ↦ max_eq_left (hc j (Finset.ne_of_mem_erase hj) hji))
    rw [hs, hA]
    ring
  · simp [hki]

/-- When all nonzero-weight other coefficients are nonpositive, a truncated reflection negates
the selected coordinate, independently of the matrix entries. -/
theorem truncatedColumnReflection_eq_update_of_nonpos (i : ι) (c : ι → ℤ)
    (hc : ∀ j, j ≠ i → A j i ≠ 0 → c j ≤ 0) :
    A.truncatedColumnReflection i c = Function.update c i (-c i) := by
  have hs : (∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0) = 0 := by
    simpa only [smul_eq_mul, mul_zero, Finset.sum_const_zero] using
      Finset.sum_smul_congr_of_ne_zero (Finset.univ.erase i) (fun j ↦ A j i)
        (fun j ↦ max (c j) 0) (fun _ ↦ (0 : ℤ))
        (fun j hj hji ↦ max_eq_right (hc j (Finset.ne_of_mem_erase hj) hji))
  unfold truncatedColumnReflection
  rw [hs, sub_zero]

/-- The simultaneous update on any finite set computes each selected coordinate from the
original column. Independence is needed for involutivity, not for this definition. -/
def truncatedColumnReflections (s : Finset ι) (c : ι → ℤ) : ι → ℤ :=
  s.piecewise (fun i ↦ A.truncatedColumnReflection i c i) c

/-- The whole-column finite-piecewise formula for a simultaneous update. -/
theorem truncatedColumnReflections_def (s : Finset ι) (c : ι → ℤ) :
    A.truncatedColumnReflections s c =
      s.piecewise (fun i ↦ A.truncatedColumnReflection i c i) c := by rfl

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

/-- The unconditional coordinate formula for a simultaneous update. -/
theorem truncatedColumnReflections_apply (s : Finset ι) (c : ι → ℤ) (i : ι) :
    A.truncatedColumnReflections s c i =
      if i ∈ s then A.truncatedColumnReflection i c i else c i := by rfl

/-- The empty colour class does nothing. -/
@[simp]
theorem truncatedColumnReflections_empty (c : ι → ℤ) :
    A.truncatedColumnReflections ∅ c = c := Finset.piecewise_empty _ _

/-- Every simultaneous truncated update fixes the zero column. -/
@[simp]
theorem truncatedColumnReflections_zero (s : Finset ι) :
    A.truncatedColumnReflections s 0 = 0 := by
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

private theorem truncatedColumnReflections_apply_of_weight_ne_zero {s : Finset ι} {i j : ι}
    (hs : ∀ k ∈ s, k ≠ i → A k i = 0) (hji : j ≠ i) (hAji : A j i ≠ 0)
    (c : ι → ℤ) : A.truncatedColumnReflections s c j = c j :=
  A.truncatedColumnReflections_apply_of_notMem (fun hj ↦ hAji (hs j hj hji)) c

private theorem sum_truncatedColumnReflections_eq (s : Finset ι) (i : ι)
    (hs : ∀ j ∈ s, j ≠ i → A j i = 0) (c : ι → ℤ) :
    (∑ j ∈ Finset.univ.erase i, A j i * max (A.truncatedColumnReflections s c j) 0) =
      ∑ j ∈ Finset.univ.erase i, A j i * max (c j) 0 := by
  simpa only [smul_eq_mul] using
    Finset.sum_smul_congr_of_ne_zero (Finset.univ.erase i) (fun j ↦ A j i)
      (fun j ↦ max (A.truncatedColumnReflections s c j) 0) (fun j ↦ max (c j) 0)
      (fun j hj hAji ↦ congrArg (fun x : ℤ ↦ max x 0)
        (A.truncatedColumnReflections_apply_of_weight_ne_zero hs
          (Finset.ne_of_mem_erase hj) hAji c))

/-- Inserting a fresh index composes its reflection with the previous update when only the
incoming entries `A j i` for previously selected `j` vanish. The opposite entries are unused. -/
theorem truncatedColumnReflections_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (hs : ∀ j ∈ s, A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections (insert i s) c =
      A.truncatedColumnReflection i (A.truncatedColumnReflections s c) := by
  rw [truncatedColumnReflections, Finset.piecewise_insert, truncatedColumnReflection_def]
  apply congrArg (Function.update (A.truncatedColumnReflections s c) i)
  rw [A.truncatedColumnReflections_apply_of_notMem hi,
    A.sum_truncatedColumnReflections_eq s i (fun j hj _ ↦ hs j hj)]
  simp only [Function.update_self]

/-- A singleton colour class is one truncated simple reflection. -/
@[simp]
theorem truncatedColumnReflections_singleton (i : ι) (c : ι → ℤ) :
    A.truncatedColumnReflections {i} c = A.truncatedColumnReflection i c := by
  rw [truncatedColumnReflections_def, Finset.piecewise_singleton,
    truncatedColumnReflection_apply_same, truncatedColumnReflection_def]

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
    rw [A.sum_truncatedColumnReflections_eq s i
      (fun j hj hji ↦ hs hi hj hji.symm) c]
    omega
  · simp [hi]

/-- Applying an independent colour-class transformation twice restores the column. -/
@[simp]
theorem truncatedColumnReflections_truncatedColumnReflections (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections s (A.truncatedColumnReflections s c) = c :=
  A.truncatedColumnReflections_involutive s hs c

/-- Every truncated simple reflection is an involution on integer coefficient columns,
for any matrix. -/
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

/-- If every nonzero-weight other coordinate entering a selected position is nonpositive,
the simultaneous update negates precisely its selected coordinates. -/
theorem truncatedColumnReflections_eq_piecewise_neg_of_nonpos (s : Finset ι) (c : ι → ℤ)
    (hc : ∀ i ∈ s, ∀ j, j ≠ i → A j i ≠ 0 → c j ≤ 0) :
    A.truncatedColumnReflections s c = s.piecewise (-c) c := by
  ext i
  by_cases hi : i ∈ s
  · rw [truncatedColumnReflections_apply_of_mem A hi,
      A.truncatedColumnReflection_eq_update_of_nonpos i c (hc i hi)]
    simp [hi]
  · simp [hi]

private theorem truncatedColumnReflections_neg_single_eq_piecewise (s : Finset ι) (i : ι) :
    A.truncatedColumnReflections s (-Pi.single i 1) =
      s.piecewise (Pi.single i 1) (-Pi.single i 1) := by
  simpa only [neg_neg] using
    A.truncatedColumnReflections_eq_piecewise_neg_of_nonpos s (-Pi.single i 1) (by
      intro j _ k _ _
      by_cases hki : k = i <;> simp [hki])

/-- A selected negative simple column is sent to the corresponding positive simple column. -/
@[simp]
theorem truncatedColumnReflections_neg_single_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s) :
    A.truncatedColumnReflections s (-Pi.single i 1) = Pi.single i 1 := by
  rw [A.truncatedColumnReflections_neg_single_eq_piecewise]
  calc
    _ = s.piecewise (Pi.single i 1) (Pi.single i 1) :=
      s.piecewise_congr (fun _ _ ↦ rfl) (fun k hk ↦ by
        have hki : k ≠ i := fun h ↦ hk (h.symm ▸ hi)
        simp [hki])
    _ = _ := Finset.piecewise_same _ _

/-- An unselected negative simple column is fixed by the simultaneous update. -/
@[simp]
theorem truncatedColumnReflections_neg_single_of_notMem {s : Finset ι} {i : ι} (hi : i ∉ s) :
    A.truncatedColumnReflections s (-Pi.single i 1) = -Pi.single i 1 := by
  rw [A.truncatedColumnReflections_neg_single_eq_piecewise]
  calc
    _ = s.piecewise (-Pi.single i 1) (-Pi.single i 1) :=
      s.piecewise_congr (fun k hk ↦ by
        have hki : k ≠ i := fun h ↦ hi (h ▸ hk)
        simp [hki]) (fun _ _ ↦ rfl)
    _ = _ := Finset.piecewise_same _ _

/-- An independent colour class containing a simple column sends it to its negative. -/
@[simp]
theorem truncatedColumnReflections_single_of_mem {s : Finset ι}
    (hs : (s : Set ι).Pairwise fun i j ↦ A j i = 0) {i : ι} (hi : i ∈ s) :
    A.truncatedColumnReflections s (Pi.single i 1) = -Pi.single i 1 := by
  have h := congrArg (A.truncatedColumnReflections s)
    (A.truncatedColumnReflections_neg_single_of_mem hi)
  simpa only [A.truncatedColumnReflections_truncatedColumnReflections s hs] using h.symm

/-- Reflection at `i` sends its negative simple column to its positive simple column. -/
@[simp]
theorem truncatedColumnReflection_neg_single_self (i : ι) :
    A.truncatedColumnReflection i (-Pi.single i 1) = Pi.single i 1 := by
  simpa only [truncatedColumnReflections_singleton] using
    A.truncatedColumnReflections_neg_single_of_mem (Finset.mem_singleton_self i)

/-- Reflection at a simple column sends it to its negative. -/
@[simp]
theorem truncatedColumnReflection_single_self (i : ι) :
    A.truncatedColumnReflection i (Pi.single i 1) = -Pi.single i 1 := by
  have h := congrArg (A.truncatedColumnReflection i) (A.truncatedColumnReflection_neg_single_self i)
  simpa only [A.truncatedColumnReflection_truncatedColumnReflection i] using h.symm

/-- Truncated reflection fixes a negative simple column at any other vertex. -/
@[simp]
theorem truncatedColumnReflection_neg_single_of_ne {i j : ι} (hji : j ≠ i) :
    A.truncatedColumnReflection i (-Pi.single j 1) = -Pi.single j 1 := by
  simpa only [truncatedColumnReflections_singleton] using
    A.truncatedColumnReflections_neg_single_of_notMem (by simpa using hji : j ∉ ({i} : Finset ι))

/-- Truncated reflections commute when both oriented entries between the selected vertices
vanish. Self-commutation without a diagonal premise is a separate unconditional fact. -/
theorem commute_truncatedColumnReflection {i j : ι}
    (hijA : A i j = 0) (hjiA : A j i = 0) :
    Function.Commute (A.truncatedColumnReflection i) (A.truncatedColumnReflection j) := by
  by_cases hij : i = j
  · subst j
    intro c
    rfl
  intro c
  have hi := A.truncatedColumnReflections_insert {j} i (by simpa using hij)
    (by simpa using hjiA) c
  have hj := A.truncatedColumnReflections_insert {i} j (by simpa using Ne.symm hij)
    (by simpa using hijA) c
  calc
    A.truncatedColumnReflection i (A.truncatedColumnReflection j c) =
        A.truncatedColumnReflections {i, j} c := by
      simpa only [truncatedColumnReflections_singleton] using hi.symm
    _ = A.truncatedColumnReflections {j, i} c := by rw [Finset.pair_comm]
    _ = A.truncatedColumnReflection j (A.truncatedColumnReflection i c) := by
      simpa only [truncatedColumnReflections_singleton] using hj

/-- A simultaneous update factors into ordered truncated reflections when the selected indices
are distinct and entries from later indices into earlier indices vanish. No sign or diagonal
condition on the matrix or coefficient column is required. -/
theorem truncatedColumnReflections_eq_foldr_truncatedColumnReflection (w : List ι)
    (hw : w.Nodup) (hs : w.Pairwise fun i j ↦ A j i = 0) (c : ι → ℤ) :
    A.truncatedColumnReflections w.toFinset c = w.foldr A.truncatedColumnReflection c := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hn := List.nodup_cons.mp hw
    have hp := List.pairwise_cons.mp hs
    rw [List.toFinset_cons, A.truncatedColumnReflections_insert w.toFinset i
      (by simpa using hn.1) (fun j hj ↦ hp.1 j (by simpa using hj))]
    rw [ih hn.2 hp.2]
    rfl

/-- For each selected `i`, only the other coordinates `j ≠ i` with `A j i ≠ 0` must be
nonnegative; its own coordinate may be negative. If entries from later vertices into earlier
vertices vanish, the simultaneous update equals the ordered ordinary Cartan reflections. -/
theorem truncatedColumnReflections_eq_foldr_columnReflection (hA : ∀ i, A i i = 2)
    (w : List ι) (hs : w.Pairwise fun i j ↦ A j i = 0)
    (c : ι → ℤ) (hc : ∀ i ∈ w, ∀ j, j ≠ i → A j i ≠ 0 → 0 ≤ c j) :
    A.truncatedColumnReflections w.toFinset c =
      w.foldr (fun i d ↦ A.columnReflection hA i d) c := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hw : (i :: w).Nodup := List.nodup_iff_pairwise_ne.mpr (hs.imp (by
      intro j k hjk h
      subst k
      simp [hA j] at hjk))
    have hi : i ∉ w.toFinset := by simpa using (List.nodup_cons.mp hw).1
    have ht : w.Pairwise fun i j ↦ A j i = 0 := (List.pairwise_cons.mp hs).2
    have he : ∀ j ∈ w.toFinset, A j i = 0 := by
      intro j hj
      exact (List.pairwise_cons.mp hs).1 j (by simpa using hj)
    rw [List.toFinset_cons, A.truncatedColumnReflections_insert w.toFinset i hi he,
      A.truncatedColumnReflection_eq_columnReflection hA]
    · rw [ih ht (fun k hk ↦ hc k (List.mem_cons_of_mem i hk))]
      rfl
    · intro j hji hAji
      rw [A.truncatedColumnReflections_apply_of_weight_ne_zero
        (fun k hk _ ↦ he k hk) hji hAji]
      exact hc i (by simp) j hji hAji

end Matrix
