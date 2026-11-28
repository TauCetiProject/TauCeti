/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Pointwise.Stabilizer
public import TauCeti.NumberTheory.Markoff.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.Ring

/-!
# Markoff–Hurwitz level sets and their symmetries

The Markoff–Hurwitz equation on ordered tuples is
`∑ i, x i ^ 2 = a * (∏ i, x i) + k`. Its quadratic dependence on each coordinate
gives a Vieta involution replacing that coordinate by the other root. These involutions,
coordinate permutations and even sign changes generate a group preserving every level
for a fixed coefficient. The coefficient-three, zero-level equation and its moves in
three variables recover the classical Markoff equation and its moves.

See Gamburd, Magee and Ronan, *An asymptotic formula for integer points on
Markoff–Hurwitz varieties*, Ann. of Math. 190 (2019), 751–809, §§1 and 2.1.
-/

public section

namespace TauCeti

open Finset
open scoped Pointwise

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- The sum of the squares of the coordinates minus `a` times their product. -/
def markoffHurwitzForm (a : R) (x : Fin n → R) : R :=
  (∑ i, x i ^ 2) - a * ∏ i, x i

/-- The Markoff–Hurwitz form as a difference of the sum of squares and the weighted product. -/
theorem markoffHurwitzForm_def (a : R) (x : Fin n → R) :
    markoffHurwitzForm a x = (∑ i, x i ^ 2) - a * ∏ i, x i := (rfl)

/-- Ordered points of the Markoff–Hurwitz hypersurface of coefficient `a` and level `k`. -/
def markoffHurwitzSet (n : ℕ) (a k : R) : Set (Fin n → R) :=
  {x | markoffHurwitzForm a x = k}

/-- A tuple belongs to the level set exactly when its Markoff–Hurwitz form is `k`. -/
theorem mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq {a k : R} {x : Fin n → R} :
    x ∈ markoffHurwitzSet n a k ↔ markoffHurwitzForm a x = k := Iff.rfl

/-- The Markoff–Hurwitz equation in sum and product form. -/
theorem mem_markoffHurwitzSet {a k : R} {x : Fin n → R} :
    x ∈ markoffHurwitzSet n a k ↔ (∑ i, x i ^ 2) = a * (∏ i, x i) + k := by
  rw [mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq, markoffHurwitzForm_def,
    sub_eq_iff_eq_add, add_comm k]

/-- The Markoff–Hurwitz form commutes with ring homomorphisms, with the coefficient mapped. -/
theorem markoffHurwitzForm_comp_ringHom (a : R) (x : Fin n → R) (f : R →+* S) :
    markoffHurwitzForm (f a) (f ∘ x) = f (markoffHurwitzForm a x) := by
  simp [markoffHurwitzForm, map_sum, map_prod]

/-- A ring homomorphism sends a Markoff–Hurwitz point to the corresponding mapped level. -/
theorem comp_mem_markoffHurwitzSet {a k : R} {x : Fin n → R}
    (hx : x ∈ markoffHurwitzSet n a k) (f : R →+* S) :
    f ∘ x ∈ markoffHurwitzSet n (f a) (f k) := by
  rw [mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq, markoffHurwitzForm_comp_ringHom,
    mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq.mp hx]

/-- The Markoff–Hurwitz form is symmetric in the coordinates. -/
@[simp]
theorem markoffHurwitzForm_comp_perm (a : R) (x : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    markoffHurwitzForm a (x ∘ σ) = markoffHurwitzForm a x := by
  simp only [markoffHurwitzForm, Function.comp_apply, Equiv.sum_comp σ fun i ↦ x i ^ 2,
    Equiv.prod_comp σ x]

/-- Coordinate permutations preserve the Markoff–Hurwitz locus. -/
@[simp]
theorem comp_perm_mem_markoffHurwitzSet_iff {a k : R} {x : Fin n → R}
    {σ : Equiv.Perm (Fin n)} :
    x ∘ σ ∈ markoffHurwitzSet n a k ↔ x ∈ markoffHurwitzSet n a k := by
  simp only [mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq, markoffHurwitzForm_comp_perm]

/-- The origin has level zero in positive dimension. -/
@[simp]
theorem zero_mem_markoffHurwitzSet_iff {a k : R} :
    (0 : Fin (n + 1) → R) ∈ markoffHurwitzSet (n + 1) a k ↔ k = 0 := by
  simp [mem_markoffHurwitzSet, eq_comm]

/-- Positive integral points of the Markoff–Hurwitz hypersurface. -/
def positiveMarkoffHurwitzSet (n : ℕ) (a k : ℤ) : Set (Fin n → ℤ) :=
  {x ∈ markoffHurwitzSet n a k | ∀ i, 0 < x i}

/-- Positive integral points satisfy the level equation and are positive in every coordinate. -/
theorem mem_positiveMarkoffHurwitzSet {a k : ℤ} {x : Fin n → ℤ} :
    x ∈ positiveMarkoffHurwitzSet n a k ↔ x ∈ markoffHurwitzSet n a k ∧ ∀ i, 0 < x i :=
  Iff.rfl

/-- Positive integral points lie on the corresponding Markoff–Hurwitz level set. -/
theorem positiveMarkoffHurwitzSet_subset_markoffHurwitzSet {a k : ℤ} :
    positiveMarkoffHurwitzSet n a k ⊆ markoffHurwitzSet n a k :=
  Set.sep_subset _ _

/-- Coordinate permutations preserve positive integral Markoff–Hurwitz points. -/
@[simp]
theorem comp_perm_mem_positiveMarkoffHurwitzSet_iff {a k : ℤ} {x : Fin n → ℤ}
    {σ : Equiv.Perm (Fin n)} :
    x ∘ σ ∈ positiveMarkoffHurwitzSet n a k ↔ x ∈ positiveMarkoffHurwitzSet n a k := by
  simp only [mem_positiveMarkoffHurwitzSet, comp_perm_mem_markoffHurwitzSet_iff,
    Function.comp_apply, σ.forall_congr_right (q := fun i ↦ 0 < x i)]

/-- The three-variable form with coefficient three is the classical Markoff form. -/
@[simp]
theorem markoffHurwitzForm_three (x : Fin 3 → R) :
    markoffHurwitzForm 3 x = markoffForm x := by
  rw [markoffHurwitzForm_def, markoffForm_eq, Fin.sum_univ_three, Fin.prod_univ_three]
  ring

/-- The three-variable zero level with coefficient three is the classical Markoff surface. -/
@[simp]
theorem markoffHurwitzSet_three : markoffHurwitzSet 3 (3 : R) 0 = markoffSet R := by
  ext x
  simp only [mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq, markoffHurwitzForm_three,
    mem_markoffSet_iff_markoffForm_eq_zero]

/-- The positive three-variable zero level with coefficient three is the classical positive
Markoff locus. -/
@[simp]
theorem positiveMarkoffHurwitzSet_three :
    positiveMarkoffHurwitzSet 3 3 0 = positiveMarkoffTriples := by
  ext x
  rw [mem_positiveMarkoffHurwitzSet, markoffHurwitzSet_three, mem_positiveMarkoffTriples]

/-! ## Vieta involutions -/

/-- The Vieta move at `i` replaces `x i` by `a * ∏_{j ≠ i} x j - x i`. -/
def markoffHurwitzMove (a : R) (i : Fin n) (x : Fin n → R) : Fin n → R :=
  Function.update x i (a * (∏ j ∈ univ.erase i, x j) - x i)

/-- The new value of the moved coordinate. -/
@[simp]
theorem markoffHurwitzMove_apply_self (a : R) (i : Fin n) (x : Fin n → R) :
    markoffHurwitzMove a i x i = a * (∏ j ∈ univ.erase i, x j) - x i := by
  simp [markoffHurwitzMove]

/-- A Vieta move fixes each coordinate other than the chosen one. -/
@[simp]
theorem markoffHurwitzMove_apply_of_ne (a : R) {i j : Fin n} (h : j ≠ i) (x : Fin n → R) :
    markoffHurwitzMove a i x j = x j := by
  simp [markoffHurwitzMove, h]

/-- Applying the Vieta move at the same index twice restores the original tuple. -/
@[simp]
theorem markoffHurwitzMove_markoffHurwitzMove (a : R) (i : Fin n) (x : Fin n → R) :
    markoffHurwitzMove a i (markoffHurwitzMove a i x) = x := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [markoffHurwitzMove_apply_self]
    simp only [markoffHurwitzMove, prod_update_of_notMem (notMem_erase _ _),
      Function.update_self]
    ring
  · simp [h]

/-- The Vieta move at `i` as an involutive permutation of all ordered tuples. -/
def markoffHurwitzMovePerm (a : R) (i : Fin n) : Equiv.Perm (Fin n → R) :=
  Function.Involutive.toPerm (markoffHurwitzMove a i) (markoffHurwitzMove_markoffHurwitzMove a i)

/-- The Vieta permutation acts by the polynomial move. -/
@[simp]
theorem markoffHurwitzMovePerm_apply (a : R) (i : Fin n) (x : Fin n → R) :
    markoffHurwitzMovePerm a i x = markoffHurwitzMove a i x := (rfl)

/-- A Vieta permutation is its own inverse. -/
@[simp]
theorem markoffHurwitzMovePerm_symm (a : R) (i : Fin n) :
    (markoffHurwitzMovePerm a i).symm = markoffHurwitzMovePerm a i := (rfl)

/-- A Vieta move fixes the origin when there is at least one other coordinate. -/
@[simp]
theorem markoffHurwitzMove_zero (a : R) (i : Fin (n + 2)) :
    markoffHurwitzMove a i 0 = 0 := by
  ext j
  obtain rfl | hj := eq_or_ne j i
  · simp [Finset.prod_const]
  · simp [hj]

/-- A Vieta move commutes with ring homomorphisms, with the coefficient mapped. -/
theorem comp_markoffHurwitzMove (a : R) (i : Fin n) (x : Fin n → R) (f : R →+* S) :
    f ∘ markoffHurwitzMove a i x = markoffHurwitzMove (f a) i (f ∘ x) := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · simp [map_prod]
  · simp [h]

/-- A Vieta move preserves the Markoff–Hurwitz form at every tuple. -/
@[simp]
theorem markoffHurwitzForm_markoffHurwitzMove (a : R) (i : Fin n) (x : Fin n → R) :
    markoffHurwitzForm a (markoffHurwitzMove a i x) = markoffHurwitzForm a x := by
  simp only [markoffHurwitzForm, markoffHurwitzMove]
  have hs (b : R) :
      (∑ j, Function.update x i b j ^ 2) = b ^ 2 + ∑ j ∈ univ.erase i, x j ^ 2 := by
    calc
      _ = ∑ j, Function.update (fun j ↦ x j ^ 2) i (b ^ 2) j :=
        sum_congr rfl fun j _ ↦ Function.apply_update (fun _ (v : R) ↦ v ^ 2) x i b j
      _ = _ := by rw [sum_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
  -- Isolate the moved coordinate in each sum and product.
  rw [hs, prod_update_of_mem (mem_univ i), sdiff_singleton_eq_erase,
    ← add_sum_erase _ (fun j ↦ x j ^ 2) (mem_univ i), ← mul_prod_erase _ x (mem_univ i)]
  ring

/-- A Vieta move preserves each Markoff–Hurwitz level in both directions. -/
@[simp]
theorem markoffHurwitzMove_mem_markoffHurwitzSet_iff {a k : R} {i : Fin n} {x : Fin n → R} :
    markoffHurwitzMove a i x ∈ markoffHurwitzSet n a k ↔ x ∈ markoffHurwitzSet n a k := by
  simp only [mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq, markoffHurwitzForm_markoffHurwitzMove]

/-- In three variables the changed coordinate uses the product of the other two coordinates
in cyclic order. -/
theorem markoffHurwitzMove_apply_self_fin_three (a : R) (i : Fin 3) (x : Fin 3 → R) :
    markoffHurwitzMove a i x i = a * x (i + 1) * x (i + 2) - x i := by
  have h : ∀ j : Fin 3, univ.erase j = {j + 1, j + 2} := by decide
  have hne : ∀ j : Fin 3, j + 1 ≠ j + 2 := by decide
  rw [markoffHurwitzMove_apply_self, h i]
  simp [hne i, mul_assoc]

/-- At coefficient three, the three-variable Vieta moves are the classical Markoff moves. -/
@[simp]
theorem markoffHurwitzMove_three (i : Fin 3) (x : Fin 3 → R) :
    markoffHurwitzMove 3 i x = markoffVieta i x := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [markoffHurwitzMove_apply_self_fin_three, markoffVieta_apply_self]
  · simp [h]

/-! ## Sign changes and the generated group -/

/-- Multiply each coordinate by its assigned sign, encoded as an integer unit. -/
def markoffHurwitzSignChange (R : Type*) [CommRing R] (ε : Fin n → ℤˣ) :
    Equiv.Perm (Fin n → R) :=
  Equiv.piCongrRight fun i ↦ (Units.map (Int.castRingHom R) (ε i)).mulLeft

/-- A sign change acts by multiplication by the cast integer sign in each coordinate. -/
@[simp]
theorem markoffHurwitzSignChange_apply (ε : Fin n → ℤˣ) (x : Fin n → R) (i : Fin n) :
    markoffHurwitzSignChange R ε x i = ((ε i : ℤ) : R) * x i := (rfl)

/-- A sign change whose signs multiply to one preserves the Markoff–Hurwitz form. -/
@[simp]
theorem markoffHurwitzForm_markoffHurwitzSignChange (a : R) (ε : Fin n → ℤˣ)
    (hε : ∏ i, ε i = 1) (x : Fin n → R) :
    markoffHurwitzForm a (markoffHurwitzSignChange R ε x) = markoffHurwitzForm a x := by
  simp only [markoffHurwitzForm, markoffHurwitzSignChange_apply]
  -- The sign condition controls the product, while each individual square is unchanged.
  have hs (i : Fin n) : (((ε i : ℤ) : R) * x i) ^ 2 = x i ^ 2 := by
    have hi : ((ε i : ℤ) : R) ^ 2 = 1 := by
      rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]
    rw [mul_pow, hi, one_mul]
  have hp : ∏ i, ((ε i : ℤ) : R) = 1 := by
    rw [← Int.cast_prod, ← Units.coe_prod, hε, Units.val_one, Int.cast_one]
  rw [Finset.sum_congr rfl (fun i _ ↦ hs i), Finset.prod_mul_distrib, hp, one_mul]

/-- Even sign changes preserve every level of the Markoff–Hurwitz form. -/
@[simp]
theorem markoffHurwitzSignChange_mem_markoffHurwitzSet_iff {a k : R} {ε : Fin n → ℤˣ}
    (hε : ∏ i, ε i = 1) {x : Fin n → R} :
    markoffHurwitzSignChange R ε x ∈ markoffHurwitzSet n a k ↔ x ∈ markoffHurwitzSet n a k := by
  simp only [mem_markoffHurwitzSet_iff_markoffHurwitzForm_eq,
    markoffHurwitzForm_markoffHurwitzSignChange a ε hε]

/-- The narrow Markoff–Hurwitz group is generated by coordinate permutations and even sign
changes. A coordinate permutation acts by precomposition with its inverse. -/
def markoffHurwitzNarrowGroup (n : ℕ) (R : Type*) [CommRing R] :
    Subgroup (Equiv.Perm (Fin n → R)) :=
  Subgroup.closure (Set.range (Equiv.piCongrLeft' (fun _ : Fin n ↦ R)) ∪
    markoffHurwitzSignChange R '' {ε : Fin n → ℤˣ | ∏ i, ε i = 1})

/-- A subgroup contains the narrow group exactly when it contains every coordinate permutation
and even sign change. -/
theorem markoffHurwitzNarrowGroup_le_iff {H : Subgroup (Equiv.Perm (Fin n → R))} :
    markoffHurwitzNarrowGroup n R ≤ H ↔
      (∀ σ : Equiv.Perm (Fin n), Equiv.piCongrLeft' (fun _ ↦ R) σ ∈ H) ∧
        ∀ ε : Fin n → ℤˣ, (∏ i, ε i = 1) → markoffHurwitzSignChange R ε ∈ H := by
  rw [markoffHurwitzNarrowGroup, Subgroup.closure_le, Set.union_subset_iff,
    Set.range_subset_iff, Set.subset_def, Set.forall_mem_image]
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]

/-- The Markoff–Hurwitz group adjoins the Vieta permutations to the narrow group. -/
def markoffHurwitzGroup (n : ℕ) (a : R) : Subgroup (Equiv.Perm (Fin n → R)) :=
  markoffHurwitzNarrowGroup n R ⊔ Subgroup.closure (Set.range (markoffHurwitzMovePerm a))

/-- A subgroup contains the Markoff–Hurwitz group exactly when it contains the narrow group
and all Vieta permutations. -/
theorem markoffHurwitzGroup_le_iff {a : R} {H : Subgroup (Equiv.Perm (Fin n → R))} :
    markoffHurwitzGroup n a ≤ H ↔
      markoffHurwitzNarrowGroup n R ≤ H ∧ ∀ i : Fin n, markoffHurwitzMovePerm a i ∈ H := by
  simp [markoffHurwitzGroup, sup_le_iff, Subgroup.closure_le, Set.range_subset_iff]

/-- The narrow group is a subgroup of the Markoff–Hurwitz group at any coefficient. -/
theorem markoffHurwitzNarrowGroup_le_markoffHurwitzGroup (n : ℕ) (a : R) :
    markoffHurwitzNarrowGroup n R ≤ markoffHurwitzGroup n a := by
  unfold markoffHurwitzGroup
  exact le_sup_left

/-- Each Vieta permutation belongs to the Markoff–Hurwitz group. -/
theorem markoffHurwitzMovePerm_mem_markoffHurwitzGroup (a : R) (i : Fin n) :
    markoffHurwitzMovePerm a i ∈ markoffHurwitzGroup n a :=
  (markoffHurwitzGroup_le_iff.mp le_rfl).2 i

/-- Every coordinate permutation belongs to the narrow Markoff–Hurwitz group. -/
theorem piCongrLeft'_mem_markoffHurwitzNarrowGroup (R : Type*) [CommRing R]
    (σ : Equiv.Perm (Fin n)) :
    Equiv.piCongrLeft' (fun _ ↦ R) σ ∈ markoffHurwitzNarrowGroup n R :=
  (markoffHurwitzNarrowGroup_le_iff.mp le_rfl).1 σ

/-- Every even sign change belongs to the narrow Markoff–Hurwitz group. -/
theorem markoffHurwitzSignChange_mem_markoffHurwitzNarrowGroup (R : Type*) [CommRing R]
    {ε : Fin n → ℤˣ} (hε : ∏ i, ε i = 1) :
    markoffHurwitzSignChange R ε ∈ markoffHurwitzNarrowGroup n R :=
  (markoffHurwitzNarrowGroup_le_iff.mp le_rfl).2 ε hε

/-- The generated Markoff–Hurwitz group stabilizes the hypersurface of every level. -/
theorem markoffHurwitzGroup_le_stabilizer (a k : R) :
    markoffHurwitzGroup n a ≤ MulAction.stabilizer _ (markoffHurwitzSet n a k) := by
  rw [markoffHurwitzGroup_le_iff, markoffHurwitzNarrowGroup_le_iff]
  refine ⟨⟨fun σ ↦ ?_, fun ε hε ↦ ?_⟩, fun i ↦ ?_⟩ <;>
    rw [MulAction.mem_stabilizer_set] <;> intro x
  · rw [Equiv.Perm.smul_def, funext (Equiv.piCongrLeft'_apply _ σ x),
      ← Function.comp_def x σ.symm]
    exact comp_perm_mem_markoffHurwitzSet_iff
  · exact markoffHurwitzSignChange_mem_markoffHurwitzSet_iff hε
  · simpa only [Equiv.Perm.smul_def, markoffHurwitzMovePerm_apply] using
      (markoffHurwitzMove_mem_markoffHurwitzSet_iff (i := i) (a := a) (k := k) (x := x))

/-- Every element of the Markoff–Hurwitz group preserves membership in each level set. -/
theorem apply_mem_markoffHurwitzSet_iff {a k : R} {g : Equiv.Perm (Fin n → R)}
    (hg : g ∈ markoffHurwitzGroup n a) {x : Fin n → R} :
    g x ∈ markoffHurwitzSet n a k ↔ x ∈ markoffHurwitzSet n a k :=
  MulAction.mem_stabilizer_set.mp (markoffHurwitzGroup_le_stabilizer a k hg) x

end TauCeti
