/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic

import TauCeti.Algebra.Order.Field.HalfInteger

/-!
# Shortest vectors in the discriminant cosets of `Dₙ`

The discriminant group of the checkerboard lattice `Dₙ` consists of the classes of `0`, of the
vector representative `v = eₙ`, of the spinor representative `s = (1/2, …, 1/2)` and of the
cospinor representative `c = s - eₙ`.  This file computes the minimum norm of each nonzero
coset, together with the vectors attaining it:

* the vector coset `v + Dₙ` consists of the integer vectors with odd coordinate sum; its minimum
  norm is `1`, attained exactly by the `2n` vectors `±eᵢ`;
* the spinor and cospinor cosets consist of the vectors with all coordinates in `ℤ + 1/2`, split
  by the parity of the coordinate sum of `x - s`; their minimum norm is `n / 4`, attained exactly
  by the vectors with all coordinates `±1/2` whose number of negative coordinates is even (for
  `s`) or odd (for `c`).

These are the shortest-norm values attached to the Conway–Sloane glue labels `[2] = v`,
`[1] = s` and `[3] = c` of a `Dₙ` component, the input for bounding the norm of a glue vector
in an orthogonal sum of root lattices.  The minima are stated as `IsLeast` over the norms of the
actual dual-lattice vectors in each discriminant class, so they record attainment as well as the
lower bound.

## Main results

* `TauCeti.IntegralLattice.one_le_checkerboardLattice_form_self_of_sub_checkerboardVector_mem`:
  vectors of the vector coset have norm at least `1`.
* `TauCeti.IntegralLattice.div_four_le_checkerboardLattice_form_self`: vectors with all
  coordinates in `ℤ + 1/2` have norm at least `n / 4`.
* `TauCeti.IntegralLattice.isLeast_form_self_checkerboardVectorClass`,
  `isLeast_form_self_checkerboardSpinorClass`, `isLeast_form_self_checkerboardCospinorClass`:
  the minimum norms `1`, `n / 4` and `n / 4` of the three nonzero cosets.
* `TauCeti.IntegralLattice.sub_checkerboardVector_mem_and_form_self_eq_one_iff`,
  `sub_checkerboardSpinor_mem_and_form_self_eq_iff`,
  `sub_checkerboardCospinor_mem_and_form_self_eq_iff`: the minimal vectors of each coset.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, §4.7.1 and
  Chapter 16, §1.
-/

public section

namespace TauCeti.IntegralLattice

open Finset

variable {n : ℕ}

/-! ## The vector coset -/

/-- A vector of the vector coset has integral coordinates, not all zero since their sum is odd;
a nonzero coordinate has square at least one. -/
private theorem exists_int_of_sub_checkerboardVector_mem [NeZero n] {x : Fin n → ℚ}
    (hx : x - checkerboardVector n ∈ checkerboardCarrier n) :
    ∃ z : Fin n → ℤ, (∀ i, x i = (z i : ℚ)) ∧ ∃ i, 1 ≤ z i * z i := by
  choose w hw using ((mem_checkerboardCarrier_iff _).mp hx).1
  have hx_eq (i : Fin n) :
      x i = ((w i + if i = checkerboardLastIndex n then 1 else 0 : ℤ) : ℚ) := by
    have := hw i
    rw [Pi.sub_apply, checkerboardVector_apply] at this
    push_cast
    split_ifs at this ⊢ <;> linarith
  refine ⟨_, hx_eq, ?_⟩
  have hodd : Odd (∑ i, (w i + if i = checkerboardLastIndex n then 1 else 0)) := by
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
    exact ((mem_checkerboardCarrier_iff_even_sum w hw).mp hx).add_one
  obtain ⟨i, hi⟩ : ∃ i, (w i + if i = checkerboardLastIndex n then 1 else 0) ≠ 0 := by
    by_contra! h
    simp [h] at hodd
  refine ⟨i, ?_⟩
  rw [← abs_mul_abs_self]
  exact one_le_mul_of_one_le_of_one_le (Int.one_le_abs hi) (Int.one_le_abs hi)

/-- **Vectors of the vector coset have norm at least one.**  Their coordinates are integers with
odd sum, so at least one of them is nonzero. -/
theorem one_le_checkerboardLattice_form_self_of_sub_checkerboardVector_mem [NeZero n]
    {x : Fin n → ℚ} (hx : x - checkerboardVector n ∈ checkerboardCarrier n) :
    1 ≤ (checkerboardLattice n).form x x := by
  obtain ⟨z, hz, i, hone⟩ := exists_int_of_sub_checkerboardVector_mem hx
  rw [checkerboardLattice_form_apply]
  have hle : x i * x i ≤ ∑ j, x j * x j :=
    Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (x j)) (Finset.mem_univ i)
  have hone' : (1 : ℚ) ≤ x i * x i := by rw [hz i]; exact_mod_cast hone
  linarith

/-- A norm-one vector of the vector coset is `±eᵢ`: one integral coordinate is nonzero, so it
has square one and all other coordinates vanish. -/
private theorem exists_eq_single_of_form_self_eq_one [NeZero n] {x : Fin n → ℚ}
    (hx : x - checkerboardVector n ∈ checkerboardCarrier n)
    (hnorm : (checkerboardLattice n).form x x = 1) :
    ∃ i, x = Pi.single i 1 ∨ x = -Pi.single i 1 := by
  obtain ⟨z, hz, i, hone⟩ := exists_int_of_sub_checkerboardVector_mem hx
  have hsum : ∑ j, z j * z j = 1 := by
    rw [checkerboardLattice_form_apply] at hnorm
    have : ((∑ j, z j * z j : ℤ) : ℚ) = 1 := by
      push_cast
      rw [← hnorm]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hz j]
    exact_mod_cast this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  have hrest : ∑ j ∈ univ.erase i, z j * z j = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun j _ ↦ mul_self_nonneg (z j))
  have hzero (j : Fin n) (hj : j ≠ i) : z j = 0 :=
    mul_self_eq_zero.mp <| (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ mul_self_nonneg (z k)).mp
      hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  refine ⟨i, ?_⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one (by linarith : z i * z i = 1) with h | h <;>
    [left; right] <;> funext j <;> rcases eq_or_ne j i with rfl | hj <;> simp [*]

/-- **The minimal vectors of the vector coset.**  A vector `x` with `x - v ∈ Dₙ` has norm one
exactly when it is one of the `2n` vectors `±eᵢ`. -/
theorem sub_checkerboardVector_mem_and_form_self_eq_one_iff [NeZero n] (x : Fin n → ℚ) :
    x - checkerboardVector n ∈ checkerboardCarrier n ∧ (checkerboardLattice n).form x x = 1 ↔
      ∃ i, x = Pi.single i 1 ∨ x = -Pi.single i 1 := by
  constructor
  · exact fun ⟨hx, hnorm⟩ ↦ exists_eq_single_of_form_self_eq_one hx hnorm
  · rintro ⟨i, hx | hx⟩ <;> subst hx
    · refine ⟨mem_checkerboardCarrier_of
        (fun j ↦ (if j = i then 1 else 0) - if j = checkerboardLastIndex n then 1 else 0)
        (fun j ↦ ?_) ?_, ?_⟩
      · simp only [Pi.sub_apply, Pi.single_apply, checkerboardVector_apply]
        push_cast
        split_ifs <;> norm_num
      · simp [Finset.sum_sub_distrib]
      · rw [checkerboardLattice_form_single, Pi.single_eq_same, mul_one]
    · refine ⟨mem_checkerboardCarrier_of
        (fun j ↦ -(if j = i then 1 else 0) - if j = checkerboardLastIndex n then 1 else 0)
        (fun j ↦ ?_) ?_, ?_⟩
      · simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_apply, checkerboardVector_apply]
        push_cast
        split_ifs <;> norm_num
      · simp [Finset.sum_sub_distrib]
      · simp

/-- **The minimum norm of the vector coset of `Dₙ` is `1`**: it is attained by `v = eₙ` and
bounds the norm of every dual vector in the vector class. -/
theorem isLeast_form_self_checkerboardVectorClass [NeZero n] :
    IsLeast {q : ℚ | ∃ x : (checkerboardLattice n).dualCarrier,
      Submodule.Quotient.mk x = checkerboardVectorClass n ∧
        (checkerboardLattice n).form x x = q} 1 := by
  refine ⟨⟨⟨checkerboardVector n, checkerboardVector_mem_dualCarrier⟩,
    (mk_eq_checkerboardVectorClass_iff _).mpr (by rw [sub_self]; exact zero_mem _),
    checkerboardLattice_form_checkerboardVector_self⟩, ?_⟩
  rintro q ⟨x, hx, rfl⟩
  exact one_le_checkerboardLattice_form_self_of_sub_checkerboardVector_mem
    ((mk_eq_checkerboardVectorClass_iff x).mp hx)

/-! ## The spinor and cospinor cosets -/

/-- A rational number in `ℤ + 1/2` has square at least `1 / 4`: the coordinatewise form of
`Int.quarter_le_cast_add_half_sq`. -/
private theorem one_div_four_le_mul_self {y : ℚ} (hy : ∃ z : ℤ, y = z + 1 / 2) :
    1 / 4 ≤ y * y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← sq]
  exact Int.quarter_le_cast_add_half_sq z

/-- **Vectors with all coordinates in `ℤ + 1/2` have norm at least `n / 4`**, since each
coordinate has square at least `1 / 4`. -/
theorem div_four_le_checkerboardLattice_form_self {x : Fin n → ℚ}
    (hx : ∀ i, ∃ z : ℤ, x i = z + 1 / 2) : (n : ℚ) / 4 ≤ (checkerboardLattice n).form x x := by
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ univ) ↦ one_div_four_le_mul_self (hx i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [checkerboardLattice_form_apply]
  linarith

/-- A vector of the spinor coset has all coordinates in `ℤ + 1/2`. -/
private theorem exists_int_add_half_of_sub_checkerboardSpinor_mem {x : Fin n → ℚ}
    (hx : x - checkerboardSpinor n ∈ checkerboardCarrier n) (i : Fin n) :
    ∃ z : ℤ, x i = z + 1 / 2 := by
  obtain ⟨z, hz⟩ := ((mem_checkerboardCarrier_iff _).mp hx).1 i
  exact ⟨z, by rw [← hz, Pi.sub_apply, checkerboardSpinor_apply]; ring⟩

/-- A vector of the cospinor coset has all coordinates in `ℤ + 1/2`. -/
private theorem exists_int_add_half_of_sub_checkerboardCospinor_mem [NeZero n] {x : Fin n → ℚ}
    (hx : x - checkerboardCospinor n ∈ checkerboardCarrier n) (i : Fin n) :
    ∃ z : ℤ, x i = z + 1 / 2 := by
  obtain ⟨z, hz⟩ := ((mem_checkerboardCarrier_iff _).mp hx).1 i
  refine ⟨z - if i = checkerboardLastIndex n then 1 else 0, ?_⟩
  rw [Pi.sub_apply, checkerboardCospinor_apply] at hz
  push_cast
  linarith

/-- A vector with coordinates in `ℤ + 1/2` has norm `n / 4` exactly when all of its coordinates
are `±1/2`. -/
private theorem form_self_eq_div_four_iff {x : Fin n → ℚ}
    (hx : ∀ i, ∃ z : ℤ, x i = z + 1 / 2) :
    (checkerboardLattice n).form x x = n / 4 ↔ ∀ i, x i = 1 / 2 ∨ x i = -(1 / 2) := by
  have hconst : (n : ℚ) / 4 = ∑ _i : Fin n, (1 / 4 : ℚ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [checkerboardLattice_form_apply, hconst, eq_comm,
    Finset.sum_eq_sum_iff_of_le fun i _ ↦ one_div_four_le_mul_self (hx i)]
  refine forall_congr' fun i ↦ ?_
  rw [imp_iff_right (Finset.mem_univ i), eq_comm, show (1 / 4 : ℚ) = 1 / 2 * (1 / 2) by norm_num,
    mul_self_eq_mul_self_iff]

/-- For a vector with all coordinates `±1/2`, the coordinates of `x - s` are `0` or `-1`, and
their sum is minus the number of negative coordinates. -/
private theorem sub_checkerboardSpinor_eq {x : Fin n → ℚ}
    (hx : ∀ i, x i = 1 / 2 ∨ x i = -(1 / 2)) (i : Fin n) :
    (x - checkerboardSpinor n) i = ((-if x i = -(1 / 2) then 1 else 0 : ℤ) : ℚ) := by
  rw [Pi.sub_apply, checkerboardSpinor_apply]
  rcases hx i with h | h <;> rw [h] <;> norm_num

/-- A `±1/2` vector lies in the spinor coset exactly when it has an even number of negative
coordinates. -/
private theorem sub_checkerboardSpinor_mem_iff {x : Fin n → ℚ}
    (hx : ∀ i, x i = 1 / 2 ∨ x i = -(1 / 2)) :
    x - checkerboardSpinor n ∈ checkerboardCarrier n ↔ Even #{i | x i = -(1 / 2)} := by
  rw [mem_checkerboardCarrier_iff_even_sum _ (sub_checkerboardSpinor_eq hx), Finset.sum_neg_distrib,
    even_neg, Finset.sum_boole, Int.even_coe_nat]

/-- A `±1/2` vector lies in the cospinor coset exactly when it has an odd number of negative
coordinates. -/
private theorem sub_checkerboardCospinor_mem_iff [NeZero n] {x : Fin n → ℚ}
    (hx : ∀ i, x i = 1 / 2 ∨ x i = -(1 / 2)) :
    x - checkerboardCospinor n ∈ checkerboardCarrier n ↔ Odd #{i | x i = -(1 / 2)} := by
  have hcoord (i : Fin n) : (x - checkerboardCospinor n) i =
      ((-(if x i = -(1 / 2) then 1 else 0) + if i = checkerboardLastIndex n then 1 else 0 : ℤ) :
        ℚ) := by
    have := sub_checkerboardSpinor_eq hx i
    rw [Pi.sub_apply, checkerboardSpinor_apply] at this
    rw [Pi.sub_apply, checkerboardCospinor_apply]
    push_cast at this ⊢
    linarith
  rw [mem_checkerboardCarrier_iff_even_sum _ hcoord, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Fintype.sum_ite_eq',
    Finset.sum_boole, even_add_one, odd_neg, Int.odd_coe_nat]

/-- **Vectors of the spinor coset have norm at least `n / 4`.** -/
theorem div_four_le_checkerboardLattice_form_self_of_sub_checkerboardSpinor_mem
    {x : Fin n → ℚ} (hx : x - checkerboardSpinor n ∈ checkerboardCarrier n) :
    (n : ℚ) / 4 ≤ (checkerboardLattice n).form x x :=
  div_four_le_checkerboardLattice_form_self (exists_int_add_half_of_sub_checkerboardSpinor_mem hx)

/-- **Vectors of the cospinor coset have norm at least `n / 4`.** -/
theorem div_four_le_checkerboardLattice_form_self_of_sub_checkerboardCospinor_mem [NeZero n]
    {x : Fin n → ℚ} (hx : x - checkerboardCospinor n ∈ checkerboardCarrier n) :
    (n : ℚ) / 4 ≤ (checkerboardLattice n).form x x :=
  div_four_le_checkerboardLattice_form_self
    (exists_int_add_half_of_sub_checkerboardCospinor_mem hx)

/-- **The minimal vectors of the spinor coset.**  A vector `x` with `x - s ∈ Dₙ` has norm `n / 4`
exactly when all of its coordinates are `±1/2` and an even number of them are negative. -/
theorem sub_checkerboardSpinor_mem_and_form_self_eq_iff (x : Fin n → ℚ) :
    x - checkerboardSpinor n ∈ checkerboardCarrier n ∧
        (checkerboardLattice n).form x x = n / 4 ↔
      (∀ i, x i = 1 / 2 ∨ x i = -(1 / 2)) ∧ Even #{i | x i = -(1 / 2)} := by
  constructor
  · rintro ⟨hx, hnorm⟩
    have hhalf :=
      (form_self_eq_div_four_iff (exists_int_add_half_of_sub_checkerboardSpinor_mem hx)).mp hnorm
    exact ⟨hhalf, (sub_checkerboardSpinor_mem_iff hhalf).mp hx⟩
  · rintro ⟨hhalf, heven⟩
    have hx := (sub_checkerboardSpinor_mem_iff hhalf).mpr heven
    exact ⟨hx, (form_self_eq_div_four_iff
      (exists_int_add_half_of_sub_checkerboardSpinor_mem hx)).mpr hhalf⟩

/-- **The minimal vectors of the cospinor coset.**  A vector `x` with `x - c ∈ Dₙ` has norm
`n / 4` exactly when all of its coordinates are `±1/2` and an odd number of them are
negative. -/
theorem sub_checkerboardCospinor_mem_and_form_self_eq_iff [NeZero n] (x : Fin n → ℚ) :
    x - checkerboardCospinor n ∈ checkerboardCarrier n ∧
        (checkerboardLattice n).form x x = n / 4 ↔
      (∀ i, x i = 1 / 2 ∨ x i = -(1 / 2)) ∧ Odd #{i | x i = -(1 / 2)} := by
  constructor
  · rintro ⟨hx, hnorm⟩
    have hhalf :=
      (form_self_eq_div_four_iff (exists_int_add_half_of_sub_checkerboardCospinor_mem hx)).mp
        hnorm
    exact ⟨hhalf, (sub_checkerboardCospinor_mem_iff hhalf).mp hx⟩
  · rintro ⟨hhalf, hodd⟩
    have hx := (sub_checkerboardCospinor_mem_iff hhalf).mpr hodd
    exact ⟨hx, (form_self_eq_div_four_iff
      (exists_int_add_half_of_sub_checkerboardCospinor_mem hx)).mpr hhalf⟩

/-- **The minimum norm of the spinor coset of `Dₙ` is `n / 4`**: it is attained by
`s = (1/2, …, 1/2)` and bounds the norm of every dual vector in the spinor class. -/
theorem isLeast_form_self_checkerboardSpinorClass :
    IsLeast {q : ℚ | ∃ x : (checkerboardLattice n).dualCarrier,
      Submodule.Quotient.mk x = checkerboardSpinorClass n ∧
        (checkerboardLattice n).form x x = q} ((n : ℚ) / 4) := by
  refine ⟨⟨⟨checkerboardSpinor n, checkerboardSpinor_mem_dualCarrier⟩,
    (mk_eq_checkerboardSpinorClass_iff _).mpr (by rw [sub_self]; exact zero_mem _),
    checkerboardLattice_form_checkerboardSpinor_self⟩, ?_⟩
  rintro q ⟨x, hx, rfl⟩
  exact div_four_le_checkerboardLattice_form_self_of_sub_checkerboardSpinor_mem
    ((mk_eq_checkerboardSpinorClass_iff x).mp hx)

/-- **The minimum norm of the cospinor coset of `Dₙ` is `n / 4`**: it is attained by
`c = (1/2, …, 1/2, -1/2)` and bounds the norm of every dual vector in the cospinor class. -/
theorem isLeast_form_self_checkerboardCospinorClass [NeZero n] :
    IsLeast {q : ℚ | ∃ x : (checkerboardLattice n).dualCarrier,
      Submodule.Quotient.mk x = checkerboardCospinorClass n ∧
        (checkerboardLattice n).form x x = q} ((n : ℚ) / 4) := by
  refine ⟨⟨⟨checkerboardCospinor n, checkerboardCospinor_mem_dualCarrier⟩,
    (mk_eq_checkerboardCospinorClass_iff _).mpr (by rw [sub_self]; exact zero_mem _),
    checkerboardLattice_form_checkerboardCospinor_self⟩, ?_⟩
  rintro q ⟨x, hx, rfl⟩
  exact div_four_le_checkerboardLattice_form_self_of_sub_checkerboardCospinor_mem
    ((mk_eq_checkerboardCospinorClass_iff x).mp hx)

end TauCeti.IntegralLattice
