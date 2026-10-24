/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic

import TauCeti.Algebra.Order.Field.HalfInteger
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.CosetNorm
import TauCeti.Data.Int.SumSquares

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

* `TauCeti.IntegralLattice.div_four_le_checkerboardLattice_form_self`: vectors with all
  coordinates in `ℤ + 1/2` have norm at least `n / 4`.
* `TauCeti.IntegralLattice.isLeast_form_self_checkerboardVectorClass`,
  `isLeast_form_self_checkerboardSpinorClass`, `isLeast_form_self_checkerboardCospinorClass`:
  the minimum norms `1`, `n / 4` and `n / 4` of the three nonzero cosets.
* `TauCeti.IntegralLattice.isLeast_form_self_zmodTwoProdAddEquivCheckerboardDiscriminantGroup`,
  `isLeast_form_self_zmodFourAddEquivCheckerboardDiscriminantGroup`: the same minima, indexed by
  the label of the class in `ℤ/2 × ℤ/2` (even `n`) or `ℤ/4` (odd `n`).
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

/-- A vector of the vector coset has integral coordinates. -/
private theorem exists_int_of_sub_checkerboardVector_mem [NeZero n] {x : Fin n → ℚ}
    (hx : x - checkerboardVector n ∈ checkerboardCarrier n) :
    ∃ z : Fin n → ℤ, ∀ i, x i = (z i : ℚ) := by
  choose w hw using ((mem_checkerboardCarrier_iff _).mp hx).1
  refine ⟨fun i ↦ w i + if i = checkerboardLastIndex n then 1 else 0, fun i ↦ ?_⟩
  have := hw i
  rw [Pi.sub_apply, checkerboardVector_apply] at this
  push_cast
  split_ifs at this ⊢ <;> linarith

/-- A norm-one vector of the vector coset is `±eᵢ`: one integral coordinate is nonzero, so it
has square one and all other coordinates vanish. -/
private theorem exists_eq_single_of_form_self_eq_one [NeZero n] {x : Fin n → ℚ}
    (hx : x - checkerboardVector n ∈ checkerboardCarrier n)
    (hnorm : (checkerboardLattice n).form x x = 1) :
    ∃ i, x = Pi.single i 1 ∨ x = -Pi.single i 1 := by
  obtain ⟨z, hz⟩ := exists_int_of_sub_checkerboardVector_mem hx
  have hsum : ∑ j, z j ^ 2 = 1 := by
    rw [checkerboardLattice_form_apply] at hnorm
    have : ((∑ j, z j ^ 2 : ℤ) : ℚ) = 1 := by
      push_cast
      rw [← hnorm]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hz j, sq]
    exact_mod_cast this
  obtain ⟨i, h | h⟩ := exists_eq_single_or_neg_single_of_sum_sq_eq_one z hsum <;>
    refine ⟨i, ?_⟩ <;> [left; right] <;> funext j <;> rw [hz j, h] <;>
    rcases eq_or_ne j i with rfl | hj <;> simp [*]

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
  have h := (isPosDef_checkerboardLattice n).isPosSemidef.isLeast_form_self_of_form_self_lt_two
    (isEven_checkerboardLattice n)
    (x := ⟨checkerboardVector n, checkerboardVector_mem_dualCarrier⟩)
    ((mk_eq_checkerboardVectorClass_iff _).mpr (by rw [sub_self]; exact zero_mem _))
    (by rw [checkerboardLattice_form_checkerboardVector_self]; norm_num)
  rwa [checkerboardLattice_form_checkerboardVector_self] at h

/-! ## The spinor and cospinor cosets -/

/-- **Vectors with all coordinates in `ℤ + 1/2` have norm at least `n / 4`**, since each
coordinate has square at least `1 / 4`. -/
theorem div_four_le_checkerboardLattice_form_self {x : Fin n → ℚ}
    (hx : ∀ i, ∃ z : ℤ, x i = z + 1 / 2) : (n : ℚ) / 4 ≤ (checkerboardLattice n).form x x := by
  have hsum : ∑ _i : Fin n, (1 / 4 : ℚ) ≤ ∑ i, x i * x i := Finset.sum_le_sum fun i _ ↦ by
    obtain ⟨z, hz⟩ := hx i
    simpa only [hz, sq] using Int.quarter_le_cast_add_half_sq (K := ℚ) z
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
    Finset.sum_eq_sum_iff_of_le (fun i _ ↦ by
      obtain ⟨z, hz⟩ := hx i
      simpa only [hz, sq] using Int.quarter_le_cast_add_half_sq (K := ℚ) z)]
  have hquarter : (1 / 4 : ℚ) = 1 / 2 * (1 / 2) := by norm_num
  refine forall_congr' fun i ↦ ?_
  rw [imp_iff_right (Finset.mem_univ i), eq_comm, hquarter, mul_self_eq_mul_self_iff]

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

/-! ## Minima indexed by labels -/

/-- **The minimum norm of each discriminant class of `Dₙ`, `n` even.**  The class labelled
`b : ZMod 2 × ZMod 2` by `zmodTwoProdAddEquivCheckerboardDiscriminantGroup` has minimum norm `0`
for `b = 0`, `1` for the vector label `(1, 0)`, and `n / 4` for the spinor and cospinor labels
`(0, 1)` and `(1, 1)`. -/
theorem isLeast_form_self_zmodTwoProdAddEquivCheckerboardDiscriminantGroup [NeZero n]
    (hn : Even n) (b : ZMod 2 × ZMod 2) :
    IsLeast {q : ℚ | ∃ x : (checkerboardLattice n).dualCarrier,
      Submodule.Quotient.mk x = zmodTwoProdAddEquivCheckerboardDiscriminantGroup n hn b ∧
        (checkerboardLattice n).form x x = q}
      (if b = 0 then 0 else if b = (1, 0) then 1 else (n : ℚ) / 4) := by
  obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = (1, 0) ∨ b = (0, 1) ∨ b = (1, 1) := by
    revert b; decide
  · rw [ite_eq_left rfl, map_zero]
    exact (isPosDef_checkerboardLattice n).isPosSemidef.isLeast_form_self_zero
  · rw [ite_eq_right (by decide), ite_eq_left rfl,
      zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero]
    exact isLeast_form_self_checkerboardVectorClass
  · rw [ite_eq_right (by decide), ite_eq_right (by decide),
      zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one]
    exact isLeast_form_self_checkerboardSpinorClass
  · rw [ite_eq_right (by decide), ite_eq_right (by decide),
      zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one]
    exact isLeast_form_self_checkerboardCospinorClass

/-- **The minimum norm of each discriminant class of `Dₙ`, `n` odd.**  The class labelled
`b : ZMod 4` by `zmodFourAddEquivCheckerboardDiscriminantGroup` has minimum norm `0` for `b = 0`,
`1` for the vector label `2`, and `n / 4` for the spinor and cospinor labels `1` and `3`. -/
theorem isLeast_form_self_zmodFourAddEquivCheckerboardDiscriminantGroup (hn : Odd n)
    (b : ZMod 4) :
    IsLeast {q : ℚ | ∃ x : (checkerboardLattice n).dualCarrier,
      Submodule.Quotient.mk x = zmodFourAddEquivCheckerboardDiscriminantGroup n hn b ∧
        (checkerboardLattice n).form x x = q}
      (if b = 0 then 0 else if b = 2 then 1 else (n : ℚ) / 4) := by
  have : NeZero n := NeZero.of_pos hn.pos
  obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
    revert b; decide
  · rw [ite_eq_left rfl, map_zero]
    exact (isPosDef_checkerboardLattice n).isPosSemidef.isLeast_form_self_zero
  · rw [ite_eq_right (by decide), ite_eq_right (by decide),
      zmodFourAddEquivCheckerboardDiscriminantGroup_apply_one]
    exact isLeast_form_self_checkerboardSpinorClass
  · rw [ite_eq_right (by decide), ite_eq_left rfl, ← checkerboardCyclicQuadraticIsometry_apply,
      checkerboardCyclicQuadraticIsometry_two]
    exact isLeast_form_self_checkerboardVectorClass
  · rw [ite_eq_right (by decide), ite_eq_right (by decide),
      zmodFourAddEquivCheckerboardDiscriminantGroup_apply_three]
    exact isLeast_form_self_checkerboardCospinorClass

end TauCeti.IntegralLattice
