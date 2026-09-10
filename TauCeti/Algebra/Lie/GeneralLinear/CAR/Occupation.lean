/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Clifford

/-!
# Occupation elements in the CAR algebra

For the Clifford algebra of the trace form on matrices, write `dᵢⱼ = ι(Eᵢⱼ)`. This file studies
the normalized quadratic elements

`pᵢⱼ = 1/2 dᵢⱼ dⱼᵢ`.

When `i ≠ j`, these are occupation projections for the hyperbolic plane spanned by `Eᵢⱼ` and
`Eⱼᵢ`. Their two orders are orthogonal. When `2` is invertible, the CAR relations also give
`pᵢⱼ + pⱼᵢ = 1`; in characteristic two the normalization vanishes instead, so the elements remain
idempotent in every characteristic. All of the occupation elements commute with one another.
Finally, the diagonal normal-ordered lift is the sum `Fᵢᵢ = ∑ k, pᵢₖ`; for a linearly ordered index
type this can be oriented using only the positive pairs. These formulas supply the commuting
off-diagonal zero-one operators used to calculate weights in the left regular CAR module.

## Main definitions

* `TauCeti.carOccupationElement`: the normalized quadratic element `pᵢⱼ`.

## Main results

* `TauCeti.carOccupationElement_add_swap`: `pᵢⱼ + pⱼᵢ = 1`.
* `TauCeti.isIdempotentElem_carOccupationElement`: off-diagonal `pᵢⱼ` are idempotent.
* `TauCeti.carOccupationElement_mul_self`: the corresponding multiplication normal form.
* `TauCeti.commute_carOccupationElement`: all occupation elements commute.
* `TauCeti.glCliffordHom_single_self_eq_sum_occupation`: `Fᵢᵢ = ∑ k, pᵢₖ`.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*,
  Transformation Groups 6 (2001), 371–396, Proposition 2.4 and Example 2.5(1).
* D. Shlyakhtenko, *Failure of Strong Convergence of Matrices with Fermionic Entries*,
  arXiv:2606.28648, §2.3.
* D. Shlyakhtenko, [`car-matrices`](https://github.com/shlyakhtenko/car-matrices),
  `MatrixNormShort/SpinExtraction.lean` at commit `659be0c6466c3ef9dbbe0e0a313f2cbb2c37d5f9`,
  the related Lean formalization of pair projectors and their commutation and idempotence.
* C. Chevalley, *The Algebraic Theory of Spinors*, Columbia University Press, 1954.
-/

public section

namespace TauCeti

open CliffordAlgebra

variable {K n : Type*} [Field K] [Fintype n]

attribute [local instance] Classical.decEq

private noncomputable abbrev carD (i j : n) :
    CliffordAlgebra (traceQuadraticForm K n) :=
  ι (traceQuadraticForm K n) (Matrix.single i j 1)

private theorem polar_single_single_eq_zero (i j k l : n)
    (h : ¬(j = k ∧ l = i)) :
    QuadraticMap.polar (traceQuadraticForm K n)
      (Matrix.single i j 1) (Matrix.single k l 1) = 0 := by
  rw [← QuadraticMap.polarBilin_apply_apply, polarBilin_traceQuadraticForm,
    ← traceBilinForm_apply, traceBilinForm_single_single, ite_eq_right h]
  simp

/-- The occupation element for the ordered matrix-unit pair `(i, j)`, normalized so that it is an
idempotent off the diagonal. For `i = j` it is the scalar `1/2`. -/
noncomputable def carOccupationElement (i j : n) :
    CliffordAlgebra (traceQuadraticForm K n) :=
  (2 : K)⁻¹ • (carD i j * carD j i)

/-- The occupation element written directly in terms of the two matrix-unit generators. -/
theorem carOccupationElement_def [decEq : DecidableEq n] (i j : n) :
    carOccupationElement (K := K) i j =
      (2 : K)⁻¹ •
        (ι (traceQuadraticForm K n) (Matrix.single i j 1) *
          ι (traceQuadraticForm K n) (Matrix.single j i 1)) := by
  cases Subsingleton.elim decEq (Classical.decEq n)
  rfl

/-- The diagonal occupation element is the scalar `1/2`. -/
@[simp]
theorem carOccupationElement_self (i : n) :
    carOccupationElement (K := K) i i = (2 : K)⁻¹ • 1 := by
  simp [carOccupationElement, carD]

/-- Oppositely oriented off-diagonal occupation elements are orthogonal in this order. -/
@[simp]
theorem carOccupationElement_mul_swap {i j : n} (hij : i ≠ j) :
    carOccupationElement (K := K) i j * carOccupationElement (K := K) j i = 0 := by
  rw [carOccupationElement, carOccupationElement, smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Expose the common scalar and reassociate so `simp` can see the nilpotent middle pair.
  change ((2 : K)⁻¹ * (2 : K)⁻¹) •
    ((carD (K := K) i j * carD j i) * (carD j i * carD i j)) = 0
  rw [mul_assoc (carD (K := K) i j) (carD j i) (carD j i * carD i j),
    ← mul_assoc (carD (K := K) j i) (carD j i) (carD i j)]
  simp [carD, hij]

section Half

variable [Invertible (2 : K)]

/-- The two orientations of an occupation element are complementary. This also holds on the
diagonal, where both terms are the scalar `1/2`. -/
@[simp]
theorem carOccupationElement_add_swap (i j : n) :
    carOccupationElement (K := K) i j + carOccupationElement (K := K) j i = 1 := by
  rw [carOccupationElement, carOccupationElement, ← smul_add]
  have hcar := traceQuadraticForm_ι_single_mul_ι_single_add_swap
    (R := K) i j j i 1 1
  simp only [one_mul] at hcar
  rw [hcar, Algebra.smul_def, ← map_mul]
  simp

/-- Reversing an occupation element gives its complement. -/
theorem carOccupationElement_swap (i j : n) :
    carOccupationElement (K := K) j i = 1 - carOccupationElement (K := K) i j :=
  eq_sub_iff_add_eq.mpr (carOccupationElement_add_swap (K := K) j i)

end Half

/-- Every off-diagonal occupation element is idempotent over every field. -/
theorem isIdempotentElem_carOccupationElement {i j : n} (hij : i ≠ j) :
    IsIdempotentElem (carOccupationElement (K := K) i j) := by
  by_cases h2 : (2 : K) = 0
  · simp [carOccupationElement, h2, IsIdempotentElem]
  · let _ : Invertible (2 : K) := invertibleOfNonzero h2
    exact (IsIdempotentElem.of_mul_add
      (carOccupationElement_mul_swap (K := K) hij)
      (carOccupationElement_add_swap (K := K) i j)).1

/-- Multiplication by an off-diagonal occupation element twice is multiplication by it once. -/
@[simp]
theorem carOccupationElement_mul_self {i j : n} (hij : i ≠ j) :
    carOccupationElement (K := K) i j * carOccupationElement (K := K) i j =
      carOccupationElement (K := K) i j :=
  (isIdempotentElem_carOccupationElement (K := K) hij).eq

/-- All occupation elements commute, including equal and oppositely oriented pairs. -/
theorem commute_carOccupationElement {i j k l : n} :
    Commute (carOccupationElement (K := K) i j)
      (carOccupationElement (K := K) k l) := by
  by_cases heq : (i, j) = (k, l)
  · cases heq
    exact Commute.refl _
  by_cases hswap : (i, j) = (l, k)
  · have hil : i = l := congrArg Prod.fst hswap
    have hjk : j = k := congrArg Prod.snd hswap
    subst l
    subst k
    have hij : i ≠ j := by
      intro hij
      subst j
      exact heq rfl
    rw [commute_iff_lie_eq, Ring.lie_def, carOccupationElement_mul_swap (K := K) hij,
      carOccupationElement_mul_swap (K := K) hij.symm, sub_self]
  · rw [commute_iff_lie_eq, carOccupationElement, carOccupationElement]
    rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_sub, ← Ring.lie_def,
      lie_ι_mul_ι_ι_mul_ι]
    have hzy : ¬(l = j ∧ i = k) := by
      rintro ⟨rfl, rfl⟩
      exact heq rfl
    have hzx : ¬(l = i ∧ j = k) := by
      rintro ⟨rfl, rfl⟩
      exact hswap rfl
    have hwy : ¬(k = j ∧ i = l) := by
      rintro ⟨rfl, rfl⟩
      exact hswap rfl
    have hxw : ¬(j = l ∧ k = i) := by
      rintro ⟨rfl, rfl⟩
      exact heq rfl
    have hpzy : QuadraticMap.polar (traceQuadraticForm K n)
        (Matrix.single k l 1) (Matrix.single j i 1) = 0 := by
      exact polar_single_single_eq_zero (K := K) k l j i hzy
    have hpzx : QuadraticMap.polar (traceQuadraticForm K n)
        (Matrix.single k l 1) (Matrix.single i j 1) = 0 := by
      exact polar_single_single_eq_zero (K := K) k l i j hzx
    have hpwy : QuadraticMap.polar (traceQuadraticForm K n)
        (Matrix.single l k 1) (Matrix.single j i 1) = 0 := by
      exact polar_single_single_eq_zero (K := K) l k j i hwy
    have hpxw : QuadraticMap.polar (traceQuadraticForm K n)
        (Matrix.single i j 1) (Matrix.single l k 1) = 0 := by
      exact polar_single_single_eq_zero (K := K) i j l k hxw
    simp [hpzy, hpzx, hpwy, hpxw]

section Diagonal

variable [Invertible (2 : K)]

/-- A diagonal normal-ordered generator is the sum of all occupation elements with its first
index fixed. The diagonal summand is the scalar `1/2`. -/
theorem glCliffordHom_single_self_eq_sum_occupation (i : n) :
    glCliffordHom (K := K) (n := n) (Matrix.single i i 1) =
      ∑ k : n, carOccupationElement (K := K) i k := by
  rw [glCliffordHom_single, Finset.smul_sum]
  simp only [carOccupationElement, carD]

/-- Orient the diagonal lift using only positive-pair occupation projections. Below `i`, the
opposite orientation is replaced by its complement. -/
theorem glCliffordHom_single_self_eq_sum_positive_occupation
    [LinearOrder n] (i : n) :
    glCliffordHom (K := K) (n := n) (Matrix.single i i 1) =
      ∑ k : n, if k < i then 1 - carOccupationElement (K := K) k i
        else carOccupationElement (K := K) i k := by
  rw [glCliffordHom_single_self_eq_sum_occupation]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hki
  · exact eq_sub_iff_add_eq.mpr (carOccupationElement_add_swap (K := K) i k)
  · rfl

end Diagonal

end TauCeti
