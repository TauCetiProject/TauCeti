/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Clifford

/-!
# Occupation projections in the CAR algebra

For the Clifford algebra of the trace form on matrices, write `dᵢⱼ = ι(Eᵢⱼ)`. This file studies
the normalized quadratic elements

`pᵢⱼ = 1/2 dᵢⱼ dⱼᵢ`.

When `i ≠ j`, these are occupation projections for the hyperbolic plane spanned by `Eᵢⱼ` and
`Eⱼᵢ`. Their two orders are orthogonal. When `2` is invertible, the CAR relations also give
`pᵢⱼ + pⱼᵢ = 1`; in characteristic two the normalization vanishes instead, so the elements remain
idempotent in every characteristic. Projections associated to distinct unordered pairs commute.
Finally, the diagonal normal-ordered lift is the sum `Fᵢᵢ = ∑ k, pᵢₖ`; for a linearly ordered index
type this can be oriented using only the positive pairs. These formulas supply the commuting
zero-one operators used to calculate weights in the left regular CAR module.

## Main definitions

* `TauCeti.carOccupationProjection`: the normalized quadratic element `pᵢⱼ`.

## Main results

* `TauCeti.carOccupationProjection_add_swap`: `pᵢⱼ + pⱼᵢ = 1`.
* `TauCeti.isIdempotentElem_carOccupationProjection`: off-diagonal `pᵢⱼ` are idempotent.
* `TauCeti.carOccupationProjection_mul_self`: the corresponding multiplication normal form.
* `TauCeti.carOccupationProjection_comm_of_ne_of_ne_swap`: distinct unordered pairs commute.
* `TauCeti.glCliffordHom_single_diagonal_eq_sum_occupation`: `Fᵢᵢ = ∑ k, pᵢₖ`.

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

/-- The occupation element for the ordered matrix-unit pair `(i, j)`, normalized so that it is an
idempotent off the diagonal. For `i = j` it is the scalar `1/2`. -/
noncomputable def carOccupationProjection (i j : n) :
    CliffordAlgebra (traceQuadraticForm K n) :=
  (2 : K)⁻¹ • (carD i j * carD j i)

/-- The diagonal occupation element is the scalar `1/2`. -/
@[simp]
theorem carOccupationProjection_self (i : n) :
    carOccupationProjection (K := K) i i = (2 : K)⁻¹ • 1 := by
  simp [carOccupationProjection, carD]

/-- Oppositely oriented off-diagonal occupation elements are orthogonal in this order. -/
@[simp]
theorem carOccupationProjection_mul_swap {i j : n} (hij : i ≠ j) :
    carOccupationProjection (K := K) i j * carOccupationProjection (K := K) j i = 0 := by
  rw [carOccupationProjection, carOccupationProjection, smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Expose the common scalar and reassociate so `simp` can see the nilpotent middle pair.
  change ((2 : K)⁻¹ * (2 : K)⁻¹) •
    ((carD (K := K) i j * carD j i) * (carD j i * carD i j)) = 0
  rw [mul_assoc (carD (K := K) i j) (carD j i) (carD j i * carD i j),
    ← mul_assoc (carD (K := K) j i) (carD j i) (carD i j)]
  simp [carD, hij]

/-- Oppositely oriented off-diagonal occupation elements are orthogonal in the reverse order. -/
@[simp]
theorem carOccupationProjection_swap_mul {i j : n} (hij : i ≠ j) :
    carOccupationProjection (K := K) j i * carOccupationProjection (K := K) i j = 0 :=
  carOccupationProjection_mul_swap (K := K) hij.symm

section Half

variable [Invertible (2 : K)]

/-- The two orientations of an occupation element are complementary. This also holds on the
diagonal, where both terms are the scalar `1/2`. -/
@[simp]
theorem carOccupationProjection_add_swap (i j : n) :
    carOccupationProjection (K := K) i j + carOccupationProjection (K := K) j i = 1 := by
  rw [carOccupationProjection, carOccupationProjection, ← smul_add]
  have hcar := traceQuadraticForm_ι_single_mul_ι_single_add_swap
    (R := K) i j j i 1 1
  simp only [one_mul] at hcar
  rw [hcar, Algebra.smul_def, ← map_mul]
  simp

/-- Reversing an occupation element gives its complementary projection. -/
theorem carOccupationProjection_swap (i j : n) :
    carOccupationProjection (K := K) j i = 1 - carOccupationProjection (K := K) i j :=
  eq_sub_iff_add_eq.mpr (carOccupationProjection_add_swap (K := K) j i)

end Half

/-- Every off-diagonal occupation element is an idempotent. When the field has characteristic two,
the normalization scalar is zero; otherwise this follows from orthogonality and complementarity. -/
theorem isIdempotentElem_carOccupationProjection {i j : n} (hij : i ≠ j) :
    IsIdempotentElem (carOccupationProjection (K := K) i j) := by
  by_cases h2 : (2 : K) = 0
  · simp [carOccupationProjection, h2, IsIdempotentElem]
  · let _ : Invertible (2 : K) := invertibleOfNonzero h2
    exact (IsIdempotentElem.of_mul_add
      (carOccupationProjection_mul_swap (K := K) hij)
      (carOccupationProjection_add_swap (K := K) i j)).1

/-- Multiplication by an off-diagonal occupation element twice is multiplication by it once. -/
@[simp]
theorem carOccupationProjection_mul_self {i j : n} (hij : i ≠ j) :
    carOccupationProjection (K := K) i j * carOccupationProjection (K := K) i j =
      carOccupationProjection (K := K) i j :=
  (isIdempotentElem_carOccupationProjection (K := K) hij).eq

/-- Occupation elements for different unordered matrix-unit pairs commute. The two inequalities
exclude equality in either orientation, exactly the cases in which a cross-contraction can be
nonzero. -/
theorem carOccupationProjection_comm_of_ne_of_ne_swap {i j k l : n}
    (hne : (i, j) ≠ (k, l)) (hneSwap : (i, j) ≠ (l, k)) :
    Commute (carOccupationProjection (K := K) i j)
      (carOccupationProjection (K := K) k l) := by
  have hac : carD (K := K) i j * carD k l = -(carD k l * carD i j) :=
    traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired i j k l 1 1 <| by
      intro h
      exact hneSwap (Prod.ext h.2.symm h.1)
  have had : carD (K := K) i j * carD l k = -(carD l k * carD i j) :=
    traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired i j l k 1 1 <| by
      intro h
      exact hne (Prod.ext h.2.symm h.1)
  have hbc : carD (K := K) j i * carD k l = -(carD k l * carD j i) :=
    traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired j i k l 1 1 <| by
      intro h
      exact hne (Prod.ext h.1 h.2.symm)
  have hbd : carD (K := K) j i * carD l k = -(carD l k * carD j i) :=
    traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired j i l k 1 1 <| by
      intro h
      exact hneSwap (Prod.ext h.1 h.2.symm)
  -- Expose the scalar-normalized products before cancelling their common scalar action.
  change ((2 : K)⁻¹ • (carD i j * carD j i)) * ((2 : K)⁻¹ • (carD k l * carD l k)) =
    ((2 : K)⁻¹ • (carD k l * carD l k)) * ((2 : K)⁻¹ • (carD i j * carD j i))
  have hsmul (x y : CliffordAlgebra (traceQuadraticForm K n)) :
      ((2 : K)⁻¹ • x) * ((2 : K)⁻¹ • y) = ((2 : K)⁻¹ * (2 : K)⁻¹) • (x * y) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hsmul, hsmul]
  apply congrArg (((2 : K)⁻¹ * (2 : K)⁻¹) • ·)
  calc
    (carD i j * carD j i) * (carD k l * carD l k) =
        carD i j * (carD j i * carD k l) * carD l k := by
      simp only [mul_assoc]
    _ = -(carD i j * (carD k l * carD j i)) * carD l k := by rw [hbc]; simp
    _ = (carD k l * carD i j) * carD j i * carD l k := by
      rw [← mul_assoc (carD (K := K) i j) (carD k l) (carD j i), hac]
      simp only [neg_mul, neg_neg, mul_assoc]
    _ = carD k l * carD i j * (carD j i * carD l k) := by simp only [mul_assoc]
    _ = -(carD k l * carD i j * (carD l k * carD j i)) := by rw [hbd]; simp
    _ = (carD k l * carD l k) * (carD i j * carD j i) := by
      rw [mul_assoc (carD (K := K) k l) (carD i j) (carD l k * carD j i),
        ← mul_assoc (carD (K := K) i j) (carD l k) (carD j i), had]
      simp only [neg_mul, mul_neg, neg_neg, mul_assoc]

/-- Positive-pair occupation elements commute unless the pairs are equal. Positivity rules out the
reverse-orientation exception in `carOccupationProjection_comm_of_ne_of_ne_swap`. -/
theorem carOccupationProjection_comm_of_lt_of_lt [LinearOrder n] {i j k l : n}
    (hij : i < j) (hkl : k < l) (hne : (i, j) ≠ (k, l)) :
    Commute (carOccupationProjection (K := K) i j)
      (carOccupationProjection (K := K) k l) := by
  apply carOccupationProjection_comm_of_ne_of_ne_swap hne
  intro h
  have hil : i = l := congrArg Prod.fst h
  have hjk : j = k := congrArg Prod.snd h
  have hji : j < i := calc
    j = k := hjk
    _ < l := hkl
    _ = i := hil.symm
  exact (not_lt_of_ge hij.le) hji

section Diagonal

variable [Invertible (2 : K)]

/-- A diagonal normal-ordered generator is the sum of all occupation elements with its first
index fixed. The diagonal summand is the scalar `1/2`. -/
theorem glCliffordHom_single_diagonal_eq_sum_occupation (i : n) :
    glCliffordHom (K := K) (n := n) (Matrix.single i i 1) =
      ∑ k : n, carOccupationProjection (K := K) i k := by
  rw [glCliffordHom_single, Finset.smul_sum]
  rfl

/-- Orient the diagonal lift using only positive-pair occupation projections. Below `i`, the
opposite orientation is replaced by its complement. -/
theorem glCliffordHom_single_diagonal_eq_sum_positive_occupation
    [LinearOrder n] (i : n) :
    glCliffordHom (K := K) (n := n) (Matrix.single i i 1) =
      ∑ k : n, if k < i then 1 - carOccupationProjection (K := K) k i
        else carOccupationProjection (K := K) i k := by
  rw [glCliffordHom_single_diagonal_eq_sum_occupation]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hki
  · exact eq_sub_iff_add_eq.mpr (carOccupationProjection_add_swap (K := K) i k)
  · rfl

end Diagonal

end TauCeti
