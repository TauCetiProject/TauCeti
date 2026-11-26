/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.StandardCoordinates
import Mathlib.LinearAlgebra.Matrix.Transvection
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

/-!
# The two ten-curve lattices of an `I₄*` fibre on an Enriques surface

Let `C₀ + C₁ + 2 (C₂ + ⋯ + C₆) + C₇ + C₈` be a fibre of Kodaira type `I₄*` (affine `D₈`) of a
genus-one fibration on an Enriques surface. The components `C₁, …, C₈` span a copy of `D₈(-1)`:
in the order `C₁, …, C₈` they have square `-2` and meet exactly along the edges

```text
(C₁, C₂), (C₂, C₃), (C₃, C₄), (C₄, C₅), (C₅, C₆), (C₆, C₇), (C₆, C₈).
```

Schröer's exclusion of `I₄*` fibres on Enriques surfaces over `𝔽₂` uses two rank-ten extensions of
this configuration:

* `N₁ = TauCeti.EnriquesTenCurve.firstGram`, the Gram matrix of `(C₁, …, C₈, R, F)` for a
  `(-2)`-curve `R` meeting only `C₄`, once, and a half-fibre `F` of the pencil, with `R · F = 1`;
* `N₂ = TauCeti.EnriquesTenCurve.secondGram`, the Gram matrix of `(C₁, …, C₈, F', F)` for two
  half-fibres with `F · F' = 1`, both orthogonal to the components; this is `D₈(-1) ⊕ U`.

This file realizes both on the standard coordinate space `ℚ¹⁰` with carrier `ℤ¹⁰`, and computes
their discriminant forms. Both matrices have determinant `-4`, and `2 N⁻¹` is an integer matrix,
so the discriminant group has order four and exponent two: it is `(ℤ/2)²`. Its nonzero classes are
those of the dual basis vectors `C₁*`, `C₇*` and `C₈*`. The vector class `C₁*` has full norm `-1`,
so the half-norm discriminant form takes the value `1/2` on it, while the two spinor classes `C₇*`
and `C₈*` have full norm `-2` and are isotropic. Consequently each lattice has exactly three
isotropic discriminant classes, including zero. Since an even overlattice of index two is obtained
by gluing an isotropic class, this is the input for locating the numerical lattice of the surface,
which contains each configuration with index two, among the overlattices of `N₁` and `N₂`.

The inverses `N₁⁻¹` and `N₂⁻¹` are Schröer's matrices `(14)` and `(16)`; this file records the
integer matrices `2 N₁⁻¹` and `2 N₂⁻¹`.

## Main definitions

* `TauCeti.EnriquesTenCurve.firstGram`, `TauCeti.EnriquesTenCurve.secondGram`: the matrices `N₁`
  and `N₂`.
* `TauCeti.EnriquesTenCurve.firstLattice`, `TauCeti.EnriquesTenCurve.secondLattice`: the integral
  lattices they present on `ℚ¹⁰`, with carrier `ℤ¹⁰`
  (`TauCeti.EnriquesTenCurve.mem_firstLattice_carrier_iff`) and Gram matrix `N₁`, resp. `N₂`, on
  the coordinate vectors (`TauCeti.EnriquesTenCurve.form_firstLattice_single_single`).
* `TauCeti.EnriquesTenCurve.firstGramTwiceInverse`,
  `TauCeti.EnriquesTenCurve.secondGramTwiceInverse`: the integer matrices `2 N₁⁻¹` and `2 N₂⁻¹`.
* `TauCeti.EnriquesTenCurve.firstDualVector`, `TauCeti.EnriquesTenCurve.secondDualVector`: the
  dual basis vectors, the columns of `N⁻¹`.
* `TauCeti.EnriquesTenCurve.firstDualClass`, `TauCeti.EnriquesTenCurve.secondDualClass`: their
  discriminant classes.

## Main results

* `TauCeti.EnriquesTenCurve.det_firstGram`, `TauCeti.EnriquesTenCurve.det_secondGram`: both
  determinants are `-4`.
* `TauCeti.EnriquesTenCurve.isEven_firstLattice`, `TauCeti.EnriquesTenCurve.isEven_secondLattice`:
  both lattices are even.
* `TauCeti.EnriquesTenCurve.natCard_discriminantGroup_firstLattice` and
  `TauCeti.EnriquesTenCurve.exponent_discriminantGroup_firstLattice`, with their `secondLattice`
  counterparts: the discriminant groups have order four and exponent two.
* `TauCeti.EnriquesTenCurve.firstDualClass_eq_firstDualClass_iff` and
  `TauCeti.EnriquesTenCurve.firstDualClass_eq_zero_iff`, with their `secondDualClass` counterparts:
  dual basis classes are compared through the columns of `2 N⁻¹` modulo two. The simp lemmas
  `TauCeti.EnriquesTenCurve.firstDualClass_one` through
  `TauCeti.EnriquesTenCurve.firstDualClass_nine` (and likewise for `secondDualClass`) identify
  every dual basis class other than `C₁*`, `C₇*` and `C₈*` with `0` or `C₁*`.
* `TauCeti.EnriquesTenCurve.bijective_vecCons_zero_firstDualClass`,
  `TauCeti.EnriquesTenCurve.bijective_vecCons_zero_secondDualClass`: the discriminant group
  consists of the four distinct classes `0`, `C₁*`, `C₇*`, `C₈*`.
* `TauCeti.EnriquesTenCurve.setOf_discriminantQuadraticMap_firstLattice_eq_zero` and
  `TauCeti.EnriquesTenCurve.ncard_setOf_discriminantQuadraticMap_firstLattice_eq_zero`, with their
  `secondLattice` counterparts: the isotropic classes are `0`, `C₇*` and `C₈*`, three in all.

## Implementation notes

The dual vectors, their classes, the order-two statement and the quadratic values are
specializations of the standard-coordinate discriminant API in
`TauCeti.LinearAlgebra.IntegralLattice.Discriminant.StandardCoordinates`, applied to
`N (2 N⁻¹) = 2`.

The determinant of `N₂` is read off from its block decomposition `D₈(-1) ⊕ U` and
`CartanMatrix.D_det`. The matrix `N₁` is congruent to `N₂` under a product of two transvections:
in a lattice with Gram matrix `N₂` in the basis `(C₁, …, C₈, F', F)`, replacing `C₄` by `C₄ + F`
and `F'` by `F' - F` gives a basis with Gram matrix `N₁`. The two Gram matrices are therefore
integrally congruent; the lattices are kept separate because their bases carry different geometric
meaning.

## References

* S. Schröer, *There is no Enriques surface over the integers*, Annals of Mathematics 197 (2023),
  §12, Propositions 12.2 and 12.3, matrices (14) and (16).
-/

public section

open Matrix

namespace TauCeti.EnriquesTenCurve

open IntegralLattice

/-! ## The Gram matrices -/

/-- The Gram matrix `N₁` of the ten curves `(C₁, …, C₈, R, F)`: the components `C₁, …, C₈` of an
`I₄*` fibre forming `D₈(-1)`, a `(-2)`-curve `R` meeting only `C₄`, once, and a half-fibre `F`
of square zero meeting only `R`, once. -/
@[expose] def firstGram : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, -2, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, -2, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, -2, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 1, -2, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, -2, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, -2, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, -2, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, -2, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- The Gram matrix `N₂ = D₈(-1) ⊕ U` of the ten curves `(C₁, …, C₈, F', F)`: the components
`C₁, …, C₈` of an `I₄*` fibre forming `D₈(-1)`, and two half-fibres `F'` and `F` of square zero,
orthogonal to the components and meeting each other once. -/
@[expose] def secondGram : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, -2, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, -2, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, -2, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, -2, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, -2, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, -2, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, -2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- The matrix `N₁` is symmetric. -/
theorem firstGram_isSymm : firstGram.IsSymm := by
  decide

/-- The matrix `N₂` is symmetric. -/
theorem secondGram_isSymm : secondGram.IsSymm := by
  decide

/-- `N₂` is the orthogonal sum of the negated Cartan matrix of type `D₈` and the hyperbolic
plane. -/
private theorem secondGram_eq_reindex_fromBlocks :
    secondGram = reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks (-CartanMatrix.D 8) 0 0 !![0, 1; 1, 0]) := by
  decide

/-- `N₁` is congruent to `N₂`: replacing `C₄` by `C₄ + F` and `F'` by `F' - F` in a basis with
Gram matrix `N₂` gives a basis with Gram matrix `N₁`. -/
private theorem firstGram_eq_transpose_mul_secondGram_mul :
    firstGram = (transvection 9 3 1 * transvection 9 8 (-1))ᵀ * secondGram *
      (transvection 9 3 1 * transvection 9 8 (-1)) := by
  decide

/-- The determinant of `N₂ = D₈(-1) ⊕ U` is `-4`. -/
theorem det_secondGram : secondGram.det = -4 := by
  rw [secondGram_eq_reindex_fromBlocks, det_reindex_self, det_fromBlocks_zero₂₁, det_neg,
    CartanMatrix.D_det (by norm_num), det_fin_two_of]
  norm_num

/-- The determinant of `N₁` is `-4`. -/
theorem det_firstGram : firstGram.det = -4 := by
  rw [firstGram_eq_transpose_mul_secondGram_mul, det_mul, det_mul, det_transpose, det_mul,
    det_transvection_of_ne _ _ (by decide), det_transvection_of_ne _ _ (by decide), det_secondGram]
  norm_num

/-! ## The first ten-curve lattice -/

/-- The first ten-curve lattice: the integral lattice on `ℚ¹⁰` with Gram matrix `N₁` in the
standard coordinate basis. Its carrier is `ℤ¹⁰`. -/
noncomputable def firstLattice : IntegralLattice (Fin 10 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 10)) firstGram firstGram_isSymm

/-- The first ten-curve lattice is the lattice presented by `N₁` on standard coordinates. -/
theorem firstLattice_def :
    firstLattice = ofGramMatrix (Pi.basisFun ℚ (Fin 10)) firstGram firstGram_isSymm :=
  (rfl)

/-- The form of the first ten-curve lattice in coordinates. -/
theorem form_firstLattice_apply (x y : Fin 10 → ℚ) :
    firstLattice.form x y = ∑ i, x i * ∑ j, ((firstGram i j : ℤ) : ℚ) * y j :=
  form_ofGramMatrix_basisFun_apply _ _ x y

/-- The Gram matrix of the first ten-curve lattice in the standard coordinate basis is `N₁`. -/
@[simp]
theorem form_firstLattice_single_single (i j : Fin 10) :
    firstLattice.form (Pi.single i 1) (Pi.single j 1) = ((firstGram i j : ℤ) : ℚ) := by
  rw [firstLattice]
  simpa only [Pi.basisFun_apply] using form_ofGramMatrix_basisFun_basisFun _ firstGram_isSymm i j

/-- The carrier of the first ten-curve lattice is `ℤ¹⁰`. -/
@[simp]
theorem mem_firstLattice_carrier_iff (x : Fin 10 → ℚ) :
    x ∈ firstLattice.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The first ten-curve lattice is even. -/
theorem isEven_firstLattice : firstLattice.IsEven := by
  rw [firstLattice, isEven_ofGramMatrix_iff]
  decide

-- `ofGramMatrix` computes determinants with classical decidable equality on `Fin 10`, so `convert`
-- identifies its determinant with the one in `det_firstGram`.
instance : firstLattice.IsNondegenerate :=
  isNondegenerate_ofGramMatrix _ _ _ (by convert det_firstGram.trans_ne (by decide : (-4 : ℤ) ≠ 0))

/-- The discriminant group of the first ten-curve lattice has order four. -/
@[simp]
theorem natCard_discriminantGroup_firstLattice :
    Nat.card firstLattice.DiscriminantGroup = 4 := by
  have h : firstGram.det.natAbs = 4 := by simp [det_firstGram]
  rw [firstLattice, natCard_discriminantGroup_ofGramMatrix]
  -- As for the instance above, `convert` reconciles the classical decidable equality on `Fin 10`.
  convert h

/-- Twice the inverse of `N₁`, an integer matrix; `N₁⁻¹` is Schröer's matrix (14). -/
@[expose] def firstGramTwiceInverse : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, -2, -2, -2, -2, -2, -1, -1, 0, 2;
    -2, -4, -4, -4, -4, -4, -2, -2, 0, 4;
    -2, -4, -6, -6, -6, -6, -3, -3, 0, 6;
    -2, -4, -6, -8, -8, -8, -4, -4, 0, 8;
    -2, -4, -6, -8, -10, -10, -5, -5, 0, 8;
    -2, -4, -6, -8, -10, -12, -6, -6, 0, 8;
    -1, -2, -3, -4, -5, -6, -4, -3, 0, 4;
    -1, -2, -3, -4, -5, -6, -3, -4, 0, 4;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
    2, 4, 6, 8, 8, 8, 4, 4, 2, -4]

/-- `N₁⁻¹` has denominator two: `N₁ (2 N₁⁻¹) = 2`. -/
theorem firstGram_mul_firstGramTwiceInverse :
    firstGram * firstGramTwiceInverse = (2 : ℤ) • 1 := by
  decide

/-- The vector of `ℚ¹⁰` dual to the `i`-th coordinate vector for the first ten-curve lattice:
the `i`-th column of `N₁⁻¹`. -/
def firstDualVector (i : Fin 10) : Fin 10 → ℚ :=
  fun j ↦ (firstGramTwiceInverse j i : ℚ) / 2

/-- The coordinates of `firstDualVector i` are the entries of the `i`-th column of `N₁⁻¹`. -/
@[simp]
theorem firstDualVector_apply (i j : Fin 10) :
    firstDualVector i j = (firstGramTwiceInverse j i : ℚ) / 2 :=
  (rfl)

/-- The vector `firstDualVector i` lies in the dual of the first ten-curve lattice. -/
theorem firstDualVector_mem_dualCarrier (i : Fin 10) :
    firstDualVector i ∈ firstLattice.dualCarrier :=
  mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one _ _ firstGram_mul_firstGramTwiceInverse
    two_ne_zero i

/-- `firstDualVector i` pairs every vector with its `i`-th coordinate. -/
@[simp]
theorem form_firstDualVector (y : Fin 10 → ℚ) (i : Fin 10) :
    firstLattice.form y (firstDualVector i) = y i :=
  form_ofGramMatrix_basisFun_of_mul_eq_smul_one _ _ firstGram_mul_firstGramTwiceInverse
    two_ne_zero y i

/-- The discriminant class of the dual basis vector `firstDualVector i`. For `i = 0, 6, 7` these
are the classes of `C₁*`, `C₇*` and `C₈*`. -/
noncomputable def firstDualClass (i : Fin 10) : firstLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨firstDualVector i, firstDualVector_mem_dualCarrier i⟩

/-- The class of `firstDualVector i` in the discriminant group is `firstDualClass i`. -/
@[simp]
theorem mk_firstDualVector (i : Fin 10) :
    (Submodule.Quotient.mk ⟨firstDualVector i, firstDualVector_mem_dualCarrier i⟩ :
      firstLattice.DiscriminantGroup) = firstDualClass i :=
  (rfl)

/-- Two dual basis classes of the first ten-curve lattice agree exactly when the corresponding
columns of `2 N₁⁻¹` are congruent modulo two. -/
theorem firstDualClass_eq_firstDualClass_iff (i i' : Fin 10) :
    firstDualClass i = firstDualClass i' ↔
      ∀ j, 2 ∣ firstGramTwiceInverse j i - firstGramTwiceInverse j i' :=
  discriminantGroup_mk_eq_mk_iff_of_mul_eq_smul_one _ _ firstGram_mul_firstGramTwiceInverse
    two_ne_zero i i'

/-- A dual basis class of the first ten-curve lattice vanishes exactly when the corresponding
column of `2 N₁⁻¹` is even. -/
theorem firstDualClass_eq_zero_iff (i : Fin 10) :
    firstDualClass i = 0 ↔ ∀ j, 2 ∣ firstGramTwiceInverse j i :=
  discriminantGroup_mk_eq_zero_iff_of_mul_eq_smul_one _ _ firstGram_mul_firstGramTwiceInverse
    two_ne_zero i

/-- The class of `C₂*` is zero. -/
@[simp]
theorem firstDualClass_one : firstDualClass 1 = 0 :=
  (firstDualClass_eq_zero_iff 1).mpr (by decide)

/-- The class of `C₃*` is the vector class `C₁*`. -/
@[simp]
theorem firstDualClass_two : firstDualClass 2 = firstDualClass 0 :=
  (firstDualClass_eq_firstDualClass_iff 2 0).mpr (by decide)

/-- The class of `C₄*` is zero. -/
@[simp]
theorem firstDualClass_three : firstDualClass 3 = 0 :=
  (firstDualClass_eq_zero_iff 3).mpr (by decide)

/-- The class of `C₅*` is the vector class `C₁*`. -/
@[simp]
theorem firstDualClass_four : firstDualClass 4 = firstDualClass 0 :=
  (firstDualClass_eq_firstDualClass_iff 4 0).mpr (by decide)

/-- The class of `C₆*` is zero. -/
@[simp]
theorem firstDualClass_five : firstDualClass 5 = 0 :=
  (firstDualClass_eq_zero_iff 5).mpr (by decide)

/-- The class of `R*` is zero. -/
@[simp]
theorem firstDualClass_eight : firstDualClass 8 = 0 :=
  (firstDualClass_eq_zero_iff 8).mpr (by decide)

/-- The class of `F*` is zero. -/
@[simp]
theorem firstDualClass_nine : firstDualClass 9 = 0 :=
  (firstDualClass_eq_zero_iff 9).mpr (by decide)

/-- Every discriminant class of the first ten-curve lattice is killed by two. -/
theorem two_nsmul_discriminantGroup_firstLattice (a : firstLattice.DiscriminantGroup) :
    2 • a = 0 :=
  nsmul_discriminantGroup_ofGramMatrix_basisFun_eq_zero _ _ firstGram_mul_firstGramTwiceInverse a

/-- Every dual basis class of the first ten-curve lattice is killed by two. -/
theorem two_nsmul_firstDualClass (i : Fin 10) : 2 • firstDualClass i = 0 :=
  two_nsmul_discriminantGroup_firstLattice _

private theorem firstDualClass_pairwise_ne :
    firstDualClass 0 ≠ 0 ∧ firstDualClass 6 ≠ 0 ∧ firstDualClass 7 ≠ 0 ∧
      firstDualClass 0 ≠ firstDualClass 6 ∧ firstDualClass 0 ≠ firstDualClass 7 ∧
      firstDualClass 6 ≠ firstDualClass 7 := by
  simp only [Ne, firstDualClass_eq_zero_iff, firstDualClass_eq_firstDualClass_iff]
  decide

/-- **The discriminant group of the first ten-curve lattice** consists of the four distinct
classes `0`, `C₁*`, `C₇*` and `C₈*`. -/
theorem bijective_vecCons_zero_firstDualClass :
    Function.Bijective ![0, firstDualClass 0, firstDualClass 6, firstDualClass 7] := by
  obtain ⟨h0, h6, h7, h06, h07, h67⟩ := firstDualClass_pairwise_ne
  have : Finite firstLattice.DiscriminantGroup := Nat.finite_of_card_ne_zero (by simp)
  refine Function.Injective.bijective_of_nat_card_le (fun i j hij ↦ ?_) (by simp)
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The discriminant group of the first ten-curve lattice has exponent two. Together with
`natCard_discriminantGroup_firstLattice`, it is `(ℤ/2)²` rather than `ℤ/4`. -/
@[simp]
theorem exponent_discriminantGroup_firstLattice :
    AddMonoid.exponent firstLattice.DiscriminantGroup = 2 :=
  have : Nontrivial firstLattice.DiscriminantGroup :=
    ⟨⟨_, _, firstDualClass_pairwise_ne.1⟩⟩
  (AddMonoid.exponent_eq_prime_iff Nat.prime_two).mpr fun a ha ↦
    addOrderOf_eq_prime (two_nsmul_discriminantGroup_firstLattice a) ha

/-- The quadratic value of the class of `firstDualVector i` is a quarter of the `i`-th diagonal
entry of `2 N₁⁻¹`, that is, half the full norm `N₁⁻¹ i i` of `firstDualVector i`. -/
theorem discriminantQuadraticMap_firstDualClass (i : Fin 10) :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass i) =
      (((firstGramTwiceInverse i i : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ)) :=
  (discriminantQuadraticMap_mk_of_mul_eq_smul_one _ _ firstGram_mul_firstGramTwiceInverse
    two_ne_zero isEven_firstLattice i).trans (by norm_num)

/-- The vector class `C₁*` of the first ten-curve lattice has full norm `-1`, so its quadratic
value is `1/2`. -/
@[simp]
theorem discriminantQuadraticMap_firstDualClass_zero :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 0) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap_firstDualClass, show firstGramTwiceInverse 0 0 = -2 from rfl,
    ← AddCircle.coe_add_period (1 : ℚ) (((-2 : ℤ) : ℚ) / 4)]
  norm_num

/-- The spinor class `C₇*` of the first ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_firstDualClass_six :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 6) = 0 := by
  rw [discriminantQuadraticMap_firstDualClass, show firstGramTwiceInverse 6 6 = -4 from rfl,
    AddCircle.coe_eq_zero_iff]
  exact ⟨-1, by norm_num⟩

/-- The spinor class `C₈*` of the first ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_firstDualClass_seven :
    firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 7) = 0 := by
  rw [discriminantQuadraticMap_firstDualClass, show firstGramTwiceInverse 7 7 = -4 from rfl,
    AddCircle.coe_eq_zero_iff]
  exact ⟨-1, by norm_num⟩

/-- The isotropic discriminant classes of the first ten-curve lattice are `0` and the two spinor
classes `C₇*` and `C₈*`. -/
theorem setOf_discriminantQuadraticMap_firstLattice_eq_zero :
    {a | firstLattice.discriminantQuadraticMap isEven_firstLattice a = 0} =
      {0, firstDualClass 6, firstDualClass 7} := by
  obtain ⟨h0, -, -, h06, h07, -⟩ := firstDualClass_pairwise_ne
  have h : firstLattice.discriminantQuadraticMap isEven_firstLattice (firstDualClass 0) ≠ 0 := by
    intro h
    have := AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := 2) two_pos
    norm_num [← discriminantQuadraticMap_firstDualClass_zero, h] at this
  ext a
  obtain ⟨k, rfl⟩ := bijective_vecCons_zero_firstDualClass.2 a
  fin_cases k <;> simp [h, h0, h06, h07, -discriminantQuadraticMap_firstDualClass_zero]

/-- The first ten-curve lattice has exactly three isotropic discriminant classes. -/
theorem ncard_setOf_discriminantQuadraticMap_firstLattice_eq_zero :
    {a | firstLattice.discriminantQuadraticMap isEven_firstLattice a = 0}.ncard = 3 := by
  obtain ⟨-, h6, h7, -, -, h67⟩ := firstDualClass_pairwise_ne
  rw [setOf_discriminantQuadraticMap_firstLattice_eq_zero]
  exact Set.ncard_eq_three.mpr ⟨0, _, _, h6.symm, h7.symm, h67, rfl⟩

/-! ## The second ten-curve lattice -/

/-- The second ten-curve lattice: the integral lattice on `ℚ¹⁰` with Gram matrix `N₂` in the
standard coordinate basis. Its carrier is `ℤ¹⁰`. -/
noncomputable def secondLattice : IntegralLattice (Fin 10 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 10)) secondGram secondGram_isSymm

/-- The second ten-curve lattice is the lattice presented by `N₂` on standard coordinates. -/
theorem secondLattice_def :
    secondLattice = ofGramMatrix (Pi.basisFun ℚ (Fin 10)) secondGram secondGram_isSymm :=
  (rfl)

/-- The form of the second ten-curve lattice in coordinates. -/
theorem form_secondLattice_apply (x y : Fin 10 → ℚ) :
    secondLattice.form x y = ∑ i, x i * ∑ j, ((secondGram i j : ℤ) : ℚ) * y j :=
  form_ofGramMatrix_basisFun_apply _ _ x y

/-- The Gram matrix of the second ten-curve lattice in the standard coordinate basis is `N₂`. -/
@[simp]
theorem form_secondLattice_single_single (i j : Fin 10) :
    secondLattice.form (Pi.single i 1) (Pi.single j 1) = ((secondGram i j : ℤ) : ℚ) := by
  rw [secondLattice]
  simpa only [Pi.basisFun_apply] using form_ofGramMatrix_basisFun_basisFun _ secondGram_isSymm i j

/-- The carrier of the second ten-curve lattice is `ℤ¹⁰`. -/
@[simp]
theorem mem_secondLattice_carrier_iff (x : Fin 10 → ℚ) :
    x ∈ secondLattice.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The second ten-curve lattice is even. -/
theorem isEven_secondLattice : secondLattice.IsEven := by
  rw [secondLattice, isEven_ofGramMatrix_iff]
  decide

-- `ofGramMatrix` computes determinants with classical decidable equality on `Fin 10`, so `convert`
-- identifies its determinant with the one in `det_secondGram`.
instance : secondLattice.IsNondegenerate :=
  isNondegenerate_ofGramMatrix _ _ _ (by convert det_secondGram.trans_ne (by decide : (-4 : ℤ) ≠ 0))

/-- The discriminant group of the second ten-curve lattice has order four. -/
@[simp]
theorem natCard_discriminantGroup_secondLattice :
    Nat.card secondLattice.DiscriminantGroup = 4 := by
  have h : secondGram.det.natAbs = 4 := by simp [det_secondGram]
  rw [secondLattice, natCard_discriminantGroup_ofGramMatrix]
  -- As for the instance above, `convert` reconciles the classical decidable equality on `Fin 10`.
  convert h

/-- Twice the inverse of `N₂`, an integer matrix; `N₂⁻¹` is Schröer's matrix (16). -/
@[expose] def secondGramTwiceInverse : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-2, -2, -2, -2, -2, -2, -1, -1, 0, 0;
    -2, -4, -4, -4, -4, -4, -2, -2, 0, 0;
    -2, -4, -6, -6, -6, -6, -3, -3, 0, 0;
    -2, -4, -6, -8, -8, -8, -4, -4, 0, 0;
    -2, -4, -6, -8, -10, -10, -5, -5, 0, 0;
    -2, -4, -6, -8, -10, -12, -6, -6, 0, 0;
    -1, -2, -3, -4, -5, -6, -4, -3, 0, 0;
    -1, -2, -3, -4, -5, -6, -3, -4, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 2, 0]

/-- `N₂⁻¹` has denominator two: `N₂ (2 N₂⁻¹) = 2`. -/
theorem secondGram_mul_secondGramTwiceInverse :
    secondGram * secondGramTwiceInverse = (2 : ℤ) • 1 := by
  decide

/-- The vector of `ℚ¹⁰` dual to the `i`-th coordinate vector for the second ten-curve lattice:
the `i`-th column of `N₂⁻¹`. -/
def secondDualVector (i : Fin 10) : Fin 10 → ℚ :=
  fun j ↦ (secondGramTwiceInverse j i : ℚ) / 2

/-- The coordinates of `secondDualVector i` are the entries of the `i`-th column of `N₂⁻¹`. -/
@[simp]
theorem secondDualVector_apply (i j : Fin 10) :
    secondDualVector i j = (secondGramTwiceInverse j i : ℚ) / 2 :=
  (rfl)

/-- The vector `secondDualVector i` lies in the dual of the second ten-curve lattice. -/
theorem secondDualVector_mem_dualCarrier (i : Fin 10) :
    secondDualVector i ∈ secondLattice.dualCarrier :=
  mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one _ _ secondGram_mul_secondGramTwiceInverse
    two_ne_zero i

/-- `secondDualVector i` pairs every vector with its `i`-th coordinate. -/
@[simp]
theorem form_secondDualVector (y : Fin 10 → ℚ) (i : Fin 10) :
    secondLattice.form y (secondDualVector i) = y i :=
  form_ofGramMatrix_basisFun_of_mul_eq_smul_one _ _ secondGram_mul_secondGramTwiceInverse
    two_ne_zero y i

/-- The discriminant class of the dual basis vector `secondDualVector i`. For `i = 0, 6, 7` these
are the classes of `C₁*`, `C₇*` and `C₈*`. -/
noncomputable def secondDualClass (i : Fin 10) : secondLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨secondDualVector i, secondDualVector_mem_dualCarrier i⟩

/-- The class of `secondDualVector i` in the discriminant group is `secondDualClass i`. -/
@[simp]
theorem mk_secondDualVector (i : Fin 10) :
    (Submodule.Quotient.mk ⟨secondDualVector i, secondDualVector_mem_dualCarrier i⟩ :
      secondLattice.DiscriminantGroup) = secondDualClass i :=
  (rfl)

/-- Two dual basis classes of the second ten-curve lattice agree exactly when the corresponding
columns of `2 N₂⁻¹` are congruent modulo two. -/
theorem secondDualClass_eq_secondDualClass_iff (i i' : Fin 10) :
    secondDualClass i = secondDualClass i' ↔
      ∀ j, 2 ∣ secondGramTwiceInverse j i - secondGramTwiceInverse j i' :=
  discriminantGroup_mk_eq_mk_iff_of_mul_eq_smul_one _ _ secondGram_mul_secondGramTwiceInverse
    two_ne_zero i i'

/-- A dual basis class of the second ten-curve lattice vanishes exactly when the corresponding
column of `2 N₂⁻¹` is even. -/
theorem secondDualClass_eq_zero_iff (i : Fin 10) :
    secondDualClass i = 0 ↔ ∀ j, 2 ∣ secondGramTwiceInverse j i :=
  discriminantGroup_mk_eq_zero_iff_of_mul_eq_smul_one _ _ secondGram_mul_secondGramTwiceInverse
    two_ne_zero i

/-- The class of `C₂*` is zero. -/
@[simp]
theorem secondDualClass_one : secondDualClass 1 = 0 :=
  (secondDualClass_eq_zero_iff 1).mpr (by decide)

/-- The class of `C₃*` is the vector class `C₁*`. -/
@[simp]
theorem secondDualClass_two : secondDualClass 2 = secondDualClass 0 :=
  (secondDualClass_eq_secondDualClass_iff 2 0).mpr (by decide)

/-- The class of `C₄*` is zero. -/
@[simp]
theorem secondDualClass_three : secondDualClass 3 = 0 :=
  (secondDualClass_eq_zero_iff 3).mpr (by decide)

/-- The class of `C₅*` is the vector class `C₁*`. -/
@[simp]
theorem secondDualClass_four : secondDualClass 4 = secondDualClass 0 :=
  (secondDualClass_eq_secondDualClass_iff 4 0).mpr (by decide)

/-- The class of `C₆*` is zero. -/
@[simp]
theorem secondDualClass_five : secondDualClass 5 = 0 :=
  (secondDualClass_eq_zero_iff 5).mpr (by decide)

/-- The class of `F'*` is zero. -/
@[simp]
theorem secondDualClass_eight : secondDualClass 8 = 0 :=
  (secondDualClass_eq_zero_iff 8).mpr (by decide)

/-- The class of `F*` is zero. -/
@[simp]
theorem secondDualClass_nine : secondDualClass 9 = 0 :=
  (secondDualClass_eq_zero_iff 9).mpr (by decide)

/-- Every discriminant class of the second ten-curve lattice is killed by two. -/
theorem two_nsmul_discriminantGroup_secondLattice (a : secondLattice.DiscriminantGroup) :
    2 • a = 0 :=
  nsmul_discriminantGroup_ofGramMatrix_basisFun_eq_zero _ _ secondGram_mul_secondGramTwiceInverse a

/-- Every dual basis class of the second ten-curve lattice is killed by two. -/
theorem two_nsmul_secondDualClass (i : Fin 10) : 2 • secondDualClass i = 0 :=
  two_nsmul_discriminantGroup_secondLattice _

private theorem secondDualClass_pairwise_ne :
    secondDualClass 0 ≠ 0 ∧ secondDualClass 6 ≠ 0 ∧ secondDualClass 7 ≠ 0 ∧
      secondDualClass 0 ≠ secondDualClass 6 ∧ secondDualClass 0 ≠ secondDualClass 7 ∧
      secondDualClass 6 ≠ secondDualClass 7 := by
  simp only [Ne, secondDualClass_eq_zero_iff, secondDualClass_eq_secondDualClass_iff]
  decide

/-- **The discriminant group of the second ten-curve lattice** consists of the four distinct
classes `0`, `C₁*`, `C₇*` and `C₈*`. -/
theorem bijective_vecCons_zero_secondDualClass :
    Function.Bijective ![0, secondDualClass 0, secondDualClass 6, secondDualClass 7] := by
  obtain ⟨h0, h6, h7, h06, h07, h67⟩ := secondDualClass_pairwise_ne
  have : Finite secondLattice.DiscriminantGroup := Nat.finite_of_card_ne_zero (by simp)
  refine Function.Injective.bijective_of_nat_card_le (fun i j hij ↦ ?_) (by simp)
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The discriminant group of the second ten-curve lattice has exponent two. Together with
`natCard_discriminantGroup_secondLattice`, it is `(ℤ/2)²` rather than `ℤ/4`. -/
@[simp]
theorem exponent_discriminantGroup_secondLattice :
    AddMonoid.exponent secondLattice.DiscriminantGroup = 2 :=
  have : Nontrivial secondLattice.DiscriminantGroup :=
    ⟨⟨_, _, secondDualClass_pairwise_ne.1⟩⟩
  (AddMonoid.exponent_eq_prime_iff Nat.prime_two).mpr fun a ha ↦
    addOrderOf_eq_prime (two_nsmul_discriminantGroup_secondLattice a) ha

/-- The quadratic value of the class of `secondDualVector i` is a quarter of the `i`-th diagonal
entry of `2 N₂⁻¹`, that is, half the full norm `N₂⁻¹ i i` of `secondDualVector i`. -/
theorem discriminantQuadraticMap_secondDualClass (i : Fin 10) :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass i) =
      (((secondGramTwiceInverse i i : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ)) :=
  (discriminantQuadraticMap_mk_of_mul_eq_smul_one _ _ secondGram_mul_secondGramTwiceInverse
    two_ne_zero isEven_secondLattice i).trans (by norm_num)

/-- The vector class `C₁*` of the second ten-curve lattice has full norm `-1`, so its quadratic
value is `1/2`. -/
@[simp]
theorem discriminantQuadraticMap_secondDualClass_zero :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 0) =
      ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap_secondDualClass, show secondGramTwiceInverse 0 0 = -2 from rfl,
    ← AddCircle.coe_add_period (1 : ℚ) (((-2 : ℤ) : ℚ) / 4)]
  norm_num

/-- The spinor class `C₇*` of the second ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_secondDualClass_six :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 6) = 0 := by
  rw [discriminantQuadraticMap_secondDualClass, show secondGramTwiceInverse 6 6 = -4 from rfl,
    AddCircle.coe_eq_zero_iff]
  exact ⟨-1, by norm_num⟩

/-- The spinor class `C₈*` of the second ten-curve lattice has full norm `-2` and is
isotropic. -/
@[simp]
theorem discriminantQuadraticMap_secondDualClass_seven :
    secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 7) = 0 := by
  rw [discriminantQuadraticMap_secondDualClass, show secondGramTwiceInverse 7 7 = -4 from rfl,
    AddCircle.coe_eq_zero_iff]
  exact ⟨-1, by norm_num⟩

/-- The isotropic discriminant classes of the second ten-curve lattice are `0` and the two spinor
classes `C₇*` and `C₈*`. -/
theorem setOf_discriminantQuadraticMap_secondLattice_eq_zero :
    {a | secondLattice.discriminantQuadraticMap isEven_secondLattice a = 0} =
      {0, secondDualClass 6, secondDualClass 7} := by
  obtain ⟨h0, -, -, h06, h07, -⟩ := secondDualClass_pairwise_ne
  have h : secondLattice.discriminantQuadraticMap isEven_secondLattice (secondDualClass 0) ≠ 0 := by
    intro h
    have := AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := 2) two_pos
    norm_num [← discriminantQuadraticMap_secondDualClass_zero, h] at this
  ext a
  obtain ⟨k, rfl⟩ := bijective_vecCons_zero_secondDualClass.2 a
  fin_cases k <;> simp [h, h0, h06, h07, -discriminantQuadraticMap_secondDualClass_zero]

/-- The second ten-curve lattice has exactly three isotropic discriminant classes. -/
theorem ncard_setOf_discriminantQuadraticMap_secondLattice_eq_zero :
    {a | secondLattice.discriminantQuadraticMap isEven_secondLattice a = 0}.ncard = 3 := by
  obtain ⟨-, h6, h7, -, -, h67⟩ := secondDualClass_pairwise_ne
  rw [setOf_discriminantQuadraticMap_secondLattice_eq_zero]
  exact Set.ncard_eq_three.mpr ⟨0, _, _, h6.symm, h7.symm, h67, rfl⟩

end TauCeti.EnriquesTenCurve
