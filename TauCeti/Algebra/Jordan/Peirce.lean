/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Peirce decomposition at an idempotent

The Jordan identity implies `2L³ - 3L² + L = 0` for multiplication by an idempotent.
Its Lagrange projections give a unique decomposition into the `1`, `⅟2` and `0` spaces.
The product rules show that the extreme spaces annihilate one another, their multiplication
operators commute, and products of half-space elements have no half-component. Multiplication
by an extreme-space element preserves every Peirce space. Together these laws reduce Jordan
algebra calculations to components at an idempotent, including diagonal frames in Albert algebras.
The four-variable identity used here is shared with the theory of inner derivations.
The base ring need only have `2` invertible; no unit in the algebra, inner product or
finite dimension is required.

The projection proofs are adapted from Bryan Ehrlich's euclidean-jordan,
`EuclideanJordan/Peirce.lean`, `PeirceMul.lean` and `Orthogonal.lean` at a83407e4.
The linearization already in Mathlib replaces the source's polarization argument.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Proposition IV.1.1.
* McCrimmon, *A Taste of Jordan Algebras*, §II.8.
-/

public section

noncomputable section

namespace TauCeti.Jordan

variable {R J : Type*} [CommRing R] [NonUnitalNonAssocCommRing J] [Module R J]
  [SMulCommClass R J J]

variable (R) in
/-- The Peirce space of eigenvalue `μ` for multiplication by `c`. -/
def peirceSpace (c : J) (μ : R) : Submodule R J := Module.End.eigenspace (LinearMap.mulLeft R c) μ

/-- The Peirce submodule is the eigenspace of left multiplication. -/
theorem peirceSpace_def (c : J) (μ : R) :
    peirceSpace R c μ = Module.End.eigenspace (LinearMap.mulLeft R c) μ := (rfl)

@[simp]
theorem mem_peirceSpace {c y : J} {μ : R} : y ∈ peirceSpace R c μ ↔ c * y = μ • y :=
  Module.End.mem_eigenspace_iff

open Polynomial in
variable (R) in
/-- The projection polynomial `2L² - L` onto the `1`-space. -/
def peirceOne (c : J) : Module.End R J :=
  aeval (LinearMap.mulLeft R c) (C 2 * X ^ 2 - X : R[X])

open Polynomial in
variable (R) in
/-- The projection polynomial `4L - 4L²` onto the half-space. -/
def peirceHalf (c : J) : Module.End R J :=
  aeval (LinearMap.mulLeft R c) (C 4 * X - C 4 * X ^ 2 : R[X])

open Polynomial in
variable (R) in
/-- The projection polynomial `1 - 3L + 2L²` onto the `0`-space. -/
def peirceZero (c : J) : Module.End R J :=
  aeval (LinearMap.mulLeft R c) (1 - C 3 * X + C 2 * X ^ 2 : R[X])

theorem peirceOne_apply (c y : J) : peirceOne R c y = (2 : R) • (c * (c * y)) - c * y := by
  simp [peirceOne, pow_two, Module.algebraMap_end_apply]

theorem peirceHalf_apply (c y : J) :
    peirceHalf R c y = (4 : R) • (c * y) - (4 : R) • (c * (c * y)) := by
  simp [peirceHalf, pow_two, Module.algebraMap_end_apply]

theorem peirceZero_apply (c y : J) :
    peirceZero R c y = y - (3 : R) • (c * y) + (2 : R) • (c * (c * y)) := by
  simp [peirceZero, pow_two, Module.algebraMap_end_apply]

/-- The three projection polynomials resolve the identity, even without idempotence. -/
@[simp]
theorem peirceOne_add_peirceHalf_add_peirceZero (c y : J) :
    peirceOne R c y + peirceHalf R c y + peirceZero R c y = y := by
  simp only [peirceOne_apply, peirceHalf_apply, peirceZero_apply]
  module

/-- The `one` projection fixes the `1`-Peirce space. -/
@[simp]
theorem peirceOne_of_mem_peirceSpace_one {c x : J}
    (hx : x ∈ peirceSpace R c 1) : peirceOne R c x = x := by
  rw [peirceOne, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  norm_num

/-- The `half` projection vanishes on the `1`-Peirce space. -/
@[simp]
theorem peirceHalf_of_mem_peirceSpace_one {c x : J}
    (hx : x ∈ peirceSpace R c 1) : peirceHalf R c x = 0 := by
  rw [peirceHalf, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  norm_num

/-- The `zero` projection vanishes on the `1`-Peirce space. -/
@[simp]
theorem peirceZero_of_mem_peirceSpace_one {c x : J}
    (hx : x ∈ peirceSpace R c 1) : peirceZero R c x = 0 := by
  rw [peirceZero, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  norm_num

/-- The `one` projection vanishes on the `0`-Peirce space. -/
@[simp]
theorem peirceOne_of_mem_peirceSpace_zero {c x : J}
    (hx : x ∈ peirceSpace R c 0) : peirceOne R c x = 0 := by
  rw [peirceOne, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  norm_num

/-- The `half` projection vanishes on the `0`-Peirce space. -/
@[simp]
theorem peirceHalf_of_mem_peirceSpace_zero {c x : J}
    (hx : x ∈ peirceSpace R c 0) : peirceHalf R c x = 0 := by
  rw [peirceHalf, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  norm_num

/-- The `zero` projection fixes the `0`-Peirce space. -/
@[simp]
theorem peirceZero_of_mem_peirceSpace_zero {c x : J}
    (hx : x ∈ peirceSpace R c 0) : peirceZero R c x = x := by
  rw [peirceZero, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  norm_num

variable [Invertible (2 : R)]

/-- The `one` projection vanishes on the `⅟(2 : R)`-Peirce space. -/
@[simp]
theorem peirceOne_of_mem_peirceSpace_invOf_two {c x : J}
    (hx : x ∈ peirceSpace R c ⅟(2 : R)) : peirceOne R c x = 0 := by
  rw [peirceOne, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  have ht : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self _
  have hp : (2 * ⅟(2 : R) ^ 2 - ⅟(2 : R)) = 0 := by
    linear_combination ⅟(2 : R) * ht
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    hp, zero_smul]

/-- The `half` projection fixes the `⅟(2 : R)`-Peirce space. -/
@[simp]
theorem peirceHalf_of_mem_peirceSpace_invOf_two {c x : J}
    (hx : x ∈ peirceSpace R c ⅟(2 : R)) : peirceHalf R c x = x := by
  rw [peirceHalf, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  have ht : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self _
  have hp : (4 * ⅟(2 : R) - 4 * ⅟(2 : R) ^ 2) = 1 := by
    linear_combination (1 - 2 * ⅟(2 : R)) * ht
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    hp, one_smul]

/-- The `zero` projection vanishes on the `⅟(2 : R)`-Peirce space. -/
@[simp]
theorem peirceZero_of_mem_peirceSpace_invOf_two {c x : J}
    (hx : x ∈ peirceSpace R c ⅟(2 : R)) : peirceZero R c x = 0 := by
  rw [peirceZero, Module.End.aeval_apply_of_mem_apply_eq_smul (mem_peirceSpace.mp hx)]
  have ht : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self _
  have hp : (1 - 3 * ⅟(2 : R) + 2 * ⅟(2 : R) ^ 2) = 0 := by
    linear_combination (⅟(2 : R) - 1) * ht
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    hp, zero_smul]

/-- Applying the projections recovers the three components of any Peirce decomposition. -/
theorem eq_projections_of_add_add_eq {c w x y z : J}
    (hx : x ∈ peirceSpace R c 1) (hy : y ∈ peirceSpace R c ⅟(2 : R))
    (hz : z ∈ peirceSpace R c 0) (h : x + y + z = w) :
    x = peirceOne R c w ∧ y = peirceHalf R c w ∧ z = peirceZero R c w := by
  subst w
  simp [map_add, hx, hy, hz]

/-- Peirce components are independent: a zero sum has all three components zero. -/
theorem eq_zero_of_mem_peirceSpace_of_add_add_eq_zero {c x y z : J}
    (hx : x ∈ peirceSpace R c 1) (hy : y ∈ peirceSpace R c ⅟(2 : R))
    (hz : z ∈ peirceSpace R c 0) (h : x + y + z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simpa using eq_projections_of_add_add_eq hx hy hz h

/-- The `1`-space meets the sum of the other two spaces trivially. -/
theorem peirceSpace_one_inf_sup_eq_bot (c : J) :
    peirceSpace R c 1 ⊓ (peirceSpace R c ⅟(2 : R) ⊔ peirceSpace R c 0) = ⊥ := by
  apply bot_unique
  rintro x ⟨hx, hx'⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
  have he : peirceOne R c (y + z) = 0 := by simp [hy, hz]
  simpa only [Submodule.mem_bot, he] using (peirceOne_of_mem_peirceSpace_one hx).symm

/-- The half- and zero-spaces meet trivially. -/
theorem peirceSpace_invOf_two_inf_zero_eq_bot (c : J) :
    peirceSpace R c ⅟(2 : R) ⊓ peirceSpace R c 0 = ⊥ := by
  apply bot_unique
  intro x hx
  have h := peirceHalf_of_mem_peirceSpace_invOf_two hx.1
  rw [peirceHalf_of_mem_peirceSpace_zero hx.2] at h
  exact h.symm

/-- The three Peirce spaces form an independent family of submodules. -/
theorem peirceSpace_iSupIndep (c : J) :
    iSupIndep ![peirceSpace R c 1, peirceSpace R c ⅟(2 : R), peirceSpace R c 0] := by
  simp only [iSupIndep_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨disjoint_iff.mpr (peirceSpace_one_inf_sup_eq_bot c), ?_, ?_⟩
  · apply disjoint_iff.mpr
    apply bot_unique
    rintro x ⟨hx, hx'⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    have he : peirceHalf R c (y + z) = 0 := by simp [hy, hz]
    simpa only [Submodule.mem_bot, he] using
      (peirceHalf_of_mem_peirceSpace_invOf_two hx).symm
  · apply disjoint_iff.mpr
    apply bot_unique
    rintro x ⟨hx, hx'⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    have he : peirceZero R c (y + z) = 0 := by simp [hy, hz]
    simpa only [Submodule.mem_bot, he] using (peirceZero_of_mem_peirceSpace_zero hx).symm

variable [IsCommJordan J]

omit [SMulCommClass R J J] in
/-- The Peirce polynomial `2L³ - 3L² + L = 0`, evaluated at `y`. -/
theorem two_smul_mul_mul_mul_add_mul {c : J} (hc : c * c = c) (y : J) :
    (2 : R) • (c * (c * (c * y))) + c * y = (3 : R) • (c * (c * y)) := by
  have h := mul_mul_mul_sub_add_add_eq_zero (isSMulRegular_two R J) c c y c
  simp only [hc, mul_comm y c, mul_comm (c * y) c] at h
  rw [← sub_eq_zero]
  convert h using 1; module

omit [SMulCommClass R J J] in
/-- The Peirce cubic identity solved for twice the third iterate of left multiplication. -/
theorem two_smul_mul_mul_mul {c : J} (hc : c * c = c) (y : J) :
    (2 : R) • (c * (c * (c * y))) = (3 : R) • (c * (c * y)) - c * y :=
  eq_sub_of_add_eq (two_smul_mul_mul_mul_add_mul hc y)

/-- The first projection takes values in the `1`-space. -/
theorem peirceOne_mem_peirceSpace {c : J} (hc : c * c = c) (y : J) :
    peirceOne R c y ∈ peirceSpace R c 1 := by
  rw [mem_peirceSpace, one_smul]
  simp only [peirceOne_apply, mul_sub, mul_smul_comm, two_smul_mul_mul_mul hc]
  module

/-- The half projection takes values in the half-space. -/
theorem peirceHalf_mem_peirceSpace {c : J} (hc : c * c = c) (y : J) :
    peirceHalf R c y ∈ peirceSpace R c ⅟(2 : R) := by
  rw [mem_peirceSpace]
  apply (smul_eq_iff_eq_invOf_smul (c := (2 : R))).mp
  simp only [peirceHalf_apply, mul_sub, mul_smul_comm]
  simp only [smul_sub, smul_smul]
  -- Reorder the scalar factors to apply the twice-cube identity.
  simp only [show (2 : R) * 4 = 4 * 2 by ring, mul_smul, two_smul_mul_mul_mul hc]
  module

/-- The last projection takes values in the `0`-space. -/
theorem peirceZero_mem_peirceSpace {c : J} (hc : c * c = c) (y : J) :
    peirceZero R c y ∈ peirceSpace R c 0 := by
  rw [mem_peirceSpace, zero_smul]
  simp only [peirceZero_apply, mul_add, mul_sub, mul_smul_comm, two_smul_mul_mul_mul hc]
  module

omit [Invertible (2 : R)] [IsCommJordan J] in
/-- The sum of the projection endomorphisms is the identity. -/
@[simp]
theorem peirceOne_add_peirceHalf_add_peirceZero_eq_id (c : J) :
    peirceOne R c + peirceHalf R c + peirceZero R c = LinearMap.id := by
  ext y
  exact peirceOne_add_peirceHalf_add_peirceZero c y

/-- The `one` projection fixes its image. -/
@[simp]
theorem peirceOne_peirceOne {c : J} (hc : c * c = c) (y : J) :
    peirceOne R c (peirceOne R c y) = peirceOne R c y :=
  peirceOne_of_mem_peirceSpace_one (peirceOne_mem_peirceSpace hc y)

/-- The `one` projection kills the half projection. -/
@[simp]
theorem peirceOne_peirceHalf {c : J} (hc : c * c = c) (y : J) :
    peirceOne R c (peirceHalf R c y) = 0 :=
  peirceOne_of_mem_peirceSpace_invOf_two (peirceHalf_mem_peirceSpace hc y)

/-- The `one` projection kills the zero projection. -/
@[simp]
theorem peirceOne_peirceZero {c : J} (hc : c * c = c) (y : J) :
    peirceOne R c (peirceZero R c y) = 0 :=
  peirceOne_of_mem_peirceSpace_zero (peirceZero_mem_peirceSpace hc y)

/-- Composition of the `one` and `one` projections. -/
@[simp]
theorem peirceOne_mul_peirceOne {c : J} (hc : c * c = c) :
    peirceOne R c * peirceOne R c = peirceOne R c := by
  ext y
  exact peirceOne_peirceOne hc y

/-- Composition of the `one` and `half` projections. -/
@[simp]
theorem peirceOne_mul_peirceHalf {c : J} (hc : c * c = c) :
    peirceOne R c * peirceHalf R c = 0 := by
  ext y
  exact peirceOne_peirceHalf hc y

/-- Composition of the `one` and `zero` projections. -/
@[simp]
theorem peirceOne_mul_peirceZero {c : J} (hc : c * c = c) :
    peirceOne R c * peirceZero R c = 0 := by
  ext y
  exact peirceOne_peirceZero hc y

/-- The `one` projection is an idempotent endomorphism. -/
theorem isIdempotentElem_peirceOne {c : J} (hc : c * c = c) :
    IsIdempotentElem (peirceOne R c) := peirceOne_mul_peirceOne hc

/-- The range of the `one` projection is its Peirce space. -/
@[simp]
theorem range_peirceOne {c : J} (hc : c * c = c) :
    LinearMap.range (peirceOne R c) = peirceSpace R c 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact peirceOne_mem_peirceSpace hc y
  · intro hx
    exact ⟨x, peirceOne_of_mem_peirceSpace_one hx⟩

/-- The `half` projection kills the one projection. -/
@[simp]
theorem peirceHalf_peirceOne {c : J} (hc : c * c = c) (y : J) :
    peirceHalf R c (peirceOne R c y) = 0 :=
  peirceHalf_of_mem_peirceSpace_one (peirceOne_mem_peirceSpace hc y)

/-- The `half` projection fixes its image. -/
@[simp]
theorem peirceHalf_peirceHalf {c : J} (hc : c * c = c) (y : J) :
    peirceHalf R c (peirceHalf R c y) = peirceHalf R c y :=
  peirceHalf_of_mem_peirceSpace_invOf_two (peirceHalf_mem_peirceSpace hc y)

/-- The `half` projection kills the zero projection. -/
@[simp]
theorem peirceHalf_peirceZero {c : J} (hc : c * c = c) (y : J) :
    peirceHalf R c (peirceZero R c y) = 0 :=
  peirceHalf_of_mem_peirceSpace_zero (peirceZero_mem_peirceSpace hc y)

/-- Composition of the `half` and `one` projections. -/
@[simp]
theorem peirceHalf_mul_peirceOne {c : J} (hc : c * c = c) :
    peirceHalf R c * peirceOne R c = 0 := by
  ext y
  exact peirceHalf_peirceOne hc y

/-- Composition of the `half` and `half` projections. -/
@[simp]
theorem peirceHalf_mul_peirceHalf {c : J} (hc : c * c = c) :
    peirceHalf R c * peirceHalf R c = peirceHalf R c := by
  ext y
  exact peirceHalf_peirceHalf hc y

/-- Composition of the `half` and `zero` projections. -/
@[simp]
theorem peirceHalf_mul_peirceZero {c : J} (hc : c * c = c) :
    peirceHalf R c * peirceZero R c = 0 := by
  ext y
  exact peirceHalf_peirceZero hc y

/-- The `half` projection is an idempotent endomorphism. -/
theorem isIdempotentElem_peirceHalf {c : J} (hc : c * c = c) :
    IsIdempotentElem (peirceHalf R c) := peirceHalf_mul_peirceHalf hc

/-- The range of the `half` projection is its Peirce space. -/
@[simp]
theorem range_peirceHalf {c : J} (hc : c * c = c) :
    LinearMap.range (peirceHalf R c) = peirceSpace R c ⅟(2 : R) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact peirceHalf_mem_peirceSpace hc y
  · intro hx
    exact ⟨x, peirceHalf_of_mem_peirceSpace_invOf_two hx⟩

/-- The `zero` projection kills the one projection. -/
@[simp]
theorem peirceZero_peirceOne {c : J} (hc : c * c = c) (y : J) :
    peirceZero R c (peirceOne R c y) = 0 :=
  peirceZero_of_mem_peirceSpace_one (peirceOne_mem_peirceSpace hc y)

/-- The `zero` projection kills the half projection. -/
@[simp]
theorem peirceZero_peirceHalf {c : J} (hc : c * c = c) (y : J) :
    peirceZero R c (peirceHalf R c y) = 0 :=
  peirceZero_of_mem_peirceSpace_invOf_two (peirceHalf_mem_peirceSpace hc y)

/-- The `zero` projection fixes its image. -/
@[simp]
theorem peirceZero_peirceZero {c : J} (hc : c * c = c) (y : J) :
    peirceZero R c (peirceZero R c y) = peirceZero R c y :=
  peirceZero_of_mem_peirceSpace_zero (peirceZero_mem_peirceSpace hc y)

/-- Composition of the `zero` and `one` projections. -/
@[simp]
theorem peirceZero_mul_peirceOne {c : J} (hc : c * c = c) :
    peirceZero R c * peirceOne R c = 0 := by
  ext y
  exact peirceZero_peirceOne hc y

/-- Composition of the `zero` and `half` projections. -/
@[simp]
theorem peirceZero_mul_peirceHalf {c : J} (hc : c * c = c) :
    peirceZero R c * peirceHalf R c = 0 := by
  ext y
  exact peirceZero_peirceHalf hc y

/-- Composition of the `zero` and `zero` projections. -/
@[simp]
theorem peirceZero_mul_peirceZero {c : J} (hc : c * c = c) :
    peirceZero R c * peirceZero R c = peirceZero R c := by
  ext y
  exact peirceZero_peirceZero hc y

/-- The `zero` projection is an idempotent endomorphism. -/
theorem isIdempotentElem_peirceZero {c : J} (hc : c * c = c) :
    IsIdempotentElem (peirceZero R c) := peirceZero_mul_peirceZero hc

/-- The range of the `zero` projection is its Peirce space. -/
@[simp]
theorem range_peirceZero {c : J} (hc : c * c = c) :
    LinearMap.range (peirceZero R c) = peirceSpace R c 0 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact peirceZero_mem_peirceSpace hc y
  · intro hx
    exact ⟨x, peirceZero_of_mem_peirceSpace_zero hx⟩

/-- The Peirce decomposition as a linear equivalence with its three component spaces. -/
def peirceLinearEquiv {c : J} (hc : c * c = c) :
    J ≃ₗ[R] peirceSpace R c 1 × peirceSpace R c ⅟(2 : R) × peirceSpace R c 0 where
  toFun y := (⟨peirceOne R c y, peirceOne_mem_peirceSpace hc y⟩,
    ⟨peirceHalf R c y, peirceHalf_mem_peirceSpace hc y⟩,
    ⟨peirceZero R c y, peirceZero_mem_peirceSpace hc y⟩)
  invFun p := p.1 + p.2.1 + p.2.2
  left_inv := peirceOne_add_peirceHalf_add_peirceZero c
  right_inv p := by
    rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
    simp [map_add, hx, hy, hz]
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp

@[simp]
theorem peirceLinearEquiv_apply {c : J} (hc : c * c = c) (y : J) :
    peirceLinearEquiv hc y = (⟨peirceOne R c y, peirceOne_mem_peirceSpace hc y⟩,
      ⟨peirceHalf R c y, peirceHalf_mem_peirceSpace hc y⟩,
      ⟨peirceZero R c y, peirceZero_mem_peirceSpace hc y⟩) := (rfl)

@[simp]
theorem peirceLinearEquiv_symm_apply {c : J} (hc : c * c = c)
    (p : peirceSpace R c 1 × peirceSpace R c ⅟(2 : R) × peirceSpace R c 0) :
    (peirceLinearEquiv hc).symm p = p.1 + p.2.1 + p.2.2 := (rfl)

/-- The three Peirce submodules span the algebra. -/
theorem peirceSpace_one_sup_invOf_two_sup_zero {c : J} (hc : c * c = c) :
    peirceSpace R c 1 ⊔ peirceSpace R c ⅟(2 : R) ⊔ peirceSpace R c 0 = ⊤ := by
  apply top_unique
  intro y _
  rw [← peirceOne_add_peirceHalf_add_peirceZero (R := R) c y]
  exact Submodule.add_mem_sup (Submodule.add_mem_sup
    (peirceOne_mem_peirceSpace hc y) (peirceHalf_mem_peirceSpace hc y))
    (peirceZero_mem_peirceSpace hc y)

/-- The independent family of three Peirce spaces spans the algebra at an idempotent. -/
theorem iSup_peirceSpace_eq_top {c : J} (hc : c * c = c) :
    ⨆ i : Fin 3, ![peirceSpace R c 1, peirceSpace R c ⅟(2 : R), peirceSpace R c 0] i = ⊤ := by
  simpa using peirceSpace_one_sup_invOf_two_sup_zero (R := R) hc

/-- Every element is a sum of elements of the three Peirce spaces. -/
theorem exists_peirce_decomposition {c : J} (hc : c * c = c) (y : J) :
    ∃ x ∈ peirceSpace R c 1, ∃ h ∈ peirceSpace R c ⅟(2 : R),
      ∃ z ∈ peirceSpace R c 0, y = x + h + z :=
  ⟨_, peirceOne_mem_peirceSpace hc y, _, peirceHalf_mem_peirceSpace hc y,
    _, peirceZero_mem_peirceSpace hc y, (peirceOne_add_peirceHalf_add_peirceZero c y).symm⟩

/-- Multiplication by an element of either extreme Peirce space commutes with `L_c`. -/
theorem mul_left_comm_of_mem_peirceSpace_one_or_zero {c x : J} (hc : c * c = c)
    (hx : x ∈ peirceSpace R c 1 ∨ x ∈ peirceSpace R c 0) (w : J) : c * (x * w) = x * (c * w) := by
  apply mul_left_comm_of_mul_eq_self_or_zero (isSMulRegular_two R J) hc
  simpa only [mem_peirceSpace, one_smul, zero_smul] using hx

/-- Multiplication by a `1`- or `0`-Peirce element preserves every `μ`-Peirce space. -/
theorem mul_mem_peirceSpace_of_mem_one_or_zero {c x y : J} {μ : R} (hc : c * c = c)
    (hx : x ∈ peirceSpace R c 1 ∨ x ∈ peirceSpace R c 0) (hy : y ∈ peirceSpace R c μ) :
    x * y ∈ peirceSpace R c μ := by
  rw [mem_peirceSpace] at hy ⊢
  rw [mul_left_comm_of_mem_peirceSpace_one_or_zero (R := R) hc hx, hy, mul_smul_comm]

/-- Multiplication by a `1`-Peirce element preserves every `μ`-Peirce space. -/
theorem mul_mem_peirceSpace_of_mem_one {c x y : J} {μ : R} (hc : c * c = c)
    (hx : x ∈ peirceSpace R c 1) (hy : y ∈ peirceSpace R c μ) :
    x * y ∈ peirceSpace R c μ :=
  mul_mem_peirceSpace_of_mem_one_or_zero hc (Or.inl hx) hy

/-- Multiplication by a `0`-Peirce element preserves every `μ`-Peirce space. -/
theorem mul_mem_peirceSpace_of_mem_zero {c x y : J} {μ : R} (hc : c * c = c)
    (hx : x ∈ peirceSpace R c 0) (hy : y ∈ peirceSpace R c μ) :
    x * y ∈ peirceSpace R c μ :=
  mul_mem_peirceSpace_of_mem_one_or_zero hc (Or.inr hx) hy

/-- The `1`-space annihilates the `0`-space. -/
theorem mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero {c x y : J}
    (hc : c * c = c) (hx : x ∈ peirceSpace R c 1)
    (hy : y ∈ peirceSpace R c 0) : x * y = 0 := by
  exact mul_eq_zero_of_mul_eq_self_of_mul_eq_zero (isSMulRegular_two R J) hc
    ((mem_peirceSpace.mp hx).trans (one_smul R x))
    ((mem_peirceSpace.mp hy).trans (zero_smul R y))

/-- A product of half-space elements has zero half-component. -/
theorem peirceHalf_mul_eq_zero_of_mem_peirceSpace_invOf_two {c x y : J} (hc : c * c = c)
    (hx : x ∈ peirceSpace R c ⅟(2 : R)) (hy : y ∈ peirceSpace R c ⅟(2 : R)) :
    peirceHalf R c (x * y) = 0 := by
  have h := mul_mul_mul_sub_add_add_eq_zero (isSMulRegular_two R J) c y x c
  rw [mem_peirceSpace] at hx hy
  simp only [hc, mul_comm _ c, hx, hy, mul_smul_comm] at h
  have he : c * (c * (x * y)) = c * (x * y) := by
    apply sub_eq_zero.mp
    convert h using 1; simp only [mul_comm, mul_smul_comm]; module
  simp only [peirceHalf_apply, he, sub_self]

/-- A product of half-Peirce elements lies in the sum of the extreme Peirce spaces. -/
theorem mul_mem_peirceSpace_one_sup_zero_of_mem_invOf_two {c x y : J} (hc : c * c = c)
    (hx : x ∈ peirceSpace R c ⅟(2 : R)) (hy : y ∈ peirceSpace R c ⅟(2 : R)) :
    x * y ∈ peirceSpace R c 1 ⊔ peirceSpace R c 0 := by
  have h := peirceOne_add_peirceHalf_add_peirceZero (R := R) c (x * y)
  rw [peirceHalf_mul_eq_zero_of_mem_peirceSpace_invOf_two hc hx hy, add_zero] at h
  rw [← h]
  exact Submodule.add_mem_sup (peirceOne_mem_peirceSpace hc _) (peirceZero_mem_peirceSpace hc _)

/-- The `1`- and `0`-space multiplication operators commute. -/
theorem mul_left_comm_of_mem_peirceSpace_one_of_mem_peirceSpace_zero {c x y : J}
    (hc : c * c = c) (hx : x ∈ peirceSpace R c 1)
    (hy : y ∈ peirceSpace R c 0) (w : J) : x * (y * w) = y * (x * w) := by
  exact mul_left_comm_of_mul_eq_self_of_mul_eq_zero (isSMulRegular_two R J) hc
    ((mem_peirceSpace.mp hx).trans (one_smul R x))
    ((mem_peirceSpace.mp hy).trans (zero_smul R y)) w

end TauCeti.Jordan
