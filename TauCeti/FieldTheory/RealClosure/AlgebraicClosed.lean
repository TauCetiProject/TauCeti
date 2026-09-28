/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.Galois
public import TauCeti.FieldTheory.RealClosure.Complexification
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Finite

/-! # Algebraic closedness of the complexification

`finrank_eq_one_of_forall_isSquare` proves that a finite extension of a finite
square-closed extension of a real closed field is trivial. `isAlgClosed_of_forall_isSquare`
then proves algebraic closedness of that square-closed field. In particular,
`isAlgClosed_quadraticAlgebra` proves that `R[i] = QuadraticAlgebra R (-1) 0` is
algebraically closed. `Polynomial.natDegree_le_two_of_irreducible` bounds irreducible degrees
by two; the polynomial IVT development uses this bound.

The proof puts finite extensions inside a finite normal closure. The 2-group argument
then applies to the Galois group over a square-closed intermediate field.

The degree bound generalizes Mathlib's `Irreducible.natDegree_le_two` from
`Mathlib.Analysis.Complex.Polynomial.Basic`, following its root, minimal polynomial,
and finite-dimension proof over an arbitrary real closed field.

## References

The algebraic argument uses a Sylow 2-subgroup of the Galois group; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open Module IntermediateField

variable {R C L : Type*} [Field R] [IsRealClosed R] [Field C] [Algebra R C]
    [FiniteDimensional R C] [Field L] [Algebra R L] [Algebra C L]
    [IsScalarTower R C L] [FiniteDimensional C L]

include R in
/-- Every finite extension of a finite square-closed extension of a real
closed field is trivial. -/
theorem finrank_eq_one_of_forall_isSquare (hsq : ∀ x : C, IsSquare x) :
    finrank C L = 1 := by
  let M := AlgebraicClosure L
  have : FiniteDimensional R L := FiniteDimensional.trans R C L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap R L).injective
  have : IsGalois R M := { }
  let N := normalClosure R L M
  let : Algebra C N := ((algebraMap L N).comp (algebraMap C L)).toAlgebra
  have : IsScalarTower C L N := .of_algebraMap_eq' rfl
  have : IsScalarTower R C N := .of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R L N, IsScalarTower.algebraMap_eq R C L]
    rfl)
  have hN : Module.finrank C N = 1 := finrank_eq_one_of_isGalois_of_forall_isSquare (R := R) hsq
  exact Nat.eq_one_of_dvd_one (hN ▸ finrank_dvd_finrank_right C L N)

include R in
/-- A finite square-closed extension of a real closed field is algebraically closed. -/
theorem isAlgClosed_of_forall_isSquare (hsq : ∀ x : C, IsSquare x) : IsAlgClosed C := by
  apply IsAlgClosed.of_exists_root
  intro p _ hp
  have : Fact (Irreducible p) := ⟨hp⟩
  have : FiniteDimensional C (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis hp.ne_zero).finite
  have hdim := finrank_eq_one_of_forall_isSquare (R := R) (L := AdjoinRoot p) hsq
  have hdeg : p.natDegree = 1 := by
    rwa [(AdjoinRoot.powerBasis hp.ne_zero).finrank] at hdim
  exact Polynomial.exists_root_of_degree_eq_one
    ((Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hdeg)

/-- The complexification `R[i]` of a real closed field is algebraically closed. -/
theorem isAlgClosed_quadraticAlgebra : IsAlgClosed (QuadraticAlgebra R (-1) 0) :=
  isAlgClosed_of_forall_isSquare (R := R) QuadraticAlgebra.isSquare

open Polynomial in
/-- Irreducible polynomials over a real closed field have degree at most two. -/
theorem _root_.Polynomial.natDegree_le_two_of_irreducible (p : R[X]) (hp : Irreducible p) :
    p.natDegree ≤ 2 := by
  have := isAlgClosed_quadraticAlgebra (R := R)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero
    (QuadraticAlgebra R (-1) 0) p (degree_pos_of_irreducible hp).ne'
  have heq := minpoly.eq_of_irreducible hp hz
  have hdeg : p.natDegree = (minpoly R z).natDegree := by
    rw [← heq, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
  rw [hdeg]
  exact (minpoly.natDegree_le z).trans_eq (QuadraticAlgebra.finrank_eq_two _ _)

end TauCeti.RealClosure
