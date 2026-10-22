/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Blowup.Submodule

/-!
# Examples: the blowup of a submodule

For `C = B = ℤ` and `F = {2}`, the graded ring `R(J)` contains `2 T` but not `T`: its degree one
coefficients are even, so `R(J)` is not all of `ℤ[T]`. For `F = {0, 1}`, which generates the unit
ideal, the morphism `Spec ℤ ⟶ Proj R(J)` pulls `D₊(0 T)` back to the empty set and `D₊(1 T)`
back to all of `Spec ℤ`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of Theorem 2.5, Case I, (1.1) and (1.2)(i).
-/

open AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry submoduleBlowup

-- For `F = {2}` the degree one piece of `R(J)` contains `2 T`.
example : ((monomialDegreeOne ℤ (Set.mem_singleton (2 : ℤ)) :
    coeffSubalgebra fun n ↦ Submodule.span ℤ {(2 : ℤ)} ^ n) : Polynomial ℤ) =
      Polynomial.monomial 1 2 :=
  coe_monomialDegreeOne ℤ _

-- For `F = {2}` the variable `T` itself does not lie in `R(J)`.
example : Polynomial.monomial 1 (1 : ℤ) ∉
    coeffSubalgebra fun n ↦ Submodule.span ℤ {(2 : ℤ)} ^ n := by
  rw [monomial_mem_coeffSubalgebra_iff, pow_one, Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  rw [smul_eq_mul] at ha
  omega

-- For `F = {0, 1}` the standard open `D₊(0 T)` pulls back to the empty set.
example : fromSpec ℤ (F := {0, 1})
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem 0 rfl)) isUnit_one) ⁻¹ᵁ
    Proj.basicOpen (gradedRing ℤ {0, 1}) (monomialDegreeOne ℤ (Set.mem_insert (0 : ℤ) {1})) =
      ⊥ :=
  (fromSpec_preimage_basicOpen ℤ _ _).trans PrimeSpectrum.basicOpen_zero

-- For `F = {0, 1}` the standard open `D₊(1 T)` pulls back to all of `Spec ℤ`.
example : fromSpec ℤ (F := {0, 1})
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem 0 rfl)) isUnit_one) ⁻¹ᵁ
    Proj.basicOpen (gradedRing ℤ {0, 1}) (monomialDegreeOne ℤ (Set.mem_insert_of_mem (0 : ℤ) rfl)) =
      ⊤ :=
  (fromSpec_preimage_basicOpen ℤ _ _).trans PrimeSpectrum.basicOpen_one
