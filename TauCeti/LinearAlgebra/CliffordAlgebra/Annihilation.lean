/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic

/-!
# Clifford elements annihilated by generators

An isotropic vector `a` annihilates, under left multiplication by `ι Q a`, every ordered product of
generators in which it occurs as a factor and to whose factors it is orthogonal. Since a product of
linearly independent generators is nonzero (`CliffordAlgebra.prod_map_ι_ofFn_ne_zero`), this
produces nonzero elements of a Clifford algebra annihilated by a whole totally isotropic subspace,
from which highest weight vectors of Clifford modules are built.

On an element annihilated by a generator, a bivector involving that generator acts by a scalar read
off from the polar form.

## Main results

* `CliffordAlgebra.ι_mul_prod_map_ι_eq_zero`: an isotropic factor orthogonal to the other factors
  annihilates the product from the left.
* `CliffordAlgebra.bivector_mul_eq_smul_of_ι_mul_eq_zero_left` and
  `CliffordAlgebra.bivector_mul_eq_smul_of_ι_mul_eq_zero_right`: the action of a bivector on an
  element annihilated by one of its two vectors.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- **An isotropic factor annihilates the product from the left**, provided that it is orthogonal to
every factor: it moves past the factors preceding its occurrence at the cost of a sign, and then
squares to `Q a = 0`. -/
theorem ι_mul_prod_map_ι_eq_zero {l : List M} {a : M} (ha : a ∈ l) (hQ : Q a = 0)
    (hortho : ∀ x ∈ l, Q.IsOrtho a x) : ι Q a * (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [← mul_assoc, ι_sq_scalar, hQ, map_zero, zero_mul]
    · rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho (hortho b List.mem_cons_self), neg_mul, mul_assoc,
        ih ha fun x hx ↦ hortho x (List.mem_cons_of_mem b hx), mul_zero, neg_zero]

variable [Invertible (2 : R)]

/-- On an element annihilated by `ι Q a`, the bivector of `a` and `b` acts through half their polar
form: `ι Q a` moves to the right of `ι Q b`, leaving the polar form behind. -/
theorem bivector_mul_eq_smul_of_ι_mul_eq_zero_left {a : M} {c : CliffordAlgebra Q}
    (hc : ι Q a * c = 0) (b : M) :
    bivector Q a b * c = (⅟(2 : R) * QuadraticMap.polar Q a b) • c := by
  have hab : ι Q a * ι Q b = algebraMap R _ (QuadraticMap.polar Q a b) - ι Q b * ι Q a :=
    eq_sub_of_add_eq (ι_mul_ι_add_swap a b)
  have hba : ι Q b * ι Q a * c = 0 := by rw [mul_assoc, hc, mul_zero]
  rw [bivector_def, smul_mul_assoc, sub_mul, hab, sub_mul, hba]
  simp [mul_smul, Algebra.algebraMap_eq_smul_one]

/-- On an element annihilated by `ι Q b`, the bivector of `a` and `b` acts through minus half their
polar form. -/
theorem bivector_mul_eq_smul_of_ι_mul_eq_zero_right (a : M) {b : M} {c : CliffordAlgebra Q}
    (hc : ι Q b * c = 0) :
    bivector Q a b * c = -(⅟(2 : R) * QuadraticMap.polar Q a b) • c := by
  rw [bivector_swap Q b a, neg_mul, bivector_mul_eq_smul_of_ι_mul_eq_zero_left hc,
    QuadraticMap.polar_comm, neg_smul]

end CliffordAlgebra
