/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Clifford algebras of zero-dimensional modules

The Clifford algebra of a subsingleton module consists only of scalars. This file records the
canonical algebra equivalence with the coefficient ring and the resulting elementary behavior of
the grading and reversal. These statements let low-dimensional Clifford-group calculations handle
dimension zero without choosing a concrete model for the zero module.

The equivalence generalizes Mathlib's `CliffordAlgebraRing.equiv` from its concrete zero quadratic
form on `Unit` to any subsingleton module.

## Main results

* `CliffordAlgebra.equivOfSubsingleton` identifies a zero-dimensional Clifford algebra with its
  coefficient ring.
* `CliffordAlgebra.even_eq_top_of_subsingleton` says that every element is even.
* `CliffordAlgebra.reverse_eq_self_of_subsingleton` says that reversal is the identity.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- The Clifford algebra of a quadratic form on a subsingleton module is canonically isomorphic
to the coefficient ring. -/
noncomputable def equivOfSubsingleton [Subsingleton M] : CliffordAlgebra Q ≃ₐ[R] R :=
  (equivOfIsometry <| QuadraticMap.IsometryEquiv.mk
    (LinearEquiv.ofSubsingleton M Unit) fun x => by
      rw [Subsingleton.elim x 0, map_zero]
      simp).trans CliffordAlgebraRing.equiv

/-- The zero-dimensional Clifford equivalence fixes scalars. -/
@[simp]
theorem equivOfSubsingleton_algebraMap [Subsingleton M] (r : R) :
    equivOfSubsingleton Q (algebraMap R (CliffordAlgebra Q) r) = r := by
  exact (equivOfSubsingleton Q).commutes r

/-- The inverse zero-dimensional Clifford equivalence is the scalar inclusion. -/
@[simp]
theorem equivOfSubsingleton_symm_apply [Subsingleton M] (r : R) :
    (equivOfSubsingleton Q).symm r = algebraMap R (CliffordAlgebra Q) r := by
  apply (equivOfSubsingleton Q).injective
  simp

/-- Every vector has zero image in the Clifford algebra of a subsingleton module. -/
@[simp]
theorem ι_eq_zero_of_subsingleton [Subsingleton M] (x : M) : ι Q x = 0 := by
  rw [Subsingleton.elim x 0, map_zero]

/-- Every element of a zero-dimensional Clifford algebra is even. -/
theorem even_eq_top_of_subsingleton [Subsingleton M] : even Q = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact (even Q).algebraMap_mem r
  | ι x => rw [ι_eq_zero_of_subsingleton]; exact (even Q).zero_mem
  | mul x y hx hy => exact (even Q).mul_mem hx hy
  | add x y hx hy => exact (even Q).add_mem hx hy

/-- Reversal is the identity on a zero-dimensional Clifford algebra. -/
@[simp]
theorem reverse_eq_self_of_subsingleton [Subsingleton M] (x : CliffordAlgebra Q) :
    reverse x = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes r
  | ι x => simp
  | mul x y hx hy =>
      rw [reverse.map_mul, hx, hy]
      apply (equivOfSubsingleton Q).injective
      simp only [map_mul, mul_comm]
  | add x y hx hy => rw [reverse.map_add, hx, hy]

end CliffordAlgebra

end
