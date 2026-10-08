/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.Centralizer.Basic
public import TauCeti.Algebra.Subalgebra.Center

/-!
# Centralizers of simple subalgebras

A simple subalgebra `B` of a finite-dimensional central simple algebra `A` is its own
double centralizer, even when `B` is not central over the base field. Its centralizer is simple,
and the centers of `B` and its centralizer have the same image in `A`.

In particular, the center of the centralizer of a subfield is that subfield itself. This is
the center identification needed to regard a centralizer as a central algebra over the subfield
and enlarge separable subfields using the Jacobson–Noether theorem. No separability assumption
on the subfield is needed for the centralizer statements here.

The simplicity and dimension count reuse the bimodule identification
`TauCeti.centralizerAlgEquivEnd` and the tensor-product simplicity theorem with the central
factor on the right. Applying the dimension count twice proves the double-centralizer equality.

## References

R. S. Pierce, *Associative Algebras*, Chapter 12; P. Gille and T. Szamuely,
*Central Simple Algebras and Galois Cohomology*, Section 2.2.
-/

public section

namespace Subalgebra

open Module

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  (B : Subalgebra K A) [IsSimpleRing B]

/-- A simple subalgebra of a finite-dimensional central simple algebra is its own double
centralizer. In particular, this applies to subfields larger than the base field. -/
@[simp]
theorem centralizer_centralizer_of_isSimpleRing :
    centralizer K (Set.centralizer (B : Set A)) = B := by
  have := B.isSimpleRing_centralizer_of_isSimpleRing_tensorProduct
  have hC : 0 < finrank K ↥(centralizer K (B : Set A)) := Module.finrank_pos
  have hdim : finrank K B = finrank K ↥(centralizer K
      (centralizer K (B : Set A) : Set A)) := by
    apply Nat.eq_of_mul_eq_mul_left hC
    rw [TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite,
      ← TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite B,
      mul_comm]
  exact (eq_of_le_of_finrank_eq (le_centralizer_centralizer K) hdim).symm

/-- The centers of a simple subalgebra and its centralizer have the same image in the
ambient central simple algebra. The centralizer need not be central over the base field. -/
-- `map_center_val` already simplifies the left-hand side to an intersection.
-- Use this theorem explicitly to rewrite it as the mapped center of `B`.
theorem map_center_centralizer_val :
    (center K ↥(centralizer K (B : Set A))).map (centralizer K (B : Set A)).val =
      (center K B).map B.val := by
  rw [map_center_val, map_center_val]
  simpa only [coe_centralizer, centralizer_centralizer_of_isSimpleRing] using
    inf_comm (centralizer K (B : Set A)) B

end Subalgebra
