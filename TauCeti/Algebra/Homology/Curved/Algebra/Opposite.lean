/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Defs
public import TauCeti.RingTheory.GradedAlgebra.Opposite

/-!
# Opposites of curved differential graded algebras

The graded opposite of a curved differential graded algebra `(A, d, w)` is the Koszul-signed
opposite algebra

`op a * op b = (-1) ^ (|a| * |b|) • op (b * a)`

with the unchanged differential `d (op a) = op (d a)` and curvature `-op w`. The sign on the
curvature is forced: the curvature has even degree, so `op a * op w = op (w * a)` and
`op w * op a = op (a * w)` carry no Koszul sign, and the right-module square
`d (d a) = a * w - w * a` becomes `op a * (-op w) - (-op w) * op a` on the opposite. The
curvature `op w` would satisfy the equation with the opposite sign, which is not the right-module
convention.

## Main results

* `IsCurvedDGAlgebra.gradedOpposite`: the Koszul-signed opposite of a curved differential graded
  algebra of curvature `w` is a curved differential graded algebra of curvature `-op w`.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
* B. Keller, *Deriving DG categories*, Section 1, for the Koszul-signed opposite.
-/

public section

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]

namespace IsCurvedDGAlgebra

variable {G : InternalGrading R A} [GradedAlgebra G.piece] {d : A →ₗ[R] A} {w : A}

/-- **The graded opposite of a curved differential graded algebra.** The Koszul-signed opposite,
with the same differential on underlying elements, is a curved differential graded algebra whose
curvature is `-op w`: the sign is forced by the right-module convention `d (d a) = a * w - w * a`,
because reversing the two products with the even-degree curvature carries no Koszul sign. -/
theorem gradedOpposite (h : IsCurvedDGAlgebra G.piece d w) :
    IsCurvedDGAlgebra (GradedOpposite.grading G).piece (GradedOpposite.differential G d)
      (-GradedOpposite.op G w) where
  map_mem hx := GradedOpposite.differential_map_mem G h.map_mem hx
  leibniz hx y := GradedOpposite.differential_leibniz G h.map_mem h.leibniz hx y
  curvature_mem := neg_mem ((GradedOpposite.op_mem_piece_iff G 2 w).2 h.curvature_mem)
  sq_eq x := by
    rw [← GradedOpposite.op_unop G x, GradedOpposite.differential_op,
      GradedOpposite.differential_op, h.sq_eq, GradedOpposite.op_sub, mul_neg, neg_mul,
      sub_neg_eq_add, GradedOpposite.op_mul_op_of_even_right G h.curvature_mem even_two,
      GradedOpposite.op_mul_op_of_even_left G h.curvature_mem even_two, neg_add_eq_sub]
  map_curvature := by
    rw [map_neg, GradedOpposite.differential_op, h.map_curvature, GradedOpposite.op_zero,
      neg_zero]

end IsCurvedDGAlgebra

end TauCeti
