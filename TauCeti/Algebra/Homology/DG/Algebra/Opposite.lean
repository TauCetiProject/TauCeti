/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.RingTheory.GradedAlgebra.Opposite

/-!
# Opposites of differential graded algebras

The opposite of a differential graded algebra uses the Koszul-signed multiplication

`op a * op b = (-1) ^ (|a| * |b|) • op (b * a)`.

With this multiplication, the unchanged differential `d (op a) = op (d a)` again obeys the
graded Leibniz rule.  The ordinary multiplicative opposite does not: reversing the two factors
without the Koszul sign puts the Leibniz sign on the wrong term.

The opposite differential `GradedOpposite.differential` and the transport of its degree and
Leibniz laws live with the graded opposite itself, in `TauCeti.RingTheory.GradedAlgebra.Opposite`;
this file adds the square-zero law.

## Main results

* `IsDGAlgebra.gradedOpposite`: the Koszul-signed opposite of a differential graded algebra is a
  differential graded algebra.

The convention follows B. Keller, *Deriving DG categories*, Section 1, and B. Keller,
*Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uA

namespace IsDGAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {G : InternalGrading R A} [GradedAlgebra G.piece] {d : A →ₗ[R] A}

/-- The Koszul-signed graded opposite of a differential graded algebra, with the same differential
on underlying elements. -/
theorem gradedOpposite (h : IsDGAlgebra G.piece d) :
    IsDGAlgebra (GradedOpposite.grading G).piece (GradedOpposite.differential G d) where
  map_mem hx := GradedOpposite.differential_map_mem G h.map_mem hx
  sq_zero x := by
    rw [← GradedOpposite.op_unop G x, GradedOpposite.differential_op,
      GradedOpposite.differential_op, h.sq_zero, GradedOpposite.op_zero]
  leibniz hx y := GradedOpposite.differential_leibniz G h.map_mem h.leibniz hx y

end IsDGAlgebra

end TauCeti
