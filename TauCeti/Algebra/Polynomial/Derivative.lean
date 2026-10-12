/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Degrees of derivatives under coefficient maps

A coefficient map can lower the degree of a polynomial, and in positive characteristic it can
lower the degree of a derivative even when it preserves the degree of the polynomial itself.
Over an additively torsion-free target the second phenomenon cannot occur: preserving the degree
of `p` preserves the degree of `p.derivative`.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*} [Semiring R] [Semiring S] [IsAddTorsionFree S]

/-- A coefficient map into an additively torsion-free semiring which preserves the degree of a
polynomial also preserves the degree of its derivative. -/
theorem _root_.Polynomial.natDegree_map_derivative_eq_of_natDegree_map_eq {f : R →+* S}
    {p : R[X]} (h : (p.map f).natDegree = p.natDegree) :
    (p.derivative.map f).natDegree = p.derivative.natDegree := by
  refine Nat.le_antisymm natDegree_map_le ?_
  rw [← derivative_map, natDegree_derivative (p.map f), h]
  exact natDegree_derivative_le p

end TauCeti
