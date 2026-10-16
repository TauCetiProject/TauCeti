/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial derivatives

This file records auxiliary results relating Mathlib's polynomial derivative APIs and controlling
degrees of derivatives under coefficient maps.

The derivation `Polynomial.derivative'` has `Polynomial.derivative` as its underlying function.

A coefficient map can lower the degree of a polynomial, and in positive characteristic it can
lower the degree of a derivative even when it preserves the degree of the polynomial itself.
Over an additively torsion-free target the second phenomenon cannot occur: preserving the degree
of `p` preserves the degree of `p.derivative`.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The derivation `derivative'` has the ordinary polynomial derivative as its underlying
function. -/
theorem _root_.Polynomial.coe_derivative' [CommSemiring R] :
    ⇑(derivative' : Derivation R R[X] R[X]) = derivative :=
  _root_.funext derivative'_apply

variable [Semiring R] [Semiring S] [HasUniqueDiv S]

/-- A coefficient map into an additively torsion-free semiring which preserves the degree of a
polynomial also preserves the degree of its derivative. -/
theorem _root_.Polynomial.natDegree_map_derivative_eq_of_natDegree_map_eq {f : R →+* S}
    {p : R[X]} (h : (p.map f).natDegree = p.natDegree) :
    (p.derivative.map f).natDegree = p.derivative.natDegree := by
  refine Nat.le_antisymm natDegree_map_le ?_
  rw [← derivative_map, natDegree_derivative (p.map f), h]
  exact natDegree_derivative_le p

end TauCeti
