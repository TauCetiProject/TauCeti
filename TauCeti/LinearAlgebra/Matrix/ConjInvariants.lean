/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Conjugation-invariant polynomial functions on square matrices

Polynomial functions on the square matrices `Matrix n n R` are `MvPolynomial (n × n) R`: the
variable `X (i, j)` is the entry `Z i j`, and a matrix is evaluated through `fun p => Z p.1 p.2`.
This file defines the subalgebra of those whose values at `R`-points are invariant under
conjugation `g • Z = g * Z * g⁻¹` by `GL n R`. Over an infinite field this is the invariant ring
of the adjoint quotient of `gl_n`; over a finite ring it can be strictly larger, since a nonzero
polynomial may vanish at every `R`-point.

## Main definitions

* `TauCeti.Matrix.conjInvariants`: the polynomial functions on square matrices whose values at
  `R`-points are invariant under conjugation.
-/

public section

open MvPolynomial

namespace TauCeti.Matrix

variable (R : Type*) [CommRing R] (n : Type*) [Fintype n] [DecidableEq n]

/-- The polynomial functions on square matrices whose values at `R`-points are invariant under
conjugation `g • Z = g * Z * g⁻¹` by `GL n R`. This is invariance at points, not as polynomials:
over an infinite field the two agree, but over a finite ring this subalgebra can be larger. -/
def conjInvariants : Subalgebra R (MvPolynomial (n × n) R) where
  carrier := {Q | ∀ (g : GL n R) (Z : Matrix n n R),
    eval (fun p => ((g : Matrix n n R) * Z * (g⁻¹ : GL n R)) p.1 p.2) Q =
      eval (fun p => Z p.1 p.2) Q}
  mul_mem' hP hQ g Z := by simp only [map_mul, hP g Z, hQ g Z]
  add_mem' hP hQ g Z := by simp only [map_add, hP g Z, hQ g Z]
  algebraMap_mem' c g Z := by simp

variable {R n}

/-- Membership in `TauCeti.Matrix.conjInvariants`, unfolded. -/
theorem mem_conjInvariants_iff {Q : MvPolynomial (n × n) R} :
    Q ∈ conjInvariants R n ↔ ∀ (g : GL n R) (Z : Matrix n n R),
      eval (fun p => ((g : Matrix n n R) * Z * (g⁻¹ : GL n R)) p.1 p.2) Q =
        eval (fun p => Z p.1 p.2) Q :=
  Iff.rfl

end TauCeti.Matrix
