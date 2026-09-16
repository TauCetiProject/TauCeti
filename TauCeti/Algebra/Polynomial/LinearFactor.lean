/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# The linear factor `X - C x`, and its reverse

Two facts about linear factors that Mathlib does not carry.

The *reversed* factor `C x - X` — the shape that arises as `x - θ` in `AdjoinRoot f` — has degree
`1`, like `X - C x` itself, which is the form Mathlib states.

A polynomial of degree at most one with root `x` is `C γ * (X - C x)` for a single scalar `γ`.
Writing it as `C a * X + C b`, the root condition gives `a * x + b = 0`, which identifies the
constant term and factors the polynomial. This works over noncommutative rings, with the scalar
factor on the left.

## Main results

* `Polynomial.natDegree_C_sub_X`: the reversed linear factor `C x - X` has degree `1`.
* `Polynomial.exists_eq_C_mul_X_sub_C_of_natDegree_le_one`: a polynomial of `natDegree ≤ 1` with
  root `x` is `C γ * (X - C x)` for some `γ`.

## Provenance

The statement of `exists_eq_C_mul_X_sub_C_of_natDegree_le_one` generalizes the commutative-ring
result adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`), `EllipticCurves/Mathlib/Basic.lean`.
Its consumer is the `x - T` descent map of
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`, where it pins down the line
through a `2`-torsion point.
-/

public section

namespace Polynomial

variable {R : Type*} [Ring R]

/-- The reversed linear polynomial `C x - X` has degree `1`, like `X - C x`. -/
@[simp]
theorem natDegree_C_sub_X {R : Type*} [Ring R] [Nontrivial R] (x : R) :
    (C x - X).natDegree = 1 := by
  rw [natDegree_sub, natDegree_X_sub_C]

/-- A polynomial of degree at most one with prescribed root `x` is a left scalar multiple of
`X - C x`, over any ring. -/
lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨a, b, hp⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
  have hx' : a * x + b = 0 := by
    simpa only [IsRoot, hp, eval_add, eval_C_mul, eval_C, eval_X] using hx
  refine ⟨a, ?_⟩
  rw [hp, mul_sub, ← C_mul, eq_neg_of_add_eq_zero_right hx', map_neg, sub_eq_add_neg]

end Polynomial

end
