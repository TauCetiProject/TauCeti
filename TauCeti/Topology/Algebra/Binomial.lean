/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Continuity of generalized binomial coefficients

In any characteristic-zero topological division semiring with a `BinomialRing` structure,
`Ring.multichoose x n` is `(n !)⁻¹` times the evaluation of the ascending Pochhammer polynomial
`ascPochhammer R n` at `x`, and is therefore continuous in `x`.

## Main declarations

* `TauCeti.continuous_multichoose` — continuity of `x ↦ Ring.multichoose x n` in any
  characteristic-zero topological division semiring with a `BinomialRing` structure.
-/

public section

namespace TauCeti

/-- In any characteristic-zero topological division semiring with a `BinomialRing` structure,
`x ↦ Ring.multichoose x n` is continuous for every `n : ℕ`. -/
theorem continuous_multichoose {R : Type*} [DivisionSemiring R] [CharZero R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [BinomialRing R] (n : ℕ) :
    Continuous fun x : R ↦ Ring.multichoose x n := by
  have h : (fun x : R ↦ Ring.multichoose x n) =
      fun x : R ↦ (n.factorial : R)⁻¹ * (ascPochhammer R n).eval x := by
    ext x
    have hfac : (n.factorial : R) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hx := Ring.factorial_nsmul_multichoose_eq_ascPochhammer x n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at hx
    rw [← hx, inv_mul_cancel_left₀ hfac]
  rw [h]
  exact continuous_const.mul (ascPochhammer R n).continuous

end TauCeti

end
