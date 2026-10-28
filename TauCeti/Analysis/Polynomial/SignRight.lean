/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.SignRight
public import TauCeti.Algebra.Polynomial.Eval.OneSided

/-! # Algebraic and analytic right-hand signs of real polynomials

Mathlib's `Polynomial.signRight x p` is the eventual sign of a real polynomial along `𝓝[>] x`.
The algebraic sign `Polynomial.derivSignRight p x`, the sign of the first nonzero derivative,
is realized on an interval immediately to the right of `x`, so the two agree on every real
polynomial, including the zero polynomial and at multiple roots.
-/

public section

open Set

namespace Polynomial

/-- Over `ℝ`, the algebraic right-hand sign is Mathlib's eventual right-hand sign. -/
theorem derivSignRight_eq_signRight (p : ℝ[X]) (a : ℝ) :
    p.derivSignRight a = signRight a p := by
  obtain ⟨-, u, -, hau, -, hu⟩ := p.exists_derivSignLeft_derivSignRight a
  exact (signRight_eq_of_eventually (Filter.mem_of_superset (Ioo_mem_nhdsGT hau) hu)).symm

end Polynomial
