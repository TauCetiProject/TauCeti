module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Basic formulas for the probabilists' Hermite polynomials

This file records low-degree formulas for Mathlib's probabilists' Hermite
polynomials.
-/

public section

namespace TauCeti

open Polynomial

/-- The second probabilists' Hermite polynomial is `X^2 - 1`. -/
theorem _root_.Polynomial.hermite_two : hermite 2 = X ^ 2 - C 1 := by
  rw [Polynomial.hermite_add_two 0, hermite_one, hermite_zero]
  simp [pow_two]

end TauCeti
