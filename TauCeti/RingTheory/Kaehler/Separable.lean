/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Kähler differentials of separable elements

This file records how the universal derivation detects separability and transcendence for field
extensions.

## Main results

* `TauCeti.D_eq_zero_of_isSeparable`: a separable algebraic element has vanishing differential.
* `TauCeti.transcendental_of_D_ne_zero`: over a perfect base field, an element with nonzero
  differential is transcendental.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial KaehlerDifferential

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}

/-- A separable algebraic element has vanishing universal differential, so the universal
derivation detects only the inseparable or transcendental part of an extension. -/
theorem D_eq_zero_of_isSeparable (hx : IsSeparable k x) : D k F x = 0 := by
  have hcoeff : aeval x (minpoly k x).derivative ≠ 0 :=
    Separable.aeval_derivative_ne_zero hx (minpoly.aeval k x)
  have hder := (D k F).map_aeval (minpoly k x) x
  rw [minpoly.aeval, map_zero] at hder
  exact (smul_eq_zero.mp hder.symm).resolve_left hcoeff

variable [PerfectField k]

/-- Over a perfect base field, an element with nonzero universal differential is transcendental:
an algebraic element is separable, hence has vanishing differential. -/
theorem transcendental_of_D_ne_zero (hx : D k F x ≠ 0) : Transcendental k x := by
  intro halg
  exact hx (D_eq_zero_of_isSeparable
    (PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)))

end TauCeti
