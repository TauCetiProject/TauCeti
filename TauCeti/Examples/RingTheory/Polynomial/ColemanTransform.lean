/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.ComputeDegree
import TauCeti.RingTheory.Polynomial.Resultant.ColemanTransform

/-!
# Examples of Coleman's transform of prescribed rank

* The rank is the dimension, not the degree: for `B = P = 1`, rank one gives `1 - T` while rank
  zero gives `1`.
* For `diag(a, 0)`, whose determinant `1 - a T` has degree one, the rank-two transform keeps the
  factor `1 - B(0) T` of the zero eigenvalue.
* `D(T, F) = F` retains nilpotent coefficients: `F = 1 - ε T²` is returned unchanged even when
  `ε² = 0`.
-/

open Polynomial TauCeti

variable {R : Type*} [CommRing R]

-- The rank is the dimension: `D_(1,0)(1, 1) = 1 - T` but `D_(0,0)(1, 1) = 1`.
example : colemanDBounded 1 0 (1 : ℤ[X]) 1 = 1 - X ∧ colemanDBounded 0 0 (1 : ℤ[X]) 1 = 1 := by
  constructor <;> simp [colemanDBounded_one]

-- `diag(a, 0)` has determinant `1 - a T`, but its rank-two transform is
-- `(1 - B(a) T) (1 - B(0) T)`.
example (a : R) (B : R[X]) :
    colemanDBounded 2 B.natDegree B (1 - C a * X) =
      (1 - C (B.eval a) * X) * (1 - C (B.coeff 0) * X) := by
  simpa [coeff_zero_eq_eval_zero] using
    colemanDBounded_multiset_prod (B := B) {a, 0} le_rfl

-- `D(T, 1 - ε T²) = 1 - ε T²` at rank two, for every `ε`, in particular a nilpotent one.
example (ε : R) :
    colemanDBounded 2 1 X (1 - C ε * X ^ 2) = 1 - C ε * X ^ 2 :=
  colemanDBounded_X (by compute_degree!) (by simp) le_rfl
