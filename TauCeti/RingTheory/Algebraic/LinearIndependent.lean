/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Basic
-- Proof-only: the dimension of the span of a linearly independent family.
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Linear independence from transcendence

The powers of a transcendental element of an algebra are linearly independent over the base ring.

## Main results

* `Transcendental.linearIndependent_pow`: the powers of a transcendental element are
  linearly independent over the base ring.
* `Transcendental.finrank_span_range_pow`: over a field, the span of the first `n` powers of a
  transcendental element has dimension `n`.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The powers of a transcendental element are linearly independent** over the base ring: they
are the images of the monomial basis of `R[X]` under the injective evaluation map at `x`. -/
theorem _root_.Transcendental.linearIndependent_pow {x : A} (hx : Transcendental R x) :
    LinearIndependent R fun n : ℕ ↦ x ^ n := by
  have h := (Polynomial.basisMonomials R).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
  simpa [Function.comp_def] using h

/-- **The span of `1, x, …, x^{n-1}` has dimension `n`** for a transcendental element `x` of an
algebra over a field. -/
theorem _root_.Transcendental.finrank_span_range_pow {K B : Type*} [Field K] [Ring B]
    [Algebra K B] {x : B} (hx : Transcendental K x) (n : ℕ) :
    Module.finrank K (Submodule.span K (Set.range fun i : Fin n ↦ x ^ (i : ℕ))) = n :=
  (finrank_span_eq_card (hx.linearIndependent_pow.comp _ Fin.val_injective)).trans
    (Fintype.card_fin n)

end TauCeti
