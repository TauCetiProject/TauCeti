/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Basic
-- Proof-only: the rank of the span of a linearly independent family.
import Mathlib.LinearAlgebra.Dimension.Constructions
-- Proof-only: a nontrivial commutative ring satisfies the strong rank condition.
import Mathlib.RingTheory.FiniteType

/-!
# Linear independence from transcendence

The powers of a transcendental element of an algebra are linearly independent over the base ring.
Consequently, the first `n` powers span a submodule of rank `n` over a nontrivial commutative ring.

## Main results

* `Transcendental.linearIndependent_pow`: the powers of a transcendental element are
  linearly independent over the base ring.
* `Transcendental.finrank_span_range_pow`: over a nontrivial commutative ring, the span of the
  first `n` powers of a transcendental element has rank `n`.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The powers of a transcendental element are linearly independent over the base ring. -/
theorem _root_.Transcendental.linearIndependent_pow {x : A} (hx : Transcendental R x) :
    LinearIndependent R fun n : ℕ ↦ x ^ n := by
  simpa [Function.comp_def] using (Polynomial.basisMonomials R).linearIndependent.map_injOn
    (Polynomial.aeval x).toLinearMap (transcendental_iff_injective.mp hx).injOn

/-- The first `n` powers of a transcendental element span a submodule of rank `n` over a
nontrivial commutative ring. -/
theorem _root_.Transcendental.finrank_span_range_pow {K B : Type*} [CommRing K] [Nontrivial K]
    [Ring B] [Algebra K B] {x : B} (hx : Transcendental K x) (n : ℕ) :
    Module.finrank K (Submodule.span K (Set.range fun i : Fin n ↦ x ^ (i : ℕ))) = n :=
  (finrank_span_eq_card (hx.linearIndependent_pow.comp _ Fin.val_injective)).trans
    (Fintype.card_fin n)

end TauCeti
