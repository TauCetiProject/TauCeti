/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Sign.Defs
public import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Basic.Sign.Basic

/-! # Polynomial evaluation signs under ordered embeddings

Mapping coefficients and the evaluation point through a strictly monotone ring homomorphism
preserves the sign of the value. This applies to embeddings into ordered real closures.
Over an ordered commutative ring, rescaling the roots by a nonzero factor `a` and multiplying by
`a ^ natDegree` preserves the sign at the correspondingly rescaled point.
-/

public section

namespace Polynomial

/-- Mapping a polynomial and its evaluation point through a strictly monotone ring homomorphism
preserves its sign. -/
theorem sign_eval_map {R S : Type*} [Semiring R] [LinearOrder R]
    [Semiring S] [Preorder S] [DecidableLT S] (p : R[X]) (f : R →+* S)
    (hf : StrictMono f) (x : R) :
    SignType.sign ((p.map f).eval (f x)) = SignType.sign (p.eval x) := by
  rw [eval_map_apply]
  exact hf.sign_comp _

/-- **Rescaling preserves signs.** Evaluating `C (a ^ q.natDegree) * q.scaleRoots a` at `f a * z`
multiplies the value of `q` at `z` by the positive square `(f a * f a) ^ q.natDegree`. -/
theorem sign_eval₂_C_pow_mul_scaleRoots {R S : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [CommSemiring S] (f : S →+* R) (q : S[X]) {a : S} (ha : f a ≠ 0)
    (z : R) :
    SignType.sign ((C (a ^ q.natDegree) * q.scaleRoots a).eval₂ f (f a * z)) =
      SignType.sign (q.eval₂ f z) := by
  simp [eval₂_pow, scaleRoots_eval₂_mul, ← mul_assoc, ← mul_pow, sign_mul, mul_self_pos, ha]

end Polynomial
