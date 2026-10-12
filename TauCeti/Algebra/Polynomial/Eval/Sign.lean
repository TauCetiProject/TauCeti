/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Sign.Defs

/-! # Polynomial evaluation signs under ordered embeddings

Mapping coefficients and the evaluation point through a strictly monotone ring homomorphism
preserves the sign of the value. This applies to embeddings into ordered real closures.
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

end Polynomial
