module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure
public import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Polynomial moments for the Chebyshev `T` measure

This file records the bare-polynomial `L²` consequences of compact support for Mathlib's
Chebyshev orthogonality measure `Polynomial.Chebyshev.measureT`.

The normalized Chebyshev modes and their orthonormality live in
`TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure`.  The lemmas here are the
un-normalized consumer forms needed on the way to the roadmap's Chebyshev Hilbert-basis target:
every real polynomial evaluation is square integrable, and this statement is available after
casting real-valued functions to any `[RCLike 𝕜]` scalar field.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- A real polynomial evaluation lies in `L²` with respect to the Chebyshev `T` measure. -/
lemma memLp_two_eval_measureT (q : Polynomial ℝ) :
    MemLp (fun x : ℝ => q.eval x) 2 Polynomial.Chebyshev.measureT :=
  memLp_two_eval_of_forall_integrable_pow (fun _ => integrable_measureT (by fun_prop)) q

/-- A real polynomial evaluation, cast to any `RCLike` scalar field, lies in `L²` with respect
to the Chebyshev `T` measure. -/
lemma memLp_two_algebraMap_eval_measureT {𝕜 : Type*} [RCLike 𝕜] (q : Polynomial ℝ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x)) 2
      Polynomial.Chebyshev.measureT := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_two_eval_measureT q).ofReal (K := 𝕜)

end TauCeti
