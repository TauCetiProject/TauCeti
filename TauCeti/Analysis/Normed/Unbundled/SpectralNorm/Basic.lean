/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Spectral norm of transcendental elements

For an element of a field extension that is transcendental over a normed field `K`, the minimal
polynomial is zero, so its spectral norm over `K` is zero.

## Main results

* `TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic`: the spectral norm over `K` of an element that
  is transcendental over `K` is zero.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [NormedField K]

/-- The spectral norm of an element that is transcendental over `K` is zero, since its minimal
polynomial is `0`. -/
theorem spectralNorm_eq_zero_of_not_isAlgebraic {L : Type*} [Field L] [Algebra K L] {y : L}
    (hy : ¬ IsAlgebraic K y) : spectralNorm K L y = 0 := by
  have h0 : spectralValueTerms (0 : K[X]) = 0 :=
    funext fun n ↦ spectralValueTerms_of_natDegree_le _ (by simp)
  rw [spectralNorm, minpoly.eq_zero fun h ↦ hy h.isAlgebraic, spectralValue, h0]
  exact ciSup_const

end TauCeti
