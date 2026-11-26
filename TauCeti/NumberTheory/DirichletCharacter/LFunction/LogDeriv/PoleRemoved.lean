/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.LogDeriv
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.Analysis.Calculus.LogDeriv

/-!
# The regular part of the principal logarithmic derivative

Clearing the principal character's pole at `1` subtracts the polar term of its logarithmic
derivative. The resulting value at `1` supplies the constant in the first Riesz remainder.
-/

public section

open Filter TauCeti
open scoped Topology

namespace DirichletCharacter

/-- At a nonzero regular value of the principal L-function, clearing its pole adds
`1 / (s - 1)` to its logarithmic derivative. -/
theorem logDeriv_LFunctionTrivChar₁_apply_of_ne_one {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1)
    (hL : LFunctionTrivChar q s ≠ 0) :
    logDeriv (LFunctionTrivChar₁ q) s = logDeriv (LFunctionTrivChar q) s + (s - 1)⁻¹ := by
  rw [logDeriv_apply, logDeriv_apply, deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs,
    LFunctionTrivChar₁_apply_of_ne_one q hs]
  field_simp [sub_ne_zero.mpr hs, hL]

/-- The finite part of the principal logarithmic derivative is the logarithmic derivative
of its pole-cleared L-function at `1`. -/
@[simp] theorem logDerivFinitePart_LFunctionTrivChar_one (q : ℕ) [NeZero q] :
    logDerivFinitePart (LFunctionTrivChar q) 1 = logDeriv (LFunctionTrivChar₁ q) 1 := by
  have hE := (differentiable_LFunctionTrivChar₁ q).analyticAt (1 : ℂ)
  have hne := LFunctionTrivChar₁_apply_one_ne_zero q
  refine (hE.logDeriv hne).logDerivFinitePart_eq ?_
  filter_upwards [(hE.continuousAt.eventually_ne hne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin (s := {1}ᶜ)] with z hz h₁
  have h₁' : z ≠ (1 : ℂ) := h₁
  have hL : LFunctionTrivChar q z ≠ 0 := by
    rw [LFunctionTrivChar₁_apply_of_ne_one q h₁', mul_ne_zero_iff] at hz
    exact hz.2
  rw [logDeriv_LFunctionTrivChar₁_apply_of_ne_one h₁' hL]
  simp [meromorphicOrderAt_LFunctionTrivChar_one, div_eq_mul_inv]

end DirichletCharacter
