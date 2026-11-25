/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter

/-!
# The trace-form Casimir of `gl n` on characters

Let `f : gl n K → K` be a Lie algebra homomorphism over a commutative ring `K`, and
`liftCharacter K (Matrix n n K) f` the infinitesimal character extending it, through which
`U(gl n)` acts on any module where `X` acts by the scalar `f X`. This file evaluates it on the
trace-form Casimir `Ω = ∑ i, ∑ j, Eᵢⱼ Eⱼᵢ`: the value is `∑ i, ∑ j, f (Eᵢⱼ) * f (Eⱼᵢ)`. In
particular `Ω` acts by `0` on the trivial module (`f = 0`), and by `n` on the rank-one module on
which `X` acts by `tr X` (`f` the trace character `TauCeti.traceLieCharacter`). Informally, the
latter is the differential of the determinant representation; for `gl₂` the value is `2`.

## Main results

* `TauCeti.liftCharacter_glCasimir`: the value of an infinitesimal character extending `f` on the
  Casimir.
* `TauCeti.liftCharacter_zero_glCasimir`, `TauCeti.liftCharacter_traceLieCharacter_glCasimir`: the
  Casimir acts by `0` on the trivial module and by `n` on the module where `X` acts by `tr X`.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [CommRing K] (n : Type*) [Fintype n] [DecidableEq n]

/-- **The trace-form Casimir on a character.** The infinitesimal character extending a Lie algebra
homomorphism `f : gl n → K` takes the value `∑ i, ∑ j, f (Eᵢⱼ) * f (Eⱼᵢ)` on the Casimir. -/
theorem liftCharacter_glCasimir (f : LieAlgebra.LieCharacter K (Matrix n n K)) :
    liftCharacter K (Matrix n n K) f ⟨glCasimir K n, glCasimir_mem_center K n⟩ =
      ∑ i, ∑ j, f (Matrix.single i j 1) * f (Matrix.single j i 1) := by
  rw [liftCharacter_apply]
  simp [glCasimir_def, map_sum, map_mul]

/-- **The Casimir acts by `0` on the trivial module.** -/
theorem liftCharacter_zero_glCasimir :
    liftCharacter K (Matrix n n K) 0 ⟨glCasimir K n, glCasimir_mem_center K n⟩ = 0 := by
  simp [liftCharacter_glCasimir]

/-- **The Casimir acts by `n` on the module where `X` acts by `tr X`**: on the infinitesimal
character extending the trace, `∑ i, ∑ j, tr(Eᵢⱼ) tr(Eⱼᵢ) = n`. For `gl₂` this is the value `2`. -/
theorem liftCharacter_traceLieCharacter_glCasimir :
    liftCharacter K (Matrix n n K) (traceLieCharacter K n)
        ⟨glCasimir K n, glCasimir_mem_center K n⟩ = Fintype.card n := by
  have h (i j : n) : (Matrix.single i j (1 : K)).trace = if i = j then 1 else 0 := by
    split_ifs with hij
    · rw [hij, Matrix.trace_single_eq_same]
    · exact Matrix.trace_single_eq_of_ne _ _ _ hij
  rw [liftCharacter_glCasimir]
  simp [h]

end TauCeti
