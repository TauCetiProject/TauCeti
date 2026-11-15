/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
public import TauCeti.RingTheory.Dagger.FiniteExtension
public import Mathlib.Algebra.DualNumber

/-!
# Faithful dagger completion with and without nilpotents

Faithful flatness includes the zero algebra. For a nonreduced dagger algebra, completion
retains its nilpotents rather than replacing the algebra by its reduced quotient.
The dual numbers supply an explicit nonzero square-zero element in the completion.
-/

public section

open TauCeti.Dagger
open scoped DualNumber

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- The field and the zero algebra are both included.
example : Function.Injective (toCompletion K K) := toCompletion_injective

example : (toCompletion K (K ⧸ (⊤ : Ideal K))).toRingHom.FaithfullyFlat :=
  faithfullyFlat_toCompletion

section DualNumbers

local instance : Module.Finite K K[ε] := inferInstanceAs (Module.Finite K (K × K))

local instance : IsDaggerAlgebra K K[ε] := IsDaggerAlgebra.of_finite (A := K)

-- In every characteristic, the nilpotent direction survives the actual completion map.
example : toCompletion K K[ε] (ε : K[ε]) ≠ 0 := by
  intro h
  have he := toCompletion_injective (K := K) (A := K[ε]) (h.trans (map_zero _).symm)
  have hs := congrArg TrivSqZeroExt.snd he
  simp at hs

example : (toCompletion K K[ε] (ε : K[ε])) ^ 2 = 0 := by
  rw [← map_pow]
  simp

end DualNumbers
