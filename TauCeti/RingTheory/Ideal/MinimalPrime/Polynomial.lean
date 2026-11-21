/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Algebraic.Basic
import TauCeti.Algebra.Polynomial.AlgebraMap

/-!
# Minimal primes of algebras over a polynomial ring

Let `B` be a reduced `R[X]`-algebra. If the image of `X` in the residue field of every minimal
prime of `B` is transcendental over `R`, then `R[X]` embeds into every component of `Spec B`, so
`B` is torsion-free over `R[X]` by
`TauCeti.isTorsionFree_of_injective_algebraMap_quotient_minimalPrimes`.

## Main results

* `TauCeti.isTorsionFree_polynomial_of_forall_transcendental`: a reduced `R[X]`-algebra on whose
  components `X` is transcendental is torsion-free over `R[X]`.
-/

public section

open Polynomial

namespace TauCeti

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra R[X] B]
  [IsScalarTower R R[X] B]

/-- **A coordinate transcendental on every component makes a reduced algebra torsion-free.** Let
`B` be a reduced `R[X]`-algebra. If the image of `X` in the residue field of every minimal prime of
`B` is transcendental over `R`, then `B` is torsion-free over `R[X]`. -/
theorem isTorsionFree_polynomial_of_forall_transcendental [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B →
      Transcendental R (algebraMap R[X] p.ResidueField X)) :
    Module.IsTorsionFree R[X] B := by
  refine isTorsionFree_of_injective_algebraMap_quotient_minimalPrimes fun p hp ↦ ?_
  have := hp.1.1
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ transcendental_iff.mp (h p hp) f ?_
  rw [← algebraMap_eq_aeval, IsScalarTower.algebraMap_apply R[X] (B ⧸ p), hf, map_zero]

end TauCeti
