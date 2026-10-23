/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Adic completeness of finite modules

Over an `I`-adically complete Noetherian ring, every finitely generated module is `I`-adically
complete. Precompleteness passes along surjective linear maps, because the adic completion functor
preserves surjections; a finite module is a quotient of a finite free module, which is complete by
`IsAdicComplete.pi`. Hausdorffness is the Krull intersection theorem
(`IsHausdorff.of_le_jacobson`), available because `I` lies in the Jacobson radical of a complete
ring.

This is what makes a finite algebra over a complete Noetherian ring Henselian along the extended
ideal, the input for lifting idempotents in such an algebra.

## Main results

* `IsPrecomplete.of_surjective`: adic precompleteness passes along a surjective linear map.
* `IsPrecomplete.of_finite`: a finite module over an adically precomplete ring is precomplete.
* `IsAdicComplete.of_finite`: a finite module over an adically complete Noetherian ring is
  complete.

## References

* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

public section

open AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Adic precompleteness passes along a surjective linear map: the adic completion functor
preserves surjections. -/
theorem IsPrecomplete.of_surjective [IsPrecomplete I M] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsPrecomplete I N := by
  refine AdicCompletion.of_surjective_iff.mp fun y ↦ ?_
  obtain ⟨z, rfl⟩ := map_surjective I hf y
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M z
  exact ⟨f x, (map_of I f x).symm⟩

variable (M)

/-- A finite module over an `I`-adically precomplete ring is `I`-adically precomplete. -/
theorem IsPrecomplete.of_finite [IsPrecomplete I R] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact IsPrecomplete.of_surjective I f hf

/-- A finite module over an `I`-adically complete Noetherian ring is `I`-adically complete. -/
theorem IsAdicComplete.of_finite [IsNoetherianRing R] [IsAdicComplete I R] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := IsPrecomplete.of_finite I M
