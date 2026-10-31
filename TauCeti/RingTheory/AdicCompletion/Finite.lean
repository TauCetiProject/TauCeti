/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Adic completion of finite modules

Over an `I`-adically complete Noetherian ring, every finitely generated module is `I`-adically
complete. Precompleteness passes along surjective linear maps, because the adic completion functor
preserves surjections; a finite module is a quotient of a finite free module, which is complete by
`IsAdicComplete.pi`. Hausdorffness is the Krull intersection theorem
(`IsHausdorff.of_le_jacobson`), available because `I` lies in the Jacobson radical of a complete
ring.

This is what makes a finite algebra over a complete Noetherian ring Henselian along the extended
ideal, the input for lifting idempotents in such an algebra.

Over any commutative ring, the completion of a finite module is generated over the completed ring
by the image of the module, so linear maps over the completed ring out of it are determined by
their restrictions to the module.

## Main results

* `IsPrecomplete.of_surjective`: adic precompleteness passes along a surjective linear map.
* `IsPrecomplete.of_finite`: a finite module over an adically precomplete ring is precomplete.
* `IsAdicComplete.of_finite`: a finite module over an adically complete Noetherian ring is
  complete.
* `AdicCompletion.linearMap_ext_of_finite`: a linear map over the completion out of the completion
  of a finite module is determined on the image of the module, since
  `AdicCompletion.ofTensorProduct` is surjective.

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

variable {M} in
/-- Linear maps over the completion out of the completion of a finite module are determined by
their values on the image of the module. -/
theorem AdicCompletion.linearMap_ext_of_finite [Module.Finite R M] {P : Type*} [AddCommGroup P]
    [Module (AdicCompletion I R) P] {g₁ g₂ : AdicCompletion I M →ₗ[AdicCompletion I R] P}
    (h : ∀ x, g₁ (of I M x) = g₂ (of I M x)) : g₁ = g₂ := by
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp [ofTensorProduct_tmul, h]
  | add s t hs ht => simp [hs, ht]
