/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite connected reduced affine groups are trivial

Let `H` be a finite-dimensional reduced commutative Hopf algebra over a field whose prime
spectrum is connected. Then its augmentation ideal is zero, so the affine group it represents is
trivial.

A finite-dimensional algebra over a field is Artinian, so its prime spectrum is discrete. A
connected discrete space has at most one point, so the reduced ring `H` is a field
(`PrimeSpectrum.subsingleton_iff_isField_of_isReduced`). The counit is then an injective ring
homomorphism out of a field, so its kernel, the augmentation ideal, is zero.

Neither smoothness nor an algebraically closed base field is needed. Reducedness is essential:
the Frobenius kernel `αₚ` is finite and connected but not trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.d and 2.a.
-/

public section

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **A finite connected reduced affine group is trivial**: a finite-dimensional reduced
commutative Hopf algebra over a field with connected prime spectrum has zero augmentation
ideal. -/
theorem augmentation_eq_bot_of_moduleFinite [Module.Finite k H] [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)] : augmentation k H = ⊥ := by
  let _ : IsArtinianRing H := IsArtinianRing.of_finite k H
  let _ : Nontrivial H := Bialgebra.nontrivial k
  have hH : IsField H := PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp
    subsingleton_of_preconnected_totallyDisconnected
  have hinj : Function.Injective (Bialgebra.counitAlgHom k H) :=
    let _ := hH.toField
    (Bialgebra.counitAlgHom k H).toRingHom.injective
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  refine hinj ?_
  rw [map_zero]
  exact (mem_augmentation k H).mp hx

end TauCeti.HopfIdeal
