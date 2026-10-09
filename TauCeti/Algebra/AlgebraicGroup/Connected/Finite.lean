/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite connected reduced affine groups are trivial

Let `H` be a finite-dimensional reduced commutative Hopf algebra over a field whose prime
spectrum is connected. Then its augmentation ideal is zero, so the affine group it represents is
trivial.

A finite-dimensional algebra over a field is Artinian, so its prime spectrum is discrete. A
connected discrete space has at most one point, so every prime ideal equals the augmentation
ideal, which is prime as the kernel of the counit to the base field. Hence augmentation elements
are nilpotent, and reducedness makes them zero.

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
  let _ : Subsingleton (PrimeSpectrum H) :=
    Set.subsingleton_univ_iff.mp isPreconnected_univ.subsingleton
  let p : PrimeSpectrum H :=
    ⟨RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom, RingHom.ker_isPrime _⟩
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro q hq
  have hpq : p = ⟨q, hq⟩ := Subsingleton.elim _ _
  have hxp : x ∈ p.asIdeal := by
    rw [RingHom.mem_ker]
    exact (mem_augmentation k H).mp hx
  rw [hpq] at hxp
  exact hxp

end TauCeti.HopfIdeal
