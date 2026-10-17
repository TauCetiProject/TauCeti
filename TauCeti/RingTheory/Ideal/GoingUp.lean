/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Lying over along an integral ring homomorphism

An integral ring homomorphism `g : S →+* T` lifts each prime ideal of `S` containing its kernel
to a prime ideal of `T`. This is Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral` stated
directly for `g`, so callers need not install an algebra structure.

## Main results

* `Ideal.exists_comap_eq_of_isIntegral`: a prime of `S` containing the kernel of `g` is the
  contraction along `g` of a prime of `T`.
* `Ideal.primesOver_eq_singleton_under_of_primesOver_eq_singleton`: a prime alone above `p` in
  `T` contracts to a prime alone above `p` in any intermediate ring over which `T` is integral.
-/

public section

namespace Ideal

variable {S T : Type*} [CommRing S] [CommRing T]

/-- Lying over along an integral ring homomorphism `g : S →+* T`: a prime `P` of `S`
containing the kernel of `g` is the contraction along `g` of a prime of `T`. -/
theorem exists_comap_eq_of_isIntegral (P : Ideal S) [P.IsPrime]
    (g : S →+* T) (hg : g.IsIntegral) (hP : RingHom.ker g ≤ P) :
    ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap g = P := by
  let _ : Algebra S T := g.toAlgebra
  have : Algebra.IsIntegral S T := ⟨hg⟩
  obtain ⟨Q, -, hQ, hQP⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal T)
    (by rwa [under_def, RingHom.algebraMap_toAlgebra, ← RingHom.ker_eq_comap_bot])
  exact ⟨Q, hQ, hQP⟩

/-- If `P` is the only prime of `T` above an ideal `p` of `R`, then `P.under S` is the only prime
of `S` above `p`, for any intermediate ring `S` over which `T` is integral and faithful. -/
theorem primesOver_eq_singleton_under_of_primesOver_eq_singleton {R : Type*} [CommRing R]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra.IsIntegral S T]
    [FaithfulSMul S T] {p : Ideal R} {P : Ideal T} (h : p.primesOver T = {P}) :
    p.primesOver S = {P.under S} := by
  obtain ⟨_, _⟩ : P ∈ p.primesOver T := h ▸ rfl
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨⟨Q', _, _⟩⟩ := nonempty_primesOver (S := T) Q
  have : Q'.LiesOver p := .trans Q' Q p
  have hmem : Q' ∈ p.primesOver T := ⟨inferInstance, inferInstance⟩
  rw [h] at hmem
  rw [LiesOver.over (P := Q') (p := Q), hmem]

end Ideal
