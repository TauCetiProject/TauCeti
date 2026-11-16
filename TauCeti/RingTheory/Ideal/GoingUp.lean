/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Lying over along an integral ring homomorphism

An integral ring homomorphism `g : S →+* T` lifts each prime ideal of `S` containing its kernel
to a prime ideal of `T`. This is Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral` stated
directly for `g`, so callers need not install an algebra structure.

Along an integral algebra, maximal ideals contract to maximal ideals, so the extension of an
ideal contained in the Jacobson radical of the contraction of an ideal `J` is contained in the
Jacobson radical of `J`.

## Main results

* `Ideal.exists_comap_eq_of_isIntegral`: a prime of `S` containing the kernel of `g` is the
  contraction along `g` of a prime of `T`.
* `Ideal.primesOver_eq_singleton_under_of_primesOver_eq_singleton`: a prime alone above `p` in
  `T` contracts to a prime alone above `p` in any intermediate ring over which `T` is integral.
* `Ideal.comap_eq_maximalIdeal_of_isIntegral`: along an integral algebra over a local ring, every
  maximal ideal contracts to the maximal ideal.
* `Ideal.map_le_jacobson_of_isIntegral`: along an integral algebra, the extension of an ideal in
  the Jacobson radical of an ideal `K` lies in the Jacobson radical of any ideal `J` above `K`.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/FiniteAlgebraIdempotents.lean`: `map_le_jacobson_of_isIntegral`
  generalises the algebra form of its `Pcf.Stacks.map_le_jacobson_bot_of_le_jacobson_of_isIntegral`
  from the zero ideals to arbitrary ideals.
-/

public section

namespace Ideal

variable {S T : Type*} [CommRing S] [CommRing T]

/-- Lying over along an integral ring homomorphism `g : S →+* T`: a prime `P` of `S`
containing the kernel of `g` is the contraction along `g` of a prime of `T`. -/
theorem exists_comap_eq_of_isIntegral (P : Ideal S) [P.IsPrime]
    (g : S →+* T) (hg : g.IsIntegral) (hP : RingHom.ker g ≤ P) :
    ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap g = P := by
  algebraize [g]
  obtain ⟨Q, -, hQ, hQP⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal T)
    (by rwa [under_def, RingHom.algebraMap_toAlgebra, ← RingHom.ker_eq_comap_bot])
  exact ⟨Q, hQ, hQP⟩

/-- If `P` is the only prime of `T` above an ideal `p` of `R`, then `P.under S` is the only prime
of `S` above `p`, for any intermediate ring `S` over which `T` is integral and faithful. -/
theorem primesOver_eq_singleton_under_of_primesOver_eq_singleton {R : Type*} [CommRing R]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra.IsIntegral S T]
    [FaithfulSMul S T] {p : Ideal R} {P : Ideal T} (h : p.primesOver T = {P}) :
    p.primesOver S = {P.under S} := by
  obtain ⟨_, _⟩ : P ∈ p.primesOver T := h ▸ Set.mem_singleton P
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨⟨Q', _, _⟩⟩ := nonempty_primesOver (S := T) Q
  have : Q'.LiesOver p := .trans Q' Q p
  have hQ' : Q' = P := Set.mem_singleton_iff.mp <| h ▸ ⟨inferInstance, inferInstance⟩
  rw [LiesOver.over (P := Q') (p := Q), hQ']

/-- Along an integral algebra `S → T`, let `K` be an ideal of `S` contained in the contraction of
an ideal `J` of `T`. Then the extension to `T` of an ideal of `S` contained in the Jacobson radical
of `K` is contained in the Jacobson radical of `J`. Taking `K = J.under S` gives the sharpest
form; taking `K` and `J` to be `⊥` gives the statement for the Jacobson radicals of the rings. -/
theorem map_le_jacobson_of_isIntegral [Algebra S T] [Algebra.IsIntegral S T] {I K : Ideal S}
    {J : Ideal T} (hKJ : K ≤ J.under S) (hI : I ≤ K.jacobson) :
    I.map (algebraMap S T) ≤ J.jacobson :=
  le_sInf fun M ⟨hJM, _⟩ ↦ map_le_iff_le_comap.mpr <| hI.trans <|
    sInf_le ⟨hKJ.trans (comap_mono hJM), IsMaximal.under S M⟩

/-- Along an integral algebra over a local ring, every maximal ideal contracts to the maximal
ideal. -/
theorem comap_eq_maximalIdeal_of_isIntegral {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal S) [P.IsMaximal] :
    P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (IsMaximal.under R P)

end Ideal
