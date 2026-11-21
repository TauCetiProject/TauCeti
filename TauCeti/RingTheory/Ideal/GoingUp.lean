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

Incomparability over the zero ideal: a prime of a `P`-algebra `B` lying over the zero ideal of `P`
is minimal as soon as `B ⧸ p` is algebraic over `P` for the minimal primes `p` below it.

## Main results

* `Ideal.exists_comap_eq_of_isIntegral`: a prime of `S` containing the kernel of `g` is the
  contraction along `g` of a prime of `T`.
* `Ideal.primesOver_eq_singleton_under_of_primesOver_eq_singleton`: a prime alone above `p` in
  `T` contracts to a prime alone above `p` in any intermediate ring over which `T` is integral.
* `Ideal.comap_eq_maximalIdeal_of_isIntegral`: along an integral algebra over a local ring, every
  maximal ideal contracts to the maximal ideal.
* `TauCeti.radical_map_maximalIdeal_of_isIntegral`: along an integral algebra of local
  rings, the radical of the extended maximal ideal is the maximal ideal of the target.
* `Ideal.map_le_jacobson_of_isIntegral`: along an integral algebra, the extension of an ideal in
  the Jacobson radical of an ideal `K` lies in the Jacobson radical of any ideal `J` above `K`.
* `Ideal.mem_minimalPrimes_of_under_eq_bot`: a prime over the zero ideal is minimal when the
  quotients by the minimal primes below it are algebraic.

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

/-- **Primes over zero along algebraic components are minimal.** Let `B` be a `P`-algebra and `q`
a prime of `B` lying over the zero ideal of `P`. If `B ⧸ p` is algebraic over `P` for every minimal
prime `p ≤ q`, then `q` is a minimal prime: a prime strictly above such a `p` contains a nonzero
element of `B ⧸ p` algebraic over `P`, and hence a nonzero element of `P`. -/
theorem mem_minimalPrimes_of_under_eq_bot {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]
    (q : Ideal B) [q.IsPrime] (hq : q.under P = ⊥)
    (h : ∀ p ∈ minimalPrimes B, p ≤ q → Algebra.IsAlgebraic P (B ⧸ p)) :
    q ∈ minimalPrimes B := by
  obtain ⟨p, hp, hpq⟩ := exists_minimalPrimes_le (bot_le : ⊥ ≤ q)
  have := hp.1.1
  suffices q ≤ p from (le_antisymm this hpq) ▸ hp
  intro d hd
  by_contra hdp
  -- The image of `d` in the domain `B ⧸ p` is nonzero and algebraic over `P`.
  have hd0 : Quotient.mk p d ≠ 0 := by rwa [ne_eq, Quotient.eq_zero_iff_mem]
  have := h p hp hpq
  have halg : IsAlgebraic P (Quotient.mk p d) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (under_ne_bot_of_algebraic_mem hd0 (mem_map_of_mem _ hd) halg)
  rw [mem_under, IsScalarTower.algebraMap_apply P B (B ⧸ p), Quotient.algebraMap_eq,
    mem_quotient_iff_mem hpq, ← mem_under, hq] at ha
  exact ha0 (mem_bot.mp ha)

end Ideal

/-- Along an integral algebra `R → S` of local rings, the radical of the extended maximal ideal
`𝔪_R S` is `𝔪_S`: the closed point of `Spec S` is the unique prime over `𝔪_R`. -/
theorem TauCeti.radical_map_maximalIdeal_of_isIntegral {R S : Type*} [CommRing R]
    [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] [Algebra.IsIntegral R S] :
    ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).radical =
      IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  · exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr <|
      Ideal.map_le_iff_le_comap.mpr
        (Ideal.comap_eq_maximalIdeal_of_isIntegral (IsLocalRing.maximalIdeal S)).ge
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hIJ, hJp⟩ ↦ ?_
    have hcomap : IsLocalRing.maximalIdeal R = J.under R :=
      (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (hJp.comap _).ne_top
        (Ideal.map_le_iff_le_comap.mp hIJ)
    exact (IsLocalRing.eq_maximalIdeal <|
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) J
        (hcomap ▸ IsLocalRing.maximalIdeal.isMaximal R)).ge
