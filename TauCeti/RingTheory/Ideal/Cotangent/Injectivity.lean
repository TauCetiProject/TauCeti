/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.RingTheory.Ideal.Cotangent.Basic
import TauCeti.RingTheory.Noetherian.RingHom

/-!
# Injectivity of Noetherian endomorphisms via cotangent spaces

For a commutative ring `R`, an endomorphism preserving an ideal `I` that is surjective modulo `I`
and on the conormal module `I ⧸ I ^ 2` is surjective modulo every power `I ^ n`
(`RingHom.quotientMap_pow_surjective` in `TauCeti.RingTheory.Ideal.Cotangent.Basic`). When `R` is
Noetherian, each quotient `R ⧸ I ^ n` is Noetherian, so the induced endomorphism on every
infinitesimal quotient is bijective (`RingHom.injective_of_surjective` in
`TauCeti.RingTheory.Noetherian.RingHom`); if `I` is adically separated (`⨅ n, I ^ n = ⊥`), in
particular when `R` is a Noetherian domain and `I ≠ ⊤` by Krull's intersection theorem, the
endomorphism is injective.

## Main results

* `RingHom.injective_of_iInf_pow_eq_bot_of_surjective_quotient_of_surjective_cotangent`: when `R`
  is Noetherian and `⨅ n, I ^ n = ⊥`, an ideal-preserving endomorphism surjective on `R ⧸ I` and
  `I ⧸ I ^ 2` is injective.
* `RingHom.injective_of_surjective_quotient_of_surjective_cotangent`: specialization to a proper
  ideal of a Noetherian domain via Krull's intersection theorem.
* `AlgHom.injective_of_iInf_pow_eq_bot_of_surjective_mapCotangent` and
  `AlgHom.injective_of_surjective_mapCotangent`: algebra-homomorphism forms phrased via
  `Ideal.mapCotangent`.

## References

* H. Matsumura, *Commutative Ring Theory*, §8 (Krull's intersection theorem).
-/

public section

namespace RingHom

variable {R : Type*} [CommRing R]

/-- An endomorphism of a commutative Noetherian ring preserving an adically separated ideal `I`
(`⨅ n, I ^ n = ⊥`) that is surjective on `R ⧸ I` and `I ⧸ I ^ 2` is injective. -/
theorem injective_of_iInf_pow_eq_bot_of_surjective_quotient_of_surjective_cotangent
    [IsNoetherianRing R] (I : Ideal R)
    (hsep : ⨅ n : ℕ, I ^ n = ⊥) (f : R →+* R) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap I f hfI))
    (hcot : ∀ y ∈ I, ∃ x ∈ I, y - f x ∈ I ^ 2) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  rw [← Ideal.mem_bot, ← hsep, Ideal.mem_iInf]
  intro n
  have hpow : I ^ n ≤ (I ^ n).comap f := Ideal.pow_le_comap_pow hfI n
  have hinj := (Ideal.quotientMap (I ^ n) f hpow).injective_of_surjective
    (f.quotientMap_pow_surjective hfI hquot hcot n)
  have hzero : Ideal.quotientMap (I ^ n) f hpow (Ideal.Quotient.mk (I ^ n) x) = 0 := by
    rw [Ideal.quotientMap_mk, hx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj (hzero.trans (map_zero _).symm))

/-- An endomorphism of a Noetherian integral domain preserving a proper ideal `I` that is
surjective on `R ⧸ I` and `I ⧸ I ^ 2` is injective. -/
theorem injective_of_surjective_quotient_of_surjective_cotangent [IsNoetherianRing R] [IsDomain R]
    (I : Ideal R) (hI : I ≠ ⊤) (f : R →+* R) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap I f hfI))
    (hcot : ∀ y ∈ I, ∃ x ∈ I, y - f x ∈ I ^ 2) :
    Function.Injective f :=
  f.injective_of_iInf_pow_eq_bot_of_surjective_quotient_of_surjective_cotangent I
    (Ideal.iInf_pow_eq_bot_of_isDomain I hI) hfI hquot hcot

end RingHom

namespace AlgHom

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- An algebra endomorphism of a commutative Noetherian algebra preserving an adically separated
ideal `I` (`⨅ n, I ^ n = ⊥`) that is surjective on `A ⧸ I` and on `I.Cotangent` is
injective. -/
theorem injective_of_iInf_pow_eq_bot_of_surjective_mapCotangent [IsNoetherianRing A]
    (I : Ideal A) (hsep : ⨅ n : ℕ, I ^ n = ⊥) (f : A →ₐ[k] A)
    (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.Quotient.mk I ∘ f))
    (hcot : Function.Surjective (Ideal.mapCotangent I I f hfI)) :
    Function.Injective f := by
  have hfI' : I ≤ I.comap (f : A →+* A) := fun x hx => hfI hx
  have hquot' : Function.Surjective (Ideal.quotientMap I (f : A →+* A) hfI') := by
    intro q
    obtain ⟨x, hx⟩ := hquot q
    exact ⟨Ideal.Quotient.mk I x, by
      simpa only [Ideal.quotientMap_mk, AlgHom.coe_toRingHom, Function.comp_apply] using hx⟩
  refine (f : A →+* A).injective_of_iInf_pow_eq_bot_of_surjective_quotient_of_surjective_cotangent
    I hsep hfI' hquot' fun y hy => ?_
  obtain ⟨c, hc⟩ := hcot (I.toCotangent ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective c
  rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq] at hc
  exact ⟨x.val, x.property, by simpa only [AlgHom.coe_toRingHom, neg_sub] using (I ^ 2).neg_mem hc⟩

/-- An algebra endomorphism of a Noetherian integral domain preserving a proper ideal `I` that is
surjective on `A ⧸ I` and on `I.Cotangent` is injective. -/
theorem injective_of_surjective_mapCotangent [IsNoetherianRing A] [IsDomain A]
    (I : Ideal A) (hI : I ≠ ⊤) (f : A →ₐ[k] A) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.Quotient.mk I ∘ f))
    (hcot : Function.Surjective (Ideal.mapCotangent I I f hfI)) :
    Function.Injective f :=
  f.injective_of_iInf_pow_eq_bot_of_surjective_mapCotangent I
    (Ideal.iInf_pow_eq_bot_of_isDomain I hI) hfI hquot hcot

end AlgHom
