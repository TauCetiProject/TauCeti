/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import TauCeti.RingTheory.Ideal.GoingUp

/-!
# Functoriality of integral closures

An `R`-algebra map `f : A → B` restricts to a map `f.mapIntegralClosure` between the integral
closures of `R` in `A` and in `B`, and more generally to `TauCeti.IsIntegralClosure.map S T f`
between any abstract integral closures `S` of `R` in `A` and `T` of `R` in `B`. This file records
that these restrictions are functorial and preserve injectivity, and that primes of an integral
closure of `R` in `A` are contractions of primes of an integral closure of `R` in `B` when `f` is
injective: the integral closure in `B` is integral over `R`, so lying over applies along the
restricted map.

## Main definitions and results

* `AlgHom.mapIntegralClosure_comp`: the restriction to `integralClosure` is functorial.
* `AlgHom.mapIntegralClosure_injective`: it preserves injectivity.
* `TauCeti.IsIntegralClosure.map`: the restriction `S →ₐ[R] T` of `f : A →ₐ[R] B` between abstract
  integral closures `S` of `R` in `A` and `T` of `R` in `B`, with
  `TauCeti.IsIntegralClosure.algebraMap_map`, `TauCeti.IsIntegralClosure.map_id`,
  `TauCeti.IsIntegralClosure.map_comp`, and `TauCeti.IsIntegralClosure.map_injective`.
* `Ideal.exists_isPrime_comap_mapIntegralClosure_eq`,
  `Ideal.exists_isPrime_comap_isIntegralClosure_map_eq`: a prime of an integral closure of `R` in
  `A` is the contraction of a prime of an integral closure of `R` in `B` along the restriction of
  an injective `f : A →ₐ[R] B`.
-/

public section

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
  [Algebra R B] [Algebra R C]

namespace AlgHom

/-- Restricting a composite algebra homomorphism to integral closures gives the composite of the
restricted algebra homomorphisms. -/
@[simp]
theorem mapIntegralClosure_comp (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (f.comp g).mapIntegralClosure = f.mapIntegralClosure.comp g.mapIntegralClosure :=
  AlgHom.ext fun _ => Subtype.ext rfl

/-- Restricting an injective algebra homomorphism to integral closures preserves injectivity. -/
theorem mapIntegralClosure_injective {f : A →ₐ[R] B} (hf : Function.Injective f) :
    Function.Injective f.mapIntegralClosure :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

end AlgHom

/-- Lying over for integral closures: along an injective `R`-algebra map `f : A → B`, every prime
of the integral closure of `R` in `A` is the contraction of a prime of the integral closure of `R`
in `B`. -/
theorem Ideal.exists_isPrime_comap_mapIntegralClosure_eq (P : Ideal (integralClosure R A))
    [P.IsPrime] {f : A →ₐ[R] B} (hf : Function.Injective f) :
    ∃ Q : Ideal (integralClosure R B), Q.IsPrime ∧ Q.comap f.mapIntegralClosure = P := by
  refine P.exists_comap_eq_of_isIntegral
    (f.mapIntegralClosure : integralClosure R A →+* integralClosure R B) ?_ ?_
  · apply RingHom.IsIntegral.tower_top (algebraMap R (integralClosure R A))
    rw [AlgHom.comp_algebraMap]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  · rw [(RingHom.injective_iff_ker_eq_bot
      (f.mapIntegralClosure : integralClosure R A →+* integralClosure R B)).mp
        (AlgHom.mapIntegralClosure_injective hf)]
    exact bot_le

namespace TauCeti

/-- An `R`-algebra homomorphism `f : A →ₐ[R] B` restricts to an `R`-algebra homomorphism
`S →ₐ[R] T` between any integral closures `S` of `R` in `A` and `T` of `R` in `B`. -/
noncomputable def IsIntegralClosure.map (S T : Type*) [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [IsIntegralClosure S R A] [CommRing T] [Algebra R T] [Algebra T B]
    [IsScalarTower R T B] [IsIntegralClosure T R B] (f : A →ₐ[R] B) : S →ₐ[R] T :=
  (IsIntegralClosure.equiv R (integralClosure R B) B T).toAlgHom.comp
    (f.mapIntegralClosure.comp (IsIntegralClosure.equiv R S A (integralClosure R A)).toAlgHom)

/-- Applying `TauCeti.IsIntegralClosure.map S T f` commutes with the ambient algebra maps into `A`
and `B`. -/
@[simp]
theorem IsIntegralClosure.algebraMap_map (S T : Type*) [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [IsIntegralClosure S R A] [CommRing T] [Algebra R T] [Algebra T B]
    [IsScalarTower R T B] [IsIntegralClosure T R B] (f : A →ₐ[R] B) (x : S) :
    algebraMap T B (IsIntegralClosure.map S T f x) = f (algebraMap S A x) := by
  simp only [IsIntegralClosure.map, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    IsIntegralClosure.algebraMap_equiv]
  exact congrArg f (IsIntegralClosure.algebraMap_equiv R S A (integralClosure R A) x)

/-- Restricting the identity `R`-algebra homomorphism on `A` to an integral closure `S` gives the
identity on `S`. -/
@[simp]
theorem IsIntegralClosure.map_id (S : Type*) [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [IsIntegralClosure S R A] :
    IsIntegralClosure.map S S (AlgHom.id R A) = AlgHom.id R S := by
  ext x
  exact IsIntegralClosure.algebraMap_injective S R A (by simp)

/-- Restricting a composite `R`-algebra homomorphism between abstract integral closures gives the
composite of the restricted homomorphisms. -/
theorem IsIntegralClosure.map_comp (S T U : Type*) [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [IsIntegralClosure S R A] [CommRing T] [Algebra R T] [Algebra T B]
    [IsScalarTower R T B] [IsIntegralClosure T R B] [CommRing U] [Algebra R U] [Algebra U C]
    [IsScalarTower R U C] [IsIntegralClosure U R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    IsIntegralClosure.map S U (f.comp g) =
      (IsIntegralClosure.map T U f).comp (IsIntegralClosure.map S T g) := by
  ext x
  exact IsIntegralClosure.algebraMap_injective U R C (by simp)

/-- Restricting an injective `R`-algebra homomorphism between abstract integral closures preserves
injectivity. -/
theorem IsIntegralClosure.map_injective (S T : Type*) [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [IsIntegralClosure S R A] [CommRing T] [Algebra R T] [Algebra T B]
    [IsScalarTower R T B] [IsIntegralClosure T R B] {f : A →ₐ[R] B}
    (hf : Function.Injective f) : Function.Injective (IsIntegralClosure.map S T f) := fun _ _ h =>
  IsIntegralClosure.algebraMap_injective S R A <| hf <| by
    simpa only [IsIntegralClosure.algebraMap_map] using congrArg (algebraMap T B) h

end TauCeti

/-- Lying over between abstract integral closures: along an injective `R`-algebra map `f : A → B`,
every prime of an integral closure `S` of `R` in `A` is the contraction along
`TauCeti.IsIntegralClosure.map S T f` of a prime of an integral closure `T` of `R` in `B`. -/
theorem Ideal.exists_isPrime_comap_isIntegralClosure_map_eq
    {S : Type*} [CommRing S] [Algebra R S] [Algebra S A] [IsScalarTower R S A]
    [IsIntegralClosure S R A] (P : Ideal S) [P.IsPrime] (T : Type*) [CommRing T] [Algebra R T]
    [Algebra T B] [IsScalarTower R T B] [IsIntegralClosure T R B]
    {f : A →ₐ[R] B} (hf : Function.Injective f) :
    ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap (TauCeti.IsIntegralClosure.map S T f) = P := by
  let eS := IsIntegralClosure.equiv R S A (integralClosure R A)
  let eT := IsIntegralClosure.equiv R (integralClosure R B) B T
  obtain ⟨Q, _, hQP⟩ :=
    (P.comap eS.symm.toRingHom).exists_isPrime_comap_mapIntegralClosure_eq hf
  refine ⟨Q.comap eT.symm.toRingHom, Ideal.comap_isPrime eT.symm.toRingHom Q, ?_⟩
  ext x
  simpa [TauCeti.IsIntegralClosure.map, eS, eT, Ideal.mem_comap] using
    SetLike.ext_iff.mp hQP (eS x)
