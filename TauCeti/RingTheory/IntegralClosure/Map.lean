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
closures of `R` in `A` and in `B`. This file records that this restriction is functorial and
preserves injectivity, and that primes of the integral closure of `R` in `A` are contractions of
primes of the integral closure of `R` in `B` when `f` is injective: the integral closure in `B` is
integral over `R`, so lying over applies along the restricted map.

## Main results

* `AlgHom.mapIntegralClosure_comp`: the restriction to integral closures is functorial.
* `AlgHom.mapIntegralClosure_injective`: it preserves injectivity.
* `Ideal.exists_isPrime_comap_mapIntegralClosure_eq`: a prime of the integral closure in `A` is
  the contraction of a prime of the integral closure in `B` along an injective `f`.
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
