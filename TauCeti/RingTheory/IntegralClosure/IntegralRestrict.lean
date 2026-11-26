/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import TauCeti.RingTheory.Ideal.Operations

/-!
# The integral trace on extended ideals

Mathlib's `Algebra.intTrace A B` is the trace of a finite extension of integrally closed domains
`B / A`, restricted from the fraction fields to the rings themselves. This file records that it
is compatible with the ideals of the base: the trace carries the extended ideal `p · B` of an
ideal `p` of `A` back into `p`. This is the case of the trace of the general fact
`LinearMap.apply_mem_of_mem_smul_top`, that an `A`-linear functional carries `p • B` into `p`,
since `p • B` is the extended ideal `p · B`.

This is the elementary half of the computation of the trace of an ideal of `B`. The other half,
which reads the exact image off the different ideal, is in
`TauCeti.RingTheory.DedekindDomain.Different.Trace`.

This file also records the equivariance of `Algebra.intNorm` under commuting ring equivalences
(`Algebra.map_intNorm_of_ringEquiv`), deduced from `Algebra.norm_eq_of_equiv_equiv` on the
fraction rings.

## Main results

* `Algebra.intTrace_mem_of_mem_map`: `Tr(p · B) ⊆ p`.
* `IsFractionRing.algebraMap_comp_ringEquivOfRingEquiv`: commuting ring equivalences lift to
  equivalences of `FractionRing`s that commute with `algebraMap`.
* `Algebra.map_intNorm_of_ringEquiv`: equivariance of `Algebra.intNorm` under commuting ring
  equivalences.
-/

public section

open scoped nonZeroDivisors

namespace Algebra

section Trace

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [Module.IsTorsionFree A B]

/-- The integral trace carries the extended ideal `p · B` of an ideal `p` of the base ring back
into `p`: it is an `A`-linear functional on `B`, and `p · B = p • B`. -/
theorem intTrace_mem_of_mem_map {p : Ideal A} {x : B} (hx : x ∈ p.map (algebraMap A B)) :
    intTrace A B x ∈ p :=
  (intTrace A B).apply_mem_of_mem_smul_top (by rwa [Ideal.smul_top_eq_map])

end Trace

section IntNorm

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

private theorem fractionRing_algebraMap_apply {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B] (a : A) :
    algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (algebraMap A B a) := by
  rw [← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B),
    IsScalarTower.algebraMap_apply A B (FractionRing B)]

/-- Commuting ring equivalences lift to equivalences of `FractionRing`s that commute with
`algebraMap`. -/
theorem _root_.IsFractionRing.algebraMap_comp_ringEquivOfRingEquiv {R S R' S' : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    [CommRing R'] [IsDomain R'] [CommRing S'] [IsDomain S'] [Algebra R' S']
    [Module.IsTorsionFree R' S'] (f : R ≃+* R') (g : S ≃+* S')
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R' S' (f r)) :
    (algebraMap (FractionRing R') (FractionRing S')).comp
        (IsFractionRing.ringEquivOfRingEquiv f :
          FractionRing R ≃+* FractionRing R').toRingHom =
      (IsFractionRing.ringEquivOfRingEquiv g :
          FractionRing S ≃+* FractionRing S').toRingHom.comp
        (algebraMap (FractionRing R) (FractionRing S)) := by
  refine IsLocalization.ringHom_ext R⁰ (RingHom.ext fun r ↦ ?_)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap f r, fractionRing_algebraMap_apply,
    fractionRing_algebraMap_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap g, hfg]

/-- **Equivariance of `Algebra.intNorm` under commuting ring equivalences.** If `f : R ≃+* R'` and
`g : S ≃+* S'` commute with `algebraMap`, then `f (intNorm R S x) = intNorm R' S' (g x)`. -/
theorem map_intNorm_of_ringEquiv {R S R' S' : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [CommRing S'] [IsDomain S'] [IsIntegrallyClosed S']
    [Algebra R' S'] [Algebra.IsIntegral R' S'] [Module.IsTorsionFree R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R' S' (f r)) (x : S) :
    f (intNorm R S x) = intNorm R' S' (g x) := by
  let ef : FractionRing R ≃+* FractionRing R' := IsFractionRing.ringEquivOfRingEquiv f
  let eg : FractionRing S ≃+* FractionRing S' := IsFractionRing.ringEquivOfRingEquiv g
  apply IsFractionRing.injective R' (FractionRing R')
  have hnorm : ef (norm (FractionRing R) (algebraMap S (FractionRing S) x)) =
      norm (FractionRing R') (eg (algebraMap S (FractionRing S) x)) := by
    simpa using congrArg ef (norm_eq_of_equiv_equiv ef eg
      (IsFractionRing.algebraMap_comp_ringEquivOfRingEquiv f g hfg)
      (algebraMap S (FractionRing S) x))
  calc algebraMap R' (FractionRing R') (f (intNorm R S x))
      = ef (algebraMap R (FractionRing R) (intNorm R S x)) :=
        (IsFractionRing.ringEquivOfRingEquiv_algebraMap f _).symm
    _ = ef (norm (FractionRing R) (algebraMap S (FractionRing S) x)) := by
        rw [algebraMap_intNorm_fractionRing]
    _ = norm (FractionRing R') (eg (algebraMap S (FractionRing S) x)) := hnorm
    _ = norm (FractionRing R') (algebraMap S' (FractionRing S') (g x)) := by
        rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap g x]
    _ = algebraMap R' (FractionRing R') (intNorm R' S' (g x)) := by
        rw [algebraMap_intNorm_fractionRing]

end IntNorm

end Algebra
