/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Unibranch and geometrically unibranch local rings

Let `A` be a local ring, `A_red = A ⧸ nilradical A` its reduction and `A'` the integral closure of
`A_red` in its fraction field. Then `A` is *unibranch* if `A_red` is a domain and `A'` is local,
and *geometrically unibranch* if moreover the residue field of `A'` is purely inseparable over the
residue field of `A` (Stacks, Definition 15.108.1 (0BPZ)). Geometrically, the points of the
normalization lying over the closed point are the branches through it: a unibranch singularity has
one branch, and a geometrically unibranch one stays unibranch after any separable extension of the
residue field. These conditions govern the behaviour of étale fundamental groups and of finite
étale covers near a singular point.

## Main definitions

* `IsLocalRing.IsUnibranch A`: the reduction of `A` is a domain whose integral closure in its
  fraction field is local.
* `IsLocalRing.IsGeometricallyUnibranch A`: `A` is unibranch and the residue field extension of
  that integral closure over `A` is purely inseparable.

## Main results

* `IsLocalRing.isUnibranch_iff_isLocalRing_integralClosure`: a domain is unibranch if and only if
  its integral closure in its fraction field is local.
* `IsLocalRing.IsGeometricallyUnibranch.of_isIntegrallyClosed_quotient`: if the reduction of `A`
  is an integrally closed domain, then `A` is geometrically unibranch.
* `IsLocalRing.IsGeometricallyUnibranch.of_isIntegrallyClosed`: a normal local domain, for
  instance a field or a discrete valuation ring, is geometrically unibranch.

## References

* [Stacks Project, Definition 15.108.1](https://stacks.math.columbia.edu/tag/0BPZ)
-/

public section

namespace IsLocalRing

variable (A : Type*) [CommRing A]

/-- A ring `A` is **unibranch** if its reduction `A ⧸ nilradical A` is a domain and the integral
closure of that domain in its fraction field is a local ring (Stacks, Definition 15.108.1
(0BPZ)). For a local ring `A` this says that exactly one branch of `Spec A` passes through the
closed point. -/
@[stacks 0BPZ]
class IsUnibranch : Prop where
  /-- The reduction of `A` is a domain. -/
  isDomain : IsDomain (A ⧸ nilradical A)
  /-- The integral closure of the reduction of `A` in its fraction field is local. -/
  isLocalRing :
    IsLocalRing (integralClosure (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A)))

attribute [instance] IsUnibranch.isDomain IsUnibranch.isLocalRing

variable {A} in
/-- A domain `A` is unibranch if and only if its integral closure in its fraction field is a
local ring. -/
theorem isUnibranch_iff_isLocalRing_integralClosure [IsDomain A] :
    IsUnibranch A ↔ IsLocalRing (integralClosure A (FractionRing A)) := by
  set B := A ⧸ nilradical A
  set L := FractionRing B
  have hN : nilradical A = ⊥ := nilradical_eq_zero A
  have : (nilradical A).IsPrime := hN ▸ Ideal.isPrime_bot
  let e : A ≃+* B := (RingEquiv.quotientBot A).symm.trans (Ideal.quotEquivOfEq hN.symm)
  -- Through `A → B`, the fraction field `L` of `B` is also a fraction field of `A`. The algebra
  -- structure transported along `e` agrees with the scalar tower one because `e` is
  -- definitionally the quotient map.
  have : IsFractionRing A L := by
    convert (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (S := L) e.symm).mp
      inferInstance
    exact Algebra.algebra_ext _ _ fun a ↦ IsScalarTower.algebraMap_apply A B L a
  have hint : (integralClosure B L).restrictScalars A = integralClosure A L := by
    ext x
    exact ⟨fun hx ↦ isIntegral_trans x hx, fun hx ↦ hx.tower_top⟩
  let f : integralClosure A (FractionRing A) ≃+* integralClosure B L :=
    ((FractionRing.algEquiv A L).mapIntegralClosure.trans
      (Subalgebra.equivOfEq _ _ hint.symm)).toRingEquiv
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨inferInstance, .of_surjective' f.toRingHom f.surjective⟩⟩
  have := h.isLocalRing
  exact .of_surjective' f.symm.toRingHom f.symm.surjective

/-- If `A` is local and its reduction is a domain, then the structure map from `A` to the
integral closure `A'` of `A ⧸ nilradical A` in its fraction field is a local homomorphism. When
`A'` is local, this supplies the residue field extension of `A'` over `A` used in the definition
of a geometrically unibranch local ring. -/
instance isLocalHom_algebraMap_integralClosure [IsLocalRing A] [IsDomain (A ⧸ nilradical A)] :
    IsLocalHom (algebraMap A
      (integralClosure (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A)))) := by
  have : IsLocalHom (algebraMap A (A ⧸ nilradical A)) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  rw [IsScalarTower.algebraMap_eq A (A ⧸ nilradical A)]
  infer_instance

/-- A local ring `A` is **geometrically unibranch** if it is unibranch and the residue field of
the integral closure `A'` of `A ⧸ nilradical A` in its fraction field is purely inseparable over
the residue field of `A` (Stacks, Definition 15.108.1 (0BPZ)). The residue field extension is the
one induced by the local homomorphism `A → A'` of `isLocalHom_algebraMap_integralClosure`. -/
@[stacks 0BPZ]
class IsGeometricallyUnibranch [IsLocalRing A] : Prop extends IsUnibranch A where
  /-- The residue field of the integral closure of the reduction is purely inseparable over the
  residue field of `A`. -/
  isPurelyInseparable :
    letI := toIsUnibranch
    IsPurelyInseparable (ResidueField A)
      (ResidueField (integralClosure (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))))

attribute [instance] IsGeometricallyUnibranch.isPurelyInseparable

variable {A}

/-- If the reduction of a local ring `A` is an integrally closed domain, then `A` is
geometrically unibranch: the integral closure of `A ⧸ nilradical A` is `A ⧸ nilradical A` itself,
so it is local and has the same residue field as `A`. -/
theorem IsGeometricallyUnibranch.of_isIntegrallyClosed_quotient [IsLocalRing A]
    [IsDomain (A ⧸ nilradical A)] [IsIntegrallyClosed (A ⧸ nilradical A)] :
    IsGeometricallyUnibranch A := by
  set B := A ⧸ nilradical A
  set A' := integralClosure B (FractionRing B)
  let e : A' ≃ₐ[B] B :=
    (Subalgebra.equivOfEq _ _ (IsIntegrallyClosed.integralClosure_eq_bot B (FractionRing B))).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective B (FractionRing B)))
  have hsurj : Function.Surjective (algebraMap B A') := fun x ↦
    ⟨e x, by simpa using (e.symm.commutes (e x)).symm⟩
  have hsurjA : Function.Surjective (algebraMap A A') := by
    rw [IsScalarTower.algebraMap_eq A B A']
    exact hsurj.comp Ideal.Quotient.mk_surjective
  have : IsLocalRing A' := .of_surjective' _ hsurjA
  refine { toIsUnibranch := ⟨inferInstance, inferInstance⟩, isPurelyInseparable := ?_ }
  have hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField A')) := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    obtain ⟨a, rfl⟩ := hsurjA y
    exact ⟨residue A a, by simp⟩
  exact ⟨.of_surjective (Algebra.ofId _ _) hres, fun x _ ↦ hres x⟩

/-- A normal local domain is geometrically unibranch. In particular fields and discrete valuation
rings are geometrically unibranch. -/
instance IsGeometricallyUnibranch.of_isIntegrallyClosed [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] : IsGeometricallyUnibranch A :=
  have h : nilradical A = ⊥ := nilradical_eq_zero A
  have : (nilradical A).IsPrime := h ▸ Ideal.isPrime_bot
  have : IsIntegrallyClosed (A ⧸ nilradical A) :=
    .of_equiv ((RingEquiv.quotientBot A).symm.trans (Ideal.quotEquivOfEq h.symm))
  .of_isIntegrallyClosed_quotient

end IsLocalRing
