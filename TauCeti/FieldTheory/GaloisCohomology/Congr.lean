/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.MapDegreeTwo

/-!
# Unit-valued Galois cohomology of isomorphic fields

A field isomorphism transports the discrete unit modules of the chosen separable closures,
continuous two-cocycles, and their explicit second cohomology groups. The group map is
contravariant, and the coefficient map is covariant. Their compatibility follows from the
conjugation equation for the chosen absolute-Galois-group equivalence. The same compatible pair
also identifies Mathlib's canonical `continuousCohomology 2` groups, by
`TauCeti.ContCohomology.continuousCohomologyMap2Equiv`, and the comparison with the explicit model
carries one identification to the other
(`RingEquiv.explicitH2AddEquivContinuousCohomology_unitsH2Congr`).

The compatible-pair construction is extracted from
`TauCeti.ClassFieldTheory.brCongr` and specializes continuous cohomology's `cocyclesMap2`
and `explicitMap2Equiv`.
Both field universes remain independent. The lift to separable closures is chosen: the
inverse below is the inverse of this supplied identification, rather than a separately
chosen lift of the inverse field isomorphism.
-/

public noncomputable section

open TauCeti TauCeti.ContCohomology

namespace RingEquiv

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]

/-- The covariant identification of discrete unit coefficients induced by a field isomorphism,
using the inverse of its chosen separable-closure identification. -/
def unitsCoeffCongr (e : K ≃+* L) : UnitsCoeff K ≃+ UnitsCoeff L :=
  (Units.mapEquiv e.separableClosureCongr.symm.toMulEquiv).toAdditive

/-- On underlying field elements, coefficient transport is the chosen separable-closure map. -/
@[simp]
theorem unitsCoeffCongr_apply (e : K ≃+* L) (x : UnitsCoeff K) :
    ((e.unitsCoeffCongr x).toMul : SeparableClosure L) =
      e.separableClosureCongr.symm (x.toMul : SeparableClosure K) :=
  (rfl)

/-- The inverse coefficient transport is the chosen map from the target separable closure. -/
@[simp]
theorem unitsCoeffCongr_symm_apply (e : K ≃+* L) (x : UnitsCoeff L) :
    ((e.unitsCoeffCongr.symm x).toMul : SeparableClosure K) =
      e.separableClosureCongr (x.toMul : SeparableClosure L) :=
  (rfl)

/-- Coefficient transport intertwines the absolute Galois actions. -/
@[simp]
theorem unitsCoeffCongr_smul (e : K ≃+* L) (g : AbsoluteGaloisGroup L)
    (x : UnitsCoeff K) :
    e.unitsCoeffCongr (e.absoluteGaloisGroupCongr g • x) = g • e.unitsCoeffCongr x := by
  apply Additive.toMul.injective
  apply Units.ext
  simp only [unitsCoeffCongr_apply, Additive.toMul_smul, AlgEquiv.smul_units_def,
    Units.coe_map, MonoidHom.coe_ofClass]
  rw [absoluteGaloisGroupCongr_apply, RingEquiv.symm_apply_apply]

/-- Transport of continuous unit-valued two-cocycles along a field isomorphism. -/
def unitsCocyclesCongr (e : K ≃+* L) :
    Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K) →+
      Z2 (AbsoluteGaloisGroup L) (UnitsCoeff L) :=
  cocyclesMap2 _ _ _ _ e.absoluteGaloisGroupCongr e.unitsCoeffCongr.toAddMonoidHom
    continuous_of_discreteTopology e.unitsCoeffCongr_smul

/-- The transported cocycle is evaluated at the transported automorphisms, then its value
is transported between the separable closures. -/
@[simp]
theorem unitsCocyclesCongr_apply (e : K ≃+* L)
    (c : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) (g h : AbsoluteGaloisGroup L) :
    (e.unitsCocyclesCongr c : _ → UnitsCoeff L) (g, h) =
      e.unitsCoeffCongr ((c : _ → UnitsCoeff K)
        (e.absoluteGaloisGroupCongr g, e.absoluteGaloisGroupCongr h)) :=
  cocyclesMap2_apply _ _ _ _ _ _ _ _ c g h

/-- A field isomorphism identifies the explicit second Galois cohomology groups with unit
coefficients. This preserves the actual field, absolute Galois group and coefficient universes. -/
def unitsH2Congr (e : K ≃+* L) :
    H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) ≃+
      H2 (AbsoluteGaloisGroup L) (UnitsCoeff L) :=
  explicitMap2Equiv _ _ _ _ e.absoluteGaloisGroupCongr e.unitsCoeffCongr
    continuous_of_discreteTopology continuous_of_discreteTopology e.unitsCoeffCongr_smul

/-- On a cocycle class, field transport is given by the transported continuous cocycle. -/
@[simp]
theorem unitsH2Congr_mk (e : K ≃+* L)
    (c : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    e.unitsH2Congr (c : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) =
      (e.unitsCocyclesCongr c : H2 (AbsoluteGaloisGroup L) (UnitsCoeff L)) := by
  unfold unitsH2Congr unitsCocyclesCongr
  exact (explicitMap2Equiv_apply (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) _ _ _ _ _ _).trans
      (explicitMap2_mk (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (AbsoluteGaloisGroup L) (UnitsCoeff L) _ _ _ _ c)

/-- Inverse transport recovers the class of a cocycle from its transported representative. -/
@[simp]
theorem unitsH2Congr_symm_unitsCocyclesCongr (e : K ≃+* L)
    (c : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    e.unitsH2Congr.symm (e.unitsCocyclesCongr c : H2 _ _) = (c : H2 _ _) := by
  rw [← unitsH2Congr_mk]
  exact e.unitsH2Congr.symm_apply_apply _

/-- The inverse identification is induced by the inverse compatible group and coefficient
maps of the chosen lift. -/
theorem unitsH2Congr_symm_mk (e : K ≃+* L)
    (c : Z2 (AbsoluteGaloisGroup L) (UnitsCoeff L)) :
    e.unitsH2Congr.symm (c : H2 (AbsoluteGaloisGroup L) (UnitsCoeff L)) =
      (cocyclesMap2 (AbsoluteGaloisGroup L) (UnitsCoeff L)
        (AbsoluteGaloisGroup K) (UnitsCoeff K) e.absoluteGaloisGroupCongr.symm
        e.unitsCoeffCongr.symm.toAddMonoidHom continuous_of_discreteTopology
        (AddEquiv.symm_map_smul_of_map_mulEquiv_smul e.unitsCoeffCongr
          e.absoluteGaloisGroupCongr.toMulEquiv e.unitsCoeffCongr_smul) c :
        H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) := by
  unfold unitsH2Congr
  exact (explicitMap2Equiv_symm_apply (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) _ _ _ _ _ _).trans
      (explicitMap2_mk (AbsoluteGaloisGroup L) (UnitsCoeff L)
        (AbsoluteGaloisGroup K) (UnitsCoeff K) _ _ _ _ c)

/-- The absolute Galois group is locally compact, being compact and Hausdorff. Instance search
does not find this within its default budget, so it is assembled here from the Krull topology
being Hausdorff, as in `TauCeti.Algebra.CrossedProduct.Comparison`. -/
local instance locallyCompactSpace_absoluteGaloisGroup {F : Type*} [Field F] :
    LocallyCompactSpace (AbsoluteGaloisGroup F) :=
  have : R1Space (AbsoluteGaloisGroup F) := @T2Space.r1Space _ _ krullTopology_t2
  have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup F) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-- A field isomorphism identifies Mathlib's canonical second continuous Galois cohomology groups
with unit coefficients, along the same group and coefficient maps as `RingEquiv.unitsH2Congr`.
The field universes remain independent. -/
def unitsContinuousH2Congr (e : K ≃+* L) :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) ≃+
      continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup L) (UnitsCoeff L)) :=
  continuousCohomologyMap2Equiv _ _ _ _ e.absoluteGaloisGroupCongr e.unitsCoeffCongr
    e.unitsCoeffCongr_smul

/-- Canonical field transport is the pullback along the transported automorphisms and the
coefficient transport. -/
theorem unitsContinuousH2Congr_apply (e : K ≃+* L)
    (x : continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) :
    e.unitsContinuousH2Congr x =
      continuousCohomologyMap2 _ _ _ _ e.absoluteGaloisGroupCongr e.unitsCoeffCongr.toAddMonoidHom
        e.unitsCoeffCongr_smul x :=
  continuousCohomologyMap2Equiv_apply _ _ _ _ _ _ _ x

/-- The comparison of the explicit `H²` with Mathlib's continuous cohomology carries explicit
field transport `RingEquiv.unitsH2Congr` to canonical field transport. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_unitsH2Congr (e : K ≃+* L)
    (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    e.unitsContinuousH2Congr (explicitH2AddEquivContinuousCohomology _ _ x) =
      explicitH2AddEquivContinuousCohomology _ _ (e.unitsH2Congr x) := by
  simp [unitsContinuousH2Congr, unitsH2Congr]

end RingEquiv
