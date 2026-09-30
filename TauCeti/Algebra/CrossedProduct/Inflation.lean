/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Cohomologous
public import TauCeti.Algebra.CrossedProduct.GaloisCocycle.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit

/-!
# Inflation of crossed-product cocycles

A `TwoCocycle K L` for a finite Galois subextension `L` of the separable closure of `K` inflates
along restriction `G_K → Gal(L/K)` to a continuous cocycle of the absolute Galois group with
values in `Additive (Kˢ)ˣ`. This file constructs its class in continuous `H²` and identifies it
with the corresponding leg of the finite-quotient description of continuous cohomology.

The multiplicative-to-additive conversion is only `Additive.ofMul`. Continuity follows because
restriction has finite discrete target. Thus cohomologous finite cocycles determine the same
continuous class, and passing to a larger finite Galois subextension does not change the class.

The conventions follow Gille--Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4,
and Serre, *Local Fields*, Chapter X.
-/

public section

noncomputable section

open groupCohomology

namespace TauCeti

open ContCohomology

variable {K : Type} [Field K]
variable (L : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K L] [IsGalois K L]

namespace TwoCocycle

/-- Inflation of a cocycle on `Gal(L/K)` to the absolute Galois group, along restriction and the
inclusion `L ⊆ Kˢ`. -/
def inflate (c : TwoCocycle K L) : TwoCocycle K (SeparableClosure K) :=
  c.comap (AlgEquiv.restrictNormalHom L) L.val fun g x ↦
    AlgEquiv.restrictNormal_commutes g L x

omit [FiniteDimensional K L] in
/-- Inflating a cocycle and evaluating it amounts to restricting both automorphisms and including
its value in the separable closure. -/
@[simp]
theorem inflate_toFun (c : TwoCocycle K L) (g h : AbsoluteGaloisGroup K) :
    (c.inflate L).toFun g h =
      Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L h)) :=
  TwoCocycle.comap_toFun c _ _ _ g h

end TwoCocycle

/-- The additive cochain on `G_K` underlying the inflation of a multiplicative crossed-product
cocycle. -/
def unitsCochain (c : TwoCocycle K L) :
    AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K :=
  fun p ↦ Additive.ofMul ((c.inflate L).toFun p.1 p.2)

omit [FiniteDimensional K L] in
/-- The additive cochain underlying an inflated crossed-product cocycle evaluates by restriction
and inclusion. -/
@[simp]
theorem unitsCochain_apply (c : TwoCocycle K L) (g h : AbsoluteGaloisGroup K) :
    unitsCochain L c (g, h) = Additive.ofMul
      (Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L h))) :=
  congrArg Additive.ofMul (TwoCocycle.inflate_toFun L c g h)

omit [FiniteDimensional K L] in
/-- The additive cochain underlying an inflated crossed-product cocycle satisfies the
inhomogeneous `2`-cocycle identity. -/
theorem unitsCochain_isCocycle₂ (c : TwoCocycle K L) :
    IsCocycle₂ (unitsCochain L c) :=
  (c.inflate L).isMulCocycle₂

/-- The cochain obtained by inflating from a finite Galois subextension is continuous. -/
theorem continuous_unitsCochain_inflate (c : TwoCocycle K L) :
    Continuous (unitsCochain L c) := by
  rw [show unitsCochain L c = (fun q : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) ↦
      Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom (c.toFun q.1 q.2))) ∘
      (fun p ↦ (AlgEquiv.restrictNormalHom L p.1,
        AlgEquiv.restrictNormalHom L p.2)) by
    funext p
    exact unitsCochain_apply L c p.1 p.2]
  apply Continuous.comp continuous_of_discreteTopology
  exact (InfiniteGalois.restrictNormalHom_continuous L).comp continuous_fst |>.prodMk
    ((InfiniteGalois.restrictNormalHom_continuous L).comp continuous_snd)

/-- The inflated cocycle as an element of the explicit continuous cocycle group `Z²`. -/
def inflateTwoCocycleZ2 (c : TwoCocycle K L) :
    Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  ⟨unitsCochain L c, mem_Z2_iff.2
    ⟨continuous_unitsCochain_inflate L c, unitsCochain_isCocycle₂ L c⟩⟩

/-- The cocycle underlying `inflateTwoCocycleZ2` is `unitsCochain`. -/
@[simp]
theorem coe_inflateTwoCocycleZ2 (c : TwoCocycle K L) :
    (inflateTwoCocycleZ2 L c : _ → UnitsCoeff K) = unitsCochain L c :=
  (rfl)

/-- Send an explicit degree-two class with multiplicative coefficients to canonical continuous
cohomology. -/
def unitsClassOfH2 : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) →+
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  (explicitH2AddEquivContinuousCohomology
    (AbsoluteGaloisGroup K) (UnitsCoeff K)).toAddMonoidHom

/-- The continuous class of an explicit continuous `2`-cocycle. -/
def unitsClassOfZ2 (z : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  unitsClassOfH2 (K := K) (H2pi _ _ z)

/-- The continuous cohomology class represented by the inflation of `c`. -/
def inflateTwoCocycleClass (c : TwoCocycle K L) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  unitsClassOfZ2 (K := K) (inflateTwoCocycleZ2 L c)

/-- Cohomologous crossed-product cocycles have the same class after inflation to continuous
cohomology. -/
theorem inflateTwoCocycleClass_eq_of_cohomologous {z w : TwoCocycle K L}
    (h : z.Cohomologous w) :
    inflateTwoCocycleClass L z = inflateTwoCocycleClass L w := by
  obtain ⟨b, hb⟩ := TwoCocycle.cohomologous_iff.1 h.symm
  apply congrArg (unitsClassOfH2 (K := K))
  refine H2pi_eq_iff.2 (mem_B2_iff'.2 ?_)
  refine ⟨fun g ↦ Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
    (b (AlgEquiv.restrictNormalHom L g))), ?_, ?_⟩
  · change Continuous ((fun σ : L ≃ₐ[K] L ↦ (Additive.ofMul
      (Units.map L.val.toRingHom.toMonoidHom (b σ)) : UnitsCoeff K)) ∘
        AlgEquiv.restrictNormalHom L)
    exact Continuous.comp continuous_of_discreteTopology
      (InfiniteGalois.restrictNormalHom_continuous L)
  · intro g k
    change g • Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
        (b (AlgEquiv.restrictNormalHom L k))) -
          Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
            (b (AlgEquiv.restrictNormalHom L (g * k)))) +
          Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
            (b (AlgEquiv.restrictNormalHom L g))) =
        unitsCochain L z (g, k) - unitsCochain L w (g, k)
    apply Additive.toMul.injective
    simp only [toMul_add, toMul_sub, toMul_ofMul, Additive.toMul_smul,
      unitsCochain_apply]
    apply Units.ext
    rw [map_mul (AlgEquiv.restrictNormalHom L) g k]
    simp only [AlgEquiv.smul_units_def, Units.val_mul, Units.val_div_eq_div_val,
      Units.coe_map]
    change g (L.val (b (AlgEquiv.restrictNormalHom L k) : L)) /
        L.val (b (AlgEquiv.restrictNormalHom L g * AlgEquiv.restrictNormalHom L k) : L) *
          L.val (b (AlgEquiv.restrictNormalHom L g) : L) =
      L.val (z.toFun (AlgEquiv.restrictNormalHom L g)
          (AlgEquiv.restrictNormalHom L k) : L) /
        L.val (w.toFun (AlgEquiv.restrictNormalHom L g)
          (AlgEquiv.restrictNormalHom L k) : L)
    have hcomm := L.val.restrictNormalHom_commutes g
      (b (AlgEquiv.restrictNormalHom L k) : L)
    rw [show L.val.restrictNormalHom g = AlgEquiv.restrictNormalHom L g from
      L.val.restrictNormalHom_eq_iff.2 fun x ↦
        (AlgEquiv.restrictNormal_commutes g L x).symm] at hcomm
    rw [← hcomm, hb]
    simp only [map_mul]
    field_simp
    rw [← map_mul]
    exact congrArg L.val (Units.mul_inv _).symm

section Refinement

variable (M : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K M] [IsGalois K M]

omit [FiniteDimensional K L] [FiniteDimensional K M] in
/-- Restricting first to a larger intermediate field and then along its inclusion into `L`
agrees with restricting directly to `L`. -/
theorem restrictNormalHom_of_comap (hLM : L ≤ M) (g : AbsoluteGaloisGroup K) :
    (IntermediateField.inclusion hLM).restrictNormalHom
        (AlgEquiv.restrictNormalHom M g) =
      AlgEquiv.restrictNormalHom L g := by
  apply (IntermediateField.inclusion hLM).restrictNormalHom_eq_iff.2
  intro x
  apply M.val.injective
  have hM := M.val.restrictNormalHom_commutes g
    (IntermediateField.inclusion hLM x)
  rw [show M.val.restrictNormalHom g = AlgEquiv.restrictNormalHom M g from
    M.val.restrictNormalHom_eq_iff.2 fun y ↦
      (AlgEquiv.restrictNormal_commutes g M y).symm] at hM
  have hL := L.val.restrictNormalHom_commutes g x
  rw [show L.val.restrictNormalHom g = AlgEquiv.restrictNormalHom L g from
    L.val.restrictNormalHom_eq_iff.2 fun y ↦
      (AlgEquiv.restrictNormal_commutes g L y).symm] at hL
  exact hM.trans (by simpa using hL.symm)

omit [FiniteDimensional K L] [FiniteDimensional K M] in
/-- Refining a finite Galois subextension before inflation does not change the cocycle on the
absolute Galois group. -/
theorem TwoCocycle.inflate_comap (hLM : L ≤ M) (c : TwoCocycle K L) :
    (c.comap (IntermediateField.inclusion hLM).restrictNormalHom
      (IntermediateField.inclusion hLM)
      (fun g x ↦ (IntermediateField.inclusion hLM).restrictNormalHom_commutes g x)).inflate M =
        c.inflate L := by
  ext g k
  rw [TwoCocycle.inflate_toFun, TwoCocycle.comap_toFun, TwoCocycle.inflate_toFun,
    restrictNormalHom_of_comap, restrictNormalHom_of_comap]
  rfl

/-- Refining the finite Galois subextension on which a cocycle is defined does not change its
inflated continuous cohomology class. -/
theorem inflateTwoCocycleClass_comap (hLM : L ≤ M) (c : TwoCocycle K L) :
    inflateTwoCocycleClass M
        (c.comap (IntermediateField.inclusion hLM).restrictNormalHom
          (IntermediateField.inclusion hLM)
          (fun g x ↦ (IntermediateField.inclusion hLM).restrictNormalHom_commutes g x)) =
      inflateTwoCocycleClass L c := by
  apply congrArg (unitsClassOfZ2 (K := K))
  apply Subtype.ext
  funext p
  change Additive.ofMul
      (((c.comap (IntermediateField.inclusion hLM).restrictNormalHom
        (IntermediateField.inclusion hLM)
        (fun g x ↦
          (IntermediateField.inclusion hLM).restrictNormalHom_commutes g x)).inflate M).toFun
          p.1 p.2) = Additive.ofMul ((c.inflate L).toFun p.1 p.2)
  rw [TwoCocycle.inflate_comap]

end Refinement

/-- A finite Galois subextension determines the open normal subgroup that fixes it pointwise. -/
def galoisOpenNormal : OpenNormalSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := L.val.fieldRange.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_fieldRange K L L.val
  isNormal' := inferInstance

/-- The quotient of the absolute Galois group by the subgroup fixing `L` is `Gal(L/K)`. -/
def galoisQuotientMap :
    AbsoluteGaloisGroup K ⧸ (galoisOpenNormal L).toSubgroup ≃* (L ≃ₐ[K] L) :=
  quotientFixingSubgroupFieldRangeEquiv K L L.val

omit [FiniteDimensional K L] in
/-- Restriction through the canonical inclusion of an intermediate field agrees with the
canonical restriction map for that intermediate field. -/
private theorem val_restrictNormalHom (g : AbsoluteGaloisGroup K) :
    L.val.restrictNormalHom g = AlgEquiv.restrictNormalHom L g :=
  L.val.restrictNormalHom_eq_iff.2 fun x ↦ (AlgEquiv.restrictNormal_commutes g L x).symm

/-- The quotient identification is induced by restriction to `L`. -/
@[simp]
theorem galoisQuotientMap_mk (g : AbsoluteGaloisGroup K) :
    galoisQuotientMap L g = AlgEquiv.restrictNormalHom L g := by
  change quotientFixingSubgroupFieldRangeEquiv K L L.val g = _
  rw [quotientFixingSubgroupFieldRangeEquiv_mk, val_restrictNormalHom]

/-- The quotient identification, bundled as a continuous homomorphism. -/
private def galoisQuotientHom :
    AbsoluteGaloisGroup K ⧸ (galoisOpenNormal L).toSubgroup →ₜ* (L ≃ₐ[K] L) :=
  { (galoisQuotientMap L).toMonoidHom with
    continuous_toFun := continuous_of_discreteTopology }

/-- Inclusion of `Lˣ` in `(Kˢ)ˣ`, viewed as an additive map into the invariants fixed by
`Gal(Kˢ/L)`. -/
private def finiteLevelCoeffHom :
    Additive Lˣ →+ FixedPoints.addSubgroup (galoisOpenNormal L).toSubgroup (UnitsCoeff K) :=
  (embeddedUnitsEquivInvariants K L L.val).toAddMonoidHom

/-- The quotient action and the inclusion of invariant units form a compatible pair. -/
private theorem finiteLevelCoeffHom_smul
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormal L).toSubgroup) (b : Additive Lˣ) :
    finiteLevelCoeffHom L (galoisQuotientHom L q • b) = q • finiteLevelCoeffHom L b := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
      rw [show galoisQuotientHom L g = L.val.restrictNormalHom g by
        change galoisQuotientMap L g = _
        rw [galoisQuotientMap_mk, val_restrictNormalHom]]
      apply Subtype.ext
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      exact embeddedUnitsEquivInvariants_restrictNormalHom_smul K L L.val g b

/-- The cocycle at the finite quotient `G_K/G_L`, with values in the units fixed by `G_L`. -/
def finiteLevelZ2 (c : TwoCocycle K L) :
    Z2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormal L).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormal L).toSubgroup (UnitsCoeff K)) := ⟨
  fun p ↦ finiteLevelCoeffHom L (Additive.ofMul
    (c.toFun (galoisQuotientMap L p.1) (galoisQuotientMap L p.2))),
  mem_Z2_iff.2 ⟨continuous_of_discreteTopology, fun q r s ↦ by
    dsimp only
    rw [map_mul (galoisQuotientMap L) q r, map_mul (galoisQuotientMap L) r s,
      ← finiteLevelCoeffHom_smul]
    rw [← (finiteLevelCoeffHom L).map_add, ← (finiteLevelCoeffHom L).map_add]
    apply congrArg (finiteLevelCoeffHom L)
    apply Additive.toMul.injective
    exact c.isMulCocycle₂ (galoisQuotientMap L q) (galoisQuotientMap L r)
      (galoisQuotientMap L s)⟩⟩

/-- The finite-level cocycle evaluates by restricting the two quotient classes and embedding the
value of the original cocycle into the separable closure. -/
@[simp]
theorem finiteLevelZ2_apply (c : TwoCocycle K L)
    (q r : AbsoluteGaloisGroup K ⧸ (galoisOpenNormal L).toSubgroup) :
    ((finiteLevelZ2 L c).1 (q, r) : UnitsCoeff K) =
      Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (galoisQuotientMap L q) (galoisQuotientMap L r))) := by
  rw [finiteLevelZ2]
  change ((embeddedUnitsEquivInvariants K L L.val)
      (Additive.ofMul (c.toFun (galoisQuotientMap L q) (galoisQuotientMap L r))) :
        UnitsCoeff K) = _
  rw [embeddedUnitsEquivInvariants_apply]
  apply Additive.toMul.injective
  exact toMul_coe_embeddedUnitsInvariants K L L.val
    (c.toFun (galoisQuotientMap L q) (galoisQuotientMap L r))

/-- The class of a crossed-product cocycle at the finite quotient `G_K/G_L`. -/
def finiteLevelClass (c : TwoCocycle K L) :
    H2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormal L).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormal L).toSubgroup (UnitsCoeff K)) :=
  H2pi _ _ (finiteLevelZ2 L c)

/-- Inflating the finite-level representative gives the cocycle obtained directly by restricting
absolute Galois automorphisms to `L`. -/
private theorem explicitInfl2_finiteLevelClass (c : TwoCocycle K L) :
    explicitInfl2 (AbsoluteGaloisGroup K) (UnitsCoeff K) (galoisOpenNormal L).toSubgroup
        (finiteLevelClass L c) =
      H2pi (AbsoluteGaloisGroup K) (UnitsCoeff K) (inflateTwoCocycleZ2 L c) := by
  change explicitInfl2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (galoisOpenNormal L).toSubgroup (finiteLevelZ2 L c : H2 _ _) = _
  rw [explicitInfl2_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup K) (UnitsCoeff K))
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  rw [cocyclesMap2_apply]
  change ((finiteLevelZ2 L c).1 (g, h) : UnitsCoeff K) = unitsCochain L c (g, h)
  rw [finiteLevelZ2_apply, galoisQuotientMap_mk, galoisQuotientMap_mk,
    unitsCochain_apply]

/-- **The inflated crossed-product class is the finite-quotient comparison class.** More
precisely, its explicit `H²` representative is the image of the class at the quotient
`G_K/G_L` under the `L`-leg of `explicitFiniteQuotientComparison2`. -/
theorem inflateTwoCocycleClass_eq_finiteQuotientComparison (c : TwoCocycle K L) :
    inflateTwoCocycleClass L c = unitsClassOfH2 (K := K)
      ((explicitFiniteQuotientComparison2 (AbsoluteGaloisGroup K) (UnitsCoeff K)).app
        (Opposite.op (galoisOpenNormal L)) (finiteLevelClass L c)) := by
  rw [inflateTwoCocycleClass, unitsClassOfZ2,
    explicitFiniteQuotientComparison2_app]
  exact congrArg (unitsClassOfH2 (K := K)) (explicitInfl2_finiteLevelClass L c).symm

namespace GaloisCocycle

/-- The continuous cohomology class obtained by inflating a bundled finite Galois cocycle. -/
def inflateClass (c : GaloisCocycle K) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  inflateTwoCocycleClass c.extension c.cocycle

end GaloisCocycle

end TauCeti
