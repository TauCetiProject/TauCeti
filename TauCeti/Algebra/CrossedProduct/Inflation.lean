/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Cohomology
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

The multiplicative-to-additive conversion is `TwoCocycle.toCocycles₂`. Continuity follows because
restriction has finite discrete target. Thus cohomologous finite cocycles determine the same
continuous class, and passing to a larger finite Galois subextension, along any compatible pair
agreeing with the inclusions into `Kˢ`, does not change the class.

The conventions follow Gille--Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4,
and Serre, *Local Fields*, Chapter X.
-/

public section

noncomputable section

open groupCohomology

namespace TauCeti

open ContCohomology

variable {K : Type} [Field K]

namespace TwoCocycle

variable (L : IntermediateField K (SeparableClosure K))

section Normal

variable [Normal K L]

/-- Inflation of a cocycle on `Gal(L/K)` to the absolute Galois group, along restriction and the
inclusion `L ⊆ Kˢ`. -/
def inflate (c : TwoCocycle K L) : TwoCocycle K (SeparableClosure K) :=
  c.comap (AlgEquiv.restrictNormalHom L) L.val fun g x ↦
    AlgEquiv.restrictNormal_commutes g L x

/-- Inflating a cocycle and evaluating it amounts to restricting both automorphisms and including
its value in the separable closure. -/
@[simp]
theorem inflate_toFun (c : TwoCocycle K L) (g h : AbsoluteGaloisGroup K) :
    (c.inflate L).toFun g h =
      Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L h)) :=
  TwoCocycle.comap_toFun c _ _ _ g h

end Normal

section Finite

variable [FiniteDimensional K L] [Normal K L]

/-- The cochain obtained by inflating from a finite normal subextension is continuous. -/
theorem continuous_toCocycles₂_inflate (c : TwoCocycle K L) :
    Continuous (Y := UnitsCoeff K) (c.inflate L).toCocycles₂ := by
  have hfactor : (⇑(c.inflate L).toCocycles₂ :
      AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) =
      (fun q : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) ↦
        Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom (c.toFun q.1 q.2))) ∘
        Prod.map (AlgEquiv.restrictNormalHom L) (AlgEquiv.restrictNormalHom L) := by
    ext p
    simp only [coe_toCocycles₂, inflate_toFun, Function.comp_apply, Prod.map_fst, Prod.map_snd]
    -- The sides agree except that the left is typed in the carrier of
    -- `Rep.ofMulDistribMulAction G_K (Kˢ)ˣ`, which is `UnitsCoeff K` by definition.
    rfl
  rw [hfactor]
  exact continuous_of_discreteTopology.comp
    ((InfiniteGalois.restrictNormalHom_continuous L).prodMap
      (InfiniteGalois.restrictNormalHom_continuous L))

/-- The inflated cocycle as an element of the explicit continuous cocycle group `Z²`. -/
def inflateZ2 (c : TwoCocycle K L) :
    Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  ⟨(c.inflate L).toCocycles₂, mem_Z2_iff.2 ⟨c.continuous_toCocycles₂_inflate L,
    (c.inflate L).coe_toCocycles₂ ▸ (c.inflate L).isMulCocycle₂⟩⟩

/-- The cocycle underlying `inflateZ2` is the additive cocycle of the inflated cocycle. -/
@[simp]
theorem coe_inflateZ2 (c : TwoCocycle K L) :
    (c.inflateZ2 L : _ → UnitsCoeff K) = (c.inflate L).toCocycles₂ :=
  (rfl)

/-- The continuous cohomology class represented by the inflation of `c`. -/
def inflateClass (c : TwoCocycle K L) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (H2pi _ _ (c.inflateZ2 L))

/-- Cohomologous crossed-product cocycles have the same class after inflation to continuous
cohomology. -/
theorem inflateClass_eq_of_cohomologous {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    z.inflateClass L = w.inflateClass L := by
  obtain ⟨b, hb⟩ := cohomologous_def.1 h.symm
  apply congrArg (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K))
  refine H2pi_eq_iff.2 (mem_B2_iff'.2 ⟨(fun σ : L ≃ₐ[K] L ↦
    Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom (b σ))) ∘
      AlgEquiv.restrictNormalHom L,
    continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous L),
    fun g k ↦ ?_⟩)
  have hbgk := congrArg (Units.map L.val.toRingHom.toMonoidHom)
    (hb (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k))
  apply Additive.toMul.injective
  apply Units.ext
  simp only [map_mul, map_div, Units.ext_iff, Units.val_mul,
    Units.val_div_eq_div_val, Units.coe_map, AlgEquiv.smul_units_def] at hbgk
  simp only [Function.comp_apply, toMul_add, toMul_sub, toMul_ofMul, Additive.toMul_smul,
    coe_inflateZ2, Pi.sub_apply, coe_toCocycles₂, inflate_toFun, Units.val_mul,
    Units.val_div_eq_div_val, Units.coe_map, AlgEquiv.smul_units_def, map_mul]
  rw [← hbgk]
  congr 2
  exact (AlgEquiv.restrictNormal_commutes g L _).symm

end Finite

section Refinement

variable {L} {M : IntermediateField K (SeparableClosure K)} [Normal K L] [Normal K M]
  (π : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hπι : ∀ g x, ι (π g x) = g (ι x))
  (hι : ∀ x, M.val (ι x) = L.val x)
include hπι hι

/-- Along a compatible pair `(π, ι)` whose embedding `ι` is compatible with the inclusions into
`Kˢ`, `π` carries restriction to `M` to restriction to `L`. -/
private theorem restrictNormalHom_of_compatible (g : AbsoluteGaloisGroup K) :
    π (AlgEquiv.restrictNormalHom M g) = AlgEquiv.restrictNormalHom L g :=
  AlgEquiv.ext fun x ↦ L.val.injective <| (hι _).symm.trans <|
    (congrArg M.val (hπι _ x)).trans <| (AlgEquiv.restrictNormal_commutes g M (ι x)).trans <|
      (congrArg g (hι x)).trans (AlgEquiv.restrictNormal_commutes g L x).symm

/-- Refining a normal subextension along a compatible pair `(π, ι)`, with `ι` compatible with the
inclusions into `Kˢ`, before inflation does not change the cocycle on the absolute Galois
group. -/
theorem inflate_comap (c : TwoCocycle K L) : (c.comap π ι hπι).inflate M = c.inflate L := by
  ext g k
  rw [inflate_toFun, comap_toFun, inflate_toFun, restrictNormalHom_of_compatible π ι hπι hι,
    restrictNormalHom_of_compatible π ι hπι hι]
  simpa using hι (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k))

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- Refining the finite normal subextension on which a cocycle is defined, along a compatible pair
`(π, ι)` with `ι` compatible with the inclusions into `Kˢ`, does not change its inflated
continuous cohomology class. -/
theorem inflateClass_comap (c : TwoCocycle K L) :
    (c.comap π ι hπι).inflateClass M = c.inflateClass L := by
  rw [inflateClass, inflateClass]
  congr 2
  exact Subtype.ext (by rw [coe_inflateZ2, coe_inflateZ2, inflate_comap π ι hπι hι])

end Refinement

section FiniteLevel

variable [FiniteDimensional K L] [Normal K L]

omit [FiniteDimensional K L] in
/-- Restriction through the canonical inclusion of an intermediate field agrees with the
canonical restriction map for that intermediate field. -/
private theorem val_restrictNormalHom (g : AbsoluteGaloisGroup K) :
    L.val.restrictNormalHom g = AlgEquiv.restrictNormalHom L g :=
  L.val.restrictNormalHom_eq_iff.2 fun x ↦ (AlgEquiv.restrictNormal_commutes g L x).symm

/-- The quotient identification, bundled as a continuous homomorphism. -/
private def galoisQuotientHom :
    AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup →ₜ* (L ≃ₐ[K] L) :=
  { (quotientFixingSubgroupFieldRangeEquiv K L L.val).toMonoidHom with
    continuous_toFun := continuous_of_discreteTopology }

/-- `galoisQuotientHom` is the quotient identification `quotientFixingSubgroupFieldRangeEquiv`. -/
private theorem galoisQuotientHom_apply
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup) :
    galoisQuotientHom L q = quotientFixingSubgroupFieldRangeEquiv K L L.val q :=
  (rfl)

/-- On the class of `g`, `galoisQuotientHom` is restriction of `g` to `L`. -/
private theorem galoisQuotientHom_mk (g : AbsoluteGaloisGroup K) :
    galoisQuotientHom L g = AlgEquiv.restrictNormalHom L g :=
  ((galoisQuotientHom_apply L g).trans (quotientFixingSubgroupFieldRangeEquiv_mk K L L.val g)).trans
    (val_restrictNormalHom L g)

/-- Inclusion of `Lˣ` in `(Kˢ)ˣ`, viewed as an additive map into the invariants fixed by
`Gal(Kˢ/L)`. -/
private def finiteLevelCoeffHom :
    Additive Lˣ →+
      FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K) :=
  (embeddedUnitsEquivInvariants K L L.val).toAddMonoidHom

/-- `finiteLevelCoeffHom` embeds a unit of `L` into `(Kˢ)ˣ`. -/
private theorem coe_finiteLevelCoeffHom (b : Additive Lˣ) :
    (finiteLevelCoeffHom L b : UnitsCoeff K) =
      Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom b.toMul) :=
  Additive.toMul.injective <| by
    have h := toMul_coe_embeddedUnitsInvariants K L L.val b.toMul
    rw [← embeddedUnitsEquivInvariants_apply] at h
    exact h

/-- The quotient action and the inclusion of invariant units form a compatible pair. -/
private theorem finiteLevelCoeffHom_smul
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
    (b : Additive Lˣ) :
    finiteLevelCoeffHom L (galoisQuotientHom L q • b) = q • finiteLevelCoeffHom L b := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
      rw [galoisQuotientHom_mk, ← val_restrictNormalHom]
      apply Subtype.ext
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      exact embeddedUnitsEquivInvariants_restrictNormalHom_smul K L L.val g b

/-- The cocycle at the finite quotient `G_K/G_L`, with values in the units fixed by `G_L`: the
pullback, along the compatible pair given by the quotient identification `G_K/G_L ≃ Gal(L/K)` and
the inclusion of `Lˣ` as the invariants, of `c` viewed as a cocycle of the discrete group
`Gal(L/K)` with discrete coefficients. -/
def finiteLevelZ2 (c : TwoCocycle K L) :
    Z2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K)) :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  haveI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  cocyclesMap2 (L ≃ₐ[K] L) (Additive Lˣ) _ _ (galoisQuotientHom L) (finiteLevelCoeffHom L)
    continuous_of_discreteTopology (finiteLevelCoeffHom_smul L)
    ⟨c.toCocycles₂, mem_Z2_iff.2
      ⟨continuous_of_discreteTopology, c.coe_toCocycles₂ ▸ c.isMulCocycle₂⟩⟩

/-- The finite-level cocycle evaluates by restricting the two quotient classes and embedding the
value of the original cocycle into the separable closure. -/
@[simp]
theorem finiteLevelZ2_apply (c : TwoCocycle K L)
    (q r : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup) :
    ((c.finiteLevelZ2 L).1 (q, r) : UnitsCoeff K) =
      Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (quotientFixingSubgroupFieldRangeEquiv K L L.val q)
          (quotientFixingSubgroupFieldRangeEquiv K L L.val r))) := by
  rw [finiteLevelZ2, cocyclesMap2_apply, coe_finiteLevelCoeffHom, galoisQuotientHom_apply,
    galoisQuotientHom_apply]
  simp only [coe_toCocycles₂, toMul_ofMul]

/-- The class of a crossed-product cocycle at the finite quotient `G_K/G_L`. -/
def finiteLevelClass (c : TwoCocycle K L) :
    H2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K)) :=
  H2pi _ _ (c.finiteLevelZ2 L)

/-- Inflating the finite-level representative gives the cocycle obtained directly by restricting
absolute Galois automorphisms to `L`. -/
private theorem explicitInfl2_finiteLevelClass (c : TwoCocycle K L) :
    explicitInfl2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (galoisOpenNormalSubgroup K L L.val).toSubgroup (c.finiteLevelClass L) =
      H2pi (AbsoluteGaloisGroup K) (UnitsCoeff K) (c.inflateZ2 L) := by
  rw [finiteLevelClass, QuotientAddGroup.mk'_apply, explicitInfl2_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup K) (UnitsCoeff K))
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  rw [cocyclesMap2_apply, AddSubgroup.subtype_apply, ContinuousMonoidHom.quotientMk_apply,
    ContinuousMonoidHom.quotientMk_apply, finiteLevelZ2_apply, ← galoisQuotientHom_apply,
    ← galoisQuotientHom_apply, galoisQuotientHom_mk, galoisQuotientHom_mk, coe_inflateZ2]
  simp only [coe_toCocycles₂, inflate_toFun]

/-- **The inflated crossed-product class is the finite-quotient comparison class.** More
precisely, its explicit `H²` representative is the image of the class at the quotient
`G_K/G_L` under the `L`-leg of `explicitFiniteQuotientComparison2`. -/
theorem inflateClass_eq_finiteQuotientComparison (c : TwoCocycle K L) :
    c.inflateClass L =
      explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)
        ((explicitFiniteQuotientComparison2 (AbsoluteGaloisGroup K) (UnitsCoeff K)).app
          (Opposite.op (galoisOpenNormalSubgroup K L L.val)) (c.finiteLevelClass L)) := by
  rw [inflateClass, explicitFiniteQuotientComparison2_app]
  exact congrArg (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K))
    (explicitInfl2_finiteLevelClass L c).symm

end FiniteLevel

end TwoCocycle

namespace GaloisCocycle

/-- The continuous cohomology class obtained by inflating a bundled finite Galois cocycle. -/
def inflateClass (c : GaloisCocycle K) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  c.cocycle.inflateClass c.extension

/-- The class of a bundled finite Galois cocycle is the inflated class of its cocycle. -/
@[simp]
theorem inflateClass_def (c : GaloisCocycle K) :
    c.inflateClass = c.cocycle.inflateClass c.extension :=
  (rfl)

end GaloisCocycle

end TauCeti
