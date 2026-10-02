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
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent

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

Conversely, strict finite-quotient descent of continuous `2`-cocycles, followed by the infinite
Galois correspondence, realizes every continuous cocycle as the inflation of a cocycle on a finite
Galois subextension. Consequently every continuous cohomology class is the inflated class of a
bundled `GaloisCocycle`.

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

/-- The representative of the continuous cohomology class `inflateClass`. -/
theorem inflateClass_def (c : TwoCocycle K L) :
    c.inflateClass L =
      explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (H2pi _ _ (c.inflateZ2 L)) :=
  (rfl)

/-- The difference of inflated cohomologous cocycles is the inflation of their finite
coboundary, hence is a continuous coboundary. -/
private theorem inflateZ2_sub_mem_B2 {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    ((z.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) -
      w.inflateZ2 L) ∈ B2 (AbsoluteGaloisGroup K) (UnitsCoeff K) := by
  obtain ⟨b, hb⟩ := cohomologous_def.1 h.symm
  refine mem_B2_iff'.2 ⟨(fun σ : L ≃ₐ[K] L ↦
    Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom (b σ))) ∘
      AlgEquiv.restrictNormalHom L,
    continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous L),
    fun g k ↦ Additive.toMul.injective ?_⟩
  -- The inflated coboundary of `b` is the image of the finite coboundary `hb` under `Kˢ ⊇ L`.
  simp only [Function.comp_apply, toMul_add, toMul_sub, toMul_ofMul, Additive.toMul_smul,
    Pi.sub_apply, coe_inflateZ2, coe_toCocycles₂, inflate_toFun]
  rw [← IntermediateField.units_map_val_restrictNormalHom, ← AlgEquiv.smul_units_def, map_mul,
    ← map_div, ← map_mul, hb, map_div]

/-- Cohomologous crossed-product cocycles have the same class after inflation to continuous
cohomology. -/
theorem inflateClass_eq_of_cohomologous {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    z.inflateClass L = w.inflateClass L := by
  apply congrArg (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K))
  exact H2pi_eq_iff.2 (inflateZ2_sub_mem_B2 L h)

end Finite

section Refinement

variable {L} {M : IntermediateField K (SeparableClosure K)} [Normal K L] [Normal K M]
  (π : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hπι : ∀ g x, ι (π g x) = g (ι x))
  (hι : ∀ x, M.val (ι x) = L.val x)
include hπι hι

/-- Refining a normal subextension along a compatible pair `(π, ι)`, with `ι` compatible with the
inclusions into `Kˢ`, before inflation does not change the cocycle on the absolute Galois
group. -/
theorem inflate_comap (c : TwoCocycle K L) : (c.comap π ι hπι).inflate M = c.inflate L := by
  ext g k
  rw [inflate_toFun, comap_toFun, inflate_toFun, restrictNormalHom_of_compatible π ι hπι hι,
    restrictNormalHom_of_compatible π ι hπι hι]
  simpa using hι (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k))

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- Refining the finite normal subextension along a compatible pair does not change the inflated
continuous cocycle. -/
theorem inflateZ2_comap (c : TwoCocycle K L) :
    (c.comap π ι hπι).inflateZ2 M = c.inflateZ2 L :=
  Subtype.ext (by rw [coe_inflateZ2, coe_inflateZ2, inflate_comap π ι hπι hι])

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
    (DFunLike.congr_fun (IntermediateField.restrictNormalHom_val L) g)

/-- Inclusion of `Lˣ` in `(Kˢ)ˣ`, as an equivalence with the units fixed by
`Gal(Kˢ/L)`. -/
private def finiteLevelCoeffEquiv :
    Additive Lˣ ≃+
      FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K) :=
  embeddedUnitsEquivInvariants K L L.val

/-- Inclusion of `Lˣ` in `(Kˢ)ˣ`, viewed as an additive map into the invariants fixed by
`Gal(Kˢ/L)`. -/
private def finiteLevelCoeffHom :
    Additive Lˣ →+
      FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K) :=
  (finiteLevelCoeffEquiv L).toAddMonoidHom

/-- `finiteLevelCoeffHom` is the underlying map of `finiteLevelCoeffEquiv`. -/
private theorem finiteLevelCoeffHom_apply (b : Additive Lˣ) :
    finiteLevelCoeffHom L b = finiteLevelCoeffEquiv L b :=
  (rfl)

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
      rw [galoisQuotientHom_mk, ← IntermediateField.restrictNormalHom_val]
      apply Subtype.ext
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      exact embeddedUnitsEquivInvariants_restrictNormalHom_smul K L L.val g b

/-- The inverse quotient identification, bundled as a continuous homomorphism. -/
private def galoisQuotientHomInv :
    (L ≃ₐ[K] L) →ₜ* AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup :=
  { (quotientFixingSubgroupFieldRangeEquiv K L L.val).symm.toMonoidHom with
    continuous_toFun := continuous_of_discreteTopology }

/-- `galoisQuotientHomInv` is the inverse quotient identification. -/
private theorem galoisQuotientHomInv_apply (g : L ≃ₐ[K] L) :
    galoisQuotientHomInv L g = (quotientFixingSubgroupFieldRangeEquiv K L L.val).symm g :=
  (rfl)

/-- The inverse quotient identification cancels the forward identification. -/
private theorem galoisQuotientHomInv_apply_quotientEquiv
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup) :
    galoisQuotientHomInv L (quotientFixingSubgroupFieldRangeEquiv K L L.val q) = q := by
  rw [galoisQuotientHomInv_apply]
  exact (quotientFixingSubgroupFieldRangeEquiv K L L.val).symm_apply_apply q

/-- The inverse coefficient identification is equivariant along the inverse quotient
identification. -/
private theorem finiteLevelCoeffEquiv_symm_smul
    (g : L ≃ₐ[K] L)
    (b : FixedPoints.addSubgroup
      (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K)) :
    (finiteLevelCoeffEquiv L).symm
        (galoisQuotientHomInv L g • b) =
      g • (finiteLevelCoeffEquiv L).symm b := by
  let φ : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup ≃*
      (L ≃ₐ[K] L) :=
    quotientFixingSubgroupFieldRangeEquiv K L L.val
  rw [galoisQuotientHomInv_apply]
  refine AddEquiv.symm_map_smul_of_map_mulEquiv_smul (finiteLevelCoeffEquiv L) φ
    (fun q m ↦ ?_) g b
  have hφ : φ q = galoisQuotientHom L q := (galoisQuotientHom_apply L q).symm
  rw [hφ, ← finiteLevelCoeffHom_apply, ← finiteLevelCoeffHom_apply]
  exact finiteLevelCoeffHom_smul L q m

/-- The inverse coefficient identification, followed by inclusion in the separable closure,
recovers the underlying invariant unit. -/
private theorem ofMul_unitsMap_finiteLevelCoeffEquiv_symm
    (b : FixedPoints.addSubgroup
      (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K)) :
    Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
        ((finiteLevelCoeffEquiv L).symm b).toMul) = (b : UnitsCoeff K) :=
  (coe_finiteLevelCoeffHom L _).symm.trans <| by
    rw [finiteLevelCoeffHom_apply, AddEquiv.apply_symm_apply]

/-- A cocycle at the finite quotient associated to `L` as a crossed-product cocycle of
`Gal(L/K)`. -/
private def ofFiniteLevelZ2
    (z : Z2 (AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K))) : TwoCocycle K L :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  letI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  let z' := cocyclesMap2 _ _ _ _ (galoisQuotientHomInv L)
    (finiteLevelCoeffEquiv L).symm.toAddMonoidHom
    continuous_of_discreteTopology (finiteLevelCoeffEquiv_symm_smul L) z
  { toFun := fun g h ↦ Additive.toMul ((z' : _ → Additive Lˣ) (g, h))
    isMulCocycle₂ := fun g h j ↦ by
      apply Additive.ofMul.injective
      simpa only [ofMul_mul, ofMul_toMul, Additive.ofMul_smul] using
        (mem_Z2_iff.1 z'.2).2 g h j }

/-- The crossed-product cocycle obtained from a finite-level cocycle evaluates by pulling the
automorphisms back through the quotient identification and the coefficient through the invariant
unit identification. -/
private theorem ofFiniteLevelZ2_toFun
    (z : Z2 (AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K))) (g h : L ≃ₐ[K] L) :
    (ofFiniteLevelZ2 L z).toFun g h =
      Additive.toMul ((finiteLevelCoeffEquiv L).symm
        ((z : _ → _) (galoisQuotientHomInv L g, galoisQuotientHomInv L h))) :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  haveI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  congrArg Additive.toMul <|
    cocyclesMap2_apply _ _ _ _ _ _ continuous_of_discreteTopology
      (finiteLevelCoeffEquiv_symm_smul L) z g h

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

/-- Converting a finite-level cocycle to a crossed-product cocycle and back recovers the
original finite-level cocycle. -/
private theorem finiteLevelZ2_ofFiniteLevelZ2
    (z : Z2 (AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K))) :
    (ofFiniteLevelZ2 L z).finiteLevelZ2 L = z := by
  apply Subtype.ext
  funext p
  obtain ⟨q, r⟩ := p
  apply Subtype.ext
  rw [finiteLevelZ2_apply, ofFiniteLevelZ2_toFun]
  rw [galoisQuotientHomInv_apply_quotientEquiv, galoisQuotientHomInv_apply_quotientEquiv]
  exact ofMul_unitsMap_finiteLevelCoeffEquiv_symm L ((z : _ → _) (q, r))

/-- The class of a crossed-product cocycle at the finite quotient `G_K/G_L`. -/
def finiteLevelClass (c : TwoCocycle K L) :
    H2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K)) :=
  H2pi _ _ (c.finiteLevelZ2 L)

/-- The representative of the finite-level cohomology class `finiteLevelClass`. -/
theorem finiteLevelClass_def (c : TwoCocycle K L) :
    c.finiteLevelClass L = H2pi _ _ (c.finiteLevelZ2 L) :=
  (rfl)

/-- Pointwise, inflating the finite-level cocycle along the quotient map recovers the directly
inflated cocycle. -/
private theorem cocyclesMap2_finiteLevelZ2_apply (c : TwoCocycle K L)
    (g h : AbsoluteGaloisGroup K) :
    (cocyclesMap2 _ _ _ _
      (ContinuousMonoidHom.quotientMk
        (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup
        (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K)).subtype
      (continuous_fixedPoints_addSubgroup_subtype _ _ _)
      (subtype_quotientMk_smul _ _ _)
      (c.finiteLevelZ2 L) :
        AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) (g, h) =
      (c.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K)
        (g, h) := by
  rw [cocyclesMap2_apply, AddSubgroup.subtype_apply, ContinuousMonoidHom.quotientMk_apply,
    ContinuousMonoidHom.quotientMk_apply, finiteLevelZ2_apply, ← galoisQuotientHom_apply,
    ← galoisQuotientHom_apply, galoisQuotientHom_mk, galoisQuotientHom_mk, coe_inflateZ2]
  simp only [coe_toCocycles₂, inflate_toFun]

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
  exact cocyclesMap2_finiteLevelZ2_apply L c g h

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

/-! ### Exhaustion by finite Galois cocycles -/

/-- **Every continuous `2`-cocycle of the absolute Galois group is inflated from a finite Galois
subextension.** The equality is on cocycle representatives: no coboundary is subtracted.

The finite subextension is the fixed field of the open normal subgroup supplied by strict
finite-quotient descent. -/
theorem exists_galoisCocycle_inflateZ2
    (z : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ∃ c : GaloisCocycle K, c.cocycle.inflateZ2 c.extension = z := by
  obtain ⟨U, y, hy⟩ := exists_openNormalSubgroup_descendZ2 z
  obtain ⟨L, _, _, rfl⟩ := exists_galoisOpenNormalSubgroup_eq U
  let c : GaloisCocycle K :=
    { extension := L
      cocycle := TwoCocycle.ofFiniteLevelZ2 L y }
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  have hinfl := TwoCocycle.cocyclesMap2_finiteLevelZ2_apply L c.cocycle g h
  rw [TwoCocycle.finiteLevelZ2_ofFiniteLevelZ2] at hinfl
  rw [← hinfl, cocyclesMap2_apply]
  exact hy g h

/-- **Every continuous degree-two class of the absolute Galois group is inflated from a finite
Galois cocycle.** -/
theorem exists_galoisCocycle_inflateClass
    (x : continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) :
    ∃ c : GaloisCocycle K, c.inflateClass = x := by
  obtain ⟨y, rfl⟩ :=
    (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)).surjective x
  induction y using QuotientAddGroup.induction_on with
  | _ z =>
      obtain ⟨c, hc⟩ := exists_galoisCocycle_inflateZ2 z
      refine ⟨c, ?_⟩
      rw [GaloisCocycle.inflateClass_def, TwoCocycle.inflateClass_def, hc]
      rw [QuotientAddGroup.mk'_apply]

end TauCeti
