/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Inflation
public import TauCeti.FieldTheory.GaloisCohomology.UnitsRestriction
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Subextension

/-!
# Inflation of compatible cocycles and field-extension restriction

Let `L/K` be a field extension, and identify its separable closure with that of `K`
using an embedding `σ : L → Kˢ`. Suppose that finite normal subextensions `E ⊆ Kˢ`
and `F ⊆ Lˢ` are related by a ring embedding compatible with that identification,
and that their automorphisms intertwine through a homomorphism `π : Aut_L(F) → Aut_K(E)`.
If two finite cocycles agree under this compatible pair, inflation of the cocycle over `F`
is restriction of the inflated class over `E`.

The comparison uses the existing `TwoCocycle.inflateClass` and `galoisResUnits`, including
the coefficient identification between the units of the two separable closures. It applies
to the restricted cocycle of an intermediate field, without requiring that intermediate
field to be normal over `K`.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

noncomputable section

namespace TauCeti

namespace TwoCocycle

open ContCohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [Normal K E]
  (F : IntermediateField L (SeparableClosure L)) [FiniteDimensional L F] [Normal L F]
  (ι : E →+* F) (π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E))
  (hι : ∀ x : E, (separableClosureRingEquiv K L σ).symm (E.val x) = F.val (ι x))
  (hπ : ∀ g x, ι (π g x) = g (ι x))
  (c : TwoCocycle K E) (d : TwoCocycle L F)
  (hd : ∀ g h, d.toFun g h = Units.map ι.toMonoidHom (c.toFun (π g) (π h)))

include hι hπ hd

/-- The inflated cocycles agree pointwise after restricting the group and identifying the
coefficient modules of the two separable closures. -/
theorem inflateZ2_restriction_apply (g h : AbsoluteGaloisGroup L) :
    unitsCoeffMap K L σ ((c.inflateZ2 E :
        AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K)
      ((absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K),
        (absoluteGaloisGroupEquivFixingSubgroup K L σ h : AbsoluteGaloisGroup K))) =
      (d.inflateZ2 F : _ → UnitsCoeff L) (g, h) := by
  apply Additive.toMul.injective
  apply Units.ext
  simp only [coe_inflateZ2, coe_toCocycles₂, inflate_toFun, toMul_unitsCoeffMap,
    toMul_ofMul, Units.coe_map, hd]
  rw [← restrictNormalHom_equivFixingSubgroup K L σ E F ι π hι hπ g,
    ← restrictNormalHom_equivFixingSubgroup K L σ E F ι π hι hπ h]
  exact hι _

/-- Inflation of a finite cocycle compatible with a field extension is the restriction of
the original inflated cohomology class, with the canonical units-coefficient transport. -/
theorem inflateClass_galoisResUnits :
    galoisResUnits K L σ 2 (c.inflateClass E) = d.inflateClass F := by
  -- Assemble local compactness directly; generic instance search explores expensive alternatives.
  have hloc (P : Type) [Field P] : LocallyCompactSpace (AbsoluteGaloisGroup P) :=
    have : R1Space (AbsoluteGaloisGroup P) := @T2Space.r1Space _ _ krullTopology_t2
    have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup P) :=
      ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
    WeaklyLocallyCompactSpace.locallyCompactSpace
  let := hloc K
  let := hloc L
  let φ : AbsoluteGaloisGroup L →ₜ* AbsoluteGaloisGroup K :=
    (ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
      (absoluteGaloisGroupEquivFixingSubgroup K L σ)
  have hf : ∀ g m, unitsCoeffMap K L σ (φ g • m) = g • unitsCoeffMap K L σ m :=
    unitsCoeffMap_smul K L σ
  rw [galoisResUnits_def, inflateClass_def, inflateClass_def]
  -- Apply the comparison equations as terms: this keeps the compatible-pair proof typed
  -- at its declared group map instead of unfolding subtype and linear-map coercions.
  refine (explicitH2AddEquivContinuousCohomology_map (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) φ (unitsCoeffMap K L σ) hf _).trans ?_
  apply congrArg (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup L) (UnitsCoeff L))
  refine (explicitMap2_mk _ _ _ _ φ (unitsCoeffMap K L σ)
    continuous_of_discreteTopology hf (c.inflateZ2 E)).trans ?_
  apply congrArg (H2pi (AbsoluteGaloisGroup L) (UnitsCoeff L))
  apply Subtype.ext
  funext p
  rcases p with ⟨g, h⟩
  exact (cocyclesMap2_apply _ _ _ _ φ (unitsCoeffMap K L σ)
    continuous_of_discreteTopology hf (c.inflateZ2 E) g h).trans
      (inflateZ2_restriction_apply σ E F ι π hι hπ c d hd g h)

end TwoCocycle

end TauCeti
