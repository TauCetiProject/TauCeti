/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Inflation from the layer of a finite Galois extension into the Brauer group

For a finite Galois extension `L/K` presented by an embedding `ι : L →ₐ[K] Kˢ`, the layer of
`TauCeti.ClassFieldTheory.unitsFormation K` cut out by `L` has two inflations into `Br K`: the
layer inflation `brInfl`, and the relative inflation `relBrInfl K L ι` of the concrete Galois
cohomology `H²(Gal(L/K), Lˣ)`. This file proves that the identification
`TauCeti.ClassFieldTheory.layerCohomologyEquiv ι` of the two cohomology groups intertwines them.
Nothing here uses that `K` is local.

## Main results

* `TauCeti.ClassFieldTheory.embeddedUnitsEquivInvariants_layerCoefficientEquiv`: the concrete
  coefficient comparison agrees with the embedding of `Lˣ` into `(Kˢ)ˣ`.
* `TauCeti.ClassFieldTheory.relBrInfl_layerCohomologyEquiv`: the concrete cohomology
  identification of the layer is compatible with inflation into `Br K`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter X, §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The concrete coefficient comparison agrees with the embedding of `Lˣ` into the units of the
separable closure. -/
theorem embeddedUnitsEquivInvariants_layerCoefficientEquiv
    (ι : L →ₐ[K] SeparableClosure K)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)) :
    ((embeddedUnitsEquivInvariants K L ι
        (Rep.toAdditive (layerCoefficientEquiv ι x)) :
      FixedPoints.addSubgroup ι.fieldRange.fixingSubgroup (UnitsCoeff K)) : UnitsCoeff K) =
      (unitsCoeffEquivUnitsFormation K).symm
        ((x : (unitsFormation K).level
          (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).top) :
            (unitsFormation K).toRep.V) := by
  rw [embeddedUnitsEquivInvariants_apply]
  apply Additive.toMul.injective
  rw [toMul_coe_embeddedUnitsInvariants]
  exact congrArg Additive.toMul (layerCoefficientEquiv_apply_coe ι x)

/-- The concrete cohomology identification of a finite Galois layer is compatible with inflation
into the Brauer group. -/
theorem relBrInfl_layerCohomologyEquiv (ι : L →ₐ[K] SeparableClosure K)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).H (unitsFormation K) 2) :
    relBrInfl K L ι (layerCohomologyEquiv ι 2 x) =
      brInfl (fixingOpenNormalSubgroup K L) x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    rw [layerCohomologyEquiv_apply, groupCohomology.H2π_comp_map_apply, relBrInfl_H2π]
    symm
    apply brInfl_H2π
    intro g h
    rw [relBrCocycle_apply, _root_.TauCeti.groupCohomology.mapCocycles₂_apply,
      layerCoefficientHom_apply]
    simp only [MonoidHom.coe_ofClass, layerGalEquiv_symm_restrictNormalHom]
    exact embeddedUnitsEquivInvariants_layerCoefficientEquiv K L ι (c _)

end TauCeti.ClassFieldTheory
