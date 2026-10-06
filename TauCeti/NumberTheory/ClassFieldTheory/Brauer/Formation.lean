/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Inflation from the layers of the units formation into the Brauer group

For a field `K` with separable closure `Kˢ` and absolute Galois group `G_K = Gal(Kˢ/K)`, the
layers `V ◁ G_K` of the formation `TauCeti.ClassFieldTheory.unitsFormation K` are the finite
layers of the Brauer group `Br K = H²(G_K, (Kˢ)ˣ)`. This file gives **the finite-layer
description of the Brauer group** for this formation: the second cohomology of the layer `V ◁ G_K`
of an open normal subgroup `V` inflates into `Br K` (`brInfl`); the inflation is injective
(`brInfl_injective`), and every Brauer class is inflated from some layer (`exists_brInfl_eq`).
This is the map through which the invariant of the Brauer group is to be transported to the
finite layers.

## Main definitions

* `TauCeti.ClassFieldTheory.layerBrLevelEquiv V`: the second cohomology of the layer `V ◁ G_K`
  as the explicit `H²(G_K ⧸ V, ((Kˢ)ˣ)^V)` of the finite level `V`.
* `TauCeti.ClassFieldTheory.brInfl V`: inflation from the layer `V ◁ G_K` into `Br K`.

## Main results

* `TauCeti.ClassFieldTheory.brInfl_injective`: inflation from a layer into `Br K` is injective.
* `TauCeti.ClassFieldTheory.brInfl_H2π`: on the class of a layer cocycle, inflation is the Brauer
  class of the inflated cocycle on `G_K`.
* `TauCeti.ClassFieldTheory.exists_brInfl_eq`: every Brauer class is inflated from a layer.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter X, §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.groupCohomology ContCohomology

variable {K : Type} [Field K]

/-! ### Inflation from the layers of open normal subgroups into the Brauer group -/

section Inflation

variable (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))

/-- The level of `V` in `unitsFormation K`, read through the coefficient dictionary, is the
subgroup of `(Kˢ)ˣ` fixed by `V`. -/
private theorem map_level_unitsFormation :
    ((unitsFormation K).level V.toOpenSubgroup).toAddSubgroup.map
        (unitsCoeffEquivUnitsFormation K).symm =
      FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K) := by
  ext y
  rw [← AddEquiv.toAddMonoidHom_eq_coe, AddSubgroup.mem_map_equiv, AddEquiv.symm_symm,
    Submodule.mem_toAddSubgroup, Formation.mem_level, FixedPoints.mem_addSubgroup, Subtype.forall]
  refine forall₂_congr fun v _ => ?_
  rw [← unitsCoeffEquivUnitsFormation_smul, (unitsCoeffEquivUnitsFormation K).injective.eq_iff]
  rfl

/-- The coefficient module of the layer `V ◁ G_K` is the fixed points of `V` in `(Kˢ)ˣ`. -/
private def ofOpenNormalRepEquiv :
    ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)).V ≃ₗ[ℤ]
      FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K) :=
  (LinearEquiv.ofEq _ _ (congrArg (unitsFormation K).level (NormalLayer.top_ofOpenNormal V))).trans
    (((unitsCoeffEquivUnitsFormation K).symm.addSubgroupMap _).trans
      (AddEquiv.addSubgroupCongr (map_level_unitsFormation V))).toIntLinearEquiv

private theorem ofOpenNormalRepEquiv_apply_coe
    (x : ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)).V) :
    ((ofOpenNormalRepEquiv V x : FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K)) :
      UnitsCoeff K) = (unitsCoeffEquivUnitsFormation K).symm
        ((x : (unitsFormation K).level (NormalLayer.ofOpenNormal V).top) :
          (unitsFormation K).toRep.V) :=
  by
    rw [ofOpenNormalRepEquiv, LinearEquiv.trans_apply, AddEquiv.coe_toIntLinearEquiv,
      AddEquiv.trans_apply, AddEquiv.addSubgroupCongr_apply,
      AddEquiv.coe_addSubgroupMap_apply, LinearEquiv.coe_ofEq_apply]

/-- **The second cohomology of the layer `V ◁ G_K` is that of the finite level `V`**: Mathlib's
`H²(G_K ⧸ V, ((Kˢ)ˣ)^V)` of the layer, carried along `NormalLayer.galOfOpenNormalEquiv`, is the
explicit `H²` of the discrete finite level by
`TauCeti.ContCohomology.explicitH2IsoGroupCohomology`. The coefficient modules are the same
subgroup of `(Kˢ)ˣ`, the level of `V`. -/
def layerBrLevelEquiv :
    (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2 ≃+
      H2 (AbsoluteGaloisGroup K ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K)) :=
  (groupCohomology.mapIso (NormalLayer.galOfOpenNormalEquiv V) (ofOpenNormalRepEquiv V)
    (fun g => by
      induction g using QuotientGroup.induction_on with
      | H u =>
        refine LinearMap.ext fun x =>
          Subtype.ext ((ofOpenNormalRepEquiv_apply_coe V _).trans ?_)
        rw [NormalLayer.rep_ρ_mk_apply_coe, LinearMap.comp_apply,
          NormalLayer.galOfOpenNormalEquiv_mk]
        refine ((AddEquiv.symm_apply_eq _).2 ?_).trans (congrArg
          (fun y : UnitsCoeff K => (u : AbsoluteGaloisGroup K) • y)
          (ofOpenNormalRepEquiv_apply_coe V x).symm)
        rw [unitsCoeffEquivUnitsFormation_smul, AddEquiv.apply_symm_apply])
    2).toLinearEquiv.toAddEquiv.trans
    (explicitH2IsoGroupCohomology _ _).symm

/-- **Inflation from the layer `V ◁ G_K` into the Brauer group** `Br K = H²(G_K, (Kˢ)ˣ)`: the
identification `layerBrLevelEquiv` of the layer's `H²` with the level of `V`, followed by
`brLevelInfl`. It is injective (`brInfl_injective`), and every Brauer class is inflated from some
layer (`exists_brInfl_eq`). -/
def brInfl : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2 →+ Br K :=
  (brLevelInfl V).comp (layerBrLevelEquiv V).toAddMonoidHom

/-- `brInfl V` is `brLevelInfl` after the identification `layerBrLevelEquiv`. -/
@[simp]
theorem brInfl_apply (x : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2) :
    brInfl V x = brLevelInfl V (layerBrLevelEquiv V x) :=
  (rfl)

/-- **Inflation from a layer into the Brauer group is injective**, by Hilbert 90 for `V`
(`brLevelInfl_injective`). -/
theorem brInfl_injective : Function.Injective (brInfl V) :=
  (brLevelInfl_injective V).comp (layerBrLevelEquiv V).injective

/-- Inflation of the explicit class of a layer cocycle pulled back along a compatible pair that
inverts `galOfOpenNormalEquiv` on Galois groups and is the coefficient dictionary on values. -/
private theorem explicitInfl2_explicitH2IsoGroupCohomology_symm_H2π
    (f : AbsoluteGaloisGroup K ⧸ V.toSubgroup →* (NormalLayer.ofOpenNormal V).Gal)
    (φ : Rep.res f ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)) ⟶
      Rep.ofDistribMulAction ℤ (AbsoluteGaloisGroup K ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K)))
    (hf : ∀ q, f q = (NormalLayer.galOfOpenNormalEquiv V).symm q)
    (hφ : ∀ x, (φ.hom x : FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K)) =
      ofOpenNormalRepEquiv V x)
    (c : cocycles₂ ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)))
    (z : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K))
    (hz : ∀ g h : AbsoluteGaloisGroup K,
      (z : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) (g, h) =
        (unitsCoeffEquivUnitsFormation K).symm
          (c ((NormalLayer.galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup),
            (NormalLayer.galOfOpenNormalEquiv V).symm (h : AbsoluteGaloisGroup K ⧸ V.toSubgroup)) :
            (unitsFormation K).level (NormalLayer.ofOpenNormal V).top)) :
    explicitInfl2 _ (UnitsCoeff K) V.toSubgroup ((explicitH2IsoGroupCohomology _ _).symm
      (H2π _ (mapCocycles₂ f φ c))) = (z : H2 _ _) := by
  rw [explicitH2IsoGroupCohomology_symm_H2π, explicitInfl2_mk]
  refine congrArg _ (Subtype.ext (funext fun p =>
    (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).trans ?_))
  rw [Z2AddEquivCocycles₂_symm_coe, TauCeti.groupCohomology.mapCocycles₂_apply]
  refine (congrArg Subtype.val (hφ _)).trans ?_
  rw [ofOpenNormalRepEquiv_apply_coe, hf, hf, ContinuousMonoidHom.quotientMk_apply,
    ContinuousMonoidHom.quotientMk_apply, hz]

/-- **Inflation into the Brauer group on cocycle classes.** `brInfl V` sends the class of a
`2`-cocycle `c` of the layer `V ◁ G_K` to the Brauer class of every continuous `2`-cocycle `z` on
`G_K` whose value at `(g, h)` is the value of `c` at the classes of `g` and `h` in
`G_K ⧸ V`, read in `(Kˢ)ˣ`. -/
theorem brInfl_H2π (c : cocycles₂ ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)))
    (z : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K))
    (hz : ∀ g h : AbsoluteGaloisGroup K,
      (z : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) (g, h) =
        (unitsCoeffEquivUnitsFormation K).symm
          (c ((NormalLayer.galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup),
            (NormalLayer.galOfOpenNormalEquiv V).symm (h : AbsoluteGaloisGroup K ⧸ V.toSubgroup)) :
            (unitsFormation K).level (NormalLayer.ofOpenNormal V).top)) :
    brInfl V (H2π _ c) = unitsRepH2Equiv K (z : H2 _ _) := by
  rw [brInfl_apply, brLevelInfl_apply]
  refine congrArg (unitsRepH2Equiv K) (Eq.trans (congrArg (fun y => explicitInfl2 _ (UnitsCoeff K)
    V.toSubgroup ((explicitH2IsoGroupCohomology _ _).symm y)) (groupCohomology.H2π_comp_map_apply
      (NormalLayer.galOfOpenNormalEquiv V).symm.toMonoidHom _ c))
    -- The pair is the one defining `layerBrLevelEquiv`, so both hypotheses hold by definition.
    (explicitInfl2_explicitH2IsoGroupCohomology_symm_H2π V _ _ (fun _ => rfl) (fun _ => rfl) c z
      hz))

variable (K) in
/-- **Every Brauer class is inflated from a layer** `V ◁ G_K` of the formation of units
(`exists_brLevelInfl_eq`). -/
theorem exists_brInfl_eq (x : Br K) :
    ∃ (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
      (y : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2), brInfl V y = x := by
  obtain ⟨V, y, rfl⟩ := exists_brLevelInfl_eq x
  exact ⟨V, (layerBrLevelEquiv V).symm y, by rw [brInfl_apply, AddEquiv.apply_symm_apply]⟩

end Inflation

end TauCeti.ClassFieldTheory
