/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.LayerInvariant
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ClassFormation

/-!
# The local class formation

Let `K` be a nonarchimedean local field with separable closure `Kˢ` and absolute Galois group
`G_K`. The formation `TauCeti.ClassFieldTheory.unitsFormation K` of the multiplicative group
`(Kˢ)ˣ`, written additively, is a **class formation** (`localClassFormation`): its finite normal
layers `V ◁ U`, the finite Galois extensions `E'/E` inside `Kˢ`, satisfy the axioms of
`TauCeti.ClassFieldTheory.ClassFormation` with invariant map the invariant
`TauCeti.ClassFieldTheory.layerInv` of the layer, that is, inflation into `Br E = H²(U, (Kˢ)ˣ)`
followed by the local invariant of `E`. The axioms come from:

* Hilbert 90, for the vanishing of `H¹` and the injectivity of inflation;
* the local invariant `TauCeti.ClassFieldTheory.invMap` and its restriction and corestriction
  squares, for the compatibility with restriction, inflation and conjugation;
* the local `H²` bound, through `invMap` being an isomorphism, for the range of the invariant.

On a layer `V ◁ G_K` over `K` itself, the invariant of the class formation is the local invariant
of `K` on the Brauer class inflated by `TauCeti.ClassFieldTheory.brInfl`
(`localClassFormation_inv`), so the invariant of the class formation and the invariant of the
local Brauer group carry one normalization.

## Main definitions

* `TauCeti.ClassFieldTheory.localClassFormation K`: the class formation of the units of a
  separable closure of a nonarchimedean local field.

## Main results

* `TauCeti.ClassFieldTheory.localClassFormation_inv`: on a layer over `K`, the invariant of the
  class formation is `invMap K ∘ brInfl`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter XI, §§1–3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.groupCohomology ContCohomology

/-! ### Layers over `K` and the Brauer group -/

section OfOpenNormal

variable {K : Type} [Field K]

/-- The identification `g ↦ g` of `G_K` with the ground subgroup `⊤` of the layer `V ◁ G_K`. -/
private def groundOfOpenNormalHom (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    AbsoluteGaloisGroup K →ₜ* (NormalLayer.ofOpenNormal V).ground.toSubgroup where
  toFun g := ⟨g, (NormalLayer.ground_ofOpenNormal V).symm ▸ OpenSubgroup.mem_top g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk _

/-- The class of `g ∈ ⊤` in the Galois group of `V ◁ G_K` corresponds to the class of `g` in
`G_K ⧸ V`. -/
private theorem coe_groundOfOpenNormalHom (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (g : AbsoluteGaloisGroup K) :
    ((groundOfOpenNormalHom V g : (NormalLayer.ofOpenNormal V).ground.toSubgroup) :
      (NormalLayer.ofOpenNormal V).Gal) =
      (NormalLayer.galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup) :=
  ((MulEquiv.symm_apply_eq _).2
    (NormalLayer.galOfOpenNormalEquiv_mk V (groundOfOpenNormalHom V g)).symm).symm

/-- The identification of `G_K` with `⊤` and the identity of `(Kˢ)ˣ` form a compatible pair. -/
private theorem groundOfOpenNormalHom_smul (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (g : AbsoluteGaloisGroup K) (m : UnitsCoeff K) :
    AddMonoidHom.id (UnitsCoeff K) (groundOfOpenNormalHom V g • m) =
      g • AddMonoidHom.id (UnitsCoeff K) m := by
  rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, Subgroup.smul_def]
  -- The underlying element of `groundOfOpenNormalHom V g` is `g` by definition.
  rfl

/-- On a layer `V ◁ G_K`, inflation to the ground subgroup `⊤` is the restriction to `⊤` of the
class on `G_K` obtained by pulling the inflated cocycle back along `G_K ≃ ⊤`. -/
private theorem explicitInfl2_ofOpenNormal_H2π (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (c : cocycles₂ ((NormalLayer.ofOpenNormal V).rep (unitsFormation K))) :
    (NormalLayer.ofOpenNormal V).explicitInfl2 (unitsCoeffEquivUnitsFormation K)
        (unitsCoeffEquivUnitsFormation_smul K) (H2π _ c) =
      explicitRes2 (AbsoluteGaloisGroup K) (UnitsCoeff K) _
        (cocyclesMap2 _ _ _ _ (groundOfOpenNormalHom V) (AddMonoidHom.id _) continuous_id
          (groundOfOpenNormalHom_smul V)
          ((NormalLayer.ofOpenNormal V).inflCocycle2 (unitsCoeffEquivUnitsFormation K)
            (unitsCoeffEquivUnitsFormation_smul K) c) :
        H2 _ _) := by
  rw [NormalLayer.explicitInfl2_H2π, explicitRes2_mk]
  refine congrArg _ (Subtype.ext (funext fun p => Eq.symm ?_))
  rw [cocyclesMap2_apply, cocyclesMap2_apply]
  -- `groundOfOpenNormalHom V u = u` for `u ∈ ⊤`, by definition and subtype eta.
  rfl

end OfOpenNormal

/-! ### The local class formation -/

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]


/-- **The local class formation**: the formation of the units of a separable closure of a
nonarchimedean local field `K` is a class formation, with the invariant `layerInv` of a layer as
invariant map. -/
def localClassFormation : ClassFormation (unitsFormation K) where
  subsingleton_h1 := subsingleton_h1_unitsFormation
  inv := layerInv K
  inv_injective := layerInv_injective K
  range_inv := range_layerInv K
  inv_restrict := layerInv_cohomologyRes K
  inv_infl := layerInv_cohomologyInfl K
  inv_conj L g x := layerInv_conjugateCohomologyIso K L g x

/-- The invariant map of the local class formation is the invariant of a layer. -/
@[simp]
theorem localClassFormation_inv_apply (L : NormalLayer (AbsoluteGaloisGroup K))
    (x : L.H (unitsFormation K) 2) : (localClassFormation K).inv L x = layerInv K L x :=
  (rfl)

/-- **The invariant of the local class formation is the local Brauer invariant**: on the layer
`V ◁ G_K` of an open normal subgroup, the invariant of a class is the local invariant `invMap K`
of its inflation `brInfl V` into `Br K`. -/
theorem localClassFormation_inv (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2) :
    (localClassFormation K).inv (NormalLayer.ofOpenNormal V) x = invMap K (brInfl V x) := by
  induction x using H2_induction_on with
  | h c =>
    have hindex : (NormalLayer.ofOpenNormal V).ground.toSubgroup.index = 1 := by
      rw [NormalLayer.ground_ofOpenNormal, OpenSubgroup.toSubgroup_top, Subgroup.index_top]
    rw [localClassFormation_inv_apply, layerInv_apply, explicitInfl2_ofOpenNormal_H2π,
      subgroupInvMap_explicitRes2]
    refine (congrArg (· • _) hindex).trans ((one_smul _ _).trans
      (congrArg (invMap K) (brInfl_H2π V c _ fun g h => ?_).symm))
    rw [cocyclesMap2_apply, AddMonoidHom.id_apply, NormalLayer.inflCocycle2_apply]
    simp only [coe_groundOfOpenNormalHom]

end TauCeti.ClassFieldTheory
