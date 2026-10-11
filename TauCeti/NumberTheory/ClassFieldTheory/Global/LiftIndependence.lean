/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LayerInvariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftingObstruction
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Naturality

/-!
# Lifts of idele-class cohomology to the ideles and their local invariants

Let `K` be a number field and `L/F` a finite Galois layer inside `Kˢ`. The global invariant of a
class of `H²(Gal(L/F), C_L)` is to be the sum of the local invariants `ideleSumLocalInv` of a lift
of it to `H²(Gal(L'/F), I_{L'})`, for a refinement `L'/F` of the layer where such a lift exists.
This file shows that two such lifts, to two refinements, have the same sum of local invariants up
to the sum of the local invariants of a global Brauer class.

The comparison runs through the multiplicative group. The sum of the local invariants of the image
of a class `y ∈ H²(Gal(L/F), Lˣ)` under the principal ideles is the sum of the local invariants of
a global Brauer class, namely of the class of `y` in `Br K` obtained by inflation to the ground
subgroup and corestriction to `G_K` (`ideleSumLocalInv_multiplicativeToIdeleH2`). This holds
because inflation and corestriction are natural in the coefficient module
(`ideleLayerCorInfl_multiplicativeToIdeleH2`), and because the localization of idele cohomology
extends the localization of Brauer classes along the principal ideles
(`ideleLocalization_principalIdele`).

Two lifts `y₁, y₂` to refinements `L₁/F` and `L₂/F` of one class are inflated to a common
refinement `M/F` (`LayerRefinement.exists_commonRefinement`). There they have the same image in
`H²(Gal(M/F), C_M)`, since the comparison with idele classes commutes with inflation
(`ideleToClassH2_cohomologyInfl`), so they differ by the image of a class of
`H²(Gal(M/F), Mˣ)` (`ker_ideleToClassH2`). Since inflation preserves the sum of the local
invariants (`ideleSumLocalInv_infl`), the sums for `y₁` and `y₂` differ by the sum of the local
invariants of a global Brauer class
(`exists_ideleSumLocalInv_eq_add_sumLocalInv_of_ideleToClassH2_eq`). Together with the reciprocity
law of the global Brauer sequence, that the local invariants of a global Brauer class sum to zero,
this makes the sum of the local invariants of a lift independent of the lift and of the refinement.

## Main definitions

* `TauCeti.ClassFieldTheory.unitsLayerCorInfl K L`: the class over `G_K` of a class of
  `H²(Gal(L/F), Lˣ)`.

## Main results

* `TauCeti.ClassFieldTheory.ideleLayerCorInfl_multiplicativeToIdeleH2`: the class over `G_K` of
  the image of a multiplicative class under the principal ideles is the image of its class over
  `G_K`.
* `TauCeti.ClassFieldTheory.ideleSumLocalInv_multiplicativeToIdeleH2`: the sum of the local
  invariants of the image of a multiplicative class is that of a global Brauer class.
* `TauCeti.ClassFieldTheory.exists_ideleSumLocalInv_eq_add_sumLocalInv_of_ideleToClassH2_eq`: two
  lifts of one idele-class class to refinements of its layer have the same sum of local invariants
  up to the sum of the local invariants of a global Brauer class.

## References

* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public noncomputable section

open CategoryTheory TauCeti.ContCohomology

namespace TauCeti.ClassFieldTheory

/-! ### The class over the absolute Galois group of a multiplicative class -/

section Field

variable (K : Type) [Field K] (L : NormalLayer (AbsoluteGaloisGroup K))

/-- **The class over `G_K` of a units-layer class**: for a layer `V ◁ U` of the units formation,
inflation `H²(U ⧸ V, ((Kˢ)ˣ)^V) → H²(U, (Kˢ)ˣ)` followed by corestriction from the open subgroup
`U` to `G_K`. In field notation it carries `H²(Gal(L/F), Lˣ)` to `Br K`. -/
def unitsLayerCorInfl : L.H (unitsFormation K) 2 →+ H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  (explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) L.ground.toSubgroup L.ground.isOpen).comp
    (L.explicitInfl2 (unitsCoeffEquivUnitsFormation K) (unitsCoeffEquivUnitsFormation_smul K))

/-- The class over `G_K` of a units-layer class is the corestriction of its inflation. -/
theorem unitsLayerCorInfl_apply (y : L.H (unitsFormation K) 2) :
    unitsLayerCorInfl K L y =
      explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) L.ground.toSubgroup L.ground.isOpen
        (L.explicitInfl2 (unitsCoeffEquivUnitsFormation K) (unitsCoeffEquivUnitsFormation_smul K)
          y) :=
  (rfl)

end Field

variable (K : Type) [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))

/-- **Inflation and corestriction commute with the principal ideles**: the class over `G_K` of the
image of `y ∈ H²(Gal(L/F), Lˣ)` in `H²(Gal(L/F), I_L)` is the image along the principal ideles
`(Kˢ)ˣ → I_{Kˢ}` of the class of `y` over `G_K`. -/
theorem ideleLayerCorInfl_multiplicativeToIdeleH2 (y : L.H (unitsFormation K) 2) :
    ideleLayerCorInfl K L (multiplicativeToIdeleH2 K L y) =
      explicitCoeff2 (AbsoluteGaloisGroup K) (UnitsCoeff K) (principalIdele K)
        continuous_of_discreteTopology (unitsLayerCorInfl K L y) := by
  rw [ideleLayerCorInfl_apply, unitsLayerCorInfl_apply, multiplicativeToIdeleH2_apply,
    L.explicitInfl2_map_repMap _ _ _ _ (principalIdeleHom K) (principalIdele K)
      (principalIdeleHom_hom_apply K),
    explicitCor2_explicitMap2_id _ _ _ _ _ _ (principalIdele K).map_smul,
    explicitCoeff2_eq_explicitMap2]

/-- **The local invariants of a principal class are those of a global Brauer class**: the sum of
the local invariants of the image of `y ∈ H²(Gal(L/F), Lˣ)` in `H²(Gal(L/F), I_L)` is the sum of
the local invariants of the class of `y` in `Br K`. -/
theorem ideleSumLocalInv_multiplicativeToIdeleH2 (y : L.H (unitsFormation K) 2) :
    ideleSumLocalInv K L (multiplicativeToIdeleH2 K L y) =
      sumLocalInv K (brLocalization K (unitsRepH2Equiv K (unitsLayerCorInfl K L y))) := by
  rw [ideleSumLocalInv_apply, ideleLayerCorInfl_multiplicativeToIdeleH2,
    ideleLocalization_principalIdele]

/-! ### Two lifts of one idele-class class -/

variable {K} in
/-- The image in idele-class cohomology of the inflation of a lift is the inflation of the lifted
class. -/
private theorem ideleToClassH2_cohomologyInfl_of_eq
    {Lay Lay' M : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement Lay Lay') (S : LayerRefinement Lay' M) {x : Lay.H (globalFormation K) 2}
    {y : Lay'.H (ideleFormation K) 2}
    (h : ideleToClassH2 K Lay' y = T.cohomologyInfl (globalFormation K) 2 x) :
    ideleToClassH2 K M (S.cohomologyInfl (ideleFormation K) 2 y) =
      (T.trans S).cohomologyInfl (globalFormation K) 2 x := by
  rw [ideleToClassH2_cohomologyInfl, h, LayerRefinement.cohomologyInfl_trans T S,
    ConcreteCategory.comp_apply]

/-- **Two lifts of one idele-class class have the same local invariants up to a global class.** Let
`y₁` and `y₂` lift the inflations of one class `x ∈ H²(Gal(L/F), C_L)` to refinements `L₁/F` and
`L₂/F` of its layer. Then the sums of the local invariants of `y₁` and `y₂` differ by the sum of
the local invariants of a global Brauer class `b ∈ Br K`. -/
theorem exists_ideleSumLocalInv_eq_add_sumLocalInv_of_ideleToClassH2_eq
    {Lay Lay₁ Lay₂ : NormalLayer (AbsoluteGaloisGroup K)}
    (T₁ : LayerRefinement Lay Lay₁) (T₂ : LayerRefinement Lay Lay₂)
    (x : Lay.H (globalFormation K) 2)
    (y₁ : Lay₁.H (ideleFormation K) 2) (y₂ : Lay₂.H (ideleFormation K) 2)
    (h₁ : ideleToClassH2 K Lay₁ y₁ = T₁.cohomologyInfl (globalFormation K) 2 x)
    (h₂ : ideleToClassH2 K Lay₂ y₂ = T₂.cohomologyInfl (globalFormation K) 2 x) :
    ∃ b : Br K, ideleSumLocalInv K Lay₁ y₁ =
      ideleSumLocalInv K Lay₂ y₂ + sumLocalInv K (brLocalization K b) := by
  -- Inflate both lifts to a common refinement `M/F`, where they have the same image in
  -- `H²(Gal(M/F), C_M)` and so differ by the image of a class of `H²(Gal(M/F), Mˣ)`.
  obtain ⟨M, S₁, S₂⟩ :=
    LayerRefinement.exists_commonRefinement (T₁.same_ground.symm.trans T₂.same_ground)
  have hker : S₁.cohomologyInfl (ideleFormation K) 2 y₁ -
      S₂.cohomologyInfl (ideleFormation K) 2 y₂ ∈ (ideleToClassH2 K M).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, ideleToClassH2_cohomologyInfl_of_eq T₁ S₁ h₁,
      ideleToClassH2_cohomologyInfl_of_eq T₂ S₂ h₂, sub_self]
  rw [ker_ideleToClassH2] at hker
  obtain ⟨w, hw⟩ := hker
  refine ⟨unitsRepH2Equiv K (unitsLayerCorInfl K M w), ?_⟩
  rw [← ideleSumLocalInv_infl K S₁, ← ideleSumLocalInv_infl K S₂,
    ← ideleSumLocalInv_multiplicativeToIdeleH2, ← map_add, hw, add_sub_cancel]

end TauCeti.ClassFieldTheory
