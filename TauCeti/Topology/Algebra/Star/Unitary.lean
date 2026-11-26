/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.Algebra.Star.Unitary

/-!
# The unitary subgroup of units

Mathlib's `isClosed_unitary` says that the unitary elements of a topological star monoid `M` are
a closed subset of `M`.  This file transfers that to the group of units: `unitarySubgroup Mˣ`,
the unitary elements of `Mˣ` packaged as a subgroup, is closed in `Mˣ`.  It also shows that
`unitarySubgroup Mˣ` is compact exactly when `unitary M` is.

Closedness is immediate once Mathlib's `Units.unitary_eq` exhibits the subgroup as the
preimage of `unitary M` under `Units.val`, which is continuous.  No hypothesis beyond the ones
`isClosed_unitary` already needs is required.

Compactness does not follow from the preimage description.  Instead, the subgroup is the image
of `unitary M` under `Unitary.toUnits`, which is continuous into `Mˣ` because the star operation
is continuous; this needs only `ContinuousStar M`, and no `T1Space` or `ContinuousMul`.  The
converse holds because `unitary M` is the image of the subgroup under the continuous `Units.val`.

The canonical equivalence between `unitarySubgroup Mˣ` and `unitary M` is a homeomorphism.
It needs only `ContinuousStar M` beyond a topological star monoid, with no separation or
continuity-of-multiplication assumption.

This is the closedness hypothesis that the Lie algebra of a closed subgroup of `Mˣ` is computed
from; see `TauCeti/Geometry/Lie/Subgroup/Unitary/Basic.lean`.

## Main results

* `TauCeti.unitarySubgroupUnitsHomeomorph`: the unitary subgroup of the units is homeomorphic
  to the unitary elements; `TauCeti.unitarySubgroupUnitsHomeomorph_apply` and
  `TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply` identify its maps.
* `Unitary.continuous_toUnits`: the unitary-to-units homomorphism is continuous.
* `Unitary.prodContinuousMulEquiv`: topological-group upgrade of `Unitary.prodEquiv`, identifying
  `unitary (A × B)` with `unitary A × unitary B`.
* `TauCeti.mem_unitary_units_iff`: a unit is unitary exactly when its underlying element is.
* `TauCeti.isClosed_unitarySubgroup_units`: the unitary subgroup of `Mˣ` is closed.
* `TauCeti.isCompact_unitarySubgroup_units_iff`: the unitary subgroup of `Mˣ` is compact exactly
  when `unitary M` is.
-/

public section

namespace Unitary

/-- The homomorphism from unitary elements to units is continuous. -/
@[fun_prop]
theorem continuous_toUnits {M : Type*} [Monoid M] [StarMul M] [TopologicalSpace M]
    [ContinuousStar M] : Continuous (toUnits : unitary M → Mˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa only [Function.comp_def, val_toUnits_apply] using
      (continuous_subtypeVal : Continuous fun u : unitary M ↦ (u : M))
  · refine continuous_subtypeVal.star.congr fun u ↦ ?_
    simp only [← map_inv, val_toUnits_apply, ← star_eq_inv, coe_star, Pi.star_apply]

section Prod

variable (A B : Type*) [Monoid A] [Monoid B] [StarMul A] [StarMul B]
  [TopologicalSpace A] [TopologicalSpace B]

/-- Unitary elements in a product of topological star monoids form the product of unitary
subgroups as a topological group, upgrading `Unitary.prodEquiv`. -/
def prodContinuousMulEquiv : unitary (A × B) ≃ₜ* unitary A × unitary B where
  toMulEquiv := prodEquiv A B
  continuous_toFun :=
    Continuous.prodMk
      (continuous_induced_rng.mpr <| (continuous_fst.comp continuous_subtypeVal).congr fun u ↦
        (congrArg Prod.fst (coe_prodEquiv_apply A B u)).symm)
      (continuous_induced_rng.mpr <| (continuous_snd.comp continuous_subtypeVal).congr fun u ↦
        (congrArg Prod.snd (coe_prodEquiv_apply A B u)).symm)
  continuous_invFun :=
    continuous_induced_rng.mpr <|
      ((continuous_subtypeVal.comp continuous_fst).prodMk
        (continuous_subtypeVal.comp continuous_snd)).congr fun u ↦
          (coe_prodEquiv_symm_apply A B u).symm

/-- `Unitary.prodContinuousMulEquiv` evaluates as `Unitary.prodEquiv`. -/
@[simp]
theorem prodContinuousMulEquiv_apply (u : unitary (A × B)) :
    prodContinuousMulEquiv A B u = prodEquiv A B u := (rfl)

/-- The inverse of `Unitary.prodContinuousMulEquiv` evaluates as `(Unitary.prodEquiv A B).symm`. -/
@[simp]
theorem prodContinuousMulEquiv_symm_apply (u : unitary A × unitary B) :
    (prodContinuousMulEquiv A B).symm u = (prodEquiv A B).symm u := (rfl)

end Prod

end Unitary

namespace TauCeti

/-- The unitary subgroup of the units is homeomorphic to the unitary elements of the monoid. -/
def unitarySubgroupUnitsHomeomorph (M : Type*) [Monoid M] [StarMul M] [TopologicalSpace M]
    [ContinuousStar M] : unitarySubgroup Mˣ ≃ₜ unitary M := by
  have hc : Continuous (unitarySubgroupUnitsEquiv : unitarySubgroup Mˣ → unitary M) := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, unitarySubgroupUnitsEquiv_apply_coe] using
      (Units.continuous_val.comp (continuous_subtypeVal (X := Mˣ)))
  have hc' : Continuous (unitarySubgroupUnitsEquiv.symm : unitary M → unitarySubgroup Mˣ) := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, coe_unitarySubgroupUnitsEquiv_symm_apply] using
      (Unitary.continuous_toUnits (M := M))
  exact
    { toEquiv := unitarySubgroupUnitsEquiv.toEquiv
      continuous_toFun := hc
      continuous_invFun := hc' }

/-- The unitary homeomorphism agrees with the canonical group isomorphism. -/
@[simp]
theorem unitarySubgroupUnitsHomeomorph_apply {M : Type*} [Monoid M] [StarMul M]
    [TopologicalSpace M] [ContinuousStar M] (u : unitarySubgroup Mˣ) :
    unitarySubgroupUnitsHomeomorph M u = unitarySubgroupUnitsEquiv u := by
  rfl

/-- The inverse unitary homeomorphism agrees with the inverse group isomorphism. -/
@[simp]
theorem unitarySubgroupUnitsHomeomorph_symm_apply {M : Type*} [Monoid M] [StarMul M]
    [TopologicalSpace M] [ContinuousStar M] (u : unitary M) :
    (unitarySubgroupUnitsHomeomorph M).symm u = unitarySubgroupUnitsEquiv.symm u := by
  rfl

/-- A unit of a star monoid is unitary exactly when its underlying element is unitary. -/
@[simp]
theorem mem_unitary_units_iff {M : Type*} [Monoid M] [StarMul M] {g : Mˣ} :
    g ∈ unitary Mˣ ↔ (g : M) ∈ unitary M := by
  simp [Units.unitary_eq]

variable (M : Type*) [Monoid M] [StarMul M] [TopologicalSpace M] [T1Space M] [ContinuousStar M]
  [ContinuousMul M]

/-- **The unitary subgroup of the units of a topological star monoid is closed.**  It is the
preimage of the closed set `unitary M` under the continuous coercion `Units.val`. -/
theorem isClosed_unitarySubgroup_units :
    IsClosed ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) := by
  convert isClosed_unitary.preimage (Units.continuous_val (M := M)) using 1
  exact Set.ext fun _ ↦ mem_unitary_units_iff

/-- **The unitary subgroup of the units of a topological star monoid is compact exactly when
`unitary M` is.**  It is the image of `unitary M` under the continuous map sending a unitary
element to the unit it defines, and `unitary M` is in turn its image under `Units.val`. -/
theorem isCompact_unitarySubgroup_units_iff {M : Type*} [Monoid M] [StarMul M]
    [TopologicalSpace M] [ContinuousStar M] :
    IsCompact ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) ↔ IsCompact (unitary M : Set M) := by
  have hrange : ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) =
      Set.range fun U : unitary M ↦ Unitary.toUnits U := by
    ext g
    refine ⟨fun hg ↦ ⟨⟨g, mem_unitary_units_iff.mp hg⟩, Units.ext rfl⟩, ?_⟩
    rintro ⟨U, rfl⟩
    exact mem_unitary_units_iff.mpr U.property
  rw [hrange]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [← Set.range_comp, Function.comp_def] using h.image Units.continuous_val
  · have : CompactSpace (unitary M) := isCompact_iff_compactSpace.mp h
    exact isCompact_range Unitary.continuous_toUnits

end TauCeti
