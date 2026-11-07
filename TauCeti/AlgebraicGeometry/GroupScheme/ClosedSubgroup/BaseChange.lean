/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Base change of closed subgroup schemes

Let `G` be a group scheme over `X` and `s : Y ⟶ X` a morphism of schemes. The base change of `G`
to `Y` is the group scheme `(Over.pullback s).mapGrp.obj G` over `Y`. This file shows that a closed
subgroup scheme `P` of `G` base-changes to a closed subgroup scheme of the base change of `G`: the
base change of a closed immersion of group schemes is again a closed immersion, since its
underlying morphism is the pullback of the original one along the projection
`G ×_X Y ⟶ G`.

## Main declarations

* `TauCeti.ClosedSubgroupScheme.baseChange s P`: the base change of a closed subgroup scheme `P`
  of `G` along `s`, a closed subgroup scheme of the base change of `G`.
* `TauCeti.ClosedSubgroupScheme.baseChange_mk`: the base change of the closed subgroup scheme
  represented by a closed immersion `i` is represented by the base change of `i`.
* `TauCeti.ClosedSubgroupScheme.baseChange_mono`: base change preserves inclusions of closed
  subgroup schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.ClosedSubgroupScheme

universe u

variable {X Y : Scheme.{u}} (s : Y ⟶ X) {G K : Grp (Over X)}

/-- The base change of a closed immersion of group schemes is a closed immersion. -/
instance isClosedImmersion_pullback_mapGrp_map (i : K ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion ((Over.pullback s).mapGrp.map i).hom.hom.left :=
  MorphismProperty.of_isPullback (Over.isPullback_pullback_map_left s i.hom.hom).flip
    inferInstance

/-- The **base change of a closed subgroup scheme** `P` of `G` along `s : Y ⟶ X`: the closed
subgroup scheme of the base change `(Over.pullback s).mapGrp.obj G` represented by the base change
of the inclusion of `P`. -/
noncomputable def baseChange (P : ClosedSubgroupScheme G) :
    ClosedSubgroupScheme ((Over.pullback s).mapGrp.obj G) :=
  mk ((Over.pullback s).mapGrp.map P.1.arrow)

/-- The base change of `P` is represented by the base change of the inclusion of `P`. -/
theorem baseChange_def (P : ClosedSubgroupScheme G) :
    baseChange s P = mk ((Over.pullback s).mapGrp.map P.1.arrow) :=
  (rfl)

/-- The base change of the closed subgroup scheme represented by a closed immersion `i` is
represented by the base change of `i`. -/
@[simp]
theorem baseChange_mk (i : K ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    baseChange s (mk i) = mk ((Over.pullback s).mapGrp.map i) := by
  refine Subtype.ext ?_
  rw [coe_mk, baseChange_def, coe_mk]
  refine Subobject.mk_eq_mk_of_comm _ _ ((Over.pullback s).mapGrp.mapIso (mkIso i)) ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← (Iso.inv_comp_eq _).1 (mkIso_inv_comp_arrow i)]

/-- Base change preserves inclusions of closed subgroup schemes. -/
theorem baseChange_mono : Monotone (baseChange (G := G) s) := by
  intro P Q h
  refine Subtype.coe_le_coe.1 ?_
  rw [baseChange_def, baseChange_def, coe_mk, coe_mk]
  exact Subobject.mk_le_mk_of_comm
    ((Over.pullback s).mapGrp.map (Subobject.ofLE _ _ (Subtype.coe_le_coe.2 h)))
    (by rw [← Functor.map_comp, Subobject.ofLE_arrow])

end TauCeti.ClosedSubgroupScheme
