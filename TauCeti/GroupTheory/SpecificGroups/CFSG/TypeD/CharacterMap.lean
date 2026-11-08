/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly

/-!
# Character pullbacks of the represented D and twisted-D Steinberg maps

The full-weight spin carrier has fundamental-weight torus coordinates indexed by the same
Bourbaki nodes as the native simply connected root datum. This file equips its validated-index
interface with that torus and identifies the character maps of Frobenius and the fork exchange.
Contravariant composition then identifies the represented Steinberg maps of `Dₙ(q)` and
`²Dₙ(q)` with the weight map of `ValidLieTypeIndex.datumSteinberg`.

The graph factor is the independently constructed spin automorphism, not a map transported from
the root datum. Its pullback is the inverse of `GraphTwistedIndex.datumGraphAut`; the involutive
fork exchange makes that inverse invisible on the coordinate permutation. No comparison with a
canonical ambient group is asserted. The triality branch uses a different, tripled carrier and
is not covered by the Steinberg comparisons here.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29, and Chapter 11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

namespace TauCeti

noncomputable section

namespace TypeDDiagramLieIndex

/-- The full-weight spin torus, in the validated index's fundamental-weight coordinates. -/
def weightTorus (d : TypeDDiagramLieIndex) :
    (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  TypeDSpinCarrier.weightTorusPoints d.1.rank d.four_le_rank d.1.Closure

/-- The indexed torus is the represented spin carrier's weight torus. This equation is not a
simp rule, so indexed character-map statements retain their torus parametrization. -/
theorem weightTorus_def (d : TypeDDiagramLieIndex) :
    d.weightTorus = TypeDSpinCarrier.weightTorusPoints d.1.rank d.four_le_rank d.1.Closure :=
  (rfl)

/-- The indexed Frobenius has the character map of the native root-datum Frobenius. -/
theorem isCharacterMap_frobenius (d : TypeDDiagramLieIndex) :
    IsCharacterMap d.weightTorus d.frobenius d.1.datumFrobenius.weightMap := by
  rw [weightTorus_def, frobenius_def, ValidLieTypeIndex.datumFrobenius_weightMap,
    d.1.fieldOrder_eq_characteristic_pow, ← Module.End.one_eq_id]
  exact TypeDSpinCarrier.isCharacterMap_frobenius _ _ _ _ _

end TypeDDiagramLieIndex

namespace TypeDLieIndex

/-- The represented untwisted spin Steinberg map pulls characters back by the native
root-datum Steinberg map. -/
theorem isCharacterMap_steinberg (d : TypeDLieIndex) :
    IsCharacterMap d.toTypeDDiagramLieIndex.weightTorus d.steinberg
      d.1.datumSteinberg.weightMap := by
  rw [ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius _
    d.toTypeDDiagramLieIndex.toGraphTwistedIndex.2]
  have hgraph : d.toTypeDDiagramLieIndex.toGraphTwistedIndex.datumGraphAut = 1 := by
    rw [GraphTwistedIndex.datumGraphAut_def]
    exact (DynkinType.diagramAut_eq_one_iff _ _).mpr d.diagramPerm_toGraphTwistedIndex
  rw [GraphTwistedIndex.datumSteinberg_weightMap, hgraph, inv_one]
  simpa [steinberg_def, ValidLieTypeIndex.datumFrobenius_weightMap] using
    d.toTypeDDiagramLieIndex.isCharacterMap_frobenius

end TypeDLieIndex

namespace TypeTwistedDLieIndex

/-- The represented fork exchange has the inverse native datum graph action as character map. -/
theorem isCharacterMap_graphAut (d : TypeTwistedDLieIndex) :
    IsCharacterMap d.toTypeDDiagramLieIndex.weightTorus d.graphAut.toMonoidHom
      d.toTypeDDiagramLieIndex.toGraphTwistedIndex.datumGraphAut⁻¹.toHom.weightMap := by
  rw [TypeDDiagramLieIndex.weightTorus_def, graphAut_def,
    GraphTwistedIndex.datumGraphAut_def, DynkinType.diagramAut_inv_weightMap,
    diagramPerm_toGraphTwistedIndex]
  exact TypeDSpinCarrier.isCharacterMap_graphAutPoints _ _ _

/-- The represented graph-twisted spin Steinberg map pulls characters back by the native
root-datum Steinberg map, with the small-field Frobenius parameter `q`. -/
theorem isCharacterMap_steinberg (d : TypeTwistedDLieIndex) :
    IsCharacterMap d.toTypeDDiagramLieIndex.weightTorus d.steinberg
      d.1.datumSteinberg.weightMap := by
  rw [steinberg_def, ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius _
    d.toTypeDDiagramLieIndex.toGraphTwistedIndex.2, GraphTwistedIndex.datumSteinberg_weightMap]
  have h := d.isCharacterMap_graphAut.comp d.toTypeDDiagramLieIndex.isCharacterMap_frobenius
  simpa only [ValidLieTypeIndex.datumFrobenius_weightMap, LinearMap.comp_smul,
    LinearMap.comp_id, Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.id_comp] using h

end TypeTwistedDLieIndex

end

end TauCeti
