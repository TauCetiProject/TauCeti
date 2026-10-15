/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange

/-!
# Base change of general-linear root subgroups

The coordinate-algebra base-change isomorphisms of `GLₙ` and `𝔾ₐ` carry the scalar
extension of the elementary root map to the elementary root map over the new ring.
In particular, they preserve its additive parameter, with no invertibility, flatness,
or reducedness assumption on the base extension. This compatibility is needed to
transport normalized root subgroups between integral and field-valued constructions.

The calculation uses `rootSubgroupCoordinateMap_apply_X` and the existing coordinate
base-change isomorphisms, rather than reconstructing either morphism from points.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable {n : ℕ} {i j : Fin n}

/-- The normalized general-linear root map commutes with scalar extension, under
the canonical coordinate-algebra identifications of `GLₙ` and `𝔾ₐ`. -/
-- Supply the ring arguments explicitly when rewriting: the extension ring
-- lives in a `max` universe, which prevents reliable global simp matching.
@[reassoc]
theorem baseChangeMap_rootSubgroupCoordinateMap_comp_baseChangeIso_hom (hij : i ≠ j) :
    CommHopfAlgCat.baseChangeMap (K := K) (rootSubgroupCoordinateMap (R := R) hij) ≫
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso R K).hom =
      (coordinateHopfAlgebraBaseChangeIso R K n).hom ≫
        rootSubgroupCoordinateMap (R := K) hij := by
  apply (cancel_epi (coordinateHopfAlgebraBaseChangeIso R K n).inv).mp
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply coordinateHopfAlgebra_algHom_ext K n
  intro a b
  simp only [BialgHom.coe_toAlgHom, Iso.inv_hom_id_assoc]
  rw [coordinateHopfAlgebraBaseChangeMap_X]
  rw [rootSubgroupCoordinateMap_apply_X, rootSubgroupCoordinateMap_apply_X]
  classical
  simp only [Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp [TensorProduct.tmul_add,
    AdditiveGroup.coordinateHopfAlgebraBaseChangeIso,
    _root_.CommHopfAlgCat.isoMk_hom]

end TauCeti.GeneralLinear
