/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivedTensor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor

/-!
# Independence of K-flat tensor models for modules

Because a quasi-isomorphism between K-flat complexes of modules remains a quasi-isomorphism after
tensoring on the right with any complex (`CochainComplex.quasiIso_tensorHom_id_of_isKFlat`, via
`TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure`), the endofunctor
`CochainComplex.kFlatTensor` of the unbounded derived category sends quasi-isomorphisms in its
K-flat input to natural isomorphisms (`CochainComplex.isIso_kFlatTensorMap`). The comparison is
induced by the specified map of models, so its identity and composition laws are those of
`CochainComplex.kFlatTensorMap`.

No boundedness, freeness or termwise flatness is required of either input.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 064L and 064M.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]

/-- A quasi-isomorphism of K-flat models induces an invertible transformation on the entire
unbounded derived category, not just on bounded or K-flat right inputs. -/
instance isIso_kFlatTensorMap
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] : IsIso (kFlatTensorMap f) := by
  have : IsIso (whiskerRight
      ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map f)
      DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro A
    simp only [whiskerRight_app, curriedTensor_map₂CochainComplex_map_app,
      Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj]
    infer_instance
  rw [kFlatTensorMap_eq_liftNatTrans]
  exact (Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    _ _ K.kFlatTensor L.kFlatTensor (asIso (whiskerRight
      ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map f)
      DerivedCategory.Q))).isIso_hom

end CochainComplex
