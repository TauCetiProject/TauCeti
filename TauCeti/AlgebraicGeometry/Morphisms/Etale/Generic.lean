/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Generic étaleness and separability of function fields

For a dominant morphism of integral schemes locally of finite type, formal unramifiedness at
the generic point is equivalent to separability of the function field extension. For a morphism
locally of finite presentation, separability characterizes the existence of an open neighbourhood
of the generic point on which the morphism is étale. This lets one check the generic hypothesis
of a codimension-one étaleness criterion on the extension of fields.

The algebraic input is Mathlib's `Algebra.FormallyUnramified.iff_isSeparable`. The passage to an
open neighbourhood uses `AlgebraicGeometry.Scheme.Hom.etaleAt_iff_stalkMap`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]

/-- A dominant morphism locally of finite type is unramified at the generic point precisely when
its extension of function fields is separable. -/
theorem formallyUnramified_stalkMap_genericPoint_iff_isSeparable_functionField
    [LocallyOfFiniteType f] :
    (f.stalkMap (genericPoint X)).hom.FormallyUnramified ↔
      letI := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField := by
  let := f.functionFieldMap.hom.toAlgebra
  -- Identify the two maps before transporting essential finite type and formal unramifiedness.
  have hmap : Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant) ≫
      f.stalkMap (genericPoint X) = f.functionFieldMap := by
    rw [f.eq_functionFieldMap_iff, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
      SpecMap_stalkMap_fromSpecStalk]
  let e : Arrow.mk f.functionFieldMap ≅ Arrow.mk (f.stalkMap (genericPoint X)) :=
    Arrow.isoMk (Y.presheaf.stalkCongr (.of_eq f.genericPoint_eq_of_isDominant.symm))
      (Iso.refl _) (by simpa [TopCat.Presheaf.stalkCongr_hom] using hmap)
  have : Algebra.EssFiniteType Y.functionField X.functionField :=
    (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff e).mpr
      (LocallyOfFiniteType.stalkMap f (genericPoint X))
  exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff e).symm.trans
    (Algebra.FormallyUnramified.iff_isSeparable _ _)

/-- A dominant morphism of integral schemes locally of finite presentation is étale on an open
neighbourhood of the generic point precisely when its extension of function fields is separable. -/
theorem etaleAt_genericPoint_iff_isSeparable_functionField [LocallyOfFinitePresentation f] :
    (∃ U : X.Opens, genericPoint X ∈ U ∧ Etale (U.ι ≫ f)) ↔
      letI := f.functionFieldMap.hom.toAlgebra
      Algebra.IsSeparable Y.functionField X.functionField := by
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [f.genericPoint_eq_of_isDominant]
    exact Field.toIsField Y.functionField
  rw [f.etaleAt_iff_stalkMap, and_iff_right (RingHom.Flat.of_isField hfield _)]
  exact f.formallyUnramified_stalkMap_genericPoint_iff_isSeparable_functionField

end AlgebraicGeometry.Scheme.Hom
