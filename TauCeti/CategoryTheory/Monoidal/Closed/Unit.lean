/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Evaluation characterization of `MonoidalClosed.unitIsoSelf`

In a monoidal category `C` where the monoidal unit `𝟙_ C` is closed, Mathlib defines
`MonoidalClosed.unitIsoSelf : ((𝟙_ C) ⟶[C] X) ≅ X` as the mate of the left unitor isomorphism
`leftUnitorNatIso C` under the adjunction `ihom.adjunction (𝟙_ C)`. This file expresses its forward
and inverse morphisms directly in terms of evaluation and currying:

* `MonoidalClosed.unitIsoSelf_hom`: `(unitIsoSelf (X := X)).hom` equals
  `(λ_ ((ihom (𝟙_ C)).obj X)).inv ≫ (ihom.ev (𝟙_ C)).app X`.
* `MonoidalClosed.unitIsoSelf_inv`: `(unitIsoSelf (X := X)).inv` equals `curry (λ_ X).hom`.
-/

public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The forward morphism `(𝟙_ C ⟶[C] X) ⟶ X` of `MonoidalClosed.unitIsoSelf` is evaluation on the
monoidal unit. -/
theorem unitIsoSelf_hom (X : C) [Closed (𝟙_ C)] :
    (unitIsoSelf (X := X)).hom = (λ_ ((ihom (𝟙_ C)).obj X)).inv ≫ (ihom.ev (𝟙_ C)).app X := by
  rw [unitIsoSelf, Iso.symm_hom, Iso.app_inv, unitNatIso, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_adjunction_id, leftUnitorNatIso_inv_app, ihom.ihom_adjunction_counit]

/-- The inverse morphism `X ⟶ (𝟙_ C ⟶[C] X)` of `MonoidalClosed.unitIsoSelf` is the curry of the
left unitor `λ_ X`. -/
theorem unitIsoSelf_inv (X : C) [Closed (𝟙_ C)] :
    (unitIsoSelf (X := X)).inv = curry (λ_ X).hom := by
  rw [unitIsoSelf, Iso.symm_inv, Iso.app_hom, unitNatIso, conjugateIsoEquiv_apply_hom, curry_eq]
  have h := unit_conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  simpa only [Functor.id_obj, Functor.id_map, Adjunction.id_unit, NatTrans.id_app,
    Category.id_comp, ihom.ihom_adjunction_unit, leftUnitorNatIso_hom_app] using h

end CategoryTheory.MonoidalClosed
