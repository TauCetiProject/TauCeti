/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Structural isometries of orthogonal products of quadratic maps

Mathlib records the commutativity isometries of `QuadraticMap.prod`
(`QuadraticMap.IsometryEquiv.prodComm` and `QuadraticMap.IsometryEquiv.prodProdProdComm`). This
file adds the two remaining structural ones: the associator, and the deletion of a factor whose
module is trivial. Together with `QuadraticMap.IsometryEquiv.prodComm` they are what makes
orthogonal sum a commutative monoid operation on isometry classes of quadratic forms.

## Main definitions

* `QuadraticMap.IsometryEquiv.prodAssoc`: `LinearEquiv.prodAssoc` is isometric.
* `QuadraticMap.IsometryEquiv.uniqueProd`: `LinearEquiv.uniqueProd` is isometric.
-/

public section

namespace QuadraticMap

variable {R M₁ M₂ M₃ P : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid P] [Module R M₁] [Module R M₂] [Module R M₃] [Module R P]

/-- `LinearEquiv.prodAssoc` is isometric. -/
def IsometryEquiv.prodAssoc (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P)
    (Q₃ : QuadraticMap R M₃ P) :
    ((Q₁.prod Q₂).prod Q₃).IsometryEquiv (Q₁.prod (Q₂.prod Q₃)) where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  map_app' _ := by simp [add_assoc]

/-- The forward map of `QuadraticMap.IsometryEquiv.prodAssoc`. -/
@[simp]
theorem IsometryEquiv.prodAssoc_toFun (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (Q₃ : QuadraticMap R M₃ P) (m : (M₁ × M₂) × M₃) :
    IsometryEquiv.prodAssoc Q₁ Q₂ Q₃ m = (m.1.1, m.1.2, m.2) := by
  change LinearEquiv.prodAssoc R M₁ M₂ M₃ m = _
  exact Equiv.prodAssoc_apply M₁ M₂ M₃ m

/-- The inverse map of `QuadraticMap.IsometryEquiv.prodAssoc`. -/
@[simp]
theorem IsometryEquiv.prodAssoc_invFun (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (Q₃ : QuadraticMap R M₃ P) (m : M₁ × M₂ × M₃) :
    (IsometryEquiv.prodAssoc Q₁ Q₂ Q₃).invFun m = ((m.1, m.2.1), m.2.2) := by
  change (LinearEquiv.prodAssoc R M₁ M₂ M₃).symm m = _
  exact Equiv.prodAssoc_symm_apply M₁ M₂ M₃ m

/-- `LinearEquiv.uniqueProd` is isometric: a factor carried by a trivial module may be deleted
from an orthogonal product. -/
def IsometryEquiv.uniqueProd [Unique M₁] (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) :
    (Q₁.prod Q₂).IsometryEquiv Q₂ where
  toLinearEquiv := LinearEquiv.uniqueProd
  map_app' m := by simp [Subsingleton.elim m.1 0]

/-- The forward map of `QuadraticMap.IsometryEquiv.uniqueProd`. -/
@[simp]
theorem IsometryEquiv.uniqueProd_toFun [Unique M₁] (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (m : M₁ × M₂) :
    IsometryEquiv.uniqueProd Q₁ Q₂ m = m.2 := by
  change LinearEquiv.uniqueProd (R := R) (M := M₂) (M₂ := M₁) m = _
  exact LinearEquiv.uniqueProd_apply m

/-- The inverse map of `QuadraticMap.IsometryEquiv.uniqueProd`. -/
@[simp]
theorem IsometryEquiv.uniqueProd_invFun [Unique M₁] (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (m : M₂) :
    (IsometryEquiv.uniqueProd Q₁ Q₂).invFun m = (default, m) := by
  change (LinearEquiv.uniqueProd (R := R) (M := M₂) (M₂ := M₁)).symm m = _
  exact LinearEquiv.uniqueProd_symm_apply m

end QuadraticMap
