/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# Structural isometries and special orthogonal groups of quadratic-map products

Mathlib records the commutativity isometries of `QuadraticMap.prod`
(`QuadraticMap.IsometryEquiv.prodComm` and `QuadraticMap.IsometryEquiv.prodProdProdComm`). This
file adds the two remaining structural ones: the associator, and the deletion of a factor whose
module is trivial. Together with `QuadraticMap.IsometryEquiv.prodComm` they are what makes
orthogonal sum a commutative monoid operation on isometry classes of quadratic forms.

For a quadratic form over a commutative ring, it also records the isometry associated to a
direct-sum decomposition of the underlying module that is orthogonal for the polar form.

It also combines special orthogonal transformations of two finite free quadratic maps with a
common codomain into a special orthogonal transformation of their product.

## Main definitions

* `QuadraticMap.IsometryEquiv.prodAssoc`: `LinearEquiv.prodAssoc` is isometric.
* `QuadraticMap.IsometryEquiv.uniqueProd`: `LinearEquiv.uniqueProd` is isometric.
* `QuadraticMap.IsometryEquiv.prodRestrictOrthogonal`: an orthogonal direct sum is isometric to
  the original form.
* `QuadraticMap.specialOrthogonalGroupProd`: combine two special orthogonal transformations.
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
theorem IsometryEquiv.prodAssoc_apply (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (Q₃ : QuadraticMap R M₃ P) (m : (M₁ × M₂) × M₃) :
    IsometryEquiv.prodAssoc Q₁ Q₂ Q₃ m = (m.1.1, m.1.2, m.2) := by
  -- Expose the underlying linear equivalence so its public application lemma applies.
  change LinearEquiv.prodAssoc R M₁ M₂ M₃ m = _
  exact Equiv.prodAssoc_apply M₁ M₂ M₃ m

/-- The inverse map of `QuadraticMap.IsometryEquiv.prodAssoc`. -/
@[simp]
theorem IsometryEquiv.prodAssoc_symm_apply (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (Q₃ : QuadraticMap R M₃ P) (m : M₁ × M₂ × M₃) :
    (IsometryEquiv.prodAssoc Q₁ Q₂ Q₃).invFun m = ((m.1, m.2.1), m.2.2) := by
  -- Expose the underlying linear equivalence so its public inverse application lemma applies.
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
theorem IsometryEquiv.uniqueProd_apply [Unique M₁] (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (m : M₁ × M₂) :
    IsometryEquiv.uniqueProd Q₁ Q₂ m = m.2 := by
  -- Expose the underlying linear equivalence so its public application lemma applies.
  change LinearEquiv.uniqueProd (R := R) (M := M₂) (M₂ := M₁) m = _
  exact LinearEquiv.uniqueProd_apply m

/-- The inverse map of `QuadraticMap.IsometryEquiv.uniqueProd`. -/
@[simp]
theorem IsometryEquiv.uniqueProd_symm_apply [Unique M₁] (Q₁ : QuadraticMap R M₁ P)
    (Q₂ : QuadraticMap R M₂ P) (m : M₂) :
    (IsometryEquiv.uniqueProd Q₁ Q₂).invFun m = (default, m) := by
  -- Expose the underlying linear equivalence so its public inverse application lemma applies.
  change (LinearEquiv.uniqueProd (R := R) (M := M₂) (M₂ := M₁)).symm m = _
  exact LinearEquiv.uniqueProd_symm_apply m

section OrthogonalDecomposition

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- An orthogonal direct-sum decomposition of a quadratic space, orthogonal for the polar form,
gives an isometry from the product of the two restricted forms to the original form. -/
noncomputable def IsometryEquiv.prodRestrictOrthogonal (Q : QuadraticForm R V)
    (W : Submodule R V) (hW : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W)) :
    ((Q.restrict W).prod
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))).IsometryEquiv Q where
  toLinearEquiv := W.prodEquivOfIsCompl (LinearMap.BilinForm.orthogonal Q.polarBilin W) hW
  map_app' x := by
    -- Expose the complementary-subspace equivalence as addition of the two components.
    change Q ((x.1 : V) + x.2) = Q x.1 + Q x.2
    rw [QuadraticMap.map_add Q, (isOrtho_polarBilin.mp (x.2.2 x.1 x.1.2)).polar_eq_zero,
      add_zero]

/-- The orthogonal-decomposition isometry sends a pair to the sum of its components. -/
@[simp]
theorem IsometryEquiv.prodRestrictOrthogonal_apply (Q : QuadraticForm R V)
    (W : Submodule R V) (hW : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W))
    (x : W × LinearMap.BilinForm.orthogonal Q.polarBilin W) :
    IsometryEquiv.prodRestrictOrthogonal Q W hW x = (x.1 : V) + x.2 :=
  Submodule.coe_prodEquivOfIsCompl' W _ hW x

/-- The inverse of the orthogonal-decomposition isometry sends a vector to its two projections
along the decomposition. -/
@[simp]
theorem IsometryEquiv.prodRestrictOrthogonal_symm_apply (Q : QuadraticForm R V)
    (W : Submodule R V) (hW : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W))
    (v : V) :
    (IsometryEquiv.prodRestrictOrthogonal Q W hW).symm v =
      (W.projectionOnto _ hW v, (LinearMap.BilinForm.orthogonal Q.polarBilin W).projectionOnto W
        hW.symm v) :=
  Submodule.prodEquivOfIsCompl_symm_apply hW v

end OrthogonalDecomposition

end QuadraticMap

open QuadraticMap

universe u v w

namespace QuadraticMap

open TauCeti.QuadraticMap

noncomputable section

variable {R : Type u} [CommRing R]

private theorem specialOrthogonalProd_mem
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    [Module.Free R M₁] [Module.Finite R M₁]
    [Module.Free R M₂] [Module.Finite R M₂]
    (f : specialOrthogonalGroup Q₁) (g : specialOrthogonalGroup Q₂) :
    (f : M₁ ≃ₗ[R] M₁).prodCongr (g : M₂ ≃ₗ[R] M₂) ∈
      specialOrthogonalGroup (Q₁.prod Q₂) := by
  have hf := mem_specialOrthogonalGroup_iff.mp f.2
  have hg := mem_specialOrthogonalGroup_iff.mp g.2
  apply mem_specialOrthogonalGroup_iff.mpr
  constructor
  · apply mem_orthogonalGroup_iff.mpr
    intro x
    let e := (orthogonalGroupEquivIsometryEquiv Q₁
      ⟨f, specialOrthogonalGroup_le_orthogonalGroup Q₁ f.2⟩).prod
        (orthogonalGroupEquivIsometryEquiv Q₂
          ⟨g, specialOrthogonalGroup_le_orthogonalGroup Q₂ g.2⟩)
    have he : e x = (f.1.prodCongr g.1) x := by
      apply Prod.ext
      · exact congrFun (coe_orthogonalGroupEquivIsometryEquiv Q₁ _) x.1
      · exact congrFun (coe_orthogonalGroupEquivIsometryEquiv Q₂ _) x.2
    rw [← he]
    exact e.map_app x
  · apply Units.ext
    rw [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
    simpa only [LinearEquiv.coe_det, Units.val_one, mul_one] using
      congrArg₂ (fun a b : R ↦ a * b) (congrArg Units.val hf.2) (congrArg Units.val hg.2)

/-- Combine special orthogonal transformations of two finite free quadratic maps with a common
codomain into a special orthogonal transformation of their product. -/
def specialOrthogonalGroupProd
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    [Module.Free R M₁] [Module.Finite R M₁]
    [Module.Free R M₂] [Module.Finite R M₂] :
    specialOrthogonalGroup Q₁ × specialOrthogonalGroup Q₂ →*
      specialOrthogonalGroup (Q₁.prod Q₂) where
  toFun fg := ⟨(fg.1 : M₁ ≃ₗ[R] M₁).prodCongr (fg.2 : M₂ ≃ₗ[R] M₂),
    specialOrthogonalProd_mem Q₁ Q₂ fg.1 fg.2⟩
  map_one' := by ext x <;> simp
  map_mul' f g := by ext x <;> simp

/-- The product of two special orthogonal transformations acts componentwise. -/
@[simp]
theorem specialOrthogonalGroupProd_apply
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    [Module.Free R M₁] [Module.Finite R M₁]
    [Module.Free R M₂] [Module.Finite R M₂]
    (fg : specialOrthogonalGroup Q₁ × specialOrthogonalGroup Q₂) (x : M₁ × M₂) :
    ((specialOrthogonalGroupProd Q₁ Q₂ fg : specialOrthogonalGroup _) :
      (M₁ × M₂) ≃ₗ[R] (M₁ × M₂)) x =
      ((fg.1 : M₁ ≃ₗ[R] M₁) x.1, (fg.2 : M₂ ≃ₗ[R] M₂) x.2) := by
  rfl

end

end QuadraticMap
