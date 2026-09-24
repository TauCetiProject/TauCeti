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
import TauCeti.LinearAlgebra.Prod

/-!
# Structural isometries and special orthogonal groups of quadratic-map products

Mathlib records the commutativity isometries of `QuadraticMap.prod`
(`QuadraticMap.IsometryEquiv.prodComm` and `QuadraticMap.IsometryEquiv.prodProdProdComm`). This
file adds the two remaining structural ones: the associator, and the deletion of a factor whose
module is trivial. Together with `QuadraticMap.IsometryEquiv.prodComm` they are what makes
orthogonal sum a commutative monoid operation on isometry classes of quadratic forms.

For a quadratic form over a commutative ring, it also records the isometry associated to a
direct-sum decomposition of the underlying module that is orthogonal for the polar form.

Finally, it embeds the product of the orthogonal groups of two quadratic maps with a common
codomain into the orthogonal group of their orthogonal sum, acting componentwise, and identifies
the image: an orthogonal transformation of `Q₁.prod Q₂` is such an orthogonal sum exactly when it
maps each summand into itself. No finiteness is needed for this, since a linear automorphism of
`M₁ × M₂` preserving both summands is automatically a product of automorphisms of the summands.
For finite free modules the determinant of an orthogonal sum is the product of the determinants,
so the embedding restricts to the special orthogonal groups.

## Main definitions

* `QuadraticMap.IsometryEquiv.prodAssoc`: `LinearEquiv.prodAssoc` is isometric.
* `QuadraticMap.IsometryEquiv.uniqueProd`: `LinearEquiv.uniqueProd` is isometric.
* `QuadraticMap.IsometryEquiv.prodRestrictOrthogonal`: an orthogonal direct sum is isometric to
  the original form.
* `QuadraticMap.orthogonalGroupProd`: the orthogonal sum `O(Q₁) × O(Q₂) →* O(Q₁.prod Q₂)`.
* `QuadraticMap.specialOrthogonalGroupProd`: its restriction
  `SO(Q₁) × SO(Q₂) →* SO(Q₁.prod Q₂)`.

## Main results

* `QuadraticMap.orthogonalGroupProd_injective` and
  `QuadraticMap.specialOrthogonalGroupProd_injective`: both maps are injective.
* `QuadraticMap.mem_range_orthogonalGroupProd_iff`: the image of `orthogonalGroupProd` is exactly
  the subgroup of orthogonal transformations of `Q₁.prod Q₂` preserving both summands.
* `QuadraticMap.det_orthogonalGroupProd`: the determinant of an orthogonal sum is the product of
  the determinants.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §43.
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

namespace QuadraticMap

open TauCeti.QuadraticMap

section OrthogonalGroup

variable {R M₁ M₂ N : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N] [Module R N]
  (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)

variable {Q₁ Q₂} in
/-- The componentwise product of orthogonal transformations of `Q₁` and `Q₂` is an orthogonal
transformation of their orthogonal sum `Q₁.prod Q₂`. -/
theorem prodCongr_mem_orthogonalGroup {f₁ : M₁ ≃ₗ[R] M₁} {f₂ : M₂ ≃ₗ[R] M₂}
    (hf₁ : f₁ ∈ orthogonalGroup Q₁) (hf₂ : f₂ ∈ orthogonalGroup Q₂) :
    f₁.prodCongr f₂ ∈ orthogonalGroup (Q₁.prod Q₂) := mem_orthogonalGroup_iff.mpr fun x ↦ by
  simp [map_app_of_mem_orthogonalGroup hf₁, map_app_of_mem_orthogonalGroup hf₂]

/-- The orthogonal sum of orthogonal transformations: a pair `(f₁, f₂)` of orthogonal
transformations of `Q₁` and `Q₂` acts on `M₁ × M₂` componentwise, preserving `Q₁.prod Q₂`.

It is injective (`orthogonalGroupProd_injective`), and its image is exactly the subgroup of
orthogonal transformations of `Q₁.prod Q₂` that preserve both summands
(`mem_range_orthogonalGroupProd_iff`). -/
def orthogonalGroupProd :
    orthogonalGroup Q₁ × orthogonalGroup Q₂ →* orthogonalGroup (Q₁.prod Q₂) where
  toFun f := ⟨(f.1 : M₁ ≃ₗ[R] M₁).prodCongr (f.2 : M₂ ≃ₗ[R] M₂),
    prodCongr_mem_orthogonalGroup f.1.2 f.2.2⟩
  map_one' := by ext x <;> simp
  map_mul' f g := by ext x <;> simp

/-- The orthogonal sum of two orthogonal transformations acts componentwise. -/
@[simp]
theorem orthogonalGroupProd_apply (f : orthogonalGroup Q₁ × orthogonalGroup Q₂) (x : M₁ × M₂) :
    (orthogonalGroupProd Q₁ Q₂ f : (M₁ × M₂) ≃ₗ[R] M₁ × M₂) x =
      ((f.1 : M₁ ≃ₗ[R] M₁) x.1, (f.2 : M₂ ≃ₗ[R] M₂) x.2) :=
  (rfl)

/-- The orthogonal transformation `orthogonalGroupProd Q₁ Q₂ f` is the product of the two
underlying linear automorphisms. -/
theorem coe_orthogonalGroupProd (f : orthogonalGroup Q₁ × orthogonalGroup Q₂) :
    (orthogonalGroupProd Q₁ Q₂ f : (M₁ × M₂) ≃ₗ[R] M₁ × M₂) =
      (f.1 : M₁ ≃ₗ[R] M₁).prodCongr (f.2 : M₂ ≃ₗ[R] M₂) :=
  (rfl)

/-- The orthogonal sum of orthogonal groups embeds into the orthogonal group of the orthogonal
sum. -/
theorem orthogonalGroupProd_injective : Function.Injective (orthogonalGroupProd Q₁ Q₂) :=
  fun f g h ↦ by
    have := congrArg Subtype.val h
    rw [coe_orthogonalGroupProd, coe_orthogonalGroupProd, LinearEquiv.prodCongr_inj] at this
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)

/-- **The image of the orthogonal sum of orthogonal groups.** An orthogonal transformation `g` of
`Q₁.prod Q₂` is an orthogonal sum `f₁ ⊕ f₂` of orthogonal transformations of `Q₁` and `Q₂`
exactly when it preserves both summands, that is, maps `M₁ × 0` into `M₁ × 0` and `0 × M₂` into
`0 × M₂`. -/
theorem mem_range_orthogonalGroupProd_iff {g : orthogonalGroup (Q₁.prod Q₂)} :
    g ∈ (orthogonalGroupProd Q₁ Q₂).range ↔
      (∀ m₁, ((g : (M₁ × M₂) ≃ₗ[R] M₁ × M₂) (m₁, 0)).2 = 0) ∧
        ∀ m₂, ((g : (M₁ × M₂) ≃ₗ[R] M₁ × M₂) (0, m₂)).1 = 0 := by
  rw [← LinearEquiv.exists_prodCongr_eq_iff]
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f.1, f.2, by rw [← hf, coe_orthogonalGroupProd]⟩, ?_⟩
  rintro ⟨e₁, e₂, he⟩
  -- The two factors are orthogonal because `g` is, evaluated on each summand.
  have he₁ : e₁ ∈ orthogonalGroup Q₁ := mem_orthogonalGroup_iff.mpr fun m ↦ by
    simpa [← he] using map_app_of_mem_orthogonalGroup g.2 (m, 0)
  have he₂ : e₂ ∈ orthogonalGroup Q₂ := mem_orthogonalGroup_iff.mpr fun m ↦ by
    simpa [← he] using map_app_of_mem_orthogonalGroup g.2 (0, m)
  exact ⟨(⟨e₁, he₁⟩, ⟨e₂, he₂⟩), Subtype.ext he⟩

end OrthogonalGroup

section SpecialOrthogonalGroup

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommMonoid N] [Module R N]
  (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
  [Module.Free R M₁] [Module.Finite R M₁] [Module.Free R M₂] [Module.Finite R M₂]

/-- The determinant of an orthogonal sum of orthogonal transformations is the product of their
determinants. -/
@[simp]
theorem det_orthogonalGroupProd (f : orthogonalGroup Q₁ × orthogonalGroup Q₂) :
    LinearEquiv.det (orthogonalGroupProd Q₁ Q₂ f : (M₁ × M₂) ≃ₗ[R] M₁ × M₂) =
      LinearEquiv.det (f.1 : M₁ ≃ₗ[R] M₁) * LinearEquiv.det (f.2 : M₂ ≃ₗ[R] M₂) := by
  rw [coe_orthogonalGroupProd, LinearEquiv.det_prodCongr]

/-- Combine special orthogonal transformations of two finite free quadratic maps with a common
codomain into a special orthogonal transformation of their product. -/
def specialOrthogonalGroupProd :
    specialOrthogonalGroup Q₁ × specialOrthogonalGroup Q₂ →*
      specialOrthogonalGroup (Q₁.prod Q₂) where
  toFun f := ⟨(f.1 : M₁ ≃ₗ[R] M₁).prodCongr (f.2 : M₂ ≃ₗ[R] M₂),
    mem_specialOrthogonalGroup_iff.mpr
      ⟨prodCongr_mem_orthogonalGroup (specialOrthogonalGroup_le_orthogonalGroup Q₁ f.1.2)
        (specialOrthogonalGroup_le_orthogonalGroup Q₂ f.2.2), by
        rw [LinearEquiv.det_prodCongr, (mem_specialOrthogonalGroup_iff.mp f.1.2).2,
          (mem_specialOrthogonalGroup_iff.mp f.2.2).2, mul_one]⟩⟩
  map_one' := by ext x <;> simp
  map_mul' f g := by ext x <;> simp

/-- The special orthogonal transformation `specialOrthogonalGroupProd Q₁ Q₂ f` is the product of
the two underlying linear automorphisms. -/
theorem coe_specialOrthogonalGroupProd (f : specialOrthogonalGroup Q₁ × specialOrthogonalGroup Q₂) :
    (specialOrthogonalGroupProd Q₁ Q₂ f : (M₁ × M₂) ≃ₗ[R] M₁ × M₂) =
      (f.1 : M₁ ≃ₗ[R] M₁).prodCongr (f.2 : M₂ ≃ₗ[R] M₂) :=
  (rfl)

/-- The product of two special orthogonal transformations acts componentwise. -/
@[simp]
theorem specialOrthogonalGroupProd_apply
    (fg : specialOrthogonalGroup Q₁ × specialOrthogonalGroup Q₂) (x : M₁ × M₂) :
    ((specialOrthogonalGroupProd Q₁ Q₂ fg : specialOrthogonalGroup _) :
      (M₁ × M₂) ≃ₗ[R] (M₁ × M₂)) x =
      ((fg.1 : M₁ ≃ₗ[R] M₁) x.1, (fg.2 : M₂ ≃ₗ[R] M₂) x.2) :=
  (rfl)

/-- The orthogonal sum of special orthogonal groups embeds into the special orthogonal group of
the orthogonal sum. -/
theorem specialOrthogonalGroupProd_injective :
    Function.Injective (specialOrthogonalGroupProd Q₁ Q₂) := fun f g h ↦ by
  have := congrArg Subtype.val h
  rw [coe_specialOrthogonalGroupProd, coe_specialOrthogonalGroupProd,
    LinearEquiv.prodCongr_inj] at this
  exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)

end SpecialOrthogonalGroup

end QuadraticMap
