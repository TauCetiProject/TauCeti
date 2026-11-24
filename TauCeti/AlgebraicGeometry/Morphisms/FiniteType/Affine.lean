/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Affine coordinates for finite type morphisms

An affine finite type morphism over an affine base is represented by a finite type algebra
map on global sections. The coordinate comparison respects its structure morphism.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- An affine finite type morphism over an affine base is represented by its finite type
map on global sections, compatibly with both structure maps. -/
theorem exists_finiteType_appTop_model {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (R : CommRingCat.{u}) (q : Y ⟶ Spec R) :
    ∃ (aB : R →+* Γ(Y, ⊤)) (aC : R →+* Γ(X, ⊤)),
      let : Algebra R Γ(Y, ⊤) := aB.toAlgebra
      let : Algebra R Γ(X, ⊤) := aC.toAlgebra
      ∃ φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤), φ.FiniteType ∧
        Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom aB) = q ∧
        X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
          f ≫ Y.isoSpec.hom := by
  let aB : R →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
  let aC : R →+* Γ(X, ⊤) := f.appTop.hom.comp aB
  let : Algebra R Γ(Y, ⊤) := aB.toAlgebra
  let : Algebra R Γ(X, ⊤) := aC.toAlgebra
  let φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤) :=
    { f.appTop.hom with commutes' := fun _ ↦ rfl }
  refine ⟨aB, aC, φ, ?_, ?_, ?_⟩
  -- Expose the algebra map chosen from global sections to apply the finite-type criterion.
  · change f.appTop.hom.FiniteType
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      f.finiteType_appLE (isAffineOpen_top Y) (isAffineOpen_top X)
        (by simp)
  -- Expose the Spec comparison chosen from the affine model.
  · change Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ q.appTop) = q
    rw [Spec.map_comp]
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp [Scheme.isoSpec]
  · exact Scheme.isoSpec_hom_naturality f

end AlgebraicGeometry.Scheme.Hom
