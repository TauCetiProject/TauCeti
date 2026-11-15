/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Points of an affine scheme over an affine base

Let `f : X ⟶ Spec R` be a morphism from an affine scheme to the spectrum of a commutative ring.
Its points with values in `Spec R`, that is the sections of `f`, are the characters
`Γ(X, ⊤) →ₐ[R] R` of its coordinate ring. This is
`TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom` (the `OverClass` form of Mathlib's
`AlgebraicGeometry.Spec.homEquivAlgHom`), read through `X ≅ Spec Γ(X, ⊤)`.

Points over `Spec R` are written as morphisms `𝟙_ (Over (Spec R)) ⟶ Over.mk f` of the cartesian
monoidal category `Over (Spec R)`, as for the points of group schemes over `Spec R`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`: for affine `X`, the points of `X` over
  `Spec R` are the characters of `Γ(X, ⊤)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom_apply`: the character attached to a point pulls
  back functions along it.
* `AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom_symm_apply_left`: the point attached to a
  character `φ` is `Spec φ`.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- **The points of an affine scheme over `Spec R` are the characters of its coordinate ring.**
Let `f : X ⟶ Spec R` be a morphism from an affine scheme, and give `Γ(X, ⊤)` the `R`-algebra
structure of the map of global sections of `f` (the hypothesis `hf`). A point `x` of `X` over
`Spec R`, that is a section of `f`, corresponds to the character of `Γ(X, ⊤)` given by pulling back
functions along `x`. This is `TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom`, read through
`X ≅ Spec Γ(X, ⊤)`. -/
noncomputable def Scheme.Hom.pointsEquivAlgHom (f : X ⟶ Spec (.of R)) [IsAffine X]
    [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    (𝟙_ (Over (Spec (.of R))) ⟶ Over.mk f) ≃ (Γ(X, ⊤) →ₐ[R] R) :=
  -- `f` is the spectrum of its map of global sections, read through `X ≅ Spec Γ(X, ⊤)`
  have e : f = X.isoSpec.hom ≫ Spec.algebraMap R Γ(X, ⊤) := by
    rw [Spec.algebraMap, hf, CommRingCat.ofHom_hom, Spec.map_comp, Scheme.isoSpec_hom,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h1 : Spec.algebraMap R R = 𝟙 _ := by simp [Spec.algebraMap]
  -- a point over `Spec R` is a section of `f`, which `X ≅ Spec Γ(X, ⊤)` turns into a morphism
  -- `Spec R ⟶ Spec Γ(X, ⊤)` over `Spec R`
  ({ toFun x := ⟨x.left ≫ X.isoSpec.hom, by
       rw [Scheme.Hom.isOver_iff, specOverSpec_over, specOverSpec_over]
       simpa [Spec.algebraMap, h1, e] using Over.w x⟩
     invFun g := Over.homMk (g.1 ≫ X.isoSpec.inv) (by
       have := g.2
       rw [Scheme.Hom.isOver_iff, specOverSpec_over, specOverSpec_over] at this
       simp [Spec.algebraMap, e] at this ⊢
       simp [this])
     left_inv x := by ext1; simp
     right_inv g := by ext1; simp } :
    (𝟙_ (Over (Spec (.of R))) ⟶ Over.mk f) ≃ {g : Spec (.of R) ⟶ Spec Γ(X, ⊤) //
      g.IsOver (Spec (.of R))}).trans TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom

/-- The character attached to a point `x` of `X` over `Spec R` pulls back functions along `x`. -/
@[simp]
theorem Scheme.Hom.pointsEquivAlgHom_apply (f : X ⟶ Spec (.of R)) [IsAffine X] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    (x : 𝟙_ (Over (Spec (.of R))) ⟶ Over.mk f) (c : Γ(X, ⊤)) :
    f.pointsEquivAlgHom hf x c = (Scheme.ΓSpecIso (.of R)).hom (x.left.appTop c) := by
  -- the character is the ring map `φ` with `Spec φ = x.left ≫ X.isoSpec.hom`
  have h : x.left = Spec.map (Spec.preimage (x.left ≫ X.isoSpec.hom)) ≫ X.isoSpec.inv := by simp
  have h2 : x.left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom =
      Spec.preimage (x.left ≫ X.isoSpec.hom) := by
    conv_lhs => rw [h]
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, X.isoSpec_inv_appTop]
    exact Iso.inv_hom_id_assoc _ _
  -- `specOverHomEquivAlgHom` gives `Spec φ = x.left ≫ X.isoSpec.hom`, so `φ` is its preimage
  have h3 : CommRingCat.ofHom (f.pointsEquivAlgHom hf x : Γ(X, ⊤) →+* R) =
      Spec.preimage (x.left ≫ X.isoSpec.hom) := by
    rw [← Spec.preimage_map (CommRingCat.ofHom _), Scheme.Hom.pointsEquivAlgHom,
      Equiv.trans_apply, TauCeti.AlgebraicGeometry.spec_map_specOverHomEquivAlgHom]
    rfl
  rw [← h2] at h3
  exact congr(CommRingCat.Hom.hom $h3 c)

/-- The point attached to a character `φ` of `Γ(X, ⊤)` is `Spec φ`, read through
`X ≅ Spec Γ(X, ⊤)`. -/
@[simp]
theorem Scheme.Hom.pointsEquivAlgHom_symm_apply_left (f : X ⟶ Spec (.of R)) [IsAffine X]
    [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    (φ : Γ(X, ⊤) →ₐ[R] R) :
    ((f.pointsEquivAlgHom hf).symm φ).left =
      Spec.map (CommRingCat.ofHom (φ : Γ(X, ⊤) →+* R)) ≫ X.isoSpec.inv := by
  rw [Scheme.Hom.pointsEquivAlgHom, Equiv.symm_trans_apply]
  exact congr($(TauCeti.AlgebraicGeometry.coe_specOverHomEquivAlgHom_symm_apply φ) ≫
    X.isoSpec.inv)

end AlgebraicGeometry
