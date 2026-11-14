/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineSpace.Basic

/-!
# Linear morphisms and automorphisms of affine spaces

Given a matrix `C : Matrix m n Γ(S, ⊤)` of global sections over a base scheme `S` (for finite `n`),
the linear combination of standard coordinates `i ↦ ∑ j, C i j * coord S j` defines an `S`-morphism
`AlgebraicGeometry.AffineSpace.linearMap S C : 𝔸(n; S) ⟶ 𝔸(m; S)` contravariantly in the variable
index and covariantly on coordinate vectors (`linearMap_comp`, `homOfVector_linearMap`). Invertible
square matrices induce `S`-automorphisms `AlgebraicGeometry.AffineSpace.linearIso`.

Composing an algebra evaluation morphism `AlgebraicGeometry.AffineSpace.homOfAlgebra R x` with a
linear morphism of affine spaces over `Spec (.of R)` corresponds to taking `R`-linear combinations
of the coordinates `x` (`homOfAlgebra_linearMap`).

## Main declarations

* `AlgebraicGeometry.AffineSpace.linearMap`: the `S`-morphism `𝔸(n; S) ⟶ 𝔸(m; S)` defined by a
  matrix `C : Matrix m n Γ(S, ⊤)`.
* `AlgebraicGeometry.AffineSpace.linearIso`: the `S`-automorphism of `𝔸(n; S)` induced by an
  invertible matrix `M : (Matrix n n Γ(S, ⊤))ˣ`.
* `AlgebraicGeometry.AffineSpace.homOfAlgebra_linearMap`: compatibility of `homOfAlgebra` with
  `linearMap`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

universe u

noncomputable section

section LinearMap

variable {m n p : Type u} [Fintype n] (S : Scheme.{u})

/-- The `S`-linear morphism `𝔸(n; S) ⟶ 𝔸(m; S)` induced by a matrix `C : Matrix m n Γ(S, ⊤)`,
sending a coordinate tuple `v` to `i ↦ ∑ j, C i j * v j`. -/
def linearMap (C : Matrix m n Γ(S, ⊤)) : 𝔸(n; S) ⟶ 𝔸(m; S) :=
  homOfVector (𝔸(n; S) ↘ S) fun i ↦ ∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j

/-- Explicit unfolding of `linearMap` in terms of `homOfVector`. -/
lemma linearMap_def (C : Matrix m n Γ(S, ⊤)) :
    linearMap S C =
      homOfVector (𝔸(n; S) ↘ S) fun i ↦ ∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j :=
  (rfl)

/-- `linearMap S C` commutes with the structure morphisms to `S`. -/
@[reassoc]
lemma linearMap_over (C : Matrix m n Γ(S, ⊤)) :
    linearMap S C ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S :=
  homOfVector_over _ _

instance (C : Matrix m n Γ(S, ⊤)) : (linearMap S C).IsOver S := by
  rw [linearMap_def]
  infer_instance

/-- Pulling back the `i`-th coordinate along `linearMap S C` yields `∑ j, C i j * coord S j`. -/
@[simp]
lemma linearMap_appTop_coord (C : Matrix m n Γ(S, ⊤)) (i : m) :
    (linearMap S C).appTop (coord S i) = ∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j :=
  homOfVector_appTop_coord _ _ _

/-- Composing a vector-defined morphism `X ⟶ 𝔸(n; S)` with `linearMap S C` multiplies the
coordinate vector by `C`. -/
@[reassoc]
lemma homOfVector_linearMap {X : Scheme.{u}} (f : X ⟶ S) (v : n → Γ(X, ⊤))
    (C : Matrix m n Γ(S, ⊤)) :
    homOfVector f v ≫ linearMap S C =
      homOfVector f (fun i ↦ ∑ j, f.appTop (C i j) * v j) := by
  refine hom_ext (by simp) fun i ↦ ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearMap_appTop_coord,
    homOfVector_appTop_coord, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, homOfVector_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    homOfVector_over]

/-- The zero matrix induces the constant zero section morphism `𝔸(n; S) ⟶ 𝔸(m; S)`. -/
@[simp]
lemma linearMap_zero :
    linearMap S (0 : Matrix m n Γ(S, ⊤)) = homOfVector (𝔸(n; S) ↘ S) 0 := by
  refine hom_ext (by simp) fun i ↦ ?_
  simp

/-- The identity matrix induces the identity morphism on `𝔸(n; S)`. -/
@[simp]
lemma linearMap_one [DecidableEq n] :
    linearMap S (1 : Matrix n n Γ(S, ⊤)) = 𝟙 𝔸(n; S) := by
  refine hom_ext (by simp) fun i ↦ ?_
  simp [Matrix.one_apply]

/-- Composition of linear morphisms of affine spaces corresponds to matrix multiplication. -/
@[reassoc]
lemma linearMap_comp [Fintype p] (C : Matrix m n Γ(S, ⊤)) (D : Matrix n p Γ(S, ⊤)) :
    linearMap S D ≫ linearMap S C = linearMap S (C * D) := by
  rw [linearMap_def S D, homOfVector_linearMap, linearMap_def S (C * D)]
  congr 1
  ext i
  simp only [Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul, mul_assoc]
  exact Finset.sum_comm

/-- Postcomposing `linearMap S C` with `reindex g S` restricts the rows of `C` along `g`. -/
@[reassoc]
lemma linearMap_reindex {q : Type u} (C : Matrix m n Γ(S, ⊤)) (g : q → m) :
    linearMap S C ≫ reindex g S = linearMap S (C.submatrix g id) := by
  refine hom_ext (by simp) fun _ ↦ ?_
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
    linearMap_appTop_coord, Matrix.submatrix_apply, id_eq]

variable {S} in
/-- Base change of `linearMap T C` along `f : S ⟶ T` applies `f.appTop` to the entries of `C`. -/
@[reassoc]
lemma map_linearMap {T : Scheme.{u}} (f : S ⟶ T) (C : Matrix m n Γ(T, ⊤)) :
    map n f ≫ linearMap T C = linearMap S (C.map f.appTop) ≫ map m f := by
  refine hom_ext (by simp) fun i ↦ ?_
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, linearMap_appTop_coord, map_appTop_coord, linearMap_appTop_coord,
    map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_appTop_coord, Matrix.map_apply, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- An invertible matrix `M : (Matrix n n Γ(S, ⊤))ˣ` induces an `S`-automorphism of `𝔸(n; S)`. -/
def linearIso [DecidableEq n] (M : (Matrix n n Γ(S, ⊤))ˣ) : 𝔸(n; S) ≅ 𝔸(n; S) where
  hom := linearMap S M.val
  inv := linearMap S M⁻¹.val
  hom_inv_id := by rw [linearMap_comp, Units.inv_mul, linearMap_one]
  inv_hom_id := by rw [linearMap_comp, Units.mul_inv, linearMap_one]

/-- The forward morphism of `linearIso S M` is `linearMap S M.val`. -/
@[simp]
lemma linearIso_hom [DecidableEq n] (M : (Matrix n n Γ(S, ⊤))ˣ) :
    (linearIso S M).hom = linearMap S M.val :=
  (rfl)

/-- The inverse morphism of `linearIso S M` is `linearMap S M⁻¹.val`. -/
@[simp]
lemma linearIso_inv [DecidableEq n] (M : (Matrix n n Γ(S, ⊤))ˣ) :
    (linearIso S M).inv = linearMap S M⁻¹.val :=
  (rfl)

instance [DecidableEq n] (M : (Matrix n n Γ(S, ⊤))ˣ) : (linearIso S M).hom.IsOver S := by
  rw [linearIso_hom]
  infer_instance

/-- The identity unit matrix induces `Iso.refl 𝔸(n; S)`. -/
@[simp]
lemma linearIso_one [DecidableEq n] :
    linearIso S (1 : (Matrix n n Γ(S, ⊤))ˣ) = Iso.refl 𝔸(n; S) :=
  Iso.ext (by simp)

/-- Inverting the unit matrix corresponds to `Iso.symm` on `linearIso`. -/
@[simp]
lemma linearIso_symm [DecidableEq n] (M : (Matrix n n Γ(S, ⊤))ˣ) :
    (linearIso S M).symm = linearIso S M⁻¹ :=
  Iso.ext (by simp)

/-- Multiplication of unit matrices reverses order under `linearIso`. -/
lemma linearIso_mul [DecidableEq n] (M N : (Matrix n n Γ(S, ⊤))ˣ) :
    linearIso S (M * N) = linearIso S N ≪≫ linearIso S M :=
  Iso.ext (by simp [linearMap_comp])

end LinearMap

/-- Composing `homOfAlgebra R x` with the linear map defined by a matrix `C : Matrix m n R` produces
`homOfAlgebra R` for the linear combinations `i ↦ ∑ j, C i j • x j`. -/
@[reassoc]
lemma homOfAlgebra_linearMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {m n : Type u} [Fintype n] (x : n → A) (C : Matrix m n R) :
    homOfAlgebra R x ≫
        linearMap (Spec (.of R)) (C.map (Scheme.ΓSpecIso (.of R)).inv) =
      homOfAlgebra R (fun i ↦ ∑ j, C i j • x j) := by
  rw [homOfAlgebra_eq_homOfVector, homOfVector_linearMap, homOfAlgebra_eq_homOfVector]
  congr 1
  ext i
  simp only [Function.comp_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Algebra.smul_def, map_mul, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, ConcreteCategory.hom_ofHom]

end

end AlgebraicGeometry.AffineSpace
