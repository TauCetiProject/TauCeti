/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Linear maps and algebra evaluation morphisms of affine spaces

Given a matrix `C : Matrix m n Γ(S, ⊤)` of global sections over a base scheme `S` (for finite `n`),
the linear combination of standard coordinates `i ↦ ∑ j, C i j * coord S j` defines an `S`-morphism
`AlgebraicGeometry.AffineSpace.linearMap S C : 𝔸(n; S) ⟶ 𝔸(m; S)` contravariantly in the variable
index and covariantly on coordinate vectors (`linearMap_comp`, `homOfVector_linearMap`). Invertible
square matrices induce `S`-automorphisms `AlgebraicGeometry.AffineSpace.linearIso`.

For an `R`-algebra `A` and an `n`-tuple `x : n → A`, `AlgebraicGeometry.AffineSpace.homOfAlgebra x`
is the canonical `Spec R`-morphism `Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` corresponding to evaluation
`MvPolynomial.aeval x`. It is a closed immersion if and only if `x` generates `A` over `R`
(`isClosedImmersion_homOfAlgebra_iff`), finite if and only if `MvPolynomial.aeval x` is
module-finite (`isFinite_homOfAlgebra_iff`), and surjective when `x` is algebraically independent
over `R` and makes `A` integral (`surjective_homOfAlgebra`). Composing `homOfAlgebra x` with a
linear morphism of affine spaces corresponds to taking linear combinations of the coordinates `x`
(`homOfAlgebra_linearMap`).

## Main declarations

* `AlgebraicGeometry.AffineSpace.linearMap`: the `S`-morphism `𝔸(n; S) ⟶ 𝔸(m; S)` defined by a
  matrix `C : Matrix m n Γ(S, ⊤)`.
* `AlgebraicGeometry.AffineSpace.linearIso`: the `S`-automorphism of `𝔸(n; S)` induced by an
  invertible matrix `M : (Matrix n n Γ(S, ⊤))ˣ`.
* `AlgebraicGeometry.AffineSpace.homOfAlgebra`: the evaluation morphism
  `Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` attached to a coordinate tuple `x : n → A`.
-/

public section

open CategoryTheory MvPolynomial

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
  refine hom_ext (by simp) fun i ↦ ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
    linearMap_appTop_coord, linearMap_appTop_coord]
  rfl

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

/-- The identity unit matrix induces `Iso.refl 𝔸(n; S)`. -/
@[simp]
lemma linearIso_one [DecidableEq n] :
    linearIso S (1 : (Matrix n n Γ(S, ⊤))ˣ) = Iso.refl 𝔸(n; S) :=
  Iso.ext (by simp)

/-- Inverting the unit matrix corresponds to `Iso.symm` on `linearIso`. -/
@[simp]
lemma linearIso_symm [DecidableEq n] (M : (Matrix n n Γ(S, ⊤))ˣ) :
    (linearIso S M).symm = linearIso S M⁻¹ :=
  (rfl)

/-- Multiplication of unit matrices reverses order under `linearIso`. -/
lemma linearIso_mul [DecidableEq n] (M N : (Matrix n n Γ(S, ⊤))ˣ) :
    linearIso S (M * N) = linearIso S N ≪≫ linearIso S M :=
  Iso.ext (by simp [linearMap_comp])

end LinearMap

section HomOfAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {m n : Type u}

/-- The `Spec R`-morphism `Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` corresponding to the `R`-algebra
evaluation homomorphism `MvPolynomial.aeval x : MvPolynomial n R →ₐ[R] A`. -/
def homOfAlgebra (x : n → A) : Spec (.of A) ⟶ 𝔸(n; Spec (.of R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) ≫
    (SpecIso n (.of R)).inv

/-- Explicit unfolding of `homOfAlgebra` in terms of `Spec.map` and `SpecIso`. -/
lemma homOfAlgebra_def (x : n → A) :
    homOfAlgebra (R := R) x =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) ≫
        (SpecIso n (.of R)).inv :=
  (rfl)

/-- Composing `homOfAlgebra x` with `(SpecIso n (.of R)).hom` recovers `Spec.map (aeval x)`. -/
@[reassoc (attr := simp)]
lemma homOfAlgebra_specIso_hom (x : n → A) :
    homOfAlgebra (R := R) x ≫ (SpecIso n (.of R)).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) := by
  simp [homOfAlgebra_def]

/-- `homOfAlgebra x` lies over `Spec (.of R)` via `Spec.map (algebraMap R A)`. -/
@[reassoc (attr := simp)]
lemma homOfAlgebra_over (x : n → A) :
    homOfAlgebra (R := R) x ≫ 𝔸(n; Spec (.of R)) ↘ Spec (.of R) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [homOfAlgebra_def, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

/-- Pulling back the `i`-th coordinate of `𝔸(n; Spec (.of R))` along `homOfAlgebra x` gives the
global section corresponding to `x i`. -/
@[simp]
lemma homOfAlgebra_appTop_coord (x : n → A) (i : n) :
    (homOfAlgebra (R := R) x).appTop (coord (Spec (.of R)) i) =
      (Scheme.ΓSpecIso (.of A)).inv (x i) := by
  rw [homOfAlgebra_def, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, SpecIso_inv_appTop_coord,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    ConcreteCategory.hom_ofHom]
  simp

/-- `homOfAlgebra (R := R)` is injective in the coordinate tuple `x : n → A`. -/
@[simp]
lemma homOfAlgebra_inj {x y : n → A} :
    homOfAlgebra (R := R) x = homOfAlgebra (R := R) y ↔ x = y := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ h ▸ rfl⟩
  simpa using congrArg (Scheme.ΓSpecIso (.of A)).hom
    (congrArg (fun f ↦ f.appTop (coord (Spec (.of R)) i)) h)

/-- Evaluating at the standard indeterminates `MvPolynomial.X` yields `(SpecIso n (.of R)).inv`. -/
@[simp]
lemma homOfAlgebra_X :
    homOfAlgebra (R := R) (MvPolynomial.X : n → MvPolynomial n R) = (SpecIso n (.of R)).inv := by
  simp [homOfAlgebra_def]

/-- `homOfAlgebra x` agrees with `homOfVector` applied to the global sections corresponding to
`x`. -/
lemma homOfAlgebra_eq_homOfVector (x : n → A) :
    homOfAlgebra (R := R) x =
      homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        ((Scheme.ΓSpecIso (.of A)).inv ∘ x) := by
  refine hom_ext (by simp) fun i ↦ ?_
  simp

/-- Postcomposing `homOfAlgebra x` with `reindex g (Spec (.of R))` reindexes the coordinates `x`
along `g`. -/
@[reassoc (attr := simp)]
lemma homOfAlgebra_reindex (x : n → A) (g : m → n) :
    homOfAlgebra (R := R) x ≫ reindex g (Spec (.of R)) = homOfAlgebra (R := R) (x ∘ g) := by
  refine hom_ext (by simp) fun j ↦ ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
    homOfAlgebra_appTop_coord, homOfAlgebra_appTop_coord]
  rfl

/-- Precomposing `homOfAlgebra x` with `Spec.map` of an `R`-algebra morphism `f : A →ₐ[R] B`
applies `f` to the coordinates `x`. -/
@[reassoc]
lemma specMap_homOfAlgebra {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (x : n → A) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ homOfAlgebra (R := R) x =
      homOfAlgebra (R := R) (f ∘ x) := by
  have hcomp : f.comp (MvPolynomial.aeval (R := R) x) = MvPolynomial.aeval (R := R) (f ∘ x) :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  simp only [homOfAlgebra_def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, hcomp]

/-- Composing `homOfAlgebra x` with the linear map defined by a matrix `C : Matrix m n R` produces
`homOfAlgebra` for the linear combinations `i ↦ ∑ j, C i j • x j`. -/
@[reassoc]
lemma homOfAlgebra_linearMap [Fintype n] (x : n → A) (C : Matrix m n R) :
    homOfAlgebra (R := R) x ≫
        linearMap (Spec (.of R)) (C.map (Scheme.ΓSpecIso (.of R)).inv) =
      homOfAlgebra (R := R) (fun i ↦ ∑ j, C i j • x j) := by
  rw [homOfAlgebra_eq_homOfVector, homOfVector_linearMap, homOfAlgebra_eq_homOfVector]
  congr 1
  ext i
  simp only [Function.comp_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Algebra.smul_def, map_mul, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, ConcreteCategory.hom_ofHom]

/-- `homOfAlgebra x : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is a closed immersion if and only if
`x` generates `A` as an `R`-algebra. -/
@[simp]
theorem isClosedImmersion_homOfAlgebra_iff {x : n → A} :
    IsClosedImmersion (homOfAlgebra (R := R) x) ↔ Algebra.adjoin R (Set.range x) = ⊤ := by
  rw [homOfAlgebra_def, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (SpecIso n (.of R)).inv,
    IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd RingHom.surjective_respectsIso,
    CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← AlgHom.range_eq_top,
    ← Algebra.adjoin_range_eq_range_aeval]

/-- `homOfAlgebra y : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is a finite morphism of schemes if and
only if `MvPolynomial.aeval y` is module-finite. -/
@[simp]
theorem isFinite_homOfAlgebra_iff {y : n → A} :
    IsFinite (homOfAlgebra (R := R) y) ↔ (MvPolynomial.aeval (R := R) y).Finite := by
  refine ⟨fun _ ↦ ?_, fun hfin ↦ ?_⟩
  · rw [AlgHom.Finite, ← CommRingCat.hom_ofHom (MvPolynomial.aeval (R := R) y).toRingHom,
      ← IsFinite.SpecMap_iff, ← homOfAlgebra_specIso_hom]
    infer_instance
  · have : IsFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) y).toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr hfin
    rw [homOfAlgebra_def]
    infer_instance

/-- If `y : n → A` is algebraically independent over `R` and makes `A` integral over
`MvPolynomial n R`, then `homOfAlgebra y : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is surjective. -/
theorem surjective_homOfAlgebra {y : n → A}
    (hind : AlgebraicIndependent R y)
    (hint : (MvPolynomial.aeval (R := R) y).toRingHom.IsIntegral) :
    Surjective (homOfAlgebra (R := R) y) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) y).toRingHom)) := by
    rw [surjective_iff]
    -- `Spec_carrier` identifies the carrier of `Spec (.of _)` with `PrimeSpectrum _` (no carrier
    -- equivalence exists in `Mathlib.AlgebraicGeometry.Scheme`); `Spec.map_apply` and
    -- `CommRingCat.hom_ofHom` then identify the underlying map with `PrimeSpectrum.comap`.
    intro q
    obtain ⟨p, hp⟩ := hint.comap_surjective (algebraicIndependent_iff_injective_aeval.mp hind) q
    exact ⟨p, (Spec.map_apply (CommRingCat.ofHom (MvPolynomial.aeval (R := R) y).toRingHom) p).trans
      (by rwa [CommRingCat.hom_ofHom])⟩
  rw [homOfAlgebra_def]
  infer_instance

end HomOfAlgebra

end

end AlgebraicGeometry.AffineSpace
