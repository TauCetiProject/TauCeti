/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.IdealLocus
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Base change of the Grassmannian scheme

Let `M` be a module over a commutative ring `R`, let `R'` be an `R`-algebra and `k` a natural
number. This file proves that the formation of the Grassmannian scheme
`Module.Grassmannian.scheme R M k` commutes with base change along `Spec R' ⟶ Spec R`: the
Grassmannian `G(k, R' ⊗[R] M)` of the base-changed module over `Spec R'` is the fibre product
`Spec R' ×_{Spec R} G(k, M)` (`Module.Grassmannian.isPullback_baseChangeHom`).

Both schemes represent the same functor on affine schemes over `Spec R'`. For an `R'`-algebra
`A`, a morphism `Spec A ⟶ G(k, R' ⊗[R] M)` over `Spec R'` is a point of
`G(k, A ⊗[R'] (R' ⊗[R] M); A)` (`Module.Grassmannian.schemeHomEquiv`), and the isomorphism
`A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M` identifies these points with the points of `G(k, A ⊗[R] M; A)`
(`Module.Grassmannian.baseChangeEquiv`), that is, with the morphisms `Spec A ⟶ G(k, M)` over
`Spec R`. This identification is natural in `A` (`Module.Grassmannian.baseChangeEquiv_map`), so
it is composition with a morphism `Module.Grassmannian.baseChangeHom R R' M k` from
`G(k, R' ⊗[R] M)` to `G(k, M)` (`AlgebraicGeometry.Scheme.homOfAffinePoints`), and the square
formed with the structure morphisms is a pullback square because it is one on affine points
(`AlgebraicGeometry.Scheme.isPullback_of_forall_spec`).

This is the comparison used to glue the Grassmannians of a finite locally free module over an
affine cover of a non-affine base: over a basic open `Spec R[1/f] ⊆ Spec R` it identifies the
restriction of `G(k, M)` with `G(k, M[1/f])`.

Closed subschemes of the Grassmannian cut out by base-change-compatible ideals of points
(`Module.Grassmannian.schemeIdealLocus`) are compatible with this base change: if the ideal `I'` of
a point of `G(k, R' ⊗[R] M)` over an `R'`-algebra `A` is the ideal `I` of its image in
`G(k, A ⊗[R] M; A)`, then the closed subscheme cut out by `I'` is the inverse image of the one cut
out by `I` (`Module.Grassmannian.comap_baseChangeHom_schemeIdealLocus`), hence its base change to
`Spec R'` (`Module.Grassmannian.isPullback_baseChangeHom_schemeIdealLocus`). Both ideal sheaves are
determined by their inverse images along morphisms from affine schemes, which classify points.

## Main definitions

* `Module.Grassmannian.baseChangeHom R R' M k`: the projection
  `G(k, R' ⊗[R] M) ⟶ G(k, M)`, sending the point classifying `N` to the point classifying its
  image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_baseChangeHom`: the characterisation of
  `baseChangeHom` on points.
* `Module.Grassmannian.isPullback_baseChangeHom`: **base change**; `G(k, R' ⊗[R] M)` is the fibre
  product of `G(k, M)` and `Spec R'` over `Spec R`.
* `Module.Grassmannian.comap_baseChangeHom_schemeIdealLocus` and
  `Module.Grassmannian.isPullback_baseChangeHom_schemeIdealLocus`: base change of the closed
  subschemes cut out by ideals of points.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type u) [AddCommGroup M]
  [Module R M] (k : ℕ)

/-- The morphism `Spec A ⟶ G(k, M)` over `Spec R` classifying the image in `G(k, A ⊗[R] M; A)` of
a point over an `R'`-algebra `A`. The algebra structure of `A` over `R` and the scalar tower are
explicit arguments, so that `baseChangePoints_congr` can compare different choices. -/
private noncomputable def baseChangePoints (A : Type u) [CommRing A] [Algebra R' A]
    (_ : Algebra R A) (_ : IsScalarTower R R' A) (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    Spec (.of A) ⟶ scheme R M k :=
  toSchemeHom (baseChangeEquiv R' N)

-- `baseChangePoints` depends on the algebra structure over `R` only through its equality class.
private lemma baseChangePoints_congr (A : Type u) [CommRing A] [Algebra R' A] (iR jR : Algebra R A)
    (t : @IsScalarTower R R' A _ _ (@Algebra.toSMul _ _ _ _ iR))
    (t' : @IsScalarTower R R' A _ _ (@Algebra.toSMul _ _ _ _ jR)) (h : iR = jR)
    (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    baseChangePoints R R' M k A iR t N = baseChangePoints R R' M k A jR t' N := by
  subst h
  rfl

/-- `baseChangePoints` with the algebra structure over `R` through `R'`. -/
private noncomputable def baseChangePoints' (A : Type u) [CommRing A] [Algebra R' A]
    (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) : Spec (.of A) ⟶ scheme R M k :=
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  baseChangePoints R R' M k A ‹_› (.of_algebraMap_eq' rfl) N

variable {R R' M k}

private lemma baseChangePoints'_eq (A : Type u) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    baseChangePoints' R R' M k A N = toSchemeHom (baseChangeEquiv R' N) :=
  baseChangePoints_congr R R' M k A _ _ _ ‹_›
    (Algebra.algebra_ext _ _ fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]) N

/-- `baseChangePoints'` is natural in the `R'`-algebra. -/
private lemma baseChangePoints'_map (A B : Type u) [CommRing A] [Algebra R' A] [CommRing B]
    [Algebra R' B] (f : A →ₐ[R'] B) (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    baseChangePoints' R R' M k B (map f N) =
      Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ baseChangePoints' R R' M k A N := by
  let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  let _ : Algebra R B := ((algebraMap R' B).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  rw [baseChangePoints'_eq, baseChangePoints'_eq, baseChangeEquiv_map, toSchemeHom_map]
  -- `f.restrictScalars R` has underlying ring map `f`
  rfl

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

variable (R R' M k) in
/-- **The projection from the Grassmannian of a base change.** For an `R`-algebra `R'`, the
morphism `G(k, R' ⊗[R] M) ⟶ G(k, M)` which sends the point classifying `N` over an `R'`-algebra
`A` to the point classifying its image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`
(`Module.Grassmannian.toSchemeHom_comp_baseChangeHom`). Together with the structure morphism of
`G(k, R' ⊗[R] M)`, it exhibits `G(k, R' ⊗[R] M)` as the base change of `G(k, M)` to `Spec R'`
(`Module.Grassmannian.isPullback_baseChangeHom`). -/
noncomputable def baseChangeHom : scheme R' (R' ⊗[R] M) k ⟶ scheme R M k :=
  homOfPoints (baseChangePoints' R R' M k) baseChangePoints'_map

/-- **`baseChangeHom` on points.** The morphism classifying `N` over an `R'`-algebra `A`, composed
with `baseChangeHom`, classifies the image of `N` in `G(k, A ⊗[R] M; A)`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_baseChangeHom (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    toSchemeHom N ≫ baseChangeHom R R' M k = toSchemeHom (baseChangeEquiv R' N) :=
  (toSchemeHom_comp_homOfPoints _ _ N).trans (baseChangePoints'_eq A N)

variable (R R' M k) in
/-- `baseChangeHom` lies over `Spec R' ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem baseChangeHom_toSpec :
    baseChangeHom R R' M k ≫ toSpec R M k =
      toSpec R' (R' ⊗[R] M) k ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  -- make `B` an `R'`-algebra through `a`, so that `a` classifies a point over `B`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R' (R' ⊗[R] M) k)
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  rw [toSchemeHom_comp_baseChangeHom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec_assoc,
    ← Spec.map_comp]
  -- `algebraMap R B` is `φ ∘ algebraMap R R'` by definition
  rfl

variable (R R' M k) in
/-- **Base change of the Grassmannian scheme.** For an `R`-algebra `R'`, the Grassmannian
`G(k, R' ⊗[R] M)` over `Spec R'` is the fibre product of `G(k, M) ⟶ Spec R` and
`Spec R' ⟶ Spec R`, with projections `baseChangeHom` and the structure morphism. -/
theorem isPullback_baseChangeHom :
    IsPullback (baseChangeHom R R' M k) (toSpec R' (R' ⊗[R] M) k) (toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  refine Scheme.isPullback_of_forall_spec (baseChangeHom_toSpec R R' M k) fun B a b hab ↦ ?_
  -- `b` makes `B` an `R'`-algebra, and `a` classifies a point of `G(k, B ⊗[R] M; B)`
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a (hab.trans (Spec.map_comp _ _).symm)
  refine ⟨toSchemeHom ((baseChangeEquiv R').symm N), ⟨by simp, toSchemeHom_toSpec _⟩, ?_⟩
  rintro c ⟨hc₁, hc₂⟩
  obtain ⟨N', rfl⟩ := exists_toSchemeHom_eq (A := B) c hc₂
  rw [toSchemeHom_comp_baseChangeHom] at hc₁
  rw [← toSchemeHom_injective hc₁, Equiv.symm_apply_apply]

end Module.Grassmannian

namespace Module.Grassmannian

open Scheme.IdealSheafData

section IdealLocus

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type u} [AddCommGroup M]
  [Module R M] {k : ℕ}
  (I : ∀ {A : Type u} [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → Ideal A)
  (hI : ∀ {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)), I (map f N) = Ideal.map f (I N))
  (I' : ∀ {A : Type u} [CommRing A] [Algebra R' A], G(k, A ⊗[R'] (R' ⊗[R] M); A) → Ideal A)
  (hI' : ∀ {A B : Type u} [CommRing A] [Algebra R' A] [CommRing B] [Algebra R' B]
    (f : A →ₐ[R'] B) (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)), I' (map f N) = Ideal.map f (I' N))

/-- **Base change of a closed subscheme cut out by ideals of points.** Let `I` be a
base-change-compatible ideal of points of `G(k, M)`, and `I'` one of points of
`G(k, R' ⊗[R] M)`, such that `I'` of a point over an `R'`-algebra is `I` of its image in
`G(k, A ⊗[R] M; A)`. Then the inverse image of the closed subscheme cut out by `I` along
`baseChangeHom` is the closed subscheme cut out by `I'`. -/
theorem comap_baseChangeHom_schemeIdealLocus
    (h : ∀ {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)), I (baseChangeEquiv R' N) = I' N) :
    (schemeIdealLocus I hI).comap (baseChangeHom R R' M k) = schemeIdealLocus I' hI' := by
  -- compare the pullbacks along every morphism from an affine scheme, which classifies a point
  have key (B : CommRingCat.{u}) (a : Spec B ⟶ scheme R' (R' ⊗[R] M) k) :
      ((schemeIdealLocus I hI).comap (baseChangeHom R R' M k)).comap a =
        (schemeIdealLocus I' hI').comap a := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R' (R' ⊗[R] M) k)
    let _ : Algebra R' B := φ.hom.toAlgebra
    let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
    have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
    obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
    rw [← comap_comp, toSchemeHom_comp_baseChangeHom, comap_toSchemeHom_schemeIdealLocus,
      comap_toSchemeHom_schemeIdealLocus, h]
  exact ext_of_comap_openCover (scheme R' (R' ⊗[R] M) k).affineCover fun i ↦ key _ _

/-- **The closed subscheme cut out by ideals of points commutes with base change.** Under the
hypothesis of `Module.Grassmannian.comap_baseChangeHom_schemeIdealLocus`, the closed subscheme of
`G(k, R' ⊗[R] M)` cut out by `I'`, as a scheme over `Spec R'`, is the base change along
`Spec R' ⟶ Spec R` of the closed subscheme of `G(k, M)` cut out by `I`, as a scheme over
`Spec R`. -/
theorem isPullback_baseChangeHom_schemeIdealLocus
    (h : ∀ {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)), I (baseChangeEquiv R' N) = I' N) :
    IsPullback
      (subschemeMap (schemeIdealLocus I' hI') (schemeIdealLocus I hI) (baseChangeHom R R' M k)
        (le_map_iff_comap_le.2 (comap_baseChangeHom_schemeIdealLocus I hI I' hI' h).le))
      ((schemeIdealLocus I' hI').subschemeι ≫ toSpec R' (R' ⊗[R] M) k)
      ((schemeIdealLocus I hI).subschemeι ≫ toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  -- the closed subscheme of `I'` is the inverse image of that of `I`, and inverse images of
  -- closed subschemes along a base change are base changes
  have key (J : (scheme R' (R' ⊗[R] M) k).IdealSheafData)
      (hJ : (schemeIdealLocus I hI).comap (baseChangeHom R R' M k) = J) (hle) :
      IsPullback (subschemeMap J (schemeIdealLocus I hI) (baseChangeHom R R' M k) hle)
        (J.subschemeι ≫ toSpec R' (R' ⊗[R] M) k)
        ((schemeIdealLocus I hI).subschemeι ≫ toSpec R M k)
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    subst hJ
    exact isPullback_subschemeMap_comap _ _ (isPullback_baseChangeHom R R' M k)
  exact key _ (comap_baseChangeHom_schemeIdealLocus I hI I' hI' h) _

end IdealLocus

end Module.Grassmannian
