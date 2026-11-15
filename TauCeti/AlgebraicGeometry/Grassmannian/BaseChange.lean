/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

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

## Main definitions

* `Module.Grassmannian.baseChangeHom R R' M k`: the projection
  `G(k, R' ⊗[R] M) ⟶ G(k, M)`, sending the point classifying `N` to the point classifying its
  image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_baseChangeHom`: the characterisation of
  `baseChangeHom` on points.
* `Module.Grassmannian.isPullback_baseChangeHom`: **base change**; `G(k, R' ⊗[R] M)` is the fibre
  product of `G(k, M)` and `Spec R'` over `Spec R`.

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

/-- The morphism `Spec A ⟶ G(k, M)` over `Spec R` classifying the point of `G(k, A ⊗[R] M; A)`
which corresponds to a morphism `Spec A ⟶ G(k, R' ⊗[R] M)` over `Spec R'`. The algebra structures
on `A` are explicit arguments, so that `baseChangeAux_congr` can compare different choices. -/
private noncomputable def baseChangeAux (A : Type u) [CommRing A] (_ : Algebra R' A)
    (_ : Algebra R A) (_ : IsScalarTower R R' A) (a : Spec (.of A) ⟶ scheme R' (R' ⊗[R] M) k)
    (ha : a ≫ toSpec R' (R' ⊗[R] M) k = Spec.map (CommRingCat.ofHom (algebraMap R' A))) :
    Spec (.of A) ⟶ scheme R M k :=
  toSchemeHom (baseChangeEquiv R' ((schemeHomEquiv R' (R' ⊗[R] M) k A).symm ⟨a, ha⟩))

-- `baseChangeAux` depends on the algebra structures on `A` only through their equality class.
private lemma baseChangeAux_congr (A : Type u) [CommRing A] (iR' jR' : Algebra R' A)
    (iR jR : Algebra R A)
    (t : @IsScalarTower R R' A _ (@Algebra.toSMul _ _ _ _ iR') (@Algebra.toSMul _ _ _ _ iR))
    (t' : @IsScalarTower R R' A _ (@Algebra.toSMul _ _ _ _ jR') (@Algebra.toSMul _ _ _ _ jR))
    (h' : iR' = jR') (h : iR = jR) (a : Spec (.of A) ⟶ scheme R' (R' ⊗[R] M) k) (ha ha') :
    baseChangeAux R R' M k A iR' iR t a ha = baseChangeAux R R' M k A jR' jR t' a ha' := by
  subst h' h
  rfl

/-- The morphism of affine points underlying `baseChangeHom`: the algebra structure of `A` over
`R'` is read off from the composite `Spec A ⟶ G(k, R' ⊗[R] M) ⟶ Spec R'`. -/
private noncomputable def baseChangePoint {A : CommRingCat.{u}}
    (a : Spec A ⟶ scheme R' (R' ⊗[R] M) k) : Spec A ⟶ scheme R M k :=
  let φ : R' →+* A := (Spec.preimage (a ≫ toSpec R' (R' ⊗[R] M) k)).hom
  letI := φ.toAlgebra
  letI : Algebra R A := (φ.comp (algebraMap R R')).toAlgebra
  baseChangeAux R R' M k A ‹_› ‹_› (.of_algebraMap_eq' rfl) a (Spec.map_preimage _).symm

variable {R R' M k}

/-- `baseChangePoint` computed with any algebra structures on `A` compatible with the morphism. -/
private lemma baseChangePoint_eq (A : Type u) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (a : Spec (.of A) ⟶ scheme R' (R' ⊗[R] M) k)
    (ha : a ≫ toSpec R' (R' ⊗[R] M) k = Spec.map (CommRingCat.ofHom (algebraMap R' A))) :
    baseChangePoint R R' M k a = baseChangeAux R R' M k A ‹_› ‹_› ‹_› a ha := by
  have hφ : (Spec.preimage (a ≫ toSpec R' (R' ⊗[R] M) k)).hom = algebraMap R' A := by
    rw [ha, Spec.preimage_map, CommRingCat.hom_ofHom]
  refine baseChangeAux_congr R R' M k A _ _ _ _ _ ‹_› ?_ ?_ a _ _
  · exact Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r
  · refine Algebra.algebra_ext _ _ fun r ↦ ?_
    rw [IsScalarTower.algebraMap_apply R R' A]
    exact DFunLike.congr_fun hφ _

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

private lemma baseChangePoint_toSchemeHom (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    baseChangePoint R R' M k (toSchemeHom N) = toSchemeHom (baseChangeEquiv R' N) := by
  rw [baseChangePoint_eq A _ (toSchemeHom_toSpec N), baseChangeAux]
  congr 2
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `baseChangePoint` is natural in the affine scheme. -/
private lemma baseChangePoint_comp {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B)
    (a : Spec B ⟶ scheme R' (R' ⊗[R] M) k) :
    baseChangePoint R R' M k (ψ ≫ a) = ψ ≫ baseChangePoint R R' M k a := by
  -- give `B` and `C` the algebra structures over `R'` read off from `a` and `ψ ≫ a`; with them,
  -- `algebraMap R' B` is `φ` by definition, and `χ` is an `R'`-algebra map `χ'`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R' (R' ⊗[R] M) k)
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  let _ : Algebra R' C := (χ.hom.comp φ.hom).toAlgebra
  let _ : Algebra R C := ((χ.hom.comp φ.hom).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' C := .of_algebraMap_eq' rfl
  let χ' : B →ₐ[R'] C := { χ.hom with commutes' := fun _ ↦ rfl }
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := (toSchemeHom_map χ' N).symm
  rw [h, baseChangePoint_toSchemeHom, baseChangePoint_toSchemeHom, baseChangeEquiv_map,
    toSchemeHom_map]
  -- `χ'.restrictScalars R` has underlying ring map `χ`
  rfl

variable (R R' M k) in
/-- **The projection from the Grassmannian of a base change.** For an `R`-algebra `R'`, the
morphism `G(k, R' ⊗[R] M) ⟶ G(k, M)` which sends the point classifying `N` over an `R'`-algebra
`A` to the point classifying its image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`
(`Module.Grassmannian.toSchemeHom_comp_baseChangeHom`). Together with the structure morphism of
`G(k, R' ⊗[R] M)`, it exhibits `G(k, R' ⊗[R] M)` as the base change of `G(k, M)` to `Spec R'`
(`Module.Grassmannian.isPullback_baseChangeHom`). -/
noncomputable def baseChangeHom : scheme R' (R' ⊗[R] M) k ⟶ scheme R M k :=
  Scheme.homOfAffinePoints (baseChangePoint R R' M k) baseChangePoint_comp

/-- **`baseChangeHom` on points.** The morphism classifying `N` over an `R'`-algebra `A`, composed
with `baseChangeHom`, classifies the image of `N` in `G(k, A ⊗[R] M; A)`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_baseChangeHom (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    toSchemeHom N ≫ baseChangeHom R R' M k = toSchemeHom (baseChangeEquiv R' N) :=
  (Scheme.comp_homOfAffinePoints _ _ _).trans (baseChangePoint_toSchemeHom N)

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
