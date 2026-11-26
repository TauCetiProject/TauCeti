/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points

/-!
# Base change of the Grassmannian scheme

Let `R → R'` be a map of commutative rings, `M` an `R`-module, `M'` an `R'`-module and
`f : M →ₗ[R] M'` an `R`-linear map exhibiting `M'` as the base change of `M` to `R'`
(`hf : IsBaseChange R' f`), and let `k` be a natural number. This file constructs the morphism of
Grassmannian schemes `hf.grassmannianSchemeHom k : G(k, M') ⟶ G(k, M)` over
`Spec R' ⟶ Spec R` and proves that it exhibits `G(k, M')` as the fibre product
`Spec R' ×_{Spec R} G(k, M)` (`IsBaseChange.isPullback_grassmannianSchemeHom`): the formation of
the Grassmannian scheme commutes with base change. These morphisms compose
(`IsBaseChange.grassmannianSchemeHom_comp`).

Both schemes represent the same functor on affine schemes over `Spec R'`. For an `R'`-algebra
`A`, a morphism `Spec A ⟶ G(k, M')` over `Spec R'` is a point of `G(k, A ⊗[R'] M'; A)`
(`Module.Grassmannian.schemeHomEquiv`), and the isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M` sending
`a ⊗ f m` to `a ⊗ m` (`IsBaseChange.cancelBaseChange`) identifies these points with the points of
`G(k, A ⊗[R] M; A)` (`IsBaseChange.grassmannianEquiv`), that is, with the morphisms
`Spec A ⟶ G(k, M)` over `Spec R`. This identification is natural in `A`, so it is composition with
a unique morphism of schemes (`Module.Grassmannian.homOfPoints`), and the square formed
with the structure morphisms is a pullback square because it is one on affine points
(`AlgebraicGeometry.Scheme.isPullback_of_forall_spec`).

`Module.Grassmannian.baseChangeHom R R' M k : G(k, R' ⊗[R] M) ⟶ G(k, M)` is the case of the
tensor product `M' = R' ⊗[R] M` with `f m = 1 ⊗ m`. For instance, over a basic open
`Spec R[1/f] ⊆ Spec R` it identifies the restriction of `G(k, M)` with `G(k, R[1/f] ⊗[R] M)`.
The general form serves modules `M'` which are base changes without being tensor products by
construction: for affine opens `V ≤ U` of a scheme `X` and a quasi-coherent `𝒪_X`-module `E`,
restriction induces an isomorphism `Γ(X, V) ⊗[Γ(X, U)] Γ(E, U) ≃ₗ[Γ(X, V)] Γ(E, V)`, but the two
modules are not definitionally identified
(`TauCeti.AlgebraicGeometry.Grassmannian.Relative.Basic`).

## Main definitions

* `IsBaseChange.grassmannianSchemeHom hf k`: the morphism `G(k, M') ⟶ G(k, M)`.
* `Module.Grassmannian.baseChangeHom R R' M k`: the projection `G(k, R' ⊗[R] M) ⟶ G(k, M)`.

## Main results

* `IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom`: the morphism on points.
* `IsBaseChange.isPullback_grassmannianSchemeHom`: **base change**; `G(k, M')` is the fibre
  product of `G(k, M)` and `Spec R'` over `Spec R`.
* `IsBaseChange.isIso_grassmannianSchemeHom`: along a bijective `algebraMap R R'`, the morphism
  `G(k, M') ⟶ G(k, M)` is an isomorphism.
* `IsBaseChange.grassmannianSchemeHom_comp`: the morphisms for two successive base changes
  compose to the morphism for the composite base change.
* `Module.Grassmannian.toSchemeHom_comp_baseChangeHom` and
  `Module.Grassmannian.isPullback_baseChangeHom`: the same for `baseChangeHom`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct Module.Grassmannian

namespace IsBaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [Module R M']
  [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)

section Scheme

variable (k : ℕ)

/-- The morphism `Spec A ⟶ G(k, M)` over `Spec R` classifying the image in `G(k, A ⊗[R] M; A)` of
a point over an `R'`-algebra `A`. The algebra structure of `A` over `R` and the scalar tower are
explicit arguments, so that `grassmannianPoints_congr` can compare different choices. -/
private noncomputable def grassmannianPoints (A : Type u) [CommRing A] [Algebra R' A]
    (_ : Algebra R A) (_ : IsScalarTower R R' A) (N : G(k, A ⊗[R'] M'; A)) :
    Spec (.of A) ⟶ scheme R M k :=
  toSchemeHom (hf.grassmannianEquiv A N)

-- `grassmannianPoints` depends on the algebra structure over `R` only through its equality class.
private lemma grassmannianPoints_congr (A : Type u) [CommRing A] [Algebra R' A]
    (iR jR : Algebra R A) (t : @IsScalarTower R R' A _ _ (@Algebra.toSMul _ _ _ _ iR))
    (t' : @IsScalarTower R R' A _ _ (@Algebra.toSMul _ _ _ _ jR)) (h : iR = jR)
    (N : G(k, A ⊗[R'] M'; A)) :
    grassmannianPoints hf k A iR t N = grassmannianPoints hf k A jR t' N := by
  subst h
  rfl

/-- `grassmannianPoints` with the algebra structure over `R` through `R'`. -/
private noncomputable def grassmannianPoints' (A : Type u) [CommRing A] [Algebra R' A]
    (N : G(k, A ⊗[R'] M'; A)) : Spec (.of A) ⟶ scheme R M k :=
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  grassmannianPoints hf k A ‹_› (.of_algebraMap_eq' rfl) N

variable {k}

private lemma grassmannianPoints'_eq (A : Type u) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (N : G(k, A ⊗[R'] M'; A)) :
    grassmannianPoints' hf k A N = toSchemeHom (hf.grassmannianEquiv A N) :=
  grassmannianPoints_congr hf k A _ _ _ ‹_›
    (by rw [← IsScalarTower.algebraMap_eq R R' A, toAlgebra_algebraMap]) N

/-- `grassmannianPoints'` is natural in the `R'`-algebra. -/
private lemma grassmannianPoints'_map (A B : Type u) [CommRing A] [Algebra R' A] [CommRing B]
    [Algebra R' B] (g : A →ₐ[R'] B) (N : G(k, A ⊗[R'] M'; A)) :
    grassmannianPoints' hf k B (map g N) =
      Spec.map (CommRingCat.ofHom (g : A →+* B)) ≫ grassmannianPoints' hf k A N := by
  let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  let _ : Algebra R B := ((algebraMap R' B).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  rw [grassmannianPoints'_eq, grassmannianPoints'_eq, grassmannianEquiv_map, toSchemeHom_map,
    AlgHom.coe_restrictScalars]

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

variable (k) in
/-- **The Grassmannian along a base change of modules.** For a base change `f : M → M'` along
`R → R'`, the morphism `G(k, M') ⟶ G(k, M)` which sends the point classifying `N` over an
`R'`-algebra `A` to the point classifying its image under `A ⊗[R'] M' ≃ A ⊗[R] M`
(`IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom`). Together with the structure morphism
of `G(k, M')`, it exhibits `G(k, M')` as the base change of `G(k, M)` to `Spec R'`
(`IsBaseChange.isPullback_grassmannianSchemeHom`). -/
noncomputable def grassmannianSchemeHom : scheme R' M' k ⟶ scheme R M k :=
  homOfPoints (grassmannianPoints' hf k) (grassmannianPoints'_map hf)

variable (k) in
/-- `grassmannianSchemeHom` depends on the base change map only through its value: two equal maps
give the same morphism, whichever proofs of the base change property are used. -/
theorem grassmannianSchemeHom_congr {f' : M →ₗ[R] M'} (hf' : IsBaseChange R' f') (h : f = f') :
    grassmannianSchemeHom hf k = grassmannianSchemeHom hf' k := by
  subst h
  rfl

/-- **`grassmannianSchemeHom` on points.** The morphism classifying `N` over an `R'`-algebra `A`,
composed with `grassmannianSchemeHom`, classifies the image of `N` in `G(k, A ⊗[R] M; A)`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_grassmannianSchemeHom (N : G(k, A ⊗[R'] M'; A)) :
    toSchemeHom N ≫ grassmannianSchemeHom hf k = toSchemeHom (hf.grassmannianEquiv A N) :=
  (toSchemeHom_comp_homOfPoints _ _ N).trans (grassmannianPoints'_eq hf A N)

variable (k) in
/-- `grassmannianSchemeHom` lies over `Spec R' ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem grassmannianSchemeHom_toSpec :
    grassmannianSchemeHom hf k ≫ toSpec R M k =
      toSpec R' M' k ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  scheme_hom_ext fun A _ _ N ↦ by
    -- make `A` an `R`-algebra through `R'`, so that `grassmannianSchemeHom` can be computed on
    -- points
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
    rw [toSchemeHom_comp_grassmannianSchemeHom_assoc, toSchemeHom_toSpec,
      toSchemeHom_toSpec_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]

variable (k) in
/-- **Base change of the Grassmannian scheme along a base change of modules.** For a base change
`f : M → M'` along `R → R'`, the Grassmannian `G(k, M')` over `Spec R'` is the fibre product of
`G(k, M) ⟶ Spec R` and `Spec R' ⟶ Spec R`, with projections `grassmannianSchemeHom` and the
structure morphism. -/
theorem isPullback_grassmannianSchemeHom :
    IsPullback (grassmannianSchemeHom hf k) (toSpec R' M' k) (toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  refine Scheme.isPullback_of_forall_spec (grassmannianSchemeHom_toSpec hf k) fun B a b hab ↦ ?_
  -- `b` makes `B` an `R'`-algebra, and `a` classifies a point of `G(k, B ⊗[R] M; B)`
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  have hφ : CommRingCat.ofHom (algebraMap R' B) = φ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a <| by
    rw [hab, IsScalarTower.algebraMap_eq R R' B, CommRingCat.ofHom_comp, hφ, Spec.map_comp]
  refine ⟨toSchemeHom ((hf.grassmannianEquiv B).symm N),
    ⟨by simp, (toSchemeHom_toSpec _).trans (by rw [hφ])⟩, ?_⟩
  rintro c ⟨hc₁, hc₂⟩
  obtain ⟨N', rfl⟩ := exists_toSchemeHom_eq (A := B) c hc₂
  rw [toSchemeHom_comp_grassmannianSchemeHom] at hc₁
  rw [← toSchemeHom_injective hc₁, Equiv.symm_apply_apply]

variable (k) in
/-- Along a bijective `algebraMap R R'`, the morphism `G(k, M') ⟶ G(k, M)` is an isomorphism: it is
the base change of `G(k, M)` along the isomorphism `Spec R' ⟶ Spec R`. -/
theorem isIso_grassmannianSchemeHom (h : Function.Bijective (algebraMap R R')) :
    IsIso (grassmannianSchemeHom hf k) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R R')) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  exact (hf.isPullback_grassmannianSchemeHom k).flip.isIso_snd_of_isIso

section Comp

variable {R'' M'' : Type u} [CommRing R''] [Algebra R' R''] [Algebra R R'']
  [IsScalarTower R R' R''] [AddCommGroup M''] [Module R'' M''] [Module R' M''] [Module R M'']
  [IsScalarTower R' R'' M''] [IsScalarTower R R'' M''] [IsScalarTower R R' M''] {g : M' →ₗ[R'] M''}
  (hg : IsBaseChange R'' g)

/-- **Composition of `grassmannianSchemeHom`.** For base changes `f : M → M'` along `R → R'` and
`g : M' → M''` along `R' → R''`, the composite of the morphisms `G(k, M'') ⟶ G(k, M')` and
`G(k, M') ⟶ G(k, M)` is the morphism of the composite base change `g ∘ f` along `R → R''`. -/
theorem grassmannianSchemeHom_comp (hgf : IsBaseChange R'' (g.restrictScalars R ∘ₗ f)) :
    grassmannianSchemeHom hg k ≫ grassmannianSchemeHom hf k = grassmannianSchemeHom hgf k := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ affinePoint_induction (R₀ := R')
    (fun A _ _ _ _ N ↦ ?_) a
  -- make `A` an `R`-algebra through `R'`
  let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  have : IsScalarTower R R'' A := .of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq R R' R'', ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R' R'' A]
    exact RingHom.algebraMap_toAlgebra _
  rw [toSchemeHom_comp_grassmannianSchemeHom_assoc, toSchemeHom_comp_grassmannianSchemeHom,
    toSchemeHom_comp_grassmannianSchemeHom]
  congr 1
  ext : 1
  rw [toSubmodule_grassmannianEquiv, toSubmodule_grassmannianEquiv, toSubmodule_grassmannianEquiv,
    ← Submodule.map_comp, ← LinearEquiv.coe_trans,
    cancelBaseChange_trans_cancelBaseChange hf hg hgf]

end Comp

end Scheme

end IsBaseChange

namespace Module.Grassmannian

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type u) [AddCommGroup M]
  [Module R M] (k : ℕ)

/-- **The projection from the Grassmannian of a base change.** For an `R`-algebra `R'`, the
morphism `G(k, R' ⊗[R] M) ⟶ G(k, M)` which sends the point classifying `N` over an `R'`-algebra
`A` to the point classifying its image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`
(`Module.Grassmannian.toSchemeHom_comp_baseChangeHom`): the morphism
`IsBaseChange.grassmannianSchemeHom` of the base change `m ↦ 1 ⊗ m`. Together with the structure
morphism of `G(k, R' ⊗[R] M)`, it exhibits `G(k, R' ⊗[R] M)` as the base change of `G(k, M)` to
`Spec R'` (`Module.Grassmannian.isPullback_baseChangeHom`). -/
noncomputable def baseChangeHom : scheme R' (R' ⊗[R] M) k ⟶ scheme R M k :=
  (TensorProduct.isBaseChange R M R').grassmannianSchemeHom k

variable {R R' M k}

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

/-- **`baseChangeHom` on points.** The morphism classifying `N` over an `R'`-algebra `A`, composed
with `baseChangeHom`, classifies the image of `N` in `G(k, A ⊗[R] M; A)`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_baseChangeHom (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    toSchemeHom N ≫ baseChangeHom R R' M k = toSchemeHom (baseChangeEquiv R' N) := by
  rw [baseChangeHom, IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom,
    baseChangeEquiv_eq_grassmannianEquiv]

variable (R R' M k) in
/-- `baseChangeHom` lies over `Spec R' ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem baseChangeHom_toSpec :
    baseChangeHom R R' M k ≫ toSpec R M k =
      toSpec R' (R' ⊗[R] M) k ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  IsBaseChange.grassmannianSchemeHom_toSpec _ k

variable (R R' M k) in
/-- **Base change of the Grassmannian scheme.** For an `R`-algebra `R'`, the Grassmannian
`G(k, R' ⊗[R] M)` over `Spec R'` is the fibre product of `G(k, M) ⟶ Spec R` and
`Spec R' ⟶ Spec R`, with projections `baseChangeHom` and the structure morphism. -/
theorem isPullback_baseChangeHom :
    IsPullback (baseChangeHom R R' M k) (toSpec R' (R' ⊗[R] M) k) (toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  IsBaseChange.isPullback_grassmannianSchemeHom _ k

end Module.Grassmannian
