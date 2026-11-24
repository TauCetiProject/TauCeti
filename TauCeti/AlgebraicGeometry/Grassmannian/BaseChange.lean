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
a unique morphism of schemes (`AlgebraicGeometry.Scheme.homOfAffinePoints`), and the square formed
with the structure morphisms is a pullback square because it is one on affine points
(`AlgebraicGeometry.Scheme.isPullback_of_forall_spec`).

`Module.Grassmannian.baseChangeHom R R' M k : G(k, R' ⊗[R] M) ⟶ G(k, M)` is the case of the
tensor product `M' = R' ⊗[R] M` with `f m = 1 ⊗ m`. For instance, over a basic open
`Spec R[1/f] ⊆ Spec R` it identifies the restriction of `G(k, M)` with `G(k, R[1/f] ⊗[R] M)`.
The general form serves modules `M'` which are base changes without being tensor products by
construction: for affine opens `V ≤ U` of a scheme `X` and a quasi-coherent `𝒪_X`-module `E`,
restriction induces an isomorphism `Γ(X, V) ⊗[Γ(X, U)] Γ(E, U) ≃ₗ[Γ(X, V)] Γ(E, V)`, but the two
modules are not definitionally identified
(`TauCeti.AlgebraicGeometry.Grassmannian.Relative`).

## Main definitions

* `IsBaseChange.grassmannianSchemeHom hf k`: the morphism `G(k, M') ⟶ G(k, M)`.
* `Module.Grassmannian.baseChangeHom R R' M k`: the projection `G(k, R' ⊗[R] M) ⟶ G(k, M)`.

## Main results

* `IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom`: the morphism on points.
* `IsBaseChange.isPullback_grassmannianSchemeHom`: **base change**; `G(k, M')` is the fibre
  product of `G(k, M)` and `Spec R'` over `Spec R`.
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

/-- The morphism `Spec A ⟶ G(k, M)` over `Spec R` classifying the point of `G(k, A ⊗[R] M; A)`
which corresponds to a morphism `Spec A ⟶ G(k, M')` over `Spec R'`. The algebra structures on `A`
are explicit arguments, so that `grassmannianAux_congr` can compare different choices. -/
private noncomputable def grassmannianAux (A : Type u) [CommRing A] (_ : Algebra R' A)
    (_ : Algebra R A) (_ : IsScalarTower R R' A) (a : Spec (.of A) ⟶ scheme R' M' k)
    (ha : a ≫ toSpec R' M' k = Spec.map (CommRingCat.ofHom (algebraMap R' A))) :
    Spec (.of A) ⟶ scheme R M k :=
  toSchemeHom (hf.grassmannianEquiv A ((schemeHomEquiv R' M' k A).symm ⟨a, ha⟩))

-- `grassmannianAux` depends on the algebra structures on `A` only through their equality class.
private lemma grassmannianAux_congr (A : Type u) [CommRing A] (iR' jR' : Algebra R' A)
    (iR jR : Algebra R A)
    (t : @IsScalarTower R R' A _ (@Algebra.toSMul _ _ _ _ iR') (@Algebra.toSMul _ _ _ _ iR))
    (t' : @IsScalarTower R R' A _ (@Algebra.toSMul _ _ _ _ jR') (@Algebra.toSMul _ _ _ _ jR))
    (h' : iR' = jR') (h : iR = jR) (a : Spec (.of A) ⟶ scheme R' M' k) (ha ha') :
    grassmannianAux hf k A iR' iR t a ha = grassmannianAux hf k A jR' jR t' a ha' := by
  subst h' h
  rfl

/-- The morphism of affine points underlying `grassmannianSchemeHom`: the algebra structure of `A`
over `R'` is read off from the composite `Spec A ⟶ G(k, M') ⟶ Spec R'`. -/
private noncomputable def grassmannianPoint {A : CommRingCat.{u}}
    (a : Spec A ⟶ scheme R' M' k) : Spec A ⟶ scheme R M k :=
  let φ : R' →+* A := (Spec.preimage (a ≫ toSpec R' M' k)).hom
  letI := φ.toAlgebra
  letI : Algebra R A := (φ.comp (algebraMap R R')).toAlgebra
  grassmannianAux hf k A ‹_› ‹_› (.of_algebraMap_eq' rfl) a (Spec.map_preimage _).symm

variable {k}

/-- `grassmannianPoint` computed with any algebra structures on `A` compatible with the
morphism. -/
private lemma grassmannianPoint_eq (A : Type u) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (a : Spec (.of A) ⟶ scheme R' M' k)
    (ha : a ≫ toSpec R' M' k = Spec.map (CommRingCat.ofHom (algebraMap R' A))) :
    grassmannianPoint hf k a = grassmannianAux hf k A ‹_› ‹_› ‹_› a ha := by
  have hφ : (Spec.preimage (a ≫ toSpec R' M' k)).hom = algebraMap R' A := by
    rw [ha, Spec.preimage_map, CommRingCat.hom_ofHom]
  refine grassmannianAux_congr hf k A _ _ _ _ _ ‹_› ?_ ?_ a _ _
  · exact Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r
  · refine Algebra.algebra_ext _ _ fun r ↦ ?_
    rw [IsScalarTower.algebraMap_apply R R' A]
    exact DFunLike.congr_fun hφ _

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

private lemma grassmannianPoint_toSchemeHom (N : G(k, A ⊗[R'] M'; A)) :
    grassmannianPoint hf k (toSchemeHom N) = toSchemeHom (hf.grassmannianEquiv A N) := by
  rw [grassmannianPoint_eq hf A _ (toSchemeHom_toSpec N), grassmannianAux]
  congr 2
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `grassmannianPoint` is natural in the affine scheme. -/
private lemma grassmannianPoint_comp {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B)
    (a : Spec B ⟶ scheme R' M' k) :
    grassmannianPoint hf k (ψ ≫ a) = ψ ≫ grassmannianPoint hf k a := by
  revert ψ
  refine affinePoint_induction (R₀ := R) (fun A _ _ _ _ N ψ ↦ ?_) a
  -- give `C` the algebra structures over `R'` and `R` through `χ`, which becomes an `R'`-algebra
  -- map `χ'`
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R' C := (χ.hom.comp (algebraMap R' A)).toAlgebra
  let _ : Algebra R C := ((χ.hom.comp (algebraMap R' A)).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' C := .of_algebraMap_eq' rfl
  let χ' : A →ₐ[R'] C := ⟨χ.hom, fun _ ↦ rfl⟩
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := by
    rw [toSchemeHom_map, AlgHom.toRingHom_mk, CommRingCat.ofHom_hom]
  rw [h, grassmannianPoint_toSchemeHom, grassmannianPoint_toSchemeHom, grassmannianEquiv_map,
    toSchemeHom_map, AlgHom.coe_restrictScalars, AlgHom.toRingHom_mk, CommRingCat.ofHom_hom]

variable (k) in
/-- **The Grassmannian along a base change of modules.** For a base change `f : M → M'` along
`R → R'`, the morphism `G(k, M') ⟶ G(k, M)` which sends the point classifying `N` over an
`R'`-algebra `A` to the point classifying its image under `A ⊗[R'] M' ≃ A ⊗[R] M`
(`IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom`). Together with the structure morphism
of `G(k, M')`, it exhibits `G(k, M')` as the base change of `G(k, M)` to `Spec R'`
(`IsBaseChange.isPullback_grassmannianSchemeHom`). -/
noncomputable def grassmannianSchemeHom : scheme R' M' k ⟶ scheme R M k :=
  Scheme.homOfAffinePoints (grassmannianPoint hf k) (grassmannianPoint_comp hf)

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
  (Scheme.comp_homOfAffinePoints _ _ _).trans (grassmannianPoint_toSchemeHom hf N)

variable (k) in
/-- `grassmannianSchemeHom` lies over `Spec R' ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem grassmannianSchemeHom_toSpec :
    grassmannianSchemeHom hf k ≫ toSpec R M k =
      toSpec R' M' k ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ affinePoint_induction (R₀ := R)
    (fun A _ _ _ _ N ↦ ?_) a
  rw [toSchemeHom_comp_grassmannianSchemeHom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

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
