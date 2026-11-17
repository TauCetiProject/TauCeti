/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

/-!
# The Grassmannian scheme of an isomorphic module

Let `M` and `M'` be modules over a commutative ring `R` and `k` a natural number. This file
proves that a linear equivalence `e : M ≃ₗ[R] M'` induces an isomorphism of Grassmannian schemes
`G(k, M) ≅ G(k, M')` over `Spec R` (`Module.Grassmannian.schemeIsoOfLinearEquiv`), functorial in
`e`.

On points over an `R`-algebra `A`, the isomorphism sends the point classifying
`N ∈ G(k, A ⊗[R] M; A)` to the point classifying its image under the base change
`A ⊗[R] M ≃ A ⊗[R] M'` of `e` (`LinearEquiv.grassmannianCongr`). This map of points is natural in
`A` (`Module.Grassmannian.map_grassmannianCongr_baseChange`), so it is composition with a morphism
of schemes (`AlgebraicGeometry.Scheme.homOfAffinePoints`), and the identities between the maps of
points give the identities between the morphisms, since a morphism out of the Grassmannian is
determined by its points (`Module.Grassmannian.scheme_hom_ext`).

This is the comparison needed for the relative Grassmannian of a finite locally free sheaf `E` on
a scheme to be independent of the trivialisations of `E`: two trivialisations over the same affine
open differ by a linear automorphism of `M`.

## Main definitions

* `Module.Grassmannian.schemeIsoOfLinearEquiv k e`: the isomorphism `G(k, M) ≅ G(k, M')` induced
  by `e : M ≃ₗ[R] M'`.

## Main results

* `Module.Grassmannian.scheme_hom_ext`: morphisms out of `G(k, M)` agreeing on the points over
  all `R`-algebras are equal.
* `Module.Grassmannian.toSchemeHom_comp_schemeIsoOfLinearEquiv_hom`: the isomorphism on points.
* `Module.Grassmannian.schemeIsoOfLinearEquiv_hom_toSpec`: the isomorphism lies over `Spec R`.
* `Module.Grassmannian.schemeIsoOfLinearEquiv_refl`, `schemeIsoOfLinearEquiv_trans` and
  `schemeIsoOfLinearEquiv_symm`: functoriality in `e`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M M' M'' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M''] {k : ℕ}

/-- **Morphisms out of the Grassmannian are determined by its points.** Two morphisms out of
`G(k, M)` which agree after composition with the morphism classifying every point over every
`R`-algebra are equal. -/
theorem scheme_hom_ext {X : Scheme.{u}} {f g : scheme R M k ⟶ X}
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)),
      toSchemeHom N ≫ f = toSchemeHom N ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  -- make `B` an `R`-algebra through `a`, so that `a` classifies a point over `B`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  let _ : Algebra R B := φ.hom.toAlgebra
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  exact h B N

/-- The morphism `Spec A ⟶ G(k, M')` classifying the transport along `e` of the point classified
by `a : Spec A ⟶ G(k, M)` over `Spec R`. The algebra structure on `A` is an explicit argument, so
that `congrAux_congr` can compare different choices. -/
private noncomputable def congrAux (e : M ≃ₗ[R] M') (A : Type u) [CommRing A] (_ : Algebra R A)
    (a : Spec (.of A) ⟶ scheme R M k)
    (ha : a ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec (.of A) ⟶ scheme R M' k :=
  toSchemeHom ((e.baseChange R A M M').grassmannianCongr ((schemeHomEquiv R M k A).symm ⟨a, ha⟩))

-- `congrAux` depends on the algebra structure on `A` only through its equality class.
private lemma congrAux_congr (e : M ≃ₗ[R] M') (A : Type u) [CommRing A] (i j : Algebra R A)
    (h : i = j) (a : Spec (.of A) ⟶ scheme R M k) (ha ha') :
    congrAux e A i a ha = congrAux e A j a ha' := by
  subst h
  rfl

/-- The map of affine points underlying `schemeIsoOfLinearEquiv`: the algebra structure of `A`
over `R` is read off from the composite `Spec A ⟶ G(k, M) ⟶ Spec R`. -/
private noncomputable def congrPoint (e : M ≃ₗ[R] M') {A : CommRingCat.{u}}
    (a : Spec A ⟶ scheme R M k) : Spec A ⟶ scheme R M' k :=
  letI : Algebra R A := (Spec.preimage (a ≫ toSpec R M k)).hom.toAlgebra
  congrAux e A ‹_› a (Spec.map_preimage _).symm

/-- `congrPoint` computed with any algebra structure on `A` compatible with the morphism. -/
private lemma congrPoint_eq (e : M ≃ₗ[R] M') (A : Type u) [CommRing A] [Algebra R A]
    (a : Spec (.of A) ⟶ scheme R M k)
    (ha : a ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    congrPoint e a = congrAux e A ‹_› a ha := by
  have hφ : (Spec.preimage (a ≫ toSpec R M k)).hom = algebraMap R A := by
    rw [ha, Spec.preimage_map, CommRingCat.hom_ofHom]
  have hi : (Spec.preimage (a ≫ toSpec R M k)).hom.toAlgebra = ‹Algebra R A› :=
    Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r
  unfold congrPoint
  exact congrAux_congr e A _ _ hi a _ _

private lemma congrPoint_toSchemeHom (e : M ≃ₗ[R] M') {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) :
    congrPoint e (toSchemeHom N) = toSchemeHom ((e.baseChange R A M M').grassmannianCongr N) := by
  rw [congrPoint_eq e A _ (toSchemeHom_toSpec N), congrAux]
  congr 2
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `congrPoint` is natural in the affine scheme. -/
private lemma congrPoint_comp (e : M ≃ₗ[R] M') {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B)
    (a : Spec B ⟶ scheme R M k) : congrPoint e (ψ ≫ a) = ψ ≫ congrPoint e a := by
  -- give `B` and `C` the algebra structures over `R` read off from `a` and `ψ ≫ a`; with them,
  -- `χ` is an `R`-algebra map `χ'`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R B := φ.hom.toAlgebra
  let _ : Algebra R C := (χ.hom.comp φ.hom).toAlgebra
  let χ' : B →ₐ[R] C := { χ.hom with commutes' := fun _ ↦ rfl }
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := (toSchemeHom_map χ' N).symm
  rw [h, congrPoint_toSchemeHom, congrPoint_toSchemeHom, ← map_grassmannianCongr_baseChange,
    toSchemeHom_map]
  -- `χ'` has underlying ring map `χ`
  rfl

variable (k) in
/-- **The Grassmannian scheme of an isomorphic module.** A linear equivalence `e : M ≃ₗ[R] M'`
induces an isomorphism `G(k, M) ≅ G(k, M')` over `Spec R`
(`Module.Grassmannian.schemeIsoOfLinearEquiv_hom_toSpec`), which sends the point classifying `N`
over an `R`-algebra `A` to the point classifying its image under `A ⊗[R] M ≃ A ⊗[R] M'`
(`Module.Grassmannian.toSchemeHom_comp_schemeIsoOfLinearEquiv_hom`). -/
noncomputable def schemeIsoOfLinearEquiv (e : M ≃ₗ[R] M') : scheme R M k ≅ scheme R M' k where
  hom := Scheme.homOfAffinePoints (congrPoint e) (congrPoint_comp e)
  inv := Scheme.homOfAffinePoints (congrPoint e.symm) (congrPoint_comp e.symm)
  hom_inv_id := scheme_hom_ext fun A _ _ N ↦ by
    rw [Scheme.comp_homOfAffinePoints_assoc, congrPoint_toSchemeHom,
      Scheme.comp_homOfAffinePoints, congrPoint_toSchemeHom, LinearEquiv.baseChange_symm,
      ← LinearEquiv.grassmannianCongr_symm, Equiv.symm_apply_apply, Category.comp_id]
  inv_hom_id := scheme_hom_ext fun A _ _ N ↦ by
    rw [Scheme.comp_homOfAffinePoints_assoc, congrPoint_toSchemeHom,
      Scheme.comp_homOfAffinePoints, congrPoint_toSchemeHom, LinearEquiv.baseChange_symm,
      ← LinearEquiv.grassmannianCongr_symm, Equiv.apply_symm_apply, Category.comp_id]

/-- **`schemeIsoOfLinearEquiv` on points.** The morphism classifying `N` over an `R`-algebra `A`,
composed with `schemeIsoOfLinearEquiv k e`, classifies the image of `N` under the base change
`A ⊗[R] M ≃ A ⊗[R] M'` of `e`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_schemeIsoOfLinearEquiv_hom (e : M ≃ₗ[R] M') {A : Type u} [CommRing A]
    [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ (schemeIsoOfLinearEquiv k e).hom =
      toSchemeHom ((e.baseChange R A M M').grassmannianCongr N) :=
  (Scheme.comp_homOfAffinePoints _ _ _).trans (congrPoint_toSchemeHom e N)

/-- The inverse of the isomorphism induced by `e` is the isomorphism induced by `e.symm`. -/
@[simp]
theorem schemeIsoOfLinearEquiv_symm (e : M ≃ₗ[R] M') :
    (schemeIsoOfLinearEquiv k e).symm = schemeIsoOfLinearEquiv k e.symm :=
  Iso.ext (by rfl)

/-- `schemeIsoOfLinearEquiv k e` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schemeIsoOfLinearEquiv_hom_toSpec (e : M ≃ₗ[R] M') :
    (schemeIsoOfLinearEquiv k e).hom ≫ toSpec R M' k = toSpec R M k :=
  scheme_hom_ext fun A _ _ N ↦ by simp [toSchemeHom_toSpec]

/-- The identity of `M` induces the identity of `G(k, M)`. -/
@[simp]
theorem schemeIsoOfLinearEquiv_refl :
    schemeIsoOfLinearEquiv k (LinearEquiv.refl R M) = Iso.refl (scheme R M k) :=
  Iso.ext <| scheme_hom_ext fun A _ _ N ↦ by
    rw [toSchemeHom_comp_schemeIsoOfLinearEquiv_hom, ← LinearEquiv.one_eq_refl,
      LinearEquiv.baseChange_one, LinearEquiv.one_eq_refl, LinearEquiv.grassmannianCongr_refl]
    simp

/-- The isomorphism induced by a composite is the composite of the isomorphisms. -/
theorem schemeIsoOfLinearEquiv_trans (e : M ≃ₗ[R] M') (e' : M' ≃ₗ[R] M'') :
    schemeIsoOfLinearEquiv k (e.trans e') =
      schemeIsoOfLinearEquiv k e ≪≫ schemeIsoOfLinearEquiv k e' :=
  Iso.ext <| scheme_hom_ext fun A _ _ N ↦ by
    simp [LinearEquiv.baseChange_trans, LinearEquiv.grassmannianCongr_trans]

end Module.Grassmannian
