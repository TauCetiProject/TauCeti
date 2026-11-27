/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Grassmannian.BaseChange

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.PointIdeals

/-!
# Closed subschemes of the Grassmannian scheme cut out by ideals of points

Let `M` be a module over a commutative ring `R`. A point of the Grassmannian scheme
`G(k, M) = Module.Grassmannian.scheme R M k` over `Spec A` is an `A`-submodule `N` of `A ⊗[R] M`
whose quotient is finite projective of constant rank `k` (`Module.Grassmannian.schemeHomEquiv`).
Many conditions on such points are closed conditions in the following sense: there is an ideal
`I N` of `A` such that, for every `R`-algebra map `f : A → B`, the base change of `N` to `B`
satisfies the condition exactly when `f` kills `I N`. Examples are being a two-sided Hopf ideal
(`Module.Grassmannian.hopfIdealLocus`) and being isotropic for a bilinear form
(`Module.Grassmannian.isotropicLocus`).

Whenever the formation of `I N` commutes with base change, `I (map f N) = (I N).map f`, this file
glues these ideals into the ideal sheaf of a closed subscheme of `G(k, M)`
(`Module.Grassmannian.schemeIdealLocus`) and proves that it represents the points `N` with
`I N = ⊥`.

Over an affine open `U` of `G(k, M)`, the inclusion `Spec Γ(G(k, M), U) ⟶ G(k, M)` classifies a
point of the Grassmannian over `Γ(G(k, M), U)`, and the ideal of the closed subscheme over `U` is
the ideal `I` of that point. These ideals are compatible with restriction to basic opens because
the formation of `I` commutes with base change.

These closed subschemes are compatible with base change along `Spec R' ⟶ Spec R`: for a base
change `f : M → M'` of modules along `R → R'` (`IsBaseChange.grassmannianSchemeHom`), if the ideal
`I'` of a point of `G(k, M')` over an `R'`-algebra `A` is the ideal `I` of its image in
`G(k, A ⊗[R] M; A)`, then the closed subscheme cut out by `I'` is the inverse image of the one cut
out by `I` (`IsBaseChange.comap_grassmannianSchemeHom_schemeIdealLocus`), hence its base change
to `Spec R'` (`IsBaseChange.isPullback_grassmannianSchemeHom_schemeIdealLocus`). The tensor
product `M' = R' ⊗[R] M` (`Module.Grassmannian.baseChangeHom`) is the special case
`Module.Grassmannian.comap_baseChangeHom_schemeIdealLocus`. Both ideal sheaves are
determined by their inverse images along morphisms from affine schemes, which classify points.

## Main definitions

* `Module.Grassmannian.schemeIdealLocus I hI`: the ideal sheaf on `G(k, M)` glued from the ideals
  `I N`.
* `Module.Grassmannian.schemeIdealLocusHomEquiv I hI A`: the points `N` of `G(k, A ⊗[R] M; A)` with
  `I N = ⊥` are the morphisms from `Spec A` to the closed subscheme over `Spec R`.

## Main results

* `Module.Grassmannian.comap_toSchemeHom_schemeIdealLocus`: the inverse image of the closed
  subscheme along the morphism `Spec A ⟶ G(k, M)` classifying a point `N` is the zero scheme of
  `I N`.
* `Module.Grassmannian.comap_chartι_schemeIdealLocus`,
  `Module.Grassmannian.idealSheafData_le_of_comap_chartι`, and
  `Module.Grassmannian.schemeIdealLocus_le_of_le`: checking inclusions of ideal sheaves on
  `G(k, M)` via pullbacks to the standard charts.
* `Module.Grassmannian.schemeIdealLocus_le_ker_toSchemeHom_iff`: **the universal property**; the
  morphism classifying `N` factors through the closed subscheme exactly when `I N = ⊥`.
* `IsBaseChange.comap_grassmannianSchemeHom_schemeIdealLocus` and
  `IsBaseChange.isPullback_grassmannianSchemeHom_schemeIdealLocus`: base change of the closed
  subschemes cut out by ideals of points, along a base change of modules `M → M'`;
  `Module.Grassmannian.comap_baseChangeHom_schemeIdealLocus` and
  `Module.Grassmannian.isPullback_baseChangeHom_schemeIdealLocus` are the case `M' = R' ⊗[R] M`.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  closed conditions on the Grassmannian.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

variable (I : ∀ {A : Type u} [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → Ideal A)
  (hI : ∀ {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)), I (map f N) = Ideal.map f (I N))

private noncomputable def schemePointIdeal
    {A : Type u} [CommRing A] [Algebra R A]
    (g : {g : Spec (.of A) ⟶ scheme R M k //
      g ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))}) : Ideal A :=
  I ((schemeHomEquiv R M k A).symm g)

private theorem schemePointIdeal_toSchemeHom
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    schemePointIdeal I ⟨toSchemeHom N, toSchemeHom_toSpec N⟩ = I N :=
  congrArg I (toSchemeHom_injective (toSchemeHom_schemeHomEquiv_symm_apply _))

include hI in
private theorem schemePointIdeal_map
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B)
    (g : {g : Spec (.of A) ⟶ scheme R M k //
      g ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (g' : {g : Spec (.of B) ⟶ scheme R M k //
      g ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R B))})
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g.val = g'.val) :
    schemePointIdeal I g' = (schemePointIdeal I g).map f := by
  have hN : (schemeHomEquiv R M k B).symm g' =
      map f ((schemeHomEquiv R M k A).symm g) := by
    apply toSchemeHom_injective
    rw [toSchemeHom_map, toSchemeHom_schemeHomEquiv_symm_apply,
      toSchemeHom_schemeHomEquiv_symm_apply]
    exact h.symm
  simp only [schemePointIdeal, hN, hI]

/-- The ideal sheaf of the **closed subscheme of the Grassmannian scheme `G(k, M)` cut out by a
base-change-compatible ideal `I N` of each point `N`**. A morphism `Spec A ⟶ G(k, M)` over
`Spec R`, classifying a point `N` of `G(k, A ⊗[R] M; A)`, factors through this closed subscheme
exactly when `I N = ⊥` (`Module.Grassmannian.schemeIdealLocus_le_ker_toSchemeHom_iff`). Over an
affine open `U`, its ideal is `I` of the point over `Γ(G(k, M), U)` classifying the inclusion of
`U`. -/
noncomputable def schemeIdealLocus : (scheme R M k).IdealSheafData :=
  (toSpec R M k).idealSheafOfAffinePoints (schemePointIdeal I) (schemePointIdeal_map I hI)

/-- **The inverse image of the closed subscheme along a point.** For an `R`-algebra `A` and a point
`N` of `G(k, A ⊗[R] M; A)`, the inverse image of `schemeIdealLocus I hI` along the morphism
`Spec A ⟶ G(k, M)` classifying `N` is the zero scheme of `I N`. -/
theorem comap_toSchemeHom_schemeIdealLocus {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) :
    (schemeIdealLocus I hI).comap (toSchemeHom N) =
      ofIdealTop ((I N).map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  simpa only [schemeIdealLocus, schemePointIdeal_toSchemeHom] using
    (toSpec R M k).comap_idealSheafOfAffinePoints (schemePointIdeal I)
      (schemePointIdeal_map I hI) ⟨toSchemeHom N, toSchemeHom_toSpec N⟩

/-- An inequality of ideal sheaves on `G(k, M)` can be checked after pulling back along every
standard chart `chartι R x`. -/
theorem idealSheafData_le_of_comap_chartι {J₁ J₂ : (scheme R M k).IdealSheafData}
    (h : ∀ x : Fin k → M, J₁.comap (chartι R x) ≤ J₂.comap (chartι R x)) : J₁ ≤ J₂ := by
  rw [← J₁.iInf_map_comap_openCover (chartOpenCover R M k),
    ← J₂.iInf_map_comap_openCover (chartOpenCover R M k)]
  exact iInf_mono fun x ↦ map_mono (chartι R x) (h x)

/-- Pulling back `schemeIdealLocus I hI` along the standard chart `chartι R x` gives the ideal
sheaf of `I` evaluated at the universal point of `ChartAlgebra R x`. -/
theorem comap_chartι_schemeIdealLocus (x : Fin k → M) :
    (schemeIdealLocus I hI).comap (chartι R x) =
      ofIdealTop ((I (chartHomEquiv R x _ (AlgHom.id R _)).val).map
        (Scheme.ΓSpecIso (.of (ChartAlgebra R x))).inv.hom) := by
  rw [← toSchemeHom_chartHomEquiv_id x, comap_toSchemeHom_schemeIdealLocus]

/-- Containment of the defining ideals at the universal point of every standard chart implies
containment of the corresponding ideal sheaves on `G(k, M)`. -/
theorem schemeIdealLocus_le_of_le
    {I₁ : ∀ {A : Type u} [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → Ideal A}
    {hI₁ : ∀ {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)), I₁ (map f N) = Ideal.map f (I₁ N)}
    {I₂ : ∀ {A : Type u} [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → Ideal A}
    {hI₂ : ∀ {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)), I₂ (map f N) = Ideal.map f (I₂ N)}
    (hle : ∀ x : Fin k → M,
      I₁ (chartHomEquiv R x _ (AlgHom.id R _)).val ≤
        I₂ (chartHomEquiv R x _ (AlgHom.id R _)).val) :
    schemeIdealLocus I₁ hI₁ ≤ schemeIdealLocus I₂ hI₂ := by
  refine idealSheafData_le_of_comap_chartι fun x ↦ ?_
  rw [comap_chartι_schemeIdealLocus, comap_chartι_schemeIdealLocus,
    ← equivOfIsAffine_symm_apply, ← equivOfIsAffine_symm_apply, map_le_map_iff]
  exact Ideal.map_mono (hle x)

/-- **The universal property of the closed subscheme cut out by `I`.** For an `R`-algebra `A`, the
morphism `Spec A ⟶ G(k, M)` classifying a point `N` of `G(k, A ⊗[R] M; A)` factors through the
closed subscheme `schemeIdealLocus I hI` exactly when `I N` vanishes. -/
theorem schemeIdealLocus_le_ker_toSchemeHom_iff {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) :
    schemeIdealLocus I hI ≤ (toSchemeHom N).ker ↔ I N = ⊥ := by
  simpa only [schemeIdealLocus, schemePointIdeal_toSchemeHom] using
    (toSpec R M k).idealSheafOfAffinePoints_le_ker_iff (schemePointIdeal I)
      (schemePointIdeal_map I hI) ⟨toSchemeHom N, toSchemeHom_toSpec N⟩

/-- **The closed subscheme cut out by `I` represents the points on which `I` vanishes.** For an
`R`-algebra `A`, the points `N` of `G(k, A ⊗[R] M; A)` with `I N = ⊥` are in bijection with the
morphisms from `Spec A` to the closed subscheme `schemeIdealLocus I hI` over `Spec R`. The
bijection composes with the inclusion into `G(k, M)` to the morphism classifying `N`
(`Module.Grassmannian.schemeIdealLocusHomEquiv_apply_comp_subschemeι` and
`Module.Grassmannian.toSchemeHom_schemeIdealLocusHomEquiv_symm_apply`). -/
noncomputable def schemeIdealLocusHomEquiv (A : Type u) [CommRing A] [Algebra R A] :
    {N : G(k, A ⊗[R] M; A) // I N = ⊥} ≃
      {h : Spec (.of A) ⟶ (schemeIdealLocus I hI).subscheme //
        h ≫ (schemeIdealLocus I hI).subschemeι ≫ toSpec R M k =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} where
  toFun N := ⟨(toSchemeHom N.val).toImage ≫
      inclusion ((schemeIdealLocus_le_ker_toSchemeHom_iff I hI N.val).2 N.property), by
    rw [Category.assoc, inclusion_subschemeι_assoc, Scheme.Hom.toImage_imageι_assoc,
      toSchemeHom_toSpec]⟩
  invFun h := ⟨(schemeHomEquiv R M k A).symm
      ⟨h.val ≫ (schemeIdealLocus I hI).subschemeι, by rw [Category.assoc, h.property]⟩, by
    rw [← schemeIdealLocus_le_ker_toSchemeHom_iff I hI, toSchemeHom_schemeHomEquiv_symm_apply]
    exact (ker_subschemeι _).ge.trans (Scheme.Hom.le_ker_comp _ _)⟩
  left_inv N := Subtype.ext <| toSchemeHom_injective <| by
    simp [toSchemeHom_schemeHomEquiv_symm_apply]
  right_inv h := Subtype.ext <| (cancel_mono (schemeIdealLocus I hI).subschemeι).1 <| by
    simp [toSchemeHom_schemeHomEquiv_symm_apply]

/-- The morphism to the closed subscheme corresponding to a point `N` with `I N = ⊥`, followed by
the inclusion into the Grassmannian scheme, is the morphism classifying `N`. -/
@[reassoc (attr := simp)]
theorem schemeIdealLocusHomEquiv_apply_comp_subschemeι {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : G(k, A ⊗[R] M; A) // I N = ⊥}) :
    (schemeIdealLocusHomEquiv I hI A N).val ≫ (schemeIdealLocus I hI).subschemeι =
      toSchemeHom N.val := by
  simp [schemeIdealLocusHomEquiv]

/-- The point corresponding to a morphism `h` to the closed subscheme is the point classified by
`h` followed by the inclusion into the Grassmannian scheme. -/
@[simp]
theorem toSchemeHom_schemeIdealLocusHomEquiv_symm_apply {A : Type u} [CommRing A] [Algebra R A]
    (h : {h : Spec (.of A) ⟶ (schemeIdealLocus I hI).subscheme //
      h ≫ (schemeIdealLocus I hI).subschemeι ≫ toSpec R M k =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeIdealLocusHomEquiv I hI A).symm h).val =
      h.val ≫ (schemeIdealLocus I hI).subschemeι :=
  toSchemeHom_schemeHomEquiv_symm_apply _

end Module.Grassmannian

namespace IsBaseChange

open Module.Grassmannian

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [Module R M']
  [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (hf : IsBaseChange R' f) {k : ℕ}
  (I : ∀ {A : Type u} [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → Ideal A)
  (hI : ∀ {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)), I (map f N) = Ideal.map f (I N))
  (I' : ∀ {A : Type u} [CommRing A] [Algebra R' A], G(k, A ⊗[R'] M'; A) → Ideal A)
  (hI' : ∀ {A B : Type u} [CommRing A] [Algebra R' A] [CommRing B] [Algebra R' B]
    (f : A →ₐ[R'] B) (N : G(k, A ⊗[R'] M'; A)), I' (map f N) = Ideal.map f (I' N))

/-- **Base change of a closed subscheme cut out by ideals of points, along a base change of
modules.** Let `f : M → M'` be a base change along `R → R'`, `I` a base-change-compatible ideal
of points of `G(k, M)`, and `I'` one of points of `G(k, M')`, such that `I'` of a point over an
`R'`-algebra is `I` of its image under `IsBaseChange.grassmannianEquiv`. Then the inverse image
of the closed subscheme cut out by `I` along `IsBaseChange.grassmannianSchemeHom` is the closed
subscheme cut out by `I'`. -/
theorem comap_grassmannianSchemeHom_schemeIdealLocus
    (h : ∀ {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (N : G(k, A ⊗[R'] M'; A)), I (hf.grassmannianEquiv A N) = I' N) :
    (schemeIdealLocus I hI).comap (hf.grassmannianSchemeHom k) = schemeIdealLocus I' hI' := by
  -- compare the pullbacks along every morphism from an affine scheme, which classifies a point
  have key (B : CommRingCat.{u}) (a : Spec B ⟶ scheme R' M' k) :
      ((schemeIdealLocus I hI).comap (hf.grassmannianSchemeHom k)).comap a =
        (schemeIdealLocus I' hI').comap a := by
    refine affinePoint_induction (R₀ := R) (fun A _ _ _ _ N ↦ ?_) a
    rw [← comap_comp, toSchemeHom_comp_grassmannianSchemeHom, comap_toSchemeHom_schemeIdealLocus,
      comap_toSchemeHom_schemeIdealLocus, h]
  exact ext_of_comap_openCover (scheme R' M' k).affineCover fun i ↦ key _ _

/-- **The closed subscheme cut out by ideals of points commutes with base change of modules.**
Under the hypothesis of `IsBaseChange.comap_grassmannianSchemeHom_schemeIdealLocus`, the closed
subscheme of `G(k, M')` cut out by `I'`, as a scheme over `Spec R'`, is the base change along
`Spec R' ⟶ Spec R` of the closed subscheme of `G(k, M)` cut out by `I`, as a scheme over
`Spec R`. -/
theorem isPullback_grassmannianSchemeHom_schemeIdealLocus
    (h : ∀ {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (N : G(k, A ⊗[R'] M'; A)), I (hf.grassmannianEquiv A N) = I' N) :
    IsPullback
      (subschemeMap (schemeIdealLocus I' hI') (schemeIdealLocus I hI) (hf.grassmannianSchemeHom k)
        (le_map_iff_comap_le.2
          (hf.comap_grassmannianSchemeHom_schemeIdealLocus I hI I' hI' h).le))
      ((schemeIdealLocus I' hI').subschemeι ≫ toSpec R' M' k)
      ((schemeIdealLocus I hI).subschemeι ≫ toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  -- the closed subscheme of `I'` is the inverse image of that of `I`, and inverse images of
  -- closed subschemes along a base change are base changes
  have key (J : (scheme R' M' k).IdealSheafData)
      (hJ : (schemeIdealLocus I hI).comap (hf.grassmannianSchemeHom k) = J) (hle) :
      IsPullback (subschemeMap J (schemeIdealLocus I hI) (hf.grassmannianSchemeHom k) hle)
        (J.subschemeι ≫ toSpec R' M' k) ((schemeIdealLocus I hI).subschemeι ≫ toSpec R M k)
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    subst hJ
    exact isPullback_subschemeMap_comap _ _ (hf.isPullback_grassmannianSchemeHom k)
  exact key _ (hf.comap_grassmannianSchemeHom_schemeIdealLocus I hI I' hI' h) _

end IsBaseChange

namespace Module.Grassmannian

section BaseChange

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
  rw [baseChangeHom_eq_grassmannianSchemeHom]
  exact IsBaseChange.comap_grassmannianSchemeHom_schemeIdealLocus
    (TensorProduct.isBaseChange R M R') I hI I' hI'
    fun N ↦ by rw [← baseChangeEquiv_eq_grassmannianEquiv, h]

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
  have H := IsBaseChange.isPullback_grassmannianSchemeHom_schemeIdealLocus
    (TensorProduct.isBaseChange R M R') I hI I' hI'
    fun N ↦ by rw [← baseChangeEquiv_eq_grassmannianEquiv, h]
  simpa only [← baseChangeHom_eq_grassmannianSchemeHom] using H

end BaseChange

end Module.Grassmannian
