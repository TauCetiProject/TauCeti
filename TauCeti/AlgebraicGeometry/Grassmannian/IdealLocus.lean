/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Grassmannian.Points

import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop

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

section AffinePoint

/-- The sections of the Grassmannian scheme over an open `U` form an `R`-algebra through the
structure morphism to `Spec R`. -/
@[instance_reducible]
private noncomputable def sectionsAlgebra (U : (scheme R M k).Opens) :
    Algebra R Γ(scheme R M k, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (toSpec R M k).appLE ⊤ U fun _ _ ↦ trivial).hom.toAlgebra

attribute [local instance] sectionsAlgebra

private theorem algebraMap_sections (U : (scheme R M k).Opens) :
    algebraMap R Γ(scheme R M k, U) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (toSpec R M k).appLE ⊤ U fun _ _ ↦ trivial).hom :=
  rfl

/-- The inclusion `Spec Γ(G(k, M), U) ⟶ G(k, M)` of an affine open lies over `Spec R`. -/
private theorem fromSpec_toSpec {U : (scheme R M k).Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ toSpec R M k =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(scheme R M k, U))) := by
  rw [IsAffineOpen.fromSpec_comp_eq_SpecMap, algebraMap_sections, CommRingCat.ofHom_hom]

/-- The point of the Grassmannian over the sections of an affine open `U` classifying the
inclusion `Spec Γ(G(k, M), U) ⟶ G(k, M)`. -/
private noncomputable def affinePoint {U : (scheme R M k).Opens} (hU : IsAffineOpen U) :
    G(k, Γ(scheme R M k, U) ⊗[R] M; Γ(scheme R M k, U)) :=
  (schemeHomEquiv R M k Γ(scheme R M k, U)).symm ⟨hU.fromSpec, fromSpec_toSpec hU⟩

private theorem toSchemeHom_affinePoint {U : (scheme R M k).Opens} (hU : IsAffineOpen U) :
    toSchemeHom (affinePoint hU) = hU.fromSpec :=
  toSchemeHom_schemeHomEquiv_symm_apply _

/-- Restriction of sections of the Grassmannian scheme, as a map of `R`-algebras. -/
private noncomputable def resₐ {U V : (scheme R M k).Opens} (h : V ≤ U) :
    Γ(scheme R M k, U) →ₐ[R] Γ(scheme R M k, V) where
  toRingHom := ((scheme R M k).presheaf.map (homOfLE h).op).hom
  commutes' r := by
    simp only [algebraMap_sections]
    exact congr(($((toSpec R M k).appLE_map (U := ⊤) (fun _ _ ↦ trivial) (homOfLE h).op)).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r))

/-- The points classifying the inclusions of nested affine opens are related by restriction. -/
private theorem map_resₐ_affinePoint {U V : (scheme R M k).Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) :
    map (resₐ h) (affinePoint hU) = affinePoint hV := by
  apply toSchemeHom_injective
  rw [toSchemeHom_map, toSchemeHom_affinePoint, toSchemeHom_affinePoint]
  exact hU.map_fromSpec hV (homOfLE h).op

/-- A morphism `Spec A ⟶ G(k, M)` over `Spec R` landing in an affine open `U` is induced by an
`R`-algebra map `Γ(G(k, M), U) → A`. -/
private theorem exists_specMap_comp_fromSpec {A : Type u} [CommRing A] [Algebra R A]
    (g : Spec (.of A) ⟶ scheme R M k)
    (hg : g ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    {U : (scheme R M k).Opens} (hU : IsAffineOpen U) (hgU : Set.range g ⊆ U) :
    ∃ φ : Γ(scheme R M k, U) →ₐ[R] A,
      Spec.map (CommRingCat.ofHom (φ : Γ(scheme R M k, U) →+* A)) ≫ hU.fromSpec = g := by
  have hU' : Set.range g ⊆ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec g hU')
  have h₁ : Spec.map φ ≫ hU.fromSpec = g := hφ ▸ IsOpenImmersion.lift_fac _ _ _
  have h₂ : CommRingCat.ofHom (algebraMap R Γ(scheme R M k, U)) ≫ φ =
      CommRingCat.ofHom (algebraMap R A) :=
    Spec.map_injective (by rw [Spec.map_comp, ← fromSpec_toSpec hU, reassoc_of% h₁, hg])
  exact ⟨{ φ.hom with commutes' := fun r ↦ congr(($h₂).hom r) }, h₁⟩

/-- The elements `a` of `A` such that, over the basic open `D(a)`, the morphism classifying `N`
lands in an affine open of the Grassmannian. -/
private def affineSet {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) : Set A :=
  {a | ∃ U : (scheme R M k).Opens, IsAffineOpen U ∧
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
      toSchemeHom N) ⊆ U}

/-- The basic opens `D(a)`, `a ∈ affineSet N`, cover `Spec A`. -/
private theorem span_affineSet {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    Ideal.span (affineSet N) = ⊤ := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hs
  let p : Spec (.of A) := ⟨m, hm.isPrime⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    (scheme R M k).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (toSchemeHom N p)) isOpen_univ
  -- a basic open `D(a)` around `p` which the morphism classifying `N` maps into `U`
  obtain ⟨_, ⟨a, rfl⟩, hpa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := toSchemeHom N ⁻¹' U) hpU (U.is_open'.preimage (toSchemeHom N).continuous)
  have has : a ∈ affineSet N := by
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hsub
      ((PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le ⟨q, rfl⟩)
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hpa (hsm (Ideal.subset_span has))

end AffinePoint

attribute [local instance] sectionsAlgebra

variable (I : ∀ {A : Type u} [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → Ideal A)
  (hI : ∀ {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)), I (map f N) = Ideal.map f (I N))

/-- The ideal sheaf of the **closed subscheme of the Grassmannian scheme `G(k, M)` cut out by a
base-change-compatible ideal `I N` of each point `N`**. A morphism `Spec A ⟶ G(k, M)` over
`Spec R`, classifying a point `N` of `G(k, A ⊗[R] M; A)`, factors through this closed subscheme
exactly when `I N = ⊥` (`Module.Grassmannian.schemeIdealLocus_le_ker_toSchemeHom_iff`). Over an
affine open `U`, its ideal is `I` of the point over `Γ(G(k, M), U)` classifying the inclusion of
`U`. -/
noncomputable def schemeIdealLocus : (scheme R M k).IdealSheafData where
  ideal U := I (affinePoint U.property)
  map_ideal_basicOpen U f := by
    rw [← map_resₐ_affinePoint U.property ((scheme R M k).affineBasicOpen f).property
      ((scheme R M k).basicOpen_le f), hI]
    rfl

/-- The inverse image of the closed subscheme along a morphism landing in an affine open `U`,
induced by an `R`-algebra map `φ : Γ(G(k, M), U) → A`. -/
private theorem comap_specMap_comp_fromSpec {A : Type u} [CommRing A] [Algebra R A]
    {U : (scheme R M k).Opens} (hU : IsAffineOpen U) (φ : Γ(scheme R M k, U) →ₐ[R] A) :
    (schemeIdealLocus I hI).comap
        (Spec.map (CommRingCat.ofHom (φ : Γ(scheme R M k, U) →+* A)) ≫ hU.fromSpec) =
      ofIdealTop ((I (map φ (affinePoint hU))).map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  rw [comap_comp, comap_fromSpec_eq_ofIdealTop, comap_ofIdealTop_map_ΓSpecIso_inv,
    CommRingCat.hom_ofHom, Ideal.map_coe, hI]
  rfl

/-- The inverse image of the closed subscheme along the morphism classifying a point, when that
morphism lands in an affine open. -/
private theorem comap_toSchemeHom_of_range_subset {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) {U : (scheme R M k).Opens} (hU : IsAffineOpen U)
    (hNU : Set.range (toSchemeHom N) ⊆ U) :
    (schemeIdealLocus I hI).comap (toSchemeHom N) =
      ofIdealTop ((I N).map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  obtain ⟨φ, hφ⟩ := exists_specMap_comp_fromSpec _ (toSchemeHom_toSpec N) hU hNU
  have hN : map φ (affinePoint hU) = N :=
    toSchemeHom_injective (by rw [toSchemeHom_map, toSchemeHom_affinePoint, hφ])
  rw [← hφ, comap_specMap_comp_fromSpec, hN]

/-- **The inverse image of the closed subscheme along a point.** For an `R`-algebra `A` and a point
`N` of `G(k, A ⊗[R] M; A)`, the inverse image of `schemeIdealLocus I hI` along the morphism
`Spec A ⟶ G(k, M)` classifying `N` is the zero scheme of `I N`. -/
theorem comap_toSchemeHom_schemeIdealLocus {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) :
    (schemeIdealLocus I hI).comap (toSchemeHom N) =
      ofIdealTop ((I N).map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  -- compare both sides on the cover of `Spec A` by the basic opens `D(a)`, `a ∈ affineSet N`
  refine ext_of_comap_openCover (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of A)
    (fun a : affineSet N ↦ a.val) (by rw [Subtype.range_coe]; exact span_affineSet N)).openCover
    fun a ↦ ?_
  obtain ⟨U, hU, hNU⟩ := a.property
  let ι : A →ₐ[R] Localization.Away a.val := IsScalarTower.toAlgHom R A _
  have hι : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫ toSchemeHom N =
      toSchemeHom (map ι N) :=
    (toSchemeHom_map ι N).symm
  rw [← comap_comp]
  -- the members of the cover are by definition the localization maps `Spec A[1/a] ⟶ Spec A`
  change (schemeIdealLocus I hI).comap
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫ toSchemeHom N) =
    (ofIdealTop _).comap (Spec.map (CommRingCat.ofHom (algebraMap A _)))
  rw [hι, comap_toSchemeHom_of_range_subset I hI _ hU (hι ▸ hNU),
    comap_ofIdealTop_map_ΓSpecIso_inv, CommRingCat.hom_ofHom, hI]
  rfl

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
  calc schemeIdealLocus I hI ≤ (toSchemeHom N).ker
      -- a morphism factors through a closed subscheme when it pulls back its ideal sheaf to `⊥`
      _ ↔ (schemeIdealLocus I hI).comap (toSchemeHom N) = ⊥ := by
        rw [← Scheme.IdealSheafData.map_bot, le_map_iff_comap_le, le_bot_iff]
      _ ↔ (I N).map (Scheme.ΓSpecIso (.of A)).inv.hom = ⊥ := by
        rw [comap_toSchemeHom_schemeIdealLocus, ofIdealTop_eq_bot_iff]
      -- `Γ(Spec A, ⊤) ≅ A` is injective
      _ ↔ I N = ⊥ := Ideal.map_eq_bot_iff_of_injective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).1

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
