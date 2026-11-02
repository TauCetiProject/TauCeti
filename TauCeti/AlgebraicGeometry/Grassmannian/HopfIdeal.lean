/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.RingTheory.Grassmannian.HopfIdeal

import TauCeti.AlgebraicGeometry.Grassmannian.Proper
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop

/-!
# The closed subscheme of Hopf ideals in the Grassmannian scheme

Let `H` be a Hopf algebra over a commutative ring `R`. A point of the Grassmannian scheme
`G(k, H) = Module.Grassmannian.scheme R H k` over `Spec A` is an `A`-submodule `N` of `A ⊗[R] H`
whose quotient is finite projective of constant rank `k`
(`Module.Grassmannian.schemeHomEquiv`). When `N` is a two-sided Hopf ideal, the quotient is a Hopf
algebra over `A`; for commutative `H`, `Spec ((A ⊗[R] H) ⧸ N)` is then a subgroup scheme of
`Spec (A ⊗[R] H)`, finite locally free of rank `k` over `A`. This file cuts out the closed
subscheme of `G(k, H)` over which the universal submodule is a Hopf ideal; for commutative `H` it
parametrises these subgroup schemes.

Over an affine open `U` of `G(k, H)`, the inclusion `Spec Γ(G(k, H), U) ⟶ G(k, H)` classifies a
point of the Grassmannian over `Γ(G(k, H), U)`, and the ideal of the closed subscheme over `U` is
the ideal `Module.Grassmannian.hopfIdealLocus` of that point. These ideals are compatible with
restriction to basic opens because the formation of `hopfIdealLocus` commutes with base change
(`Module.Grassmannian.hopfIdealLocus_map`).

## Main definitions

* `Module.Grassmannian.schemeHopfIdealLocus R H k`: the ideal sheaf on `G(k, H)` of the closed
  subscheme of Hopf ideals.
* `Module.Grassmannian.schemeHopfIdealLocusHomEquiv R H k A`: the points of `G(k, A ⊗[R] H; A)`
  which are two-sided Hopf ideals are the morphisms from `Spec A` to this closed subscheme over
  `Spec R`.

## Main results

* `Module.Grassmannian.comap_toSchemeHom_schemeHopfIdealLocus`: the inverse image of the closed
  subscheme along the morphism `Spec A ⟶ G(k, H)` classifying a point `N` is the zero scheme of
  `N.hopfIdealLocus`.
* `Module.Grassmannian.schemeHopfIdealLocus_le_ker_toSchemeHom_iff`: **the universal property**;
  the morphism classifying `N` factors through the closed subscheme exactly when `N` is a
  two-sided Hopf ideal of `A ⊗[R] H`.
* `Module.Grassmannian.isProper_subschemeι_schemeHopfIdealLocus_toSpec`: for `H` finite over `R`,
  the closed subscheme is proper over `Spec R`.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R]

section AffinePoint

variable {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

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
  calc hU.fromSpec ≫ toSpec R M k
      -- over `U`, `toSpec` is `Spec` of its map on sections `Γ(Spec R, ⊤) → Γ(G(k, M), U)`
      _ = Spec.map ((toSpec R M k).appLE ⊤ U fun _ _ ↦ trivial) ≫ (Spec (.of R)).isoSpec.inv := by
        rw [← IsAffineOpen.fromSpec_top]
        exact (IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top _) hU _).symm
      -- the isomorphism `Spec R ≅ Spec Γ(Spec R, ⊤)` is `Spec` of `ΓSpecIso R`
      _ = Spec.map (CommRingCat.ofHom (algebraMap R Γ(scheme R M k, U))) := by
        rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp, algebraMap_sections, CommRingCat.ofHom_hom]

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

end AffinePoint

variable {H : Type u} [Ring H] [HopfAlgebra R H] {k : ℕ}

attribute [local instance] sectionsAlgebra

variable (R H k) in
/-- The ideal sheaf of the **closed subscheme of Hopf ideals** in the Grassmannian scheme
`G(k, H)` of a Hopf algebra `H` over `R`. A morphism `Spec A ⟶ G(k, H)` over `Spec R`, classifying
a point `N` of `G(k, A ⊗[R] H; A)`, factors through this closed subscheme exactly when `N` is a
two-sided Hopf ideal of `A ⊗[R] H`
(`Module.Grassmannian.schemeHopfIdealLocus_le_ker_toSchemeHom_iff`). Over an affine open `U`, its
ideal is `Module.Grassmannian.hopfIdealLocus` of the point over `Γ(G(k, H), U)` classifying the
inclusion of `U`. -/
noncomputable def schemeHopfIdealLocus : (scheme R H k).IdealSheafData where
  ideal U := (affinePoint U.2).hopfIdealLocus
  map_ideal_basicOpen U f := by
    rw [← map_resₐ_affinePoint U.2 ((scheme R H k).affineBasicOpen f).2
      ((scheme R H k).basicOpen_le f), hopfIdealLocus_map]
    rfl

/-- Transporting `hopfIdealLocus` to global sections of `Spec` commutes with base change along an
`R`-algebra map `φ : B → A`. -/
private theorem map_appTop_map_hopfIdealLocus {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : B →ₐ[R] A) (P : G(k, B ⊗[R] H; B)) :
    (P.hopfIdealLocus.map (Scheme.ΓSpecIso (.of B)).inv.hom).map
        (Spec.map (CommRingCat.ofHom (φ : B →+* A))).appTop.hom =
      (map φ P).hopfIdealLocus.map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  calc _ = P.hopfIdealLocus.map ((Spec.map (CommRingCat.ofHom (φ : B →+* A))).appTop.hom.comp
          (Scheme.ΓSpecIso (.of B)).inv.hom) := Ideal.map_map _ _
      -- naturality of `ΓSpecIso`
      _ = P.hopfIdealLocus.map ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (φ : B →+* A)) := by
        rw [← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      -- the formation of `hopfIdealLocus` commutes with base change
      _ = _ := by rw [← Ideal.map_map, Ideal.map_coe, hopfIdealLocus_map]

/-- The inverse image of the closed subscheme of Hopf ideals along a morphism landing in an affine
open `U`, induced by an `R`-algebra map `φ : Γ(G(k, H), U) → A`. -/
private theorem comap_specMap_comp_fromSpec {A : Type u} [CommRing A] [Algebra R A]
    {U : (scheme R H k).Opens} (hU : IsAffineOpen U) (φ : Γ(scheme R H k, U) →ₐ[R] A) :
    (schemeHopfIdealLocus R H k).comap
        (Spec.map (CommRingCat.ofHom (φ : Γ(scheme R H k, U) →+* A)) ≫ hU.fromSpec) =
      ofIdealTop ((map φ (affinePoint hU)).hopfIdealLocus.map
        (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  calc _ = (ofIdealTop (((schemeHopfIdealLocus R H k).ideal ⟨U, hU⟩).map
          (Scheme.ΓSpecIso Γ(scheme R H k, U)).inv.hom)).comap
            (Spec.map (CommRingCat.ofHom (φ : Γ(scheme R H k, U) →+* A))) := by
        rw [comap_comp, comap_fromSpec_eq_ofIdealTop]
    -- the ideal of `schemeHopfIdealLocus` over `U` is by definition `hopfIdealLocus`
    _ = ofIdealTop (((affinePoint hU).hopfIdealLocus.map
          (Scheme.ΓSpecIso Γ(scheme R H k, U)).inv.hom).map
            (Spec.map (CommRingCat.ofHom (φ : Γ(scheme R H k, U) →+* A))).appTop.hom) :=
        comap_ofIdealTop _ _
    _ = _ := congrArg ofIdealTop (map_appTop_map_hopfIdealLocus φ _)

/-- The inverse image of the closed subscheme of Hopf ideals along the morphism classifying a
point, when that morphism lands in an affine open. -/
private theorem comap_toSchemeHom_of_range_subset {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] H; A)) {U : (scheme R H k).Opens} (hU : IsAffineOpen U)
    (hNU : Set.range (toSchemeHom N) ⊆ U) :
    (schemeHopfIdealLocus R H k).comap (toSchemeHom N) =
      ofIdealTop (N.hopfIdealLocus.map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  obtain ⟨φ, hφ⟩ := exists_specMap_comp_fromSpec _ (toSchemeHom_toSpec N) hU hNU
  have hN : map φ (affinePoint hU) = N :=
    toSchemeHom_injective (by rw [toSchemeHom_map, toSchemeHom_affinePoint, hφ])
  rw [← hφ, comap_specMap_comp_fromSpec, hN]

/-- The elements `a` of `A` such that, over the basic open `D(a)`, the morphism classifying `N`
lands in an affine open of the Grassmannian. -/
private def affineSet {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] H; A)) : Set A :=
  {a | ∃ U : (scheme R H k).Opens, IsAffineOpen U ∧
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
      toSchemeHom N) ⊆ U}

/-- The basic opens `D(a)`, `a ∈ affineSet N`, cover `Spec A`. -/
private theorem span_affineSet {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] H; A)) :
    Ideal.span (affineSet N) = ⊤ := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hs
  let p : Spec (.of A) := ⟨m, hm.isPrime⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    (scheme R H k).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (toSchemeHom N p)) isOpen_univ
  -- a basic open `D(a)` around `p` which the morphism classifying `N` maps into `U`
  obtain ⟨_, ⟨a, rfl⟩, hpa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := toSchemeHom N ⁻¹' U) hpU (U.2.preimage (toSchemeHom N).continuous)
  have has : a ∈ affineSet N := by
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hsub
      ((PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le ⟨q, rfl⟩)
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hpa (hsm (Ideal.subset_span has))

/-- **The inverse image of the closed subscheme of Hopf ideals along a point.** For an
`R`-algebra `A` and a point `N` of `G(k, A ⊗[R] H; A)`, the inverse image of the closed subscheme
of Hopf ideals along the morphism `Spec A ⟶ G(k, H)` classifying `N` is the zero scheme of
`N.hopfIdealLocus`. -/
theorem comap_toSchemeHom_schemeHopfIdealLocus {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] H; A)) :
    (schemeHopfIdealLocus R H k).comap (toSchemeHom N) =
      ofIdealTop (N.hopfIdealLocus.map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  -- compare both sides on the cover of `Spec A` by the basic opens `D(a)`, `a ∈ affineSet N`
  refine ext_of_comap_openCover (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of A)
    (fun a : affineSet N ↦ a.1) (by rw [Subtype.range_coe]; exact span_affineSet N)).openCover
    fun a ↦ ?_
  obtain ⟨U, hU, hNU⟩ := a.2
  let ι : A →ₐ[R] Localization.Away a.1 := IsScalarTower.toAlgHom R A _
  have hι : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.1))) ≫ toSchemeHom N =
      toSchemeHom (map ι N) :=
    (toSchemeHom_map ι N).symm
  rw [← comap_comp]
  -- the members of the cover are by definition the localization maps `Spec A[1/a] ⟶ Spec A`
  change (schemeHopfIdealLocus R H k).comap
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.1))) ≫ toSchemeHom N) =
    (ofIdealTop _).comap (Spec.map (CommRingCat.ofHom (algebraMap A _)))
  rw [hι, comap_toSchemeHom_of_range_subset _ hU (hι ▸ hNU), comap_ofIdealTop]
  exact congrArg ofIdealTop (map_appTop_map_hopfIdealLocus ι N).symm

/-- **The universal property of the closed subscheme of Hopf ideals.** For an `R`-algebra `A`, the
morphism `Spec A ⟶ G(k, H)` classifying a point `N` of `G(k, A ⊗[R] H; A)` factors through the
closed subscheme of Hopf ideals exactly when `N.hopfIdealLocus` vanishes, that is, exactly when `N`
is a two-sided Hopf ideal of `A ⊗[R] H` (`Module.Grassmannian.hopfIdealLocus_eq_bot_iff`). -/
theorem schemeHopfIdealLocus_le_ker_toSchemeHom_iff {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] H; A)) :
    schemeHopfIdealLocus R H k ≤ (toSchemeHom N).ker ↔ N.hopfIdealLocus = ⊥ := by
  calc schemeHopfIdealLocus R H k ≤ (toSchemeHom N).ker
      -- a morphism factors through a closed subscheme when it pulls back its ideal sheaf to `⊥`
      _ ↔ (schemeHopfIdealLocus R H k).comap (toSchemeHom N) = ⊥ := by
        rw [← Scheme.IdealSheafData.map_bot, le_map_iff_comap_le, le_bot_iff]
      _ ↔ N.hopfIdealLocus.map (Scheme.ΓSpecIso (.of A)).inv.hom = ⊥ := by
        rw [comap_toSchemeHom_schemeHopfIdealLocus, ofIdealTop_eq_bot_iff]
      -- `Γ(Spec A, ⊤) ≅ A` is injective
      _ ↔ N.hopfIdealLocus = ⊥ := Ideal.map_eq_bot_iff_of_injective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).1

variable (R H k) in
/-- **The closed subscheme of Hopf ideals represents the Hopf ideals in the Grassmannian.** For an
`R`-algebra `A`, the points `N` of `G(k, A ⊗[R] H; A)` which are two-sided Hopf ideals, that is,
with `N.hopfIdealLocus = ⊥` (`Module.Grassmannian.hopfIdealLocus_eq_bot_iff`), are in bijection
with the morphisms from `Spec A` to the closed subscheme of Hopf ideals over `Spec R`. The
bijection composes with the inclusion into `G(k, H)` to the morphism classifying `N`
(`Module.Grassmannian.schemeHopfIdealLocusHomEquiv_apply_comp_subschemeι` and
`Module.Grassmannian.toSchemeHom_schemeHopfIdealLocusHomEquiv_symm_apply`). -/
noncomputable def schemeHopfIdealLocusHomEquiv (A : Type u) [CommRing A] [Algebra R A] :
    {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥} ≃
      {h : Spec (.of A) ⟶ (schemeHopfIdealLocus R H k).subscheme //
        h ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} where
  toFun N := ⟨(toSchemeHom N.1).toImage ≫
      inclusion ((schemeHopfIdealLocus_le_ker_toSchemeHom_iff N.1).2 N.2), by
    rw [Category.assoc, inclusion_subschemeι_assoc, Scheme.Hom.toImage_imageι_assoc,
      toSchemeHom_toSpec]⟩
  invFun h := ⟨(schemeHomEquiv R H k A).symm
      ⟨h.1 ≫ (schemeHopfIdealLocus R H k).subschemeι, by rw [Category.assoc, h.2]⟩, by
    rw [← schemeHopfIdealLocus_le_ker_toSchemeHom_iff, toSchemeHom_schemeHomEquiv_symm_apply]
    exact (ker_subschemeι _).ge.trans (Scheme.Hom.le_ker_comp _ _)⟩
  left_inv N := Subtype.ext <| toSchemeHom_injective <| by
    simp [toSchemeHom_schemeHomEquiv_symm_apply]
  right_inv h := Subtype.ext <| (cancel_mono (schemeHopfIdealLocus R H k).subschemeι).1 <| by
    simp [toSchemeHom_schemeHomEquiv_symm_apply]

/-- The morphism to the closed subscheme of Hopf ideals corresponding to a Hopf ideal `N`, followed
by the inclusion into the Grassmannian scheme, is the morphism classifying `N`. -/
@[reassoc (attr := simp)]
theorem schemeHopfIdealLocusHomEquiv_apply_comp_subschemeι {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥}) :
    (schemeHopfIdealLocusHomEquiv R H k A N).1 ≫ (schemeHopfIdealLocus R H k).subschemeι =
      toSchemeHom N.1 := by
  simp [schemeHopfIdealLocusHomEquiv]

/-- The Hopf ideal corresponding to a morphism `h` to the closed subscheme of Hopf ideals is the
point classified by `h` followed by the inclusion into the Grassmannian scheme. -/
@[simp]
theorem toSchemeHom_schemeHopfIdealLocusHomEquiv_symm_apply {A : Type u} [CommRing A]
    [Algebra R A] (h : {h : Spec (.of A) ⟶ (schemeHopfIdealLocus R H k).subscheme //
      h ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeHopfIdealLocusHomEquiv R H k A).symm h).1 =
      h.1 ≫ (schemeHopfIdealLocus R H k).subschemeι :=
  toSchemeHom_schemeHomEquiv_symm_apply _

/-- For `H` finite over `R`, the closed subscheme of Hopf ideals is proper over `Spec R`, as a
closed subscheme of the proper Grassmannian scheme. -/
instance isProper_subschemeι_schemeHopfIdealLocus_toSpec [Module.Finite R H] :
    IsProper ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) :=
  inferInstance

end Module.Grassmannian
