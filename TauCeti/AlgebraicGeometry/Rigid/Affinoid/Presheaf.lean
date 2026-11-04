/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The presheaf on classical affinoid subdomains

The affinoid subdomains of `Sp A = MaximalSpectrum A` form a partially ordered set, with
inclusions as morphisms. Choose a representing algebra for each subdomain. The universal
property supplies restriction maps, and makes these into a presheaf of commutative
`K`-algebras. Its sections on any subdomain are canonically isomorphic to any other
representing algebra, compatibly with restrictions and with the maps from `A`.
In particular the sections on the whole spectrum recover `A`, including its nilpotents.

This is a presheaf on affinoid subdomains, not on all subsets of the maximal spectrum.
No sheaf condition or topology on the indexing category is asserted here. The construction
provides the coordinate algebras and restriction maps for affinoid-cover descent.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§7.2.2 and 8.2, for affinoid subdomains and their presheaf of functions.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

universe u

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type u) [CommRing A] [Algebra K A]

/-- An affinoid subdomain of the classical spectrum, regarded as a subset admitting a
representing affinoid algebra. The representation is a property, not extra data. -/
structure AffinoidSubdomain where
  /-- The underlying set of classical points. -/
  carrier : Set (MaximalSpectrum A)
  /-- There exists an affinoid algebra representing this set. -/
  exists_representation : ∃ B : CommAlgCat.{u} K, ∃ φ : A →ₐ[K] B,
    IsAffinoidSubdomainMap φ carrier

namespace AffinoidSubdomain

variable {K A}

-- Coercions and categorical inclusions must compute as sets and subset inclusions.
instance : SetLike (AffinoidSubdomain K A) (MaximalSpectrum A) where
  coe := carrier
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ rfl; rfl

@[ext]
theorem ext {U V : AffinoidSubdomain K A} (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h

instance : PartialOrder (AffinoidSubdomain K A) := .ofSetLike _

/-- Regard a represented subset as an affinoid subdomain. -/
def ofMap {B : Type u} [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U) : AffinoidSubdomain K A :=
  ⟨U, ⟨CommAlgCat.of K B, φ, h⟩⟩

@[simp]
theorem coe_ofMap {B : Type u} [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U) :
    (ofMap h : Set (MaximalSpectrum A)) = U := (rfl)

@[simp]
theorem mem_ofMap {B : Type u} [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U) (x : MaximalSpectrum A) :
    x ∈ ofMap h ↔ x ∈ U := Iff.rfl

/-- A chosen representing algebra of an affinoid subdomain. -/
noncomputable def sections (U : AffinoidSubdomain K A) : CommAlgCat.{u} K :=
  U.exists_representation.choose

/-- The structure map from the ambient algebra to the sections on a subdomain. -/
noncomputable def toSections (U : AffinoidSubdomain K A) : A →ₐ[K] U.sections :=
  U.exists_representation.choose_spec.choose

/-- The chosen sections and structure map represent the subdomain. -/
theorem isAffinoidSubdomainMap (U : AffinoidSubdomain K A) :
    IsAffinoidSubdomainMap U.toSections (U : Set (MaximalSpectrum A)) :=
  U.exists_representation.choose_spec.choose_spec

/-- The algebra of sections on an affinoid subdomain is affinoid. -/
theorem isAffinoidAlgebra (U : AffinoidSubdomain K A) : IsAffinoidAlgebra K U.sections :=
  U.isAffinoidSubdomainMap.isAffinoidAlgebra

/-- Restriction of functions along an inclusion of affinoid subdomains. -/
noncomputable def restrict {U V : AffinoidSubdomain K A} (h : U ≤ V) :
    V.sections →ₐ[K] U.sections :=
  V.isAffinoidSubdomainMap.lift U.isAffinoidAlgebra U.toSections
    (U.isAffinoidSubdomainMap.range_maximalSpectrumComap_subset.trans h)

@[simp]
theorem restrict_comp_toSections {U V : AffinoidSubdomain K A} (h : U ≤ V) :
    (restrict h).comp V.toSections = U.toSections :=
  IsAffinoidSubdomainMap.lift_comp ..

@[simp]
theorem restrict_toSections {U V : AffinoidSubdomain K A} (h : U ≤ V) (a : A) :
    restrict h (V.toSections a) = U.toSections a :=
  DFunLike.congr_fun (restrict_comp_toSections h) a

@[simp]
theorem restrict_refl (U : AffinoidSubdomain K A) :
    restrict (le_refl U) = AlgHom.id K U.sections := by
  apply U.isAffinoidSubdomainMap.algHom_ext U.isAffinoidAlgebra
  simp

/-- Restrictions compose along chains of subdomains. -/
@[simp]
theorem restrict_comp {U V W : AffinoidSubdomain K A} (hUV : U ≤ V) (hVW : V ≤ W) :
    (restrict hUV).comp (restrict hVW) = restrict (hUV.trans hVW) := by
  apply W.isAffinoidSubdomainMap.algHom_ext U.isAffinoidAlgebra
  simp [AlgHom.comp_assoc]

/-- The presheaf of representing affinoid algebras on the inclusion preorder of subdomains.
Its object formula is exposed so that its section types are the chosen representing algebras. -/
@[expose] noncomputable def presheaf : (AffinoidSubdomain K A)ᵒᵖ ⥤ CommAlgCat.{u} K where
  obj U := U.unop.sections
  map f := CommAlgCat.ofHom (restrict (leOfHom f.unop))
  map_id U := by
    apply CommAlgCat.hom_ext
    simp
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact (restrict_comp (leOfHom g.unop) (leOfHom f.unop)).symm

@[simp]
theorem presheaf_obj (U : AffinoidSubdomain K A) :
    (presheaf (K := K) (A := A)).obj (op U) = U.sections := (rfl)

@[simp]
theorem presheaf_map_hom {U V : AffinoidSubdomain K A} (h : U ≤ V) :
    ((presheaf (K := K) (A := A)).map (homOfLE h).op).hom = restrict h := (rfl)

/-- Comparison of the chosen sections with any algebra representing the same subdomain. -/
noncomputable def sectionsAlgEquiv (U : AffinoidSubdomain K A) {B : Type u}
    [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    (h : IsAffinoidSubdomainMap φ (U : Set (MaximalSpectrum A))) : U.sections ≃ₐ[K] B :=
  U.isAffinoidSubdomainMap.algEquiv h

@[simp]
theorem sectionsAlgEquiv_toSections (U : AffinoidSubdomain K A) {B : Type u}
    [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    (h : IsAffinoidSubdomainMap φ (U : Set (MaximalSpectrum A))) (a : A) :
    U.sectionsAlgEquiv h (U.toSections a) = φ a := by
  simp only [sectionsAlgEquiv, IsAffinoidSubdomainMap.algEquiv_apply]

@[simp]
theorem sectionsAlgEquiv_symm_apply (U : AffinoidSubdomain K A) {B : Type u}
    [CommRing B] [Algebra K B] {φ : A →ₐ[K] B}
    (h : IsAffinoidSubdomainMap φ (U : Set (MaximalSpectrum A))) (a : A) :
    (U.sectionsAlgEquiv h).symm (φ a) = U.toSections a := by
  apply (U.sectionsAlgEquiv h).injective
  simp

/-- Comparison with other representing algebras commutes with restriction. The map `ψ`
need only commute with the ambient structure maps; uniqueness supplies the square. -/
theorem sectionsAlgEquiv_restrict {U V : AffinoidSubdomain K A} (hUV : U ≤ V)
    {B C : Type u} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    {φ : A →ₐ[K] B} {χ : A →ₐ[K] C}
    (hB : IsAffinoidSubdomainMap φ (V : Set (MaximalSpectrum A)))
    (hC : IsAffinoidSubdomainMap χ (U : Set (MaximalSpectrum A)))
    (ψ : B →ₐ[K] C) (hψ : ψ.comp φ = χ) :
    (U.sectionsAlgEquiv hC).toAlgHom.comp (restrict hUV) =
      ψ.comp (V.sectionsAlgEquiv hB).toAlgHom := by
  apply V.isAffinoidSubdomainMap.algHom_ext hC.isAffinoidAlgebra
  ext a
  simpa using (AlgHom.congr_fun hψ a).symm

/-- The whole classical spectrum as an affinoid subdomain. -/
def univ (hA : IsAffinoidAlgebra K A) : AffinoidSubdomain K A :=
  ofMap (IsAffinoidSubdomainMap.id hA)

@[simp]
theorem coe_univ (hA : IsAffinoidAlgebra K A) :
    (univ hA : Set (MaximalSpectrum A)) = Set.univ := (rfl)

@[simp]
theorem mem_univ (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) : x ∈ univ hA :=
  Set.mem_univ x

@[simp]
theorem le_univ (U : AffinoidSubdomain K A) (hA : IsAffinoidAlgebra K A) : U ≤ univ hA := by
  apply SetLike.coe_subset_coe.mp
  rw [coe_univ]
  exact Set.subset_univ _

/-- Global sections recover the ambient affinoid algebra, not its reduction. -/
noncomputable def globalSectionsAlgEquiv (hA : IsAffinoidAlgebra K A) :
    (univ hA).sections ≃ₐ[K] A :=
  (univ hA).sectionsAlgEquiv (IsAffinoidSubdomainMap.id hA)

@[simp]
theorem globalSectionsAlgEquiv_toSections (hA : IsAffinoidAlgebra K A) (a : A) :
    globalSectionsAlgEquiv hA ((univ hA).toSections a) = a :=
  sectionsAlgEquiv_toSections (univ hA) (IsAffinoidSubdomainMap.id hA) a

@[simp]
theorem globalSectionsAlgEquiv_symm_apply (hA : IsAffinoidAlgebra K A) (a : A) :
    (globalSectionsAlgEquiv hA).symm a = (univ hA).toSections a := by
  apply (globalSectionsAlgEquiv hA).injective
  simp

/-- The empty affinoid subdomain, represented by the zero quotient of the ambient algebra. -/
def empty (hA : IsAffinoidAlgebra K A) : AffinoidSubdomain K A :=
  ofMap (IsAffinoidSubdomainMap.empty hA)

@[simp]
theorem coe_empty (hA : IsAffinoidAlgebra K A) :
    (empty hA : Set (MaximalSpectrum A)) = ∅ := (rfl)

@[simp]
theorem not_mem_empty (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) : x ∉ empty hA :=
  Set.notMem_empty x

/-- The algebra of sections on the empty subdomain is the zero algebra. -/
theorem subsingleton_sections_empty (hA : IsAffinoidAlgebra K A) :
    Subsingleton (empty hA).sections :=
  ((empty hA).sectionsAlgEquiv (IsAffinoidSubdomainMap.empty hA)).injective.subsingleton

section Order

variable [hA : Fact (IsAffinoidAlgebra K A)]

/-- The whole spectrum and the empty set are affinoid subdomains. -/
instance : BoundedOrder (AffinoidSubdomain K A) where
  top := univ hA.out
  le_top U := U.le_univ hA.out
  bot := empty hA.out
  bot_le U := by
    rw [← SetLike.coe_subset_coe, coe_empty]
    exact Set.empty_subset _

@[simp]
theorem coe_top : (↑(⊤ : AffinoidSubdomain K A) : Set (MaximalSpectrum A)) = Set.univ := by
  -- The top subdomain is the existing `univ` construction.
  exact coe_univ hA.out

@[simp]
theorem coe_bot : (↑(⊥ : AffinoidSubdomain K A) : Set (MaximalSpectrum A)) = ∅ := by
  -- The bottom subdomain is the existing `empty` construction.
  exact coe_empty hA.out

/-- The order embedding of affinoid subdomains into the subsets of the classical spectrum. -/
def setEmbedding : AffinoidSubdomain K A ↪o Set (MaximalSpectrum A) :=
  .ofMapLEIff (↑) (fun _ _ ↦ SetLike.coe_subset_coe)

omit hA in
@[simp]
theorem setEmbedding_apply (U : AffinoidSubdomain K A) :
    setEmbedding U = (U : Set (MaximalSpectrum A)) := (rfl)

end Order

end AffinoidSubdomain

end TauCeti
