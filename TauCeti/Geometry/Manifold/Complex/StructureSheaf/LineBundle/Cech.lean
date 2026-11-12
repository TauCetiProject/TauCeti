/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Basic
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# Čech cohomology of the sheaf of holomorphic sections of a vector bundle

Let `V` be a complex vector bundle with model fibre `F` over a complex manifold `X`. This file
takes the cover-colimit Čech cohomology `Hⁿ(X, 𝒪(V))` of its sheaf of holomorphic sections
`TauCeti.holomorphicSectionSheaf I F V`, with complex vector space coefficients. For `F = ℂ` and
holomorphic coordinate changes this is the Čech cohomology `Hⁿ(X, 𝒪(L))` of a holomorphic line
bundle `L` (Forster, *Lectures on Riemann Surfaces*, §29), the cohomology of line bundles on
compact Riemann surfaces.

The results are the cohomological form of the sheaf-level API of
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Basic`: degree zero is the space of
global holomorphic sections, isomorphic bundles have isomorphic cohomology, the trivial line
bundle has the cohomology of the holomorphic structure sheaf, and the cohomology of a direct sum
is the direct sum of the cohomologies. No hypothesis is made on `X` beyond its charted space
structure, except for the dimension count of global sections of the trivial bundle, which needs
`X` to be a nonempty compact connected complex manifold without boundary (`IsManifold I 1 X`,
`I.Boundaryless`).

## Main definitions

* `TauCeti.holomorphicSectionCechCohomology I F V n`: the degree `n` Čech cohomology of the sheaf
  of holomorphic sections of `V`.
* `TauCeti.holomorphicSectionCechCohomology.map`: the map on cohomology induced by a morphism of
  sheaves of holomorphic sections, and `mapIso` for an isomorphism.
* `TauCeti.holomorphicSectionCechCohomology.zeroIso`: degree zero cohomology is the space of global
  holomorphic sections.
* `TauCeti.holomorphicSectionCechCohomology.isoOfLinearEquiv`: an isomorphism of holomorphic
  vector bundles induces an isomorphism on cohomology.
* `TauCeti.holomorphicSectionCechCohomology.trivialIso`: the cohomology of the trivial line bundle
  is the cohomology of the holomorphic structure sheaf.
* `TauCeti.holomorphicSectionCechCohomology.prodIso`: the cohomology of a direct sum `V₁ ×ᵇ V₂` is
  the biproduct of the two cohomologies, and `prodLinearEquiv` the product of vector spaces.

## Main results

* `TauCeti.holomorphicSectionCechCohomology.zeroIso_hom_naturality`: the degree zero
  identification is natural in morphisms of sheaves of holomorphic sections.
* `TauCeti.holomorphicSectionCechCohomology.finrank_trivial_zero`: on a nonempty compact connected
  complex manifold the trivial line bundle has a one-dimensional `H⁰`.
* `TauCeti.holomorphicSectionCechCohomology.finrank_prod`: dimensions of finite-dimensional
  cohomologies add over direct sums. Finite direct sums are iterated binary ones.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §§12, 29.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : X → Type) [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V]

/-- The degree `n` Čech cohomology `Hⁿ(X, 𝒪(V))` of the sheaf of holomorphic sections of the
vector bundle `V`: the colimit over point-neighborhood covers of `X` of the Čech cohomologies of
the covers, as a complex vector space. For a holomorphic line bundle `L` this is `Hⁿ(X, 𝒪(L))`. -/
abbrev holomorphicSectionCechCohomology (n : ℕ) : ModuleCat.{0} ℂ :=
  (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj
    (holomorphicSectionSheaf I F V).obj

namespace holomorphicSectionCechCohomology

/-! ### Functoriality and degree zero -/

/-- **Degree zero cohomology is global sections.** The degree zero Čech cohomology of the sheaf
of holomorphic sections of `V` is the space of holomorphic sections of `V` over all of `X`. -/
def zeroIso :
    (holomorphicSectionSheaf I F V).obj.obj (op ⊤) ≅ holomorphicSectionCechCohomology I F V 0 :=
  Topology.cechCohomologyZeroIso (holomorphicSectionSheaf I F V)

/-- The degree zero identification as a linear equivalence. -/
def zeroLinearEquiv :
    (holomorphicSectionSheaf I F V).obj.obj (op ⊤) ≃ₗ[ℂ] holomorphicSectionCechCohomology I F V 0 :=
  (zeroIso I F V).toLinearEquiv

@[simp]
theorem zeroLinearEquiv_apply (s : (holomorphicSectionSheaf I F V).obj.obj (op ⊤)) :
    zeroLinearEquiv I F V s = (zeroIso I F V).hom s := (rfl)

@[simp]
theorem zeroLinearEquiv_symm_apply (c : holomorphicSectionCechCohomology I F V 0) :
    (zeroLinearEquiv I F V).symm c = (zeroIso I F V).inv c := (rfl)

variable {I}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  {V₁ : X → Type} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
  [FiberBundle F₁ V₁] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℂ (V₁ x)] [VectorBundle ℂ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  {V₂ : X → Type} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
  [FiberBundle F₂ V₂] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℂ (V₂ x)] [VectorBundle ℂ F₂ V₂]

/-- The map on degree `n` Čech cohomology induced by a morphism of sheaves of holomorphic
sections. -/
def map (f : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂) (n : ℕ) :
    holomorphicSectionCechCohomology I F₁ V₁ n ⟶ holomorphicSectionCechCohomology I F₂ V₂ n :=
  (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map f.hom

@[simp]
theorem map_id (n : ℕ) :
    map (𝟙 (holomorphicSectionSheaf I F₁ V₁)) n = 𝟙 (holomorphicSectionCechCohomology I F₁ V₁ n) :=
  (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_id _

@[reassoc (attr := simp)]
theorem map_comp {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
    {V₃ : X → Type} [TopologicalSpace (TotalSpace F₃ V₃)] [∀ x, TopologicalSpace (V₃ x)]
    [FiberBundle F₃ V₃] [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℂ (V₃ x)] [VectorBundle ℂ F₃ V₃]
    (f : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂)
    (g : holomorphicSectionSheaf I F₂ V₂ ⟶ holomorphicSectionSheaf I F₃ V₃) (n : ℕ) :
    map f n ≫ map g n = map (f ≫ g) n :=
  ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_comp _ _).symm

@[simp]
theorem map_zero (n : ℕ) :
    map (0 : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂) n = 0 :=
  (sheafToPresheaf _ _ ⋙ Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_zero _ _

@[simp]
theorem map_add (f g : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂)
    (n : ℕ) : map (f + g) n = map f n + map g n :=
  (sheafToPresheaf _ _ ⋙ Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_add

/-- The degree zero identification is natural: on global sections, a morphism of sheaves of
holomorphic sections induces its map on degree zero cohomology. -/
@[reassoc]
theorem zeroIso_hom_naturality
    (f : holomorphicSectionSheaf I F₁ V₁ ⟶ holomorphicSectionSheaf I F₂ V₂) :
    f.hom.app (op ⊤) ≫ (zeroIso I F₂ V₂).hom = (zeroIso I F₁ V₁).hom ≫ map f 0 :=
  Topology.cechCohomologyZeroIso_hom_naturality _ f

/-- The isomorphism on degree `n` Čech cohomology induced by an isomorphism of sheaves of
holomorphic sections. -/
def mapIso (e : holomorphicSectionSheaf I F₁ V₁ ≅ holomorphicSectionSheaf I F₂ V₂) (n : ℕ) :
    holomorphicSectionCechCohomology I F₁ V₁ n ≅ holomorphicSectionCechCohomology I F₂ V₂ n :=
  (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).mapIso
    ((sheafToPresheaf _ _).mapIso e)

@[simp]
theorem mapIso_hom (e : holomorphicSectionSheaf I F₁ V₁ ≅ holomorphicSectionSheaf I F₂ V₂)
    (n : ℕ) : (mapIso e n).hom = map e.hom n := (rfl)

@[simp]
theorem mapIso_inv (e : holomorphicSectionSheaf I F₁ V₁ ≅ holomorphicSectionSheaf I F₂ V₂)
    (n : ℕ) : (mapIso e n).inv = map e.inv n := (rfl)

/-! ### Isomorphic bundles -/

/-- **Isomorphism invariance.** An isomorphism of holomorphic vector bundles, given as fibrewise
complex linear isomorphisms whose total-space maps in both directions are complex analytic,
induces an isomorphism on every Čech cohomology of the sheaves of holomorphic sections. -/
def isoOfLinearEquiv (φ : ∀ x, V₁ x ≃ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (hφ' : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₁ v.proj ((φ v.proj).symm v.2))) (n : ℕ) :
    holomorphicSectionCechCohomology I F₁ V₁ n ≅ holomorphicSectionCechCohomology I F₂ V₂ n :=
  mapIso (holomorphicSectionSheaf.isoOfLinearEquiv φ hφ hφ') n

@[simp]
theorem isoOfLinearEquiv_hom (φ : ∀ x, V₁ x ≃ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (hφ' : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₁ v.proj ((φ v.proj).symm v.2))) (n : ℕ) :
    (isoOfLinearEquiv φ hφ hφ' n).hom =
      map (holomorphicSectionSheaf.isoOfLinearEquiv φ hφ hφ').hom n :=
  (rfl)

@[simp]
theorem isoOfLinearEquiv_inv (φ : ∀ x, V₁ x ≃ₗ[ℂ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℂ, F₁)) (I.prod 𝓘(ℂ, F₂)) ω
      (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (φ v.proj v.2)))
    (hφ' : ContMDiff (I.prod 𝓘(ℂ, F₂)) (I.prod 𝓘(ℂ, F₁)) ω
      (fun v : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₁ v.proj ((φ v.proj).symm v.2))) (n : ℕ) :
    (isoOfLinearEquiv φ hφ hφ' n).inv =
      map (holomorphicSectionSheaf.isoOfLinearEquiv φ hφ hφ').inv n :=
  (rfl)

/-! ### The trivial line bundle -/

section Trivial

variable (I X)

/-- The Čech cohomology of the trivial line bundle `X × ℂ` is the Čech cohomology of the
holomorphic structure sheaf `TauCeti.holomorphicStructureSheafModules`. -/
def trivialIso (n : ℕ) :
    holomorphicSectionCechCohomology I ℂ (Trivial X ℂ) n ≅
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj
        (holomorphicStructureSheafModules I X).obj :=
  (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).mapIso
    ((sheafToPresheaf _ _).mapIso (holomorphicSectionSheaf.trivialIso I X))

@[simp]
theorem trivialIso_hom (n : ℕ) :
    (trivialIso I X n).hom =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (holomorphicSectionSheaf.trivialIso I X).hom.hom :=
  (rfl)

@[simp]
theorem trivialIso_inv (n : ℕ) :
    (trivialIso I X n).inv =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (holomorphicSectionSheaf.trivialIso I X).inv.hom :=
  (rfl)

/-- **`h⁰(𝒪) = 1`.** On a nonempty compact connected complex manifold without boundary, the
degree zero Čech cohomology of the trivial line bundle is one-dimensional: its global
holomorphic sections are the constant functions. -/
@[simp]
theorem finrank_trivial_zero [I.Boundaryless] [IsManifold I 1 X] [CompactSpace X]
    [PreconnectedSpace X] [Nonempty X] :
    Module.finrank ℂ (holomorphicSectionCechCohomology I ℂ (Trivial X ℂ) 0) = 1 := by
  have e : (holomorphicSectionSheaf I ℂ (Trivial X ℂ)).obj.obj (op ⊤) ≅
      (holomorphicStructureSheafModules I X).obj.obj (op ⊤) :=
    ((sheafToPresheaf _ _).mapIso (holomorphicSectionSheaf.trivialIso I X)).app (op ⊤)
  rw [← (zeroIso I ℂ (Trivial X ℂ)).toLinearEquiv.finrank_eq, e.toLinearEquiv.finrank_eq]
  exact holomorphicStructureSheafModules.finrank_globalSections I X

end Trivial

/-! ### Direct sums -/

section Prod

variable (I F₁ V₁ F₂ V₂)

/-- The Čech cohomology of the sheaf of holomorphic sections of a direct sum `V₁ ×ᵇ V₂`, with
the maps induced by the fibrewise projections and inclusions, as a bicone over the two
cohomologies: the image of `TauCeti.holomorphicSectionSheaf.prodBicone` under Čech cohomology. -/
-- Exposed so that the cone point is visibly the cohomology of the direct sum: otherwise the legs
-- cannot be stated as the maps induced by the sheaf-level projections and inclusions below.
@[expose]
def prodBicone (n : ℕ) :
    BinaryBicone (holomorphicSectionCechCohomology I F₁ V₁ n)
      (holomorphicSectionCechCohomology I F₂ V₂ n) :=
  (sheafToPresheaf _ _ ⋙ Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).mapBinaryBicone
    (holomorphicSectionSheaf.prodBicone I F₁ V₁ F₂ V₂)

@[simp]
theorem prodBicone_pt (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).pt = holomorphicSectionCechCohomology I (F₁ × F₂) (V₁ ×ᵇ V₂) n :=
  (rfl)

@[simp]
theorem prodBicone_fst (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).fst = map (holomorphicSectionSheaf.prodFst I F₁ V₁ F₂ V₂) n :=
  (rfl)

@[simp]
theorem prodBicone_snd (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).snd = map (holomorphicSectionSheaf.prodSnd I F₁ V₁ F₂ V₂) n :=
  (rfl)

@[simp]
theorem prodBicone_inl (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).inl = map (holomorphicSectionSheaf.prodInl I F₁ V₁ F₂ V₂) n :=
  (rfl)

@[simp]
theorem prodBicone_inr (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).inr = map (holomorphicSectionSheaf.prodInr I F₁ V₁ F₂ V₂) n :=
  (rfl)

/-- **Additivity.** The Čech cohomology of the sheaf of holomorphic sections of a direct sum
`V₁ ×ᵇ V₂` is the biproduct of the two cohomologies, since Čech cohomology is an additive
functor of the sheaf and so preserves the biproduct
`TauCeti.holomorphicSectionSheaf.prodBiconeIsBilimit`. -/
def prodBiconeIsBilimit (n : ℕ) : (prodBicone I F₁ V₁ F₂ V₂ n).IsBilimit :=
  have := preservesBinaryBiproduct_of_preservesBiproduct
    (sheafToPresheaf _ _ ⋙ Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n)
    (holomorphicSectionSheaf I F₁ V₁) (holomorphicSectionSheaf I F₂ V₂)
  isBinaryBilimitOfPreserves _ (holomorphicSectionSheaf.prodBiconeIsBilimit I F₁ V₁ F₂ V₂)

/-- The Čech cohomology of the sheaf of holomorphic sections of a direct sum `V₁ ×ᵇ V₂` is
isomorphic to the biproduct `⊞` of the two cohomologies. -/
def prodIso (n : ℕ) :
    holomorphicSectionCechCohomology I (F₁ × F₂) (V₁ ×ᵇ V₂) n ≅
      holomorphicSectionCechCohomology I F₁ V₁ n ⊞ holomorphicSectionCechCohomology I F₂ V₂ n :=
  biprod.uniqueUpToIso _ _ (prodBiconeIsBilimit I F₁ V₁ F₂ V₂ n)

/-- The isomorphism with the biproduct is given by the maps induced by the two projections. -/
@[simp]
theorem prodIso_hom (n : ℕ) :
    (prodIso I F₁ V₁ F₂ V₂ n).hom =
      biprod.lift (map (holomorphicSectionSheaf.prodFst I F₁ V₁ F₂ V₂) n)
        (map (holomorphicSectionSheaf.prodSnd I F₁ V₁ F₂ V₂) n) :=
  (rfl)

/-- The inverse of the isomorphism with the biproduct is given by the maps induced by the two
inclusions. -/
@[simp]
theorem prodIso_inv (n : ℕ) :
    (prodIso I F₁ V₁ F₂ V₂ n).inv =
      biprod.desc (map (holomorphicSectionSheaf.prodInl I F₁ V₁ F₂ V₂) n)
        (map (holomorphicSectionSheaf.prodInr I F₁ V₁ F₂ V₂) n) :=
  (rfl)

/-- The Čech cohomology of a direct sum `V₁ ×ᵇ V₂` is the product of the two cohomologies, as
complex vector spaces. -/
def prodLinearEquiv (n : ℕ) :
    holomorphicSectionCechCohomology I (F₁ × F₂) (V₁ ×ᵇ V₂) n ≃ₗ[ℂ]
      holomorphicSectionCechCohomology I F₁ V₁ n × holomorphicSectionCechCohomology I F₂ V₂ n :=
  (prodIso I F₁ V₁ F₂ V₂ n ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv

variable {I F₁ V₁ F₂ V₂}

/-- The linear equivalence with the product sends a class to its images under the maps induced
by the two projections. -/
@[simp]
theorem prodLinearEquiv_apply (n : ℕ)
    (c : holomorphicSectionCechCohomology I (F₁ × F₂) (V₁ ×ᵇ V₂) n) :
    prodLinearEquiv I F₁ V₁ F₂ V₂ n c =
      (map (holomorphicSectionSheaf.prodFst I F₁ V₁ F₂ V₂) n c,
        map (holomorphicSectionSheaf.prodSnd I F₁ V₁ F₂ V₂) n c) := by
  have h₁ := (Iso.inv_comp_eq _).1 (ModuleCat.biprodIsoProd_inv_comp_fst
    (holomorphicSectionCechCohomology I F₁ V₁ n) (holomorphicSectionCechCohomology I F₂ V₂ n))
  have h₂ := (Iso.inv_comp_eq _).1 (ModuleCat.biprodIsoProd_inv_comp_snd
    (holomorphicSectionCechCohomology I F₁ V₁ n) (holomorphicSectionCechCohomology I F₂ V₂ n))
  refine Prod.ext ?_ ?_
  · have := ConcreteCategory.congr_hom ((prodIso I F₁ V₁ F₂ V₂ n).hom ≫= h₁) c
    rw [prodIso_hom, biprod.lift_fst] at this
    exact this.symm
  · have := ConcreteCategory.congr_hom ((prodIso I F₁ V₁ F₂ V₂ n).hom ≫= h₂) c
    rw [prodIso_hom, biprod.lift_snd] at this
    exact this.symm

/-- The inverse of the linear equivalence with the product sends a pair of classes to the sum of
their images under the maps induced by the two inclusions. -/
@[simp]
theorem prodLinearEquiv_symm_apply (n : ℕ) (a : holomorphicSectionCechCohomology I F₁ V₁ n)
    (b : holomorphicSectionCechCohomology I F₂ V₂ n) :
    (prodLinearEquiv I F₁ V₁ F₂ V₂ n).symm (a, b) =
      map (holomorphicSectionSheaf.prodInl I F₁ V₁ F₂ V₂) n a +
        map (holomorphicSectionSheaf.prodInr I F₁ V₁ F₂ V₂) n b := by
  rw [LinearEquiv.symm_apply_eq, prodLinearEquiv_apply]
  simp [← ConcreteCategory.comp_apply]

/-- The cohomology of a direct sum is finite-dimensional when both summands' are. -/
instance finiteDimensional_prod (n : ℕ)
    [FiniteDimensional ℂ (holomorphicSectionCechCohomology I F₁ V₁ n)]
    [FiniteDimensional ℂ (holomorphicSectionCechCohomology I F₂ V₂ n)] :
    FiniteDimensional ℂ (holomorphicSectionCechCohomology I (F₁ × F₂) (V₁ ×ᵇ V₂) n) :=
  (prodLinearEquiv I F₁ V₁ F₂ V₂ n).symm.finiteDimensional

/-- Dimensions of finite-dimensional Čech cohomologies add over direct sums of bundles. -/
theorem finrank_prod (n : ℕ)
    [FiniteDimensional ℂ (holomorphicSectionCechCohomology I F₁ V₁ n)]
    [FiniteDimensional ℂ (holomorphicSectionCechCohomology I F₂ V₂ n)] :
    Module.finrank ℂ (holomorphicSectionCechCohomology I (F₁ × F₂) (V₁ ×ᵇ V₂) n) =
      Module.finrank ℂ (holomorphicSectionCechCohomology I F₁ V₁ n) +
        Module.finrank ℂ (holomorphicSectionCechCohomology I F₂ V₂ n) := by
  rw [(prodLinearEquiv I F₁ V₁ F₂ V₂ n).finrank_eq, Module.finrank_prod]

end Prod

end holomorphicSectionCechCohomology

end TauCeti
