/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.Algebra.Category.ModuleCat.Biproducts
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

Since `TauCeti.holomorphicSectionCechCohomology` is an abbreviation for the cover-colimit Čech
cohomology functor `Topology.cechCohomology` applied to this sheaf, its functoriality in
morphisms of sheaves of holomorphic sections, and in particular its invariance under the
sheaf-level isomorphism `TauCeti.holomorphicSectionSheaf.isoOfLinearEquiv` induced by an
isomorphism of holomorphic bundles, is that of the functor. Likewise its degree zero
identification with global holomorphic sections is `Topology.cechCohomologyZeroIso` applied to
`TauCeti.holomorphicSectionSheaf I F V`. This file adds the results specific to these sheaves: the
trivial line bundle has the cohomology of the holomorphic structure sheaf, and the cohomology of a
direct sum is the direct sum of the cohomologies. No hypothesis is made on `X` beyond its charted
space structure, except for the dimension count of global sections of the trivial bundle, which
needs `X` to be a nonempty compact connected complex manifold without boundary
(`IsManifold I 1 X`, `I.Boundaryless`).

## Main definitions

* `TauCeti.holomorphicSectionCechCohomology I F V n`: the degree `n` Čech cohomology of the sheaf
  of holomorphic sections of `V`.
* `TauCeti.holomorphicSectionCechCohomology.trivialIso`: the cohomology of the trivial line bundle
  is the cohomology of the holomorphic structure sheaf.
* `TauCeti.holomorphicSectionCechCohomology.prodIso`: the cohomology of a direct sum `V₁ ×ᵇ V₂` is
  the biproduct of the two cohomologies, and `prodLinearEquiv` the product of vector spaces.

## Main results

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

variable {I}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  {V₁ : X → Type} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
  [FiberBundle F₁ V₁] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℂ (V₁ x)] [VectorBundle ℂ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  {V₂ : X → Type} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
  [FiberBundle F₂ V₂] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℂ (V₂ x)] [VectorBundle ℂ F₂ V₂]

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
  rw [← (Topology.cechCohomologyZeroIso
    (holomorphicSectionSheaf I ℂ (Trivial X ℂ))).toLinearEquiv.finrank_eq,
    e.toLinearEquiv.finrank_eq]
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
    (prodBicone I F₁ V₁ F₂ V₂ n).fst =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (holomorphicSectionSheaf.prodFst I F₁ V₁ F₂ V₂).hom :=
  (rfl)

@[simp]
theorem prodBicone_snd (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).snd =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (holomorphicSectionSheaf.prodSnd I F₁ V₁ F₂ V₂).hom :=
  (rfl)

@[simp]
theorem prodBicone_inl (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).inl =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (holomorphicSectionSheaf.prodInl I F₁ V₁ F₂ V₂).hom :=
  (rfl)

@[simp]
theorem prodBicone_inr (n : ℕ) :
    (prodBicone I F₁ V₁ F₂ V₂ n).inr =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (holomorphicSectionSheaf.prodInr I F₁ V₁ F₂ V₂).hom :=
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
      biprod.lift
        ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodFst I F₁ V₁ F₂ V₂).hom)
        ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodSnd I F₁ V₁ F₂ V₂).hom) :=
  (rfl)

/-- The inverse of the isomorphism with the biproduct is given by the maps induced by the two
inclusions. -/
@[simp]
theorem prodIso_inv (n : ℕ) :
    (prodIso I F₁ V₁ F₂ V₂ n).inv =
      biprod.desc
        ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodInl I F₁ V₁ F₂ V₂).hom)
        ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodInr I F₁ V₁ F₂ V₂).hom) :=
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
      ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodFst I F₁ V₁ F₂ V₂).hom c,
        (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodSnd I F₁ V₁ F₂ V₂).hom c) := by
  rw [prodLinearEquiv, Iso.toLinearEquiv_apply]
  simp [biprod.lift_eq]

/-- The inverse of the linear equivalence with the product sends a pair of classes to the sum of
their images under the maps induced by the two inclusions. -/
@[simp]
theorem prodLinearEquiv_symm_apply (n : ℕ) (a : holomorphicSectionCechCohomology I F₁ V₁ n)
    (b : holomorphicSectionCechCohomology I F₂ V₂ n) :
    (prodLinearEquiv I F₁ V₁ F₂ V₂ n).symm (a, b) =
      (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodInl I F₁ V₁ F₂ V₂).hom a +
        (Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
          (holomorphicSectionSheaf.prodInr I F₁ V₁ F₂ V₂).hom b := by
  rw [prodLinearEquiv, Iso.toLinearEquiv_symm, Iso.toLinearEquiv_apply]
  simp [biprod.desc_eq, ← Category.assoc, -ModuleCat.hom_comp]

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
