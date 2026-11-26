/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective.Model
public import TauCeti.Algebra.Homology.Curved.Module.Right.Resolution.ProdTotal

/-!
# The graded-projective model of the contraderived category

This file proves Positselski's graded-projective model theorem for the contraderived category
`D_ctr` of curved differential graded right modules over a right-convention curved DG algebra `A`
(Positselski, *Differential graded Koszul duality: an introductory survey*, Theorem 7.9(b)).

By `instIsTriangulatedGradedProjective` (from `Graded.Projective.Basic`), the graded-projective
curved right modules form a triangulated subcategory `gradedProjective R h` of the curved homotopy
category, so the restriction `(gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h` of the
contraderived localization functor is a triangle functor. Because contraacyclic objects are right
orthogonal to graded-projective objects, this restriction is unconditionally fully faithful (via
`Graded.Projective.Model`).

Essential surjectivity holds whenever every countable product of projective graded right
`A`-modules has finite projective dimension
(`HasFiniteProjectiveDimensionOfCountableProductsOfProjective`, which in particular follows from
Positselski's uniform countable-product hypothesis `(**)`). Given any curved right module `M`:

1. Choose a graded-projective left resolution `r` of `M` (`LeftResolution.ofGradedProjective`).
2. Its product totalization `Tot^Π(r)` has underlying graded module isomorphic to the countable
   product of the shifted graded-projective terms, so by the countable-product hypothesis it has
   finite graded projective dimension `d`.
3. By `exists_gradedProjective_absolutelyAcyclic_trW` (from `Graded.Projective.Model`), there is a
   morphism `Q ⟶ Tot^Π(r)` in the curved homotopy category from a graded-projective curved module
   `Q` whose cone is absolutely acyclic, hence contraacyclic.
4. Lifting to a closed morphism and composing with the augmentation `Tot^Π(r) ⟶ M` (whose cone is
   contraacyclic by `LeftResolution.contraacyclic_cone_prodTotalAug`) produces a closed morphism
   `Q ⟶ M` with contraacyclic cone.

Combining full faithfulness with this replacement yields the triangulated equivalence
`(gradedProjective R h).FullSubcategory ≌ ContraderivedCategory R h`. When every graded right
`A`-module has finite projective dimension (for instance when the graded right global dimension is
finite), `HasFiniteProjectiveDimensionOfCountableProductsOfProjective` holds immediately, and
`Graded.Projective.Model` also proves the equivalence directly without product totalization.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.HasFiniteProjectiveDimensionOfCountableProductsOfProjective`: the
  countable-product projective-dimension hypothesis for graded right `A`-modules (generalizing
  Positselski's uniform condition `(**)`).
* `gradedProjectiveEquivalenceOfHasFiniteProjectiveDimensionOfCountableProductsOfProjective` (in
  `ContraderivedCategory`): under `HasFiniteProjectiveDimensionOfCountableProductsOfProjective`, the
  equivalence between the homotopy category of graded-projective curved right modules and the
  contraderived category.

## Main results

* `TauCeti.CurvedDGRightModuleCat.exists_gradedProjective_contraacyclic_cone`: when countable
  products of projective graded right `A`-modules have finite projective dimension, every curved
  right module admits a closed morphism from a graded-projective curved right module with
  contraacyclic mapping cone.
* `isEquivalence_ι_comp_Q_of_hasFiniteProjectiveDimensionOfCountableProductsOfProjective` (in
  `ContraderivedCategory`): Positselski's Theorem 7.9(b), asserting that
  `(gradedProjective R h).ι ⋙ Q` is an equivalence when countable products of projective graded
  right `A`-modules have finite projective dimension.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.9, Theorem 7.9(b).
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

local instance : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-! ### Graded-projective replacement under countable-product finite projective dimension -/

variable (𝒜) in
/-- Every countable product of projective graded right `A`-modules has finite projective
dimension. In particular, this holds under Positselski's uniform countable-product
projective-dimension condition `(**)`. -/
def HasFiniteProjectiveDimensionOfCountableProductsOfProjective : Prop :=
  ∀ (P : ULift.{u} ℕ →
      GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece),
    (∀ n, Projective (P n)) → ∃ d : ℕ, HasProjectiveDimensionLE (∏ᶜ P) d

variable (𝒜) in
/-- Defining characterization of `HasFiniteProjectiveDimensionOfCountableProductsOfProjective`. -/
theorem hasFiniteProjectiveDimensionOfCountableProductsOfProjective_def :
    HasFiniteProjectiveDimensionOfCountableProductsOfProjective 𝒜 ↔
      ∀ (P : ULift.{u} ℕ →
          GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece),
        (∀ n, Projective (P n)) → ∃ d : ℕ, HasProjectiveDimensionLE (∏ᶜ P) d :=
  Iff.rfl

/-- If every countable product of projective graded right modules has finite projective dimension,
then every curved right module admits a closed morphism from a graded-projective curved right
module whose mapping cone is contraacyclic. -/
theorem exists_gradedProjective_contraacyclic_cone
    (hprod : HasFiniteProjectiveDimensionOfCountableProductsOfProjective 𝒜)
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (Q : CurvedDGRightModuleCat.{u, u, u} h)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M),
      Projective (toGradedModuleCat Q) ∧
        contraacyclic R h (DGHomotopyCategory.of R (cone f)) := by
  let r := LeftResolution.ofGradedProjective M
  let P : ULift.{u} ℕ → GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece :=
    fun n ↦ toGradedModuleCat ((r.term n.down).shift (n.down : ℤ))
  have hP : ∀ n, Projective (P n) := fun n ↦
    have := LeftResolution.projective_ofGradedProjective_term M n.down
    inferInstance
  obtain ⟨d, hProdDim⟩ :=
    (hasFiniteProjectiveDimensionOfCountableProductsOfProjective_def 𝒜).1 hprod P hP
  have hTotDim : HasProjectiveDimensionLT
      (toGradedModuleCat (DGHomotopyCategory.of R r.prodTotal).underlying) (d + 1) :=
    hasProjectiveDimensionLT_of_iso r.prodTotalToPiIso.symm (d + 1)
  obtain ⟨Q, s, hQ, hs⟩ :=
    exists_gradedProjective_absolutelyAcyclic_trW (d + 1) (DGHomotopyCategory.of R r.prodTotal)
  obtain ⟨g, hg⟩ := (dgClosedToHomotopy R).map_surjective
    (eqToHom (DGHomotopyCategory.of_underlying R Q) ≫ s)
  refine ⟨Q.underlying, g ≫ r.prodTotalAug, (gradedProjective_iff Q).1 hQ, ?_⟩
  have hgCone : contraacyclic R h (DGHomotopyCategory.of R (cone g)) :=
    (trW_dgClosedToHomotopy_map_iff (contraacyclic R h) g).1 <| by
      rw [hg]
      exact MorphismProperty.comp_mem _ _ _ (ObjectProperty.trW_of_isIso _ _)
        (ObjectProperty.trW_monotone (absolutelyAcyclic_le_contraacyclic R h) _ hs)
  exact cone_comp_mem_of_isTriangulated (contraacyclic R h) g r.prodTotalAug
    hgCone r.contraacyclic_cone_prodTotalAug

/-! ### The graded-projective model of `D_ctr` -/

namespace ContraderivedCategory

variable (R h) in
/-- **Positselski's graded-projective model of the contraderived category (Theorem 7.9(b)).**
If every countable product of projective graded right `A`-modules has finite projective dimension,
then the restriction of the contraderived localization functor to the triangulated full subcategory
of graded-projective curved right modules is an equivalence. -/
theorem isEquivalence_ι_comp_Q_of_hasFiniteProjectiveDimensionOfCountableProductsOfProjective
    (hprod : HasFiniteProjectiveDimensionOfCountableProductsOfProjective 𝒜) :
    ((gradedProjective R h).ι ⋙ Q R h).IsEquivalence := by
  refine ObjectProperty.isEquivalence_ι_comp_of_le_leftOrthogonal (Q R h)
    (gradedProjective_le_leftOrthogonal_contraacyclic R h) fun X ↦ ?_
  obtain ⟨P, f, hP, hf⟩ := exists_gradedProjective_contraacyclic_cone hprod X.underlying
  refine ⟨DGHomotopyCategory.of R P, (dgClosedToHomotopy R).map f,
    (gradedProjective_iff _).2 hP, ?_⟩
  exact (trW_dgClosedToHomotopy_map_iff _ f).2 hf

variable (R h) in
/-- Under `HasFiniteProjectiveDimensionOfCountableProductsOfProjective`, the triangulated full
subcategory of graded-projective curved right modules is equivalent to the contraderived category
via the localization functor. -/
noncomputable def
    gradedProjectiveEquivalenceOfHasFiniteProjectiveDimensionOfCountableProductsOfProjective
    (hprod : HasFiniteProjectiveDimensionOfCountableProductsOfProjective 𝒜) :
    (gradedProjective R h).FullSubcategory ≌ ContraderivedCategory R h :=
  have :=
    isEquivalence_ι_comp_Q_of_hasFiniteProjectiveDimensionOfCountableProductsOfProjective R h hprod
  ((gradedProjective R h).ι ⋙ Q R h).asEquivalence

/-- The forward functor of
`gradedProjectiveEquivalenceOfHasFiniteProjectiveDimensionOfCountableProductsOfProjective` is the
restriction of the contraderived localization functor. -/
@[simp]
theorem
    gradedProjectiveEquivalenceOfHasFiniteProjectiveDimensionOfCountableProductsOfProjective_functor
    (hprod : HasFiniteProjectiveDimensionOfCountableProductsOfProjective 𝒜) :
    (gradedProjectiveEquivalenceOfHasFiniteProjectiveDimensionOfCountableProductsOfProjective
      R h hprod).functor =
      (gradedProjective R h).ι ⋙ Q R h :=
  (rfl)

/-- The restriction of the contraderived localization functor to graded-projective curved right
modules is a triangle functor. -/
example : ((gradedProjective R h).ι ⋙ Q R h).IsTriangulated := inferInstance

end ContraderivedCategory

end TauCeti.CurvedDGRightModuleCat
