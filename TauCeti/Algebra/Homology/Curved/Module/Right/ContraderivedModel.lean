/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Resolution.ProdTotal
public import TauCeti.CategoryTheory.Triangulated.Orthogonal.Localization

/-!
# The graded-projective model of the contraderived category

This file proves Positselski's graded-projective model theorem for the contraderived category
`D_ctr` of curved differential graded right modules over a right-convention curved DG algebra `A`
(Positselski, *Differential graded Koszul duality: an introductory survey*, Theorem 7.9(b)).

By `instIsTriangulatedGradedProjective` (from `Graded.Projective`), the graded-projective curved
right modules form a triangulated subcategory `gradedProjective R h` of the curved homotopy
category, so the restriction `(gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h` of the
contraderived localization functor is a triangle functor. Because contraacyclic objects are right
orthogonal to graded-projective objects, this restriction is unconditionally fully faithful.

Essential surjectivity holds under Positselski's countable-product hypothesis `(**)`: there exists
a uniform bound `d : ℕ` such that every countable product of projective graded right `A`-modules
has projective dimension at most `d`. Given any curved right module `M`:

1. Choose a graded-projective left resolution `r` of `M` (`LeftResolution.ofGradedProjective`).
2. Its product totalization `Tot^Π(r)` has underlying graded module isomorphic to the countable
   product of the shifted graded-projective terms, so by `(**)` it has graded projective dimension
   at most `d`.
3. By `exists_gradedProjective_absolutelyAcyclic_cone`, there is a closed morphism
   `g : Q ⟶ Tot^Π(r)` from a graded-projective curved module `Q` whose cone is absolutely acyclic,
   hence contraacyclic.
4. Composing `g` with the augmentation `Tot^Π(r) ⟶ M` (whose cone is contraacyclic by
   `LeftResolution.contraacyclic_cone_prodTotalAug`) produces a closed morphism `Q ⟶ M` with
   contraacyclic cone.

Combining full faithfulness with this replacement yields the triangulated equivalence
`(gradedProjective R h).FullSubcategory ≌ ContraderivedCategory R h`. In particular, the
equivalence holds whenever the abelian category of graded right `A`-modules has finite global
dimension.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.CountableProjectiveCondition`: Positselski's countable-product
  projective-dimension bound `(**)` for graded right `A`-modules.
* `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.gradedProjectiveEquivalence`: under
  Positselski's countable-product projective-dimension bound `(**)`, the equivalence between the
  homotopy category of graded-projective curved right modules and the contraderived category.

## Main results

* `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.full_gradedProjective_ι_comp_Q` and
  `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.faithful_gradedProjective_ι_comp_Q`: the
  contraderived localization functor is unconditionally full and faithful on graded-projective
  curved right modules.
* `TauCeti.CurvedDGRightModuleCat.exists_gradedProjective_contraacyclic_cone`: under condition
  `(**)`, every curved right module admits a closed morphism from a graded-projective curved right
  module with contraacyclic mapping cone.
* `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.isEquivalence_gradedProjective_ι_comp_Q`:
  Positselski's Theorem 7.9(b), asserting that `(gradedProjective R h).ι ⋙ Q` is an equivalence
  under condition `(**)`.
* `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.isEquivalence_of_hasProjectiveDimensionLE`:
  the specialization to graded algebras of finite right graded global dimension.

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

/-! ### Graded-projective replacement under Positselski's condition `(**)` -/

variable (𝒜) in
/-- Positselski's countable-product projective-dimension condition `(**)` for graded right
`A`-modules: there exists a uniform bound `d : ℕ` such that every countable product of projective
graded right `A`-modules has projective dimension at most `d`. -/
def CountableProjectiveCondition : Prop :=
  ∃ d : ℕ, ∀ (P : ULift.{u} ℕ →
      GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece),
    (∀ n, Projective (P n)) → HasProjectiveDimensionLE (∏ᶜ P) d

private theorem exists_gradedProjective_contraacyclic_cone_of_bound (d : ℕ)
    (hprod : ∀ (P : ULift.{u} ℕ →
        GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece),
      (∀ n, Projective (P n)) → HasProjectiveDimensionLE (∏ᶜ P) d)
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
  have hProdDim : HasProjectiveDimensionLE (∏ᶜ P) d := hprod P hP
  have hTotDim : HasProjectiveDimensionLE (toGradedModuleCat r.prodTotal) d :=
    hasProjectiveDimensionLT_of_iso r.prodTotalToPiIso.symm (d + 1)
  obtain ⟨Q, g, hQ, hg⟩ := exists_gradedProjective_absolutelyAcyclic_cone hTotDim
  refine ⟨Q, g ≫ r.prodTotalAug, hQ, ?_⟩
  have hgW : (contraacyclic R h).trW ((dgClosedToHomotopy R).map g) :=
    (trW_dgClosedToHomotopy_map_iff _ g).2 (absolutelyAcyclic_le_contraacyclic R h _ hg)
  have haugW : (contraacyclic R h).trW ((dgClosedToHomotopy R).map r.prodTotalAug) :=
    (trW_dgClosedToHomotopy_map_iff _ r.prodTotalAug).2 r.contraacyclic_cone_prodTotalAug
  have hcompW : (contraacyclic R h).trW ((dgClosedToHomotopy R).map (g ≫ r.prodTotalAug)) := by
    rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ hgW haugW
  exact (trW_dgClosedToHomotopy_map_iff _ (g ≫ r.prodTotalAug)).1 hcompW

/-- Under Positselski's countable-product projective-dimension bound `(**)`, every curved right
module admits a closed morphism from a graded-projective curved right module whose mapping cone
is contraacyclic. -/
theorem exists_gradedProjective_contraacyclic_cone (hprod : CountableProjectiveCondition 𝒜)
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (Q : CurvedDGRightModuleCat.{u, u, u} h)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M),
      Projective (toGradedModuleCat Q) ∧
        contraacyclic R h (DGHomotopyCategory.of R (cone f)) := by
  obtain ⟨d, hd⟩ := hprod
  exact exists_gradedProjective_contraacyclic_cone_of_bound d hd M

/-! ### The graded-projective model of `D_ctr` -/

namespace ContraderivedCategory

variable (R h) in
/-- The localization functor to the contraderived category is full on graded-projective curved
right modules. -/
instance full_gradedProjective_ι_comp_Q :
    ((gradedProjective R h).ι ⋙ Q R h).Full :=
  ObjectProperty.full_ι_comp_of_le_leftOrthogonal (Q R h)
    ((ObjectProperty.le_leftOrthogonal_iff_le_rightOrthogonal _ _).2
      (contraacyclic_le_rightOrthogonal_gradedProjective R h))

variable (R h) in
/-- The localization functor to the contraderived category is faithful on graded-projective curved
right modules. -/
instance faithful_gradedProjective_ι_comp_Q :
    ((gradedProjective R h).ι ⋙ Q R h).Faithful :=
  ObjectProperty.faithful_ι_comp_of_le_leftOrthogonal (Q R h)
    ((ObjectProperty.le_leftOrthogonal_iff_le_rightOrthogonal _ _).2
      (contraacyclic_le_rightOrthogonal_gradedProjective R h))

variable (R h) in
/-- **Positselski's graded-projective model of the contraderived category (Theorem 7.9(b)).**
If every countable product of projective graded right `A`-modules has uniformly bounded projective
dimension, then the restriction of the contraderived localization functor to the triangulated full
subcategory of graded-projective curved right modules is an equivalence. -/
theorem isEquivalence_gradedProjective_ι_comp_Q (hprod : CountableProjectiveCondition 𝒜) :
    ((gradedProjective R h).ι ⋙ Q R h).IsEquivalence := by
  refine ObjectProperty.isEquivalence_ι_comp_of_le_leftOrthogonal (Q R h)
    ((ObjectProperty.le_leftOrthogonal_iff_le_rightOrthogonal _ _).2
      (contraacyclic_le_rightOrthogonal_gradedProjective R h)) fun X ↦ ?_
  obtain ⟨P, f, hP, hf⟩ := exists_gradedProjective_contraacyclic_cone hprod X.underlying
  refine ⟨DGHomotopyCategory.of R P, (dgClosedToHomotopy R).map f,
    (gradedProjective_iff _).2 hP, ?_⟩
  exact (trW_dgClosedToHomotopy_map_iff _ f).2 hf

variable (R h) in
/-- Under Positselski's countable-product projective-dimension bound `(**)`, the triangulated full
subcategory of graded-projective curved right modules is equivalent to the contraderived category
via the localization functor. -/
noncomputable def gradedProjectiveEquivalence (hprod : CountableProjectiveCondition 𝒜) :
    (gradedProjective R h).FullSubcategory ≌ ContraderivedCategory R h :=
  have := isEquivalence_gradedProjective_ι_comp_Q R h hprod
  ((gradedProjective R h).ι ⋙ Q R h).asEquivalence

/-- The forward functor of `gradedProjectiveEquivalence` is the restriction of the contraderived
localization functor. -/
@[simp]
theorem gradedProjectiveEquivalence_functor (hprod : CountableProjectiveCondition 𝒜) :
    (gradedProjectiveEquivalence R h hprod).functor =
      (gradedProjective R h).ι ⋙ Q R h :=
  (rfl)

variable (R h) in
/-- If the abelian category of graded right `A`-modules has finite global dimension `≤ d`, then
the contraderived localization functor restricts to an equivalence from graded-projective curved
right modules to the contraderived category. -/
theorem isEquivalence_of_hasProjectiveDimensionLE (d : ℕ)
    (hd : ∀ X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE X d) :
    ((gradedProjective R h).ι ⋙ Q R h).IsEquivalence :=
  isEquivalence_gradedProjective_ι_comp_Q R h ⟨d, fun P _ ↦ hd (∏ᶜ P)⟩

/-- The restriction of the contraderived localization functor to graded-projective curved right
modules is a triangle functor. -/
example : ((gradedProjective R h).ι ⋙ Q R h).IsTriangulated := inferInstance

end ContraderivedCategory

end TauCeti.CurvedDGRightModuleCat
