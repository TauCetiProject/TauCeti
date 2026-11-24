/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective.Basic
public import TauCeti.CategoryTheory.Triangulated.Orthogonal.Localization

/-!
# Graded-projective replacements of curved modules

Let `(A, d, w)` be a right-convention curved DG algebra. Positselski's graded-projective model of
the contraderived category (Theorem 7.9(b)) says that, under a bound on the projective dimensions
of countable products of projective graded modules, the curved modules whose underlying graded
module is projective compute the contraderived category. Its proof has two steps: a product
totalization of a graded-projective resolution replaces an arbitrary curved module by one whose
underlying graded module has finite projective dimension, and a finite resolution then replaces
the latter by a graded-projective module. This file proves the second step, and the resulting
model theorem when every graded right module has finite projective dimension.

**Finite projective dimension.** If the underlying graded module of `X` has projective dimension
`< n`, there is a morphism `s : P ⟶ X` in the curved homotopy category with `P` graded-projective
and absolutely acyclic cone (`exists_gradedProjective_absolutelyAcyclic_trW`). Choose an
epimorphism `Q ⟶ X` from a contractible graded-projective module, with kernel `K`. The underlying
graded module of `K` has projective dimension `< n - 1`, and since `Q` is zero in the homotopy
category, the totalization of `K ⟶ Q ⟶ X` provides a morphism `K[1] ⟶ X` with absolutely acyclic
cone (`exists_absolutelyAcyclic_trW_of_shortExact_of_isZero`). Replacing `K` by induction and
shifting gives `s`.

**The model theorem.** Graded-projective modules are left orthogonal to the contraacyclic ones, so
the localization `Q_ctr` to the contraderived category is fully faithful on them, with no
hypothesis on `A`. When every graded right module has finite projective dimension, for instance
when the graded right global dimension is finite, every curved module has a graded-projective
replacement, so `Q_ctr` restricts to an equivalence from the full subcategory of graded-projective
modules of the curved homotopy category onto the contraderived category
(`ContraderivedCategory.gradedProjectiveEquivalence`). No product totalization is needed in this
case. Under Positselski's condition `(**)` alone, a curved module need not have finite graded
projective dimension, and the first step is still required.

## Main results

* `TauCeti.CurvedDGRightModuleCat.exists_gradedProjective_absolutelyAcyclic_trW`: a curved module
  whose underlying graded module has finite projective dimension receives a morphism with
  absolutely acyclic cone from a graded-projective module.
* `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.isEquivalence_ι_comp_Q`: if every graded
  right module has finite projective dimension, graded-projective modules compute the
  contraderived category.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6 and Theorem 7.9(b).
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

/-! ### Graded-projective replacements in finite projective dimension -/

/-- A curved module whose underlying graded module has projective dimension `< m + 1` receives a
morphism with absolutely acyclic cone from a graded-projective module. -/
private theorem exists_gradedProjective_absolutelyAcyclic_trW_of_succ :
    ∀ (m : ℕ) (M : CurvedDGRightModuleCat.{u, u, u} h),
      HasProjectiveDimensionLT (toGradedModuleCat M) (m + 1) →
      ∃ (P : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
        (s : P ⟶ DGHomotopyCategory.of R M),
        gradedProjective R h P ∧ (absolutelyAcyclic R h).trW s
  | 0, M, hM => ⟨_, 𝟙 _, by
      rw [gradedProjective_iff, DGHomotopyCategory.underlying_of]
      exact projective_iff_hasProjectiveDimensionLT_one.mpr hM,
    MorphismProperty.id_mem _ _⟩
  | m + 1, M, hM => by
    -- Dimension shifting along a contractible graded-projective cover `Q ⟶ M`.
    obtain ⟨K, Q, f, g, hfg, hS, hQ0, hKdim⟩ :=
      exists_shortExact_contractible_of_hasProjectiveDimensionLT (R := R) M hM
    obtain ⟨P, s, hP, hs⟩ := exists_gradedProjective_absolutelyAcyclic_trW_of_succ m K hKdim
    obtain ⟨t, ht⟩ := exists_absolutelyAcyclic_trW_of_shortExact_of_isZero hS hQ0
    exact ⟨P⟦(1 : ℤ)⟧, s⟦(1 : ℤ)⟧' ≫ t, (gradedProjective R h).le_shift 1 _ hP,
      MorphismProperty.comp_mem _ _ _ (hs.shift 1) ht⟩

/-- **Graded-projective replacement.** If the underlying graded module of a curved module `X` has
finite projective dimension, there is a morphism `P ⟶ X` in the curved homotopy category from a
graded-projective module `P` whose cone is absolutely acyclic. -/
theorem exists_gradedProjective_absolutelyAcyclic_trW (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n] :
    ∃ (P : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) (s : P ⟶ X),
      gradedProjective R h P ∧ (absolutelyAcyclic R h).trW s := by
  obtain ⟨P, s, hP, hs⟩ := exists_gradedProjective_absolutelyAcyclic_trW_of_succ n X.underlying
    (hasProjectiveDimensionLT_of_ge _ n (n + 1) (Nat.le_succ n))
  exact ⟨P, s ≫ eqToHom (DGHomotopyCategory.of_underlying R X), hP,
    MorphismProperty.comp_mem _ _ _ hs (ObjectProperty.trW_of_isIso _ _)⟩

/-! ### The graded-projective model of the contraderived category -/

namespace ContraderivedCategory

/-- The localization to the contraderived category is full on graded-projective modules. -/
instance : ((gradedProjective R h).ι ⋙ Q R h).Full :=
  ObjectProperty.full_ι_comp_of_le_leftOrthogonal _
    (gradedProjective_le_leftOrthogonal_contraacyclic R h)

/-- The localization to the contraderived category is faithful on graded-projective modules. -/
instance : ((gradedProjective R h).ι ⋙ Q R h).Faithful :=
  ObjectProperty.faithful_ι_comp_of_le_leftOrthogonal _
    (gradedProjective_le_leftOrthogonal_contraacyclic R h)

section FiniteProjectiveDimension

variable
  (hn : ∀ V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
    ∃ n, HasProjectiveDimensionLT V n)
include hn

/-- **The graded-projective model in finite projective dimension.** If every graded right module
has finite projective dimension, the localization to the contraderived category restricts to an
equivalence on the full subcategory of graded-projective curved modules. -/
theorem isEquivalence_ι_comp_Q : ((gradedProjective R h).ι ⋙ Q R h).IsEquivalence :=
  ObjectProperty.isEquivalence_ι_comp_of_le_leftOrthogonal _
    (gradedProjective_le_leftOrthogonal_contraacyclic R h) fun X ↦
      have ⟨n, _⟩ := hn (toGradedModuleCat X.underlying)
      have ⟨P, s, hP, hs⟩ := exists_gradedProjective_absolutelyAcyclic_trW n X
      ⟨P, s, hP, ObjectProperty.trW_monotone (absolutelyAcyclic_le_contraacyclic R h) _ hs⟩

variable (R h) in
/-- If every graded right module has finite projective dimension, the full subcategory of the
curved homotopy category on graded-projective modules is equivalent to the contraderived category,
by the localization functor. -/
noncomputable def gradedProjectiveEquivalence :
    (gradedProjective R h).FullSubcategory ≌ ContraderivedCategory R h :=
  have := isEquivalence_ι_comp_Q (R := R) (h := h) hn
  ((gradedProjective R h).ι ⋙ Q R h).asEquivalence

/-- The functor of `gradedProjectiveEquivalence` is the localization functor. -/
@[simp]
theorem gradedProjectiveEquivalence_functor :
    (gradedProjectiveEquivalence R h hn).functor = (gradedProjective R h).ι ⋙ Q R h :=
  (rfl)

end FiniteProjectiveDimension

end ContraderivedCategory

end TauCeti.CurvedDGRightModuleCat
