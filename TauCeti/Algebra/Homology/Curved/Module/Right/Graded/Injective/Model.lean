/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective.Basic
public import TauCeti.CategoryTheory.Triangulated.Orthogonal.Localization

/-!
# Graded-injective replacements of curved modules

Let `(A, d, w)` be a right-convention curved DG algebra. Positselski's graded-injective model of
the coderived category (Theorem 7.9(a)) says that, under a bound on the injective dimensions of
countable direct sums of injective graded modules, the curved modules whose underlying graded
module is injective compute the coderived category. Its proof has two steps: a coproduct
totalization of a graded-injective coresolution replaces an arbitrary curved module by one whose
underlying graded module has finite injective dimension, and a finite coresolution then replaces
the latter by a graded-injective module. This file proves the second step, and the resulting
model theorem when every graded right module has finite injective dimension.

**Finite injective dimension.** If the underlying graded module of `X` has injective dimension
`< n`, there is a morphism `s : X ⟶ I` in the curved homotopy category with `I` graded-injective
and absolutely acyclic cone (`exists_gradedInjective_absolutelyAcyclic_trW`). Choose a
monomorphism `X ⟶ Q` into a contractible graded-injective module, with cokernel `C`. The underlying
graded module of `C` has injective dimension `< n - 1`, and since `Q` is zero in the homotopy
category, the totalization of `X ⟶ Q ⟶ C` provides a morphism `X ⟶ C[-1]` with absolutely acyclic
cone (`exists_absolutelyAcyclic_trW_shift_neg_one_of_shortExact_of_isZero`). Replacing `C` by
induction and shifting gives `s`.

**The model theorem.** Graded-injective modules are right orthogonal to the coacyclic ones, so
the localization `Q_co` to the coderived category is fully faithful on them, with no hypothesis
on `A`. When every graded right module has finite injective dimension, for instance when the
graded right global dimension is finite, every curved module has a graded-injective replacement,
so `Q_co` restricts to an equivalence from the full subcategory of graded-injective modules of the
curved homotopy category onto the coderived category
(`CoderivedCategory.gradedInjectiveEquivalence`). Under Positselski's condition `(*)` alone, a
curved module need not have finite graded injective dimension, and the first step is still
required.

## Main results

* `TauCeti.CurvedDGRightModuleCat.exists_gradedInjective_absolutelyAcyclic_trW`: a curved module
  whose underlying graded module has finite injective dimension admits a morphism with absolutely
  acyclic cone into a graded-injective module.
* `TauCeti.CurvedDGRightModuleCat.CoderivedCategory.isEquivalence_ι_comp_Q`: if every graded right
  module has finite injective dimension, graded-injective modules compute the coderived category.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.5 and Section 3.7.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6 and Theorem 7.9(a).
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective.Model`,
  for the dual graded-projective model of the contraderived category.
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

/-! ### Graded-injective replacements in finite injective dimension -/

/-- A curved module whose underlying graded module has injective dimension `< m + 1` admits a
morphism with absolutely acyclic cone into a graded-injective module. -/
private theorem exists_gradedInjective_absolutelyAcyclic_trW_of_succ :
    ∀ (m : ℕ) (M : CurvedDGRightModuleCat.{u, u, u} h),
      HasInjectiveDimensionLT (toGradedModuleCat M) (m + 1) →
      ∃ (I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
        (s : DGHomotopyCategory.of R M ⟶ I),
        gradedInjective R h I ∧ (absolutelyAcyclic R h).trW s
  | 0, M, hM => ⟨_, 𝟙 _, by
      rw [gradedInjective_iff, DGHomotopyCategory.underlying_of]
      exact injective_iff_hasInjectiveDimensionLT_one.mpr hM,
    MorphismProperty.id_mem _ _⟩
  | m + 1, M, hM => by
    -- Dimension shifting along a contractible graded-injective embedding `M ⟶ Q`.
    obtain ⟨Q, C, f, g, hfg, hS, hQ0, hCdim⟩ :=
      exists_shortExact_contractible_of_hasInjectiveDimensionLT (R := R) M hM
    obtain ⟨I, t, hI, ht⟩ := exists_gradedInjective_absolutelyAcyclic_trW_of_succ m C hCdim
    obtain ⟨s, hs⟩ := exists_absolutelyAcyclic_trW_shift_neg_one_of_shortExact_of_isZero hS hQ0
    exact ⟨I⟦(-1 : ℤ)⟧, s ≫ t⟦(-1 : ℤ)⟧', (gradedInjective R h).le_shift (-1) _ hI,
      MorphismProperty.comp_mem _ _ _ hs (ht.shift (-1))⟩

/-- **Graded-injective replacement.** If the underlying graded module of a curved module `X` has
finite injective dimension, there is a morphism `X ⟶ I` in the curved homotopy category into a
graded-injective module `I` whose cone is absolutely acyclic. -/
theorem exists_gradedInjective_absolutelyAcyclic_trW (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n] :
    ∃ (I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) (s : X ⟶ I),
      gradedInjective R h I ∧ (absolutelyAcyclic R h).trW s := by
  obtain ⟨I, s, hI, hs⟩ := exists_gradedInjective_absolutelyAcyclic_trW_of_succ n X.underlying
    (hasInjectiveDimensionLT_of_ge _ n (n + 1) (Nat.le_succ n))
  exact ⟨I, eqToHom (DGHomotopyCategory.of_underlying R X).symm ≫ s, hI,
    MorphismProperty.comp_mem _ _ _ (ObjectProperty.trW_of_isIso _ _) hs⟩

/-! ### The graded-injective model of the coderived category -/

namespace CoderivedCategory

/-- The localization to the coderived category is full on graded-injective modules. -/
instance : ((gradedInjective R h).ι ⋙ Q R h).Full :=
  ObjectProperty.full_ι_comp_of_le_rightOrthogonal _
    (gradedInjective_le_rightOrthogonal_coacyclic R h)

/-- The localization to the coderived category is faithful on graded-injective modules. -/
instance : ((gradedInjective R h).ι ⋙ Q R h).Faithful :=
  ObjectProperty.faithful_ι_comp_of_le_rightOrthogonal _
    (gradedInjective_le_rightOrthogonal_coacyclic R h)

section FiniteInjectiveDimension

variable
  (hn : ∀ V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
    ∃ n, HasInjectiveDimensionLT V n)
include hn

/-- **The graded-injective model in finite injective dimension.** If every graded right module
has finite injective dimension, the localization to the coderived category restricts to an
equivalence on the full subcategory of graded-injective curved modules. -/
theorem isEquivalence_ι_comp_Q : ((gradedInjective R h).ι ⋙ Q R h).IsEquivalence :=
  ObjectProperty.isEquivalence_ι_comp_of_le_rightOrthogonal _
    (gradedInjective_le_rightOrthogonal_coacyclic R h) fun X ↦
      have ⟨n, _⟩ := hn (toGradedModuleCat X.underlying)
      have ⟨I, s, hI, hs⟩ := exists_gradedInjective_absolutelyAcyclic_trW n X
      ⟨I, s, hI, ObjectProperty.trW_monotone (absolutelyAcyclic_le_coacyclic R h) _ hs⟩

variable (R h) in
/-- If every graded right module has finite injective dimension, the full subcategory of the
curved homotopy category on graded-injective modules is equivalent to the coderived category,
by the localization functor. -/
noncomputable def gradedInjectiveEquivalence :
    (gradedInjective R h).FullSubcategory ≌ CoderivedCategory R h :=
  have := isEquivalence_ι_comp_Q (R := R) (h := h) hn
  ((gradedInjective R h).ι ⋙ Q R h).asEquivalence

/-- The functor of `gradedInjectiveEquivalence` is the localization functor. -/
@[simp]
theorem gradedInjectiveEquivalence_functor :
    (gradedInjectiveEquivalence R h hn).functor = (gradedInjective R h).ι ⋙ Q R h :=
  (rfl)

end FiniteInjectiveDimension

end CoderivedCategory

end TauCeti.CurvedDGRightModuleCat
