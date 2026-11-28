/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.Sequence
public import TauCeti.CategoryTheory.Exact.YonedaExt.AuslanderReitenDuality
import TauCeti.Algebra.Category.FGModuleCat.Ext.FiniteLength
import TauCeti.CategoryTheory.Exact.YonedaExt.Abelian
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Projective

/-!
# Auslander–Reiten duality on finitely generated modules over Artin algebras

For an Artin algebra `A` over a commutative Artinian ring `R`, the category of finitely generated
left `A`-modules has Auslander–Reiten duality for its abelian exact structure. The coefficient
module can be an injective hull of `R ⧸ J(R)`. The specialization of
`ExactStructure.nonempty_auslanderReitenDuality` uses almost-split sequences and
`FGModuleCat.isFiniteLength_ext1_of_isFiniteLength`, which follows from projective presentations
in this category.

For a duality with injective coefficients `Q` satisfying
`length_R Hom_R(R/𝔪, Q) = 1` for every maximal ideal `𝔪`, its translate on an indecomposable
module agrees in the injectively stable category with the dual of the minimal
transpose using the same `Q`. The comparison uses
`ExactStructure.AuslanderReitenDuality.isoTranslateOfIsAlmostSplit` and
`FGModuleCat.exists_isAlmostSplit_arTranslate` to identify both with the starting term of an
almost-split sequence.

## References

* O. Iyama, H. Nakaoka, Y. Palu, *Auslander–Reiten theory in extriangulated categories*,
  arXiv:1805.03776v3, Theorem 3.6, over a field.
* H. Enomoto, *Classifications of exact structures and Cohen–Macaulay-finite algebras*,
  arXiv:1705.02163v4, Theorem A.9, over a complete local Noetherian ring.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Theorem V.1.15, for the almost-split sequences.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti
open scoped ModuleCat.Algebra

namespace TauCeti.FGModuleCat

universe u v w x

variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

variable (R) {Q : Type x} [AddCommGroup Q] [Module R Q] [Module.Injective R Q] [Small.{x} R] in
/-- The abelian exact structure on the finitely generated left modules over an Artin algebra has
Auslander–Reiten duality with coefficients in any injective `R`-module `Q` such that
`Hom_R(R ⧸ 𝔪, Q)` has length one for every maximal ideal `𝔪` of `R`. -/
theorem nonempty_auslanderReitenDuality [Small.{w} A]
    (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1) :
    letI : IsArtinianRing A := IsArtinianRing.of_finite R A
    Nonempty ((ExactStructure.abelian (FGModuleCat.{w} A)).AuslanderReitenDuality R Q) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  refine (ExactStructure.abelian (FGModuleCat.{w} A)).nonempty_auslanderReitenDuality R Q hQ
    (fun Z W ↦ Z.isFiniteLength_ext1_of_isFiniteLength W
      (isFiniteLength_of_finite_trans R A W.obj)) ?_ ?_
  · intro Z hZ hP
    obtain ⟨X, Y, i, p, h, hS⟩ := _root_.FGModuleCat.exists_isAlmostSplit R Z hZ
      ((ExactStructure.abelian_isProjective_iff Z).not.mp hP)
    exact ⟨X, ExactStructure.Extension.ofShortExact _ hS.shortExact, hS⟩
  · intro T hT hI
    obtain ⟨Y, Z, i, p, h, hS⟩ := _root_.FGModuleCat.exists_isAlmostSplit_of_not_injective R T hT
      ((ExactStructure.abelian_isInjective_iff T).not.mp hI)
    exact ⟨Z, ExactStructure.Extension.ofShortExact _ hS.shortExact, hS⟩

variable {Q : Type u} [AddCommGroup Q] [Module R Q] [Module.Injective R Q]

/-- On an indecomposable module, an Auslander–Reiten duality with injective coefficients `Q`
satisfying `length_R Hom_R(R/𝔪, Q) = 1` for every maximal ideal `𝔪` has translate isomorphic in
the injectively stable category to the minimal transpose dualized with the same `Q`. For a
projective module both sides are zero objects. -/
theorem nonempty_iso_quotient_obj_arTranslate_of_auslanderReitenDuality :
    letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
    ∀ (D : (ExactStructure.abelian (FGModuleCat.{max u v w} A)).AuslanderReitenDuality R Q)
      (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1),
    ∀ {Z : FGModuleCat.{max u v w} A}, Indecomposable Z →
    letI : Module.Finite R Q := finite_of_forall_isMaximal hQ
    let E := ExactStructure.abelian (FGModuleCat.{max u v w} A)
    Nonempty (E.injectivelyTrivialIdeal.quotientFunctor.obj (_root_.FGModuleCat.arTranslate R Q Z) ≅
      D.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) := by
  have : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  intro D hQ Z hZ
  have : Module.Finite R Q := finite_of_forall_isMaximal hQ
  by_cases hP : Projective Z
  · -- Both sides vanish: `D Tr` of a projective module is zero, and a projective object is zero
    -- in the projectively stable category.
    have hτ : IsZero (_root_.FGModuleCat.arTranslate R Q Z) := by
      rw [IsZero.iff_id_eq_zero]
      apply (ObjectProperty.ι _).map_injective
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
      have h₀ : IsZero (ModuleCat.arTranslate R Q Z.obj) :=
        (ModuleCat.isZero_arTranslate_iff (nontrivial_linearMap_of_isMaximal hQ) Z.obj).mpr
          ((_root_.FGModuleCat.projective_obj_iff Z).mpr hP)
      rw [← _root_.FGModuleCat.arTranslate_obj R Q Z] at h₀
      exact (IsZero.iff_id_eq_zero _).mp h₀
    have := D.isEquivalence
    let E := ExactStructure.abelian (FGModuleCat.{max u v w} A)
    exact ⟨(E.injectivelyTrivialIdeal.quotientFunctor.map_isZero hτ).iso
      (D.functor.map_isZero ((MorphismIdeal.isZero_quotientFunctor_obj_iff _ Z).mpr
        ((E.id_mem_projectivelyTrivialIdeal_iff Z).mpr
          ((ExactStructure.abelian_isProjective_iff Z).mpr hP))))⟩
  obtain ⟨Y, i, p, h, hS⟩ := _root_.FGModuleCat.exists_isAlmostSplit_arTranslate R Q hQ Z hZ hP
  let E := ExactStructure.abelian (FGModuleCat.{max u v w} A)
  have hfin (W : FGModuleCat.{max u v w} A) : IsFiniteLength R (E.Ext1 Z W) :=
    Z.isFiniteLength_ext1_of_isFiniteLength W (isFiniteLength_of_finite_trans R A W.obj)
  exact ⟨D.isoTranslateOfIsAlmostSplit hQ hfin
    (ExactStructure.Extension.ofShortExact (ShortComplex.mk i p h) hS.shortExact) hS⟩

end TauCeti.FGModuleCat
