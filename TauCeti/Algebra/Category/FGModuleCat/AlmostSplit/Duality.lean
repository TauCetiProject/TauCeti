/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.Sequence
public import TauCeti.CategoryTheory.Exact.YonedaExt.AuslanderReitenDuality
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Module.LinearMap.FiniteLength
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.Exact.YonedaExt.Projective

/-!
# Auslander–Reiten duality on finitely generated modules over Artin algebras

For an Artin algebra `A` over a commutative Artinian ring `R`, the category of finitely generated
left `A`-modules has Auslander–Reiten duality for its abelian exact structure. The coefficient
module can be an injective hull of `R ⧸ J(R)`. The specialization of
`ExactStructure.nonempty_auslanderReitenDuality` uses almost-split sequences and
`FGModuleCat.isFiniteLength_ext1_of_isFiniteLength`, which follows from projective presentations
in this category.

For a duality with finite injective coefficients `Q` satisfying
`length_R Hom_R(R/𝔪, Q) = 1` for every maximal ideal `𝔪`, its translate on an indecomposable
nonprojective module agrees in the injectively stable category with the dual of the minimal
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

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

namespace FGModuleCat

universe u v w x

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- Over an algebra `A` that is left Noetherian, Yoneda `Ext¹(Z, W)` in `FGModuleCat A` has
finite length over the base ring if `W` does. -/
theorem isFiniteLength_ext1_of_isFiniteLength [IsNoetherianRing A] [Small.{w} A]
    (Z W : FGModuleCat.{w} A) (hW : IsFiniteLength R W.obj) :
    IsFiniteLength R ((ExactStructure.abelian (FGModuleCat.{w} A)).Ext1 Z W) :=
  ExactStructure.abelian_enoughProjectives.isFiniteLength_ext1 R Z W fun K ↦
    (InducedCategory.homLinearEquiv (R := R) ≪≫ₗ ModuleCat.homLinearEquiv).symm.isFiniteLength
      (isFiniteLength_linearMap K.obj W.obj hW)

end FGModuleCat

namespace TauCeti.FGModuleCat

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
    obtain ⟨S, hS, ⟨e⟩⟩ := _root_.FGModuleCat.exists_isAlmostSplit R Z hZ
      ((ExactStructure.abelian_isProjective_iff Z).not.mp hP)
    obtain ⟨i, p, h, hS', -, -⟩ := (𝟭 (FGModuleCat.{w} A)).exists_isAlmostSplit_of_obj_iso
      hS (Iso.refl S.X₁) (Iso.refl S.X₂) e.symm
    exact ⟨S.X₁, ⟨S.X₂, i, p, h, (ExactStructure.abelian_conflation _).mpr hS'.shortExact⟩, hS'⟩
  · intro T hT hI
    obtain ⟨S, hS, ⟨e⟩⟩ := _root_.FGModuleCat.exists_isAlmostSplit_of_not_injective R T hT
      ((ExactStructure.abelian_isInjective_iff T).not.mp hI)
    obtain ⟨i, p, h, hS', -, -⟩ := (𝟭 (FGModuleCat.{w} A)).exists_isAlmostSplit_of_obj_iso
      hS e.symm (Iso.refl S.X₂) (Iso.refl S.X₃)
    exact ⟨S.X₃, ⟨S.X₂, i, p, h, (ExactStructure.abelian_conflation _).mpr hS'.shortExact⟩, hS'⟩

variable {Q : Type u} [AddCommGroup Q] [Module R Q] [Module.Injective R Q] [Module.Finite R Q]

/-- On an indecomposable nonprojective module, an Auslander–Reiten duality with finite injective
coefficients `Q` satisfying `length_R Hom_R(R/𝔪, Q) = 1` for every maximal ideal `𝔪` has
translate isomorphic in the injectively stable category to the minimal transpose dualized with
the same `Q`. -/
theorem nonempty_iso_quotient_obj_arTranslate_of_auslanderReitenDuality :
    letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
    ∀ (D : (ExactStructure.abelian (FGModuleCat.{max u v w} A)).AuslanderReitenDuality R Q),
    (∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1) →
    ∀ {Z : FGModuleCat.{max u v w} A}, Indecomposable Z → ¬ Projective Z →
    let E := ExactStructure.abelian (FGModuleCat.{max u v w} A)
    Nonempty (E.injectivelyTrivialIdeal.quotientFunctor.obj (_root_.FGModuleCat.arTranslate R Q Z) ≅
      D.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) := by
  have : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  intro D hQ Z hZ hP
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₃⟩⟩ :=
    _root_.FGModuleCat.exists_isAlmostSplit_arTranslate R Q hQ Z hZ hP
  let E := ExactStructure.abelian (FGModuleCat.{max u v w} A)
  let e : E.Extension S.X₃ S.X₁ :=
    ⟨S.X₂, S.f, S.g, S.zero, (ExactStructure.abelian_conflation S).mpr hS.shortExact⟩
  have hfin (W : FGModuleCat.{max u v w} A) : IsFiniteLength R (E.Ext1 S.X₃ W) :=
    S.X₃.isFiniteLength_ext1_of_isFiniteLength W (isFiniteLength_of_finite_trans R A W.obj)
  exact ⟨E.injectivelyTrivialIdeal.quotientFunctor.mapIso e₁.symm ≪≫
    D.isoTranslateOfIsAlmostSplit hQ hfin e hS ≪≫
    D.functor.mapIso (E.projectivelyTrivialIdeal.quotientFunctor.mapIso e₃)⟩

end TauCeti.FGModuleCat
