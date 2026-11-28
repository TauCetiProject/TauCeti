/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution.Sigma

/-!
# Left derived functors commute with coproducts

Let `C` and `D` be abelian categories in which coproducts indexed by `J` exist and are exact, and
let `F : C ⥤ D` be an additive functor preserving them. Then every left derived functor
`F.leftDerived n` preserves coproducts indexed by `J`
(`CategoryTheory.Functor.preservesColimitsOfShape_leftDerived`).

The proof computes on resolutions. The coproduct of projective resolutions `Pⱼ` of objects `Xⱼ`
is a projective resolution of `∐ Xⱼ` (`CategoryTheory.ProjectiveResolution.sigma`). Then
`Lₙ F (∐ Xⱼ)` is the `n`-th homology of `F (∐ Pⱼ) ≅ ∐ F Pⱼ`, and homology commutes with exact
coproducts (`TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits

universe w

variable {C : Type*} [Category* C] [Abelian C] {J : Type w} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C]
  {D : Type*} [Category* D] [Abelian D] [HasColimitsOfShape (Discrete J) D]
  [HasExactColimitsOfShape (Discrete J) D] [HasProjectiveResolutions C] (F : C ⥤ D) [F.Additive]
  [PreservesColimitsOfShape (Discrete J) F]

/-- **Left derived functors commute with exact coproducts.** If coproducts indexed by `J` are
exact in `C` and `D` and preserved by the additive functor `F`, then every left derived functor
`Lₙ F` preserves them. -/
instance Functor.preservesColimitsOfShape_leftDerived (n : ℕ) :
    PreservesColimitsOfShape (Discrete J) (F.leftDerived n) := by
  suffices ∀ X : J → C, PreservesColimit (Discrete.functor X) (F.leftDerived n) from
    preservesColimitsOfShape_of_discrete _
  intro X
  let P : ∀ j, ProjectiveResolution (X j) := fun j ↦ projectiveResolution (X j)
  let Q := ProjectiveResolution.sigma P
  let H : ChainComplex C ℕ ⥤ D := F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  have : PreservesColimitsOfShape (Discrete J) (F.mapHomologicalComplex (ComplexShape.down ℕ)) :=
    inferInstance
  have : PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n) :=
    inferInstance
  have : PreservesColimitsOfShape (Discrete J) H := comp_preservesColimitsOfShape _ _
  let e : ∀ j, (F.leftDerived n).obj (X j) ≅ H.obj (P j).complex :=
    fun j ↦ (P j).isoLeftDerivedObj F n
  let eQ : (F.leftDerived n).obj (∐ X) ≅ H.obj (∐ fun j ↦ (P j).complex) :=
    Q.isoLeftDerivedObj F n
  have hcomp : sigmaComparison (F.leftDerived n) X =
      Limits.Sigma.map (fun j ↦ (e j).hom) ≫
        sigmaComparison H (fun j ↦ (P j).complex) ≫ eQ.inv := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [ι_comp_sigmaComparison, Sigma.ι_map_assoc, ι_comp_sigmaComparison_assoc]
    exact F.leftDerived_map_eq n (Sigma.ι X j) (P := P j) (Q := Q)
      (Sigma.ι (fun j ↦ (P j).complex) j) (ProjectiveResolution.ι_sigma_π P j)
  have : IsIso (sigmaComparison (F.leftDerived n) X) := by
    rw [hcomp]
    infer_instance
  exact PreservesCoproduct.of_iso_comparison _ _

end CategoryTheory
