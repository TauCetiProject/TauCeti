/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import TauCeti.Algebra.Homology.DerivedCategory.DerivedHom
public import TauCeti.Algebra.Homology.LinearHomComplex.Curry
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Resolution
public import TauCeti.Algebra.Homology.ModuleCat.KInjective
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor

/-!
# The derived tensor–Hom adjunction for modules

Let `A` be a commutative ring and `L` an object of the unbounded derived category `D(A)` of
`A`-modules. For every left derived bifunctor `T` of the totalized tensor product of complexes
(one exists by `TauCeti.hasLeftDerivedFunctor₂_tensor`), the functor `K ↦ T(K, L) = K ⊗^L_A L` is
left adjoint to the derived Hom functor `M ↦ RHom_A(L, M)` of `TauCeti.derivedHom`:

`Hom_{D(A)}(K ⊗^L_A L, M) ≃ Hom_{D(A)}(K, RHom_A(L, M))`

naturally in `K` and `M` (`TauCeti.derivedTensorHomAdj`). No boundedness or perfectness of `K`,
`L` or `M` is assumed.

The construction follows the Stacks Project. Represent `L` by a K-flat complex `P`. Currying is an
adjunction `- ⊗ P ⊣ Hom(P, -)` on the homotopy category of complexes
(`TauCeti.tensorRightLinearHomComplexHomotopyAdjunction`). Composing it with the adjunction
`DerivedCategory.Qh ⊣ TauCeti.kInjectiveReplacement` gives an adjunction between the homotopy
category and `D(A)`. Since `P` is K-flat, `- ⊗ P` computes `T(-, P)`, and since `Hom(P, I)` is
K-injective for K-injective `I`, the right adjoint takes values in the image of the fully faithful
functor `TauCeti.kInjectiveReplacement`. Restricting along that functor gives the model adjunction
`TauCeti.derivedTensorHomAdjOfIsKFlat`. Finally, when `P` maps quasi-isomorphically to the
K-injective replacement of `L`, precomposition identifies `Hom(P, I)` with `RHom_A(L, -)`
(`TauCeti.derivedHomObjIsoOfQuasiIso`).

## Main definitions

* `TauCeti.derivedTensorHomAdjOfIsKFlat`: for a K-flat complex `P`, the adjunction between
  `T(-, P)` and the Hom complex out of `P` into K-injective replacements.
* `TauCeti.derivedTensorHomAdj`: the derived tensor–Hom adjunction `T(-, L) ⊣ RHom_A(L, -)`.

## Main results

* `TauCeti.nonempty_derivedTensorHomAdj`: the functor `T(-, L)` is left adjoint to
  `RHom_A(L, -)`.

## References

* [Stacks Project, Lemma 15.73.1 (Tag 0A5Y)](https://stacks.math.columbia.edu/tag/0A5Y) and
  [Stacks Project, Lemma 15.75.1 (Tag 0A65)](https://stacks.math.columbia.edu/tag/0A65).
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory DerivedCategory Opposite

universe w u

namespace TauCeti

variable {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  (T : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} A))
  (α : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj DerivedCategory.Q).obj T ⟶
    curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} A)))
  [T.IsLeftDerivedFunctor₂ α (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]

include α

/-- For a K-flat complex `P`, the derived tensor product `T(-, P)` on the homotopy category is
the totalized tensor product with `P`. -/
private def qhCompFlipObjIsoOfIsKFlat (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKFlat] :
    Qh ⋙ T.flip.obj (Q.obj P) ≅
      ((curriedTensor (ModuleCat.{u} A)).map₂HomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj
        ((HomotopyCategory.quotient _ _).obj P) ⋙ Qh :=
  CategoryTheory.Quotient.natIsoLift _ <| NatIso.ofComponents
    (F := HomotopyCategory.quotient _ _ ⋙ Qh ⋙ T.flip.obj (Q.obj P))
    (G := HomotopyCategory.quotient _ _ ⋙
      ((curriedTensor (ModuleCat.{u} A)).map₂HomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj
        ((HomotopyCategory.quotient _ _).obj P) ⋙ Qh)
    (fun K ↦ (T.flip.obj (Q.obj P)).mapIso ((quotientCompQhIso _).app K) ≪≫
      asIso ((α.app K).app P) ≪≫ ((quotientCompQhIso _).app (K ⊗ P)).symm)
    (fun {K K'} f ↦ by
      have h₁ := congrArg (fun g ↦ (T.map g).app (Q.obj P))
        ((quotientCompQhIso (ModuleCat.{u} A)).hom.naturality f)
      have h₂ := congrArg (fun τ ↦ τ.app P) (α.naturality f)
      have h₃ := (quotientCompQhIso (ModuleCat.{u} A)).inv.naturality (f ▷ P)
      dsimp at h₁ h₂ h₃
      simp only [Functor.map_comp, NatTrans.comp_app] at h₁
      have key : (T.map (Qh.map ((HomotopyCategory.quotient _ _).map f))).app (Q.obj P) ≫
          (T.map ((quotientCompQhIso _).hom.app K')).app (Q.obj P) ≫ (α.app K').app P ≫
            (quotientCompQhIso _).inv.app (K' ⊗ P) =
          ((T.map ((quotientCompQhIso _).hom.app K)).app (Q.obj P) ≫ (α.app K).app P ≫
            (quotientCompQhIso _).inv.app (K ⊗ P)) ≫
              Qh.map ((HomotopyCategory.quotient _ _).map (f ▷ P)) := by
        rw [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc, Category.assoc]
      -- The goal is `key` with the components of the composite isomorphisms written out, and with
      -- the homotopy-category tensor of `f` and `P` written as the class of `f ▷ P`, which is its
      -- value by `Functor.map₂HomotopyCategory_map_app`.
      exact key)

/-- **Tensor–Hom adjunction on K-flat models.** For a K-flat complex `P`, the derived tensor
product `T(-, P)` is left adjoint to the functor sending `M` to the Hom complex out of `P` into
the K-injective replacement of `M`. -/
def derivedTensorHomAdjOfIsKFlat (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKFlat] :
    T.flip.obj (Q.obj P) ⊣ kInjectiveReplacement (ModuleCat.{u} A) ⋙
      (linearHomComplexHomotopyFunctor A (ModuleCat.{u} A)).obj
        (op ((HomotopyCategory.quotient _ _).obj P)) ⋙ Qh :=
  ((tensorRightLinearHomComplexHomotopyAdjunction P).comp
    (kInjectiveReplacementAdjunction _)).restrictFullyFaithful
    (fullyFaithfulKInjectiveReplacement _) (Functor.FullyFaithful.id _)
    (Functor.isoWhiskerLeft _ (qhCompFlipObjIsoOfIsKFlat T α P).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (kInjectiveReplacementAdjunction _).counit) _ ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    -- The Hom complex out of the K-flat `P` into a K-injective complex is K-injective, so the
    -- unit of `Qh ⊣ kInjectiveReplacement` is an isomorphism on it.
    (NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ _
      ((kInjectiveReplacementAdjunction _).isIso_unit_app_iff_mem_essImage.2
        ((mem_essImage_kInjectiveReplacement_iff _).2
          (isKInjective_linearHomComplex (L := P) ((kInjectiveReplacement _).obj M).as))))
      (fun _ ↦ (kInjectiveReplacementAdjunction _).unit.naturality _))

/-- **The derived tensor–Hom adjunction.** For every left derived bifunctor `T` of the tensor
product of complexes of `A`-modules and every `L` in `D(A)`, the functor `K ↦ T(K, L)` is left
adjoint to the derived Hom functor `M ↦ RHom_A(L, M)`. It is built from a chosen K-flat complex
with a quasi-isomorphism to the K-injective replacement of `L`. -/
def derivedTensorHomAdj (L : DerivedCategory (ModuleCat.{u} A)) :
    T.flip.obj L ⊣ (derivedHom A (ModuleCat.{u} A)).obj (op L) :=
  let h := CochainComplex.exists_quasiIso_isKFlat_moduleCat ((kInjectiveReplacement _).obj L).as
  have : h.choose.IsKFlat := h.choose_spec.choose_spec.2
  have : QuasiIso h.choose_spec.choose := h.choose_spec.choose_spec.1
  ((derivedTensorHomAdjOfIsKFlat T α h.choose).ofNatIsoLeft
    (T.flip.mapIso (((asIso (kInjectiveReplacementAdjunction _).counit).app L).symm ≪≫
      (quotientCompQhIso _).app _ ≪≫ (asIso (Q.map h.choose_spec.choose)).symm)).symm).ofNatIsoRight
    (derivedHomObjIsoOfQuasiIso A L h.choose_spec.choose).symm

/-- **The derived tensor–Hom adjunction.** For every left derived bifunctor `T` of the tensor
product of complexes of `A`-modules and every `L` in `D(A)`, the functor `K ↦ T(K, L)` is left
adjoint to `M ↦ RHom_A(L, M)`, so that `Hom(K ⊗^L L, M) ≃ Hom(K, RHom_A(L, M))` naturally in `K`
and `M`. No boundedness or perfectness of `L` is assumed. -/
theorem nonempty_derivedTensorHomAdj (L : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty (T.flip.obj L ⊣ (derivedHom A (ModuleCat.{u} A)).obj (op L)) :=
  ⟨derivedTensorHomAdj T α L⟩

end TauCeti
