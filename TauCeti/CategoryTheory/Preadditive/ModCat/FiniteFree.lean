/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Finite free modules over preadditive categories

Finite free modules are finite coproducts of representables up to isomorphism. They
are projective, and their cokernels give the finitely presented modules. These
presentations allow arguments by generators and relations in the additive functor
category itself.
-/

public section

universe v u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

private abbrev ι (C : Type u) [Category.{v} C] [Preadditive C] :=
  (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι

private noncomputable def yonedaCoproductIso {n : ℕ} (Y : Fin n → C) :
    (∐ fun j ↦ preadditiveYoneda.obj (Y j)) ≅ (ι C).obj (∐ (yoneda C).obj ∘ Y) :=
  asIso (sigmaComparison (ι C) ((yoneda C).obj ∘ Y))

variable (C) in
/-- A finite free module is isomorphic to a finite coproduct of representable modules. -/
def isFiniteFree : ObjectProperty (ModCat.{v} C) := fun F ↦ IsFiniteSumOfRepresentables F.obj

/-- A finite free module admits an isomorphism to a coproduct indexed by some `Fin n`. -/
theorem isFiniteFree_def {F : ModCat.{v} C} :
    isFiniteFree C F ↔
      ∃ (n : ℕ) (Y : Fin n → C), Nonempty (F ≅ ∐ fun j ↦ (yoneda C).obj (Y j)) := by
  rw [isFiniteFree, isFiniteSumOfRepresentables_def]
  constructor
  · rintro ⟨n, Y, ⟨e⟩⟩
    exact ⟨n, Y, ⟨(ι C).preimageIso (e ≪≫ yonedaCoproductIso Y)⟩⟩
  · rintro ⟨n, Y, ⟨e⟩⟩
    exact ⟨n, Y, ⟨(ι C).mapIso e ≪≫ (yonedaCoproductIso Y).symm⟩⟩

/-- Finite free modules are represented up to isomorphism by finite families in a small
model of the source category. -/
instance [EssentiallySmall.{v} C] :
    ObjectProperty.EssentiallySmall.{v} (isFiniteFree C) := by
  let e := equivSmallModel.{v} C
  let P := ObjectProperty.ofObj fun X : Σ n : ℕ, Fin n → SmallModel.{v} C ↦
    ∐ fun j ↦ (yoneda C).obj (e.inverse.obj (X.2 j))
  refine ⟨P, inferInstance, fun F hF ↦ ?_⟩
  obtain ⟨n, X, ⟨hX⟩⟩ := isFiniteFree_def.mp hF
  refine ⟨_, ⟨⟨n, e.functor.obj ∘ X⟩⟩, ⟨hX ≪≫ ?_⟩⟩
  exact Sigma.mapIso fun j ↦ (yoneda C).mapIso (e.unitIso.app (X j))

/-- Finite free modules are equivalently the finite biproducts of representable modules,
up to isomorphism. -/
theorem isFiniteFree_iff_exists_iso_biproduct {F : ModCat.{v} C} :
    isFiniteFree C F ↔
      ∃ (n : ℕ) (Y : Fin n → C), Nonempty (F ≅ ⨁ fun j ↦ (yoneda C).obj (Y j)) := by
  rw [isFiniteFree_def]
  constructor
  · rintro ⟨n, Y, ⟨e⟩⟩
    exact ⟨n, Y, ⟨e ≪≫ (biproduct.isoCoproduct ((yoneda C).obj ∘ Y)).symm⟩⟩
  · rintro ⟨n, Y, ⟨e⟩⟩
    exact ⟨n, Y, ⟨e ≪≫ biproduct.isoCoproduct ((yoneda C).obj ∘ Y)⟩⟩

instance : (isFiniteFree C).IsClosedUnderIsomorphisms where
  of_iso e h := IsFiniteSumOfRepresentables.of_iso h ((ι C).mapIso e)

/-- A finite coproduct of representable modules is finite free. -/
theorem isFiniteFree_coproduct_yoneda {n : ℕ} (Y : Fin n → C) :
    isFiniteFree C (∐ fun j ↦ (yoneda C).obj (Y j)) :=
  (isFiniteSumOfRepresentables_sigma Y).of_iso (yonedaCoproductIso Y)

/-- A finite biproduct of representable modules is finite free. -/
theorem isFiniteFree_biproduct_yoneda {n : ℕ} (Y : Fin n → C) :
    isFiniteFree C (⨁ fun j ↦ (yoneda C).obj (Y j)) :=
  isFiniteFree_iff_exists_iso_biproduct.mpr ⟨n, Y, ⟨Iso.refl _⟩⟩

/-- A representable module is finite free. -/
theorem isFiniteFree_yoneda_obj (X : C) : isFiniteFree C ((yoneda C).obj X) :=
  isFiniteSumOfRepresentables_preadditiveYoneda_obj X

/-- A choice of an element at each representing object defines a map from the sum of the
representables, taking each identity generator to the chosen element. -/
theorem exists_biproduct_desc_app_id {F : ModCat.{v} C} {m : ℕ} {Y : Fin m → C}
    (y : ∀ j, F.obj.obj (op (Y j))) :
    ∃ p : (⨁ (yoneda C).obj ∘ Y) ⟶ F, ∀ j,
      (biproduct.ι ((yoneda C).obj ∘ Y) j ≫ p).hom.app (op (Y j)) (𝟙 (Y j)) = y j := by
  have := (additiveFunctor_iff F.obj).1 F.property
  let a (j : Fin m) : (yoneda C).obj (Y j) ⟶ F := by
    let p : CategoryTheory.yoneda.obj (Y j) ⟶ F.obj ⋙ forget AddCommGrpCat :=
      yonedaEquiv.symm (y j)
    exact ObjectProperty.homMk
      { app T := AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (fun f ↦ p.app T f) (fun f g ↦ by
            -- The inverse Yoneda component evaluates the action of the arrow on `y j`.
            change F.obj.map (f + g).op (y j) = F.obj.map f.op (y j) + F.obj.map g.op (y j)
            simp only [op_add, Functor.map_add, AddCommGrpCat.hom_add_apply]) :
            (T.unop ⟶ Y j) →+ F.obj.obj T)
        naturality T U g := by
          ext (f : T.unop ⟶ Y j)
          exact p.naturality_apply g f }
  refine ⟨biproduct.desc a, fun j ↦ ?_⟩
  rw [biproduct.ι_desc]
  exact (yonedaEquiv (X := Y j) (F := F.obj ⋙ forget AddCommGrpCat)).apply_symm_apply (y j)

/-- A finite free module is projective. -/
theorem projective_of_isFiniteFree {P : ModCat.{v} C} (hP : isFiniteFree C P) :
    Projective P := by
  obtain ⟨n, Y, ⟨e⟩⟩ := isFiniteFree_def.mp hP
  have (j : Fin n) : Projective ((yoneda C).obj (Y j)) := inferInstance
  exact Projective.of_iso e.symm (Projective.of_isColimit_cofan (coproductIsCoproduct _))

/-- The underlying functor of a finite free module is finitely presented. -/
theorem isFinitelyPresentedFunctor_of_isFiniteFree {P : ModCat.{v} C} (hP : isFiniteFree C P) :
    IsFinitelyPresentedFunctor P.obj := by
  obtain ⟨n, Y, ⟨e⟩⟩ := isFiniteSumOfRepresentables_def.mp hP
  exact (isFinitelyPresentedFunctor C).prop_of_iso e.symm
    ((isFinitelyPresentedFunctor C).prop_coproduct
      fun j ↦ isFinitelyPresentedFunctor_preadditiveYoneda_obj (Y j))

/-- A module has a finitely presented underlying functor exactly when it is a cokernel of a
morphism between finite free modules. -/
theorem isFinitelyPresentedFunctor_iff_exists_finiteFree_presentation {P : ModCat.{v} C} :
    IsFinitelyPresentedFunctor P.obj ↔
      ∃ (U V : ModCat.{v} C) (_ : isFiniteFree C U) (_ : isFiniteFree C V)
        (d : U ⟶ V) (p : V ⟶ P) (h : d ≫ p = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ p h)) := by
  constructor
  · intro hP
    obtain ⟨m, n, X, Y, d, p, h, ⟨hc⟩⟩ :=
      isFinitelyPresentedFunctor_iff_exists_isColimit.mp hP
    let U := ∐ (yoneda C).obj ∘ X
    let V := ∐ (yoneda C).obj ∘ Y
    let eX := yonedaCoproductIso X
    let eY := yonedaCoproductIso Y
    let d' : U ⟶ V := (ι C).preimage (eX.inv ≫ d ≫ eY.hom)
    let p' : V ⟶ P := (ι C).preimage (eY.inv ≫ p)
    have h' : d' ≫ p' = 0 := by
      apply (ι C).map_injective
      simp only [Functor.map_comp, Functor.map_zero, d', p', Functor.map_preimage]
      simp [h]
    refine ⟨U, V, isFiniteFree_coproduct_yoneda X, isFiniteFree_coproduct_yoneda Y,
      d', p', h', ⟨?_⟩⟩
    apply isColimitOfReflects (ι C)
    refine (isColimitMapCoconeCoforkEquiv' (ι C) h').symm ?_
    exact IsCokernel.ofIso d hc _ eX eY (Iso.refl _)
      (by simp only [d', Functor.map_preimage, Iso.hom_inv_id_assoc])
      (by simp only [CokernelCofork.π_ofπ, p', Functor.map_preimage, Iso.hom_inv_id_assoc,
        Iso.refl_hom, Category.comp_id])
  · rintro ⟨U, V, hU, hV, d, p, hp, ⟨hc⟩⟩
    have := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).preservesCokernels_ι d
    exact IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork
      (isColimitCoforkMapOfIsColimit' (ι C) hp hc)
      (isFinitelyPresentedFunctor_of_isFiniteFree hU).isFinitelyGeneratedFunctor
      (isFinitelyPresentedFunctor_of_isFiniteFree hV)

end TauCeti.ModCat
