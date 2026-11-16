/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Limits.FinallySmall
public import TauCeti.CategoryTheory.Sites.Point.Category

/-!
# Fibres and left exactness of pullback sheaves

Let `F : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, let `Φ` be a point of
`(D, K)`, and let `Ψ` be a point of `(C, J)` equipped with a natural isomorphism
`e : F ⋙ Φ.fiber ≅ Ψ.fiber`.

* **Skyscraper and stalk comparison**: pushing forward skyscraper sheaves at `Φ` along `F` produces
  skyscraper sheaves at `Ψ` (`Point.skyscraperSheafFunctorCompSheafPushforwardContinuousIso`), so
  taking mates identifies the stalk of a pullback sheaf `F^* G` at `Φ` with the stalk of `G` at `Ψ`
  (`Point.sheafPullbackCompSheafFiberIso`), without assuming `RepresentablyFlat F` or
  `CoverPreserving J K F`. Its action on germs is recorded by
  `Point.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app` and
  `Point.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app`.
* **Inverse image point**: when `F` is representably flat and cover-preserving,
  `(F ⋙ Φ.fiber).Elements` inherits initial smallness from `Ψ` via `initiallySmall_elements_of_iso`,
  yielding `Φ.comap F hF ≅ Ψ` (`Point.comapIsoOfFiberIso`) and identifying
  `sheafPullbackCompSheafFiberIso` with `sheafFiberComapIso` composed with `sheafFiberIso`.
* **Left exactness of sheaf pullback**: if a family of points `Φ i` of `(D, K)` has fibre functors
  in `A` that jointly reflect isomorphisms and each `F ⋙ (Φ i).fiber` is isomorphic to `(Ψ i).fiber`
  for a point `Ψ i` of `(C, J)`, and `A` satisfies `AB5OfSize.{w, w}`, then `F.sheafPullback A J K`
  preserves finite limits
  (`Functor.preservesFiniteLimits_sheafPullback_of_jointlyReflectIsomorphisms`).

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §3.2 and §6.2.
-/

public section

universe w

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace GrothendieckTopology.Point

section Comap

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (Φ : Point.{w} K) (F : C ⥤ D) {Ψ : Point.{w} J}

/-- Given a continuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`, points `Φ` of
`(D, K)` and `Ψ` of `(C, J)`, and a natural isomorphism `e : F ⋙ Φ.fiber ≅ Ψ.fiber`, pushing
forward skyscraper sheaves at `Φ` along `F` yields skyscraper sheaves at `Ψ`. -/
noncomputable def skyscraperSheafFunctorCompSheafPushforwardContinuousIso
    (e : F ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [HasProducts.{w} A]
    [F.IsContinuous J K] :
    Φ.skyscraperSheafFunctor ⋙ F.sheafPushforwardContinuous A J K ≅
      Ψ.skyscraperSheafFunctor :=
  NatIso.ofComponents
    (fun M ↦
      let α := Functor.isoWhiskerRight (NatIso.op e.symm) (piConst.obj M)
      { hom := ⟨α.hom⟩
        inv := ⟨α.inv⟩
        hom_inv_id := by ext : 1; exact α.hom_inv_id
        inv_hom_id := by ext : 1; exact α.inv_hom_id })
    (fun {M N} f ↦ by
      ext X
      exact ((piConst.map f).naturality (e.inv.app X.unop).op).symm)

@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π
    (e : F ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [HasProducts.{w} A]
    [F.IsContinuous J K] (M : A) (X : C) (y : Ψ.fiber.obj X) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) y =
      Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) (e.inv.app X y) :=
  (Pi.map'_comp_π _ _ y).trans (Category.comp_id _)

@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π_assoc
    (e : F ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [HasProducts.{w} A]
    [F.IsContinuous J K] (M : A) (X : C) (y : Ψ.fiber.obj X) {Z : A} (h : M ⟶ Z) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) y ≫ h =
      Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) (e.inv.app X y) ≫ h :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ h)
    (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π F e A M X y))

@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_inv_app_hom_app_π
    (e : F ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [HasProducts.{w} A]
    [F.IsContinuous J K] (M : A) (X : C) (x : Φ.fiber.obj (F.obj X)) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).inv.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) x =
      Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) (e.hom.app X x) :=
  (Pi.map'_comp_π _ _ x).trans (Category.comp_id _)

@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_inv_app_hom_app_π_assoc
    (e : F ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [HasProducts.{w} A]
    [F.IsContinuous J K] (M : A) (X : C) (x : Φ.fiber.obj (F.obj X)) {Z : A} (h : M ⟶ Z) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).inv.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) x ≫ h =
      Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) (e.hom.app X x) ≫ h :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ h)
    (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_inv_app_hom_app_π F e A M X x))

/-- When `F : (C, J) ⥤ (D, K)` is continuous and `e : F ⋙ Φ.fiber ≅ Ψ.fiber`, taking the stalk at
`Φ` after sheaf pullback along `F` is naturally isomorphic to taking the stalk at `Ψ`. -/
noncomputable def sheafPullbackCompSheafFiberIso (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber :=
  ((conjugateIsoEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    Ψ.skyscraperSheafAdjunction).symm
      (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A)).symm

@[simp]
lemma conjugateEquiv_sheafPullbackCompSheafFiberIso_inv (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
      Ψ.skyscraperSheafAdjunction (Φ.sheafPullbackCompSheafFiberIso F e A).inv =
      (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom := by
  simp [sheafPullbackCompSheafFiberIso]

/-- Under the inverse of `sheafPullbackCompSheafFiberIso`, the germ at `Ψ` of a section of `G` over
`X` maps to the germ at `Φ` of its pullback along the adjunction unit. -/
@[simp]
lemma toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) (X : C) (y : Ψ.fiber.obj X) :
    Ψ.toPresheafFiber X y G.obj ≫ (Φ.sheafPullbackCompSheafFiberIso F e A).inv.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) (e.inv.app X y) ((F.sheafPullback A J K).obj G).obj := by
  have h := unit_conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp
    Φ.skyscraperSheafAdjunction) Ψ.skyscraperSheafAdjunction
    (Φ.sheafPullbackCompSheafFiberIso F e A).inv G
  rw [conjugateEquiv_sheafPullbackCompSheafFiberIso_inv] at h
  let α : Ψ.presheafFiber.obj G.obj ⟶ (F.sheafPullback A J K ⋙ Φ.sheafFiber).obj G :=
    (Φ.sheafPullbackCompSheafFiberIso F e A).inv.app G
  have hrhs : (Ψ.skyscraperSheafAdjunction.unit.app G ≫
      Ψ.skyscraperSheafFunctor.map ((Φ.sheafPullbackCompSheafFiberIso F e A).inv.app G)).hom =
      Ψ.skyscraperPresheafHomEquiv α :=
    (congrArg (·.hom) (Ψ.skyscraperSheafAdjunction.homEquiv_unit G _ α).symm).trans
      (Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom α)
  let idΦ : Φ.presheafFiber.obj ((F.sheafPullback A J K).obj G).obj ⟶
      (F.sheafPullback A J K ⋙ Φ.sheafFiber).obj G := 𝟙 _
  have hlhs : (Φ.skyscraperSheafAdjunction.unit.app ((F.sheafPullback A J K).obj G)).hom =
      Φ.skyscraperPresheafHomEquiv idΦ :=
    (congrArg (fun (f : (F.sheafPullback A J K).obj G ⟶ _) ↦ f.hom)
      (Φ.skyscraperSheafAdjunction.homEquiv_id ((F.sheafPullback A J K).obj G)).symm).trans
      (Φ.skyscraperSheafAdjunction_homEquiv_apply_hom idΦ)
  have h1 : (Ψ.skyscraperPresheafHomEquiv α).app (op X) ≫ Pi.π _ y =
      (((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction).unit.app G ≫
        (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom.app _).hom.app
          (op X) ≫ Pi.π _ y :=
    congrArg (fun (f : G.obj ⟶ _) ↦ f.app (op X) ≫ Pi.π _ y)
      (hrhs.symm.trans (congrArg (·.hom) h.symm))
  have h2 : (((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction).unit.app G ≫
        (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom.app _).hom.app
          (op X) ≫ Pi.π _ y =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        (Φ.skyscraperPresheafHomEquiv idΦ).app (op (F.obj X)) ≫ Pi.π _ (e.inv.app X y) := by
    simp only [Adjunction.comp_unit_app]
    refine (Category.assoc _ _ _).trans ?_
    have hπ :=
      Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π F e A
        ((F.sheafPullback A J K ⋙ Φ.sheafFiber).obj G) X y
    refine (congrArg (_ ≫ ·) hπ).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun (f : ((F.sheafPullback A J K).obj G).obj ⟶
        Φ.skyscraperPresheaf ((F.sheafPullback A J K ⋙ Φ.sheafFiber).obj G)) ↦
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        f.app (op (F.obj X)) ≫ Pi.π _ (e.inv.app X y)) hlhs
  exact (Ψ.skyscraperPresheafHomEquiv_app_π α X y).symm.trans
    (h1.trans (h2.trans (congrArg (_ ≫ ·)
      ((Φ.skyscraperPresheafHomEquiv_app_π idΦ (F.obj X) (e.inv.app X y)).trans
        (Category.comp_id _)))))

@[simp]
lemma toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app_assoc (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) (X : C) (y : Ψ.fiber.obj X) {Z : A}
    (h : Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G) ⟶ Z) :
    Ψ.toPresheafFiber X y G.obj ≫ (Φ.sheafPullbackCompSheafFiberIso F e A).inv.app G ≫ h =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) (e.inv.app X y) ((F.sheafPullback A J K).obj G).obj ≫ h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ h)
      (Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app F e A G X y)).trans
      (Category.assoc _ _ _))

/-- Under `sheafPullbackCompSheafFiberIso`, the germ at `Φ` of the pullback of a section of `G`
over `X` along the adjunction unit maps to its germ at `Ψ`. -/
@[simp]
lemma unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) (X : C) (x : Φ.fiber.obj (F.obj X)) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj ≫
          (Φ.sheafPullbackCompSheafFiberIso F e A).hom.app G =
      Ψ.toPresheafFiber X (e.hom.app X x) G.obj := by
  have h := Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app F e A G X (e.hom.app X x)
  have hx : e.inv.app X (e.hom.app X x) = x := by simp
  rw [hx] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) ((Φ.sheafPullbackCompSheafFiberIso F e A).inv_hom_id_app G)).trans
          (Category.comp_id _))))

@[simp]
lemma unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app_assoc
    (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) (X : C) (x : Φ.fiber.obj (F.obj X)) {Z : A} (h : Ψ.sheafFiber.obj G ⟶ Z) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj ≫
          (Φ.sheafPullbackCompSheafFiberIso F e A).hom.app G ≫ h =
      Ψ.toPresheafFiber X (e.hom.app X x) G.obj ≫ h :=
  (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ h)
      (Φ.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app F e A G X x)))

variable [RepresentablyFlat F] (hF : CoverPreserving J K F)

/-- When `F ⋙ Φ.fiber ≅ Ψ.fiber`, the inverse image point `Φ.comap F hF` is isomorphic to `Ψ`. -/
def comapIsoOfFiberIso (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    letI := initiallySmall_elements_of_iso.{w} e
    Φ.comap F hF ≅ Ψ :=
  letI := initiallySmall_elements_of_iso.{w} e
  isoMk e.symm

@[simp]
lemma comapIsoOfFiberIso_hom_hom (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    let := initiallySmall_elements_of_iso.{w} e
    (comapIsoOfFiberIso Φ F hF e).hom.hom = e.inv :=
  letI := initiallySmall_elements_of_iso.{w} e
  isoMk_hom_hom (Φ₁ := Φ.comap F hF) (Φ₂ := Ψ) e.symm

@[simp]
lemma comapIsoOfFiberIso_inv_hom (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    let := initiallySmall_elements_of_iso.{w} e
    (comapIsoOfFiberIso Φ F hF e).inv.hom = e.hom :=
  letI := initiallySmall_elements_of_iso.{w} e
  isoMk_inv_hom (Φ₁ := Φ.comap F hF) (Φ₂ := Ψ) e.symm

/-- When `F` is representably flat and cover-preserving, `sheafPullbackCompSheafFiberIso` agrees
with Mathlib's `sheafFiberComapIso` composed with `sheafFiberIso (comapIsoOfFiberIso ...)`. -/
lemma sheafPullbackCompSheafFiberIso_eq_sheafFiberComapIso (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    let := initiallySmall_elements_of_iso.{w} e
    Φ.sheafPullbackCompSheafFiberIso F e A =
      (Φ.sheafFiberComapIso F hF A).symm ≪≫ sheafFiberIso (Φ.comapIsoOfFiberIso F hF e) A := by
  let := initiallySmall_elements_of_iso.{w} e
  let e₀ : F ⋙ Φ.fiber ≅ (Φ.comap F hF).fiber := Iso.refl _
  have hrefl :
      Φ.sheafPullbackCompSheafFiberIso F (Ψ := Φ.comap F hF) e₀ A =
        (Φ.sheafFiberComapIso F hF A).symm := by
    apply Iso.symm_eq_iff.mp
    apply Iso.ext
    apply (conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
      (Φ.comap F hF).skyscraperSheafAdjunction).injective
    rw [Iso.symm_hom, conjugateEquiv_sheafPullbackCompSheafFiberIso_inv]
    have hcomap :
        conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
          (Φ.comap F hF).skyscraperSheafAdjunction (Φ.sheafFiberComapIso F hF A).hom =
          (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom := by
      simp [sheafFiberComapIso]
    rw [Iso.symm_hom, Iso.symm_inv, hcomap]
    ext M X
    apply Pi.hom_ext
    intro x
    exact (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π F
      (Ψ := Φ.comap F hF) e₀ A M X.unop x).trans (Category.id_comp _).symm
  apply Iso.symm_eq_iff.mp
  apply Iso.ext
  ext G : 2
  apply Ψ.presheafFiber_hom_ext
  intro X y
  refine (Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app F e A G X y).trans ?_
  have hcomp :
      Ψ.toPresheafFiber X y G.obj ≫
          ((Φ.sheafFiberComapIso F hF A).symm ≪≫
            sheafFiberIso (Φ.comapIsoOfFiberIso F hF e) A).inv.app G =
        (Φ.comap F hF).toPresheafFiber X (e.inv.app X y) G.obj ≫
          (Φ.sheafFiberComapIso F hF A).hom.app G := by
    simp only [Iso.trans_inv, Iso.symm_inv, sheafFiberIso_inv]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine congrArg (· ≫ _) ?_
    simp only [Functor.whiskerLeft_app, Hom.presheafFiber_app, comapIsoOfFiberIso_hom_hom]
    exact Ψ.toPresheafFiber_presheafFiberDesc _ _ X y
  refine Eq.trans ?_ hcomp.symm
  have h0 := Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app F (Ψ := Φ.comap F hF)
    e₀ A G X (e.inv.app X y)
  rw [hrefl] at h0
  exact h0.symm

end Comap

end GrothendieckTopology.Point

namespace Functor

/-- **Left exactness of sheaf pullback from conservative points.** Let `F : (C, J) ⥤ (D, K)` be a
continuous functor admitting a sheaf pullback into an `AB5` category `A`. If `Φ : ι → Point.{w} K`
is a family of points whose sheaf fibre functors in `A` jointly reflect isomorphisms, and each
`F ⋙ (Φ i).fiber` is isomorphic to `(Ψ i).fiber` for a point `Ψ i` of `(C, J)`, then
`F.sheafPullback A J K` preserves finite limits. -/
lemma preservesFiniteLimits_sheafPullback_of_jointlyReflectIsomorphisms
    {C D : Type*} [Category* C] [Category* D] [LocallySmall.{w} C] [LocallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {A : Type*} [Category* A] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [HasFiniteLimits A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A] [AB5OfSize.{w, w} A]
    {ι : Type*} (Φ : ι → GrothendieckTopology.Point.{w} K)
    (Ψ : ι → GrothendieckTopology.Point.{w} J)
    (e : ∀ i, F ⋙ (Φ i).fiber ≅ (Ψ i).fiber)
    (hΦ : JointlyReflectIsomorphisms fun i ↦ (Φ i).sheafFiber (A := A)) :
    PreservesFiniteLimits (F.sheafPullback A J K) where
  preservesFiniteLimits _ _ _ := ⟨fun {_} ↦
    { preserves {_} hc :=
        ⟨hΦ.jointlyReflectsLimit fun i ↦
          IsLimit.mapConeEquiv ((Φ i).sheafPullbackCompSheafFiberIso F (e i) A).symm
            (isLimitOfPreserves (Ψ i).sheafFiber hc)⟩ }⟩

end Functor

end CategoryTheory
