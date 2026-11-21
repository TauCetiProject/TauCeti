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

For a continuous functor `F : (C, J) ⥤ (D, K)` and points `Φ` of `(D, K)` and `Ψ` of `(C, J)` with
`e : F ⋙ Φ.fiber ≅ Ψ.fiber`:

* `Point.skyscraperSheafFunctorCompSheafPushforwardContinuousIso` and
  `Point.sheafPullbackCompSheafFiberIso` identify stalks of `F^* G` at `Φ` with stalks of `G` at
  `Ψ` (with action on germs `Point.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app`,
  `Point.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app`), without assuming
  `RepresentablyFlat F` or `CoverPreserving J K F`.
* When `F` is representably flat and cover-preserving, `Point.comapIsoOfFiberIso` yields
  `Φ.comap F hF ≅ Ψ` and `Point.sheafPullbackCompSheafFiberIso_eq_sheafFiberComapIso` compares
  with Mathlib's `sheafFiberComapIso`.
* `Functor.preservesFiniteLimits_sheafPullback_of_jointlyReflectIsomorphisms` deduces left
  exactness of `F.sheafPullback A J K` in an `AB5` category from a conservative family of points.

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

section Skyscraper

variable (e : F ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [HasProducts.{w} A]
  [F.IsContinuous J K]

/-- Given a continuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`, points `Φ` of
`(D, K)` and `Ψ` of `(C, J)`, and a natural isomorphism `e : F ⋙ Φ.fiber ≅ Ψ.fiber`, pushing
forward skyscraper sheaves at `Φ` along `F` yields skyscraper sheaves at `Ψ`. -/
noncomputable def skyscraperSheafFunctorCompSheafPushforwardContinuousIso :
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
    (M : A) (X : C) (y : Ψ.fiber.obj X) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) y =
      Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) (e.inv.app X y) :=
  (Pi.map'_comp_π _ _ y).trans (Category.comp_id _)

-- Explicit: `@[reassoc]` leaves the four `_assoc` lemmas left-associated across `Point` `def`s.
@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π_assoc
    (M : A) (X : C) (y : Ψ.fiber.obj X) {Z : A} (h : M ⟶ Z) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) y ≫ h =
      Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) (e.inv.app X y) ≫ h := by
  erw [← Category.assoc,
    Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π]
  rfl

@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_inv_app_hom_app_π
    (M : A) (X : C) (x : Φ.fiber.obj (F.obj X)) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).inv.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) x =
      Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) (e.hom.app X x) :=
  (Pi.map'_comp_π _ _ x).trans (Category.comp_id _)

@[simp]
lemma skyscraperSheafFunctorCompSheafPushforwardContinuousIso_inv_app_hom_app_π_assoc
    (M : A) (X : C) (x : Φ.fiber.obj (F.obj X)) {Z : A} (h : M ⟶ Z) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).inv.app M).hom.app
        (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj (F.obj X)) ↦ M) x ≫ h =
      Pi.π (fun (_ : Ψ.fiber.obj X) ↦ M) (e.hom.app X x) ≫ h := by
  erw [← Category.assoc,
    Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_inv_app_hom_app_π]
  rfl

variable [HasColimitsOfSize.{w, w} A] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- When `F : (C, J) ⥤ (D, K)` is continuous and `e : F ⋙ Φ.fiber ≅ Ψ.fiber`, taking the stalk at
`Φ` after sheaf pullback along `F` is naturally isomorphic to taking the stalk at `Ψ`. -/
noncomputable def sheafPullbackCompSheafFiberIso :
    F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber :=
  ((conjugateIsoEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    Ψ.skyscraperSheafAdjunction).symm
      (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A)).symm

@[simp]
lemma conjugateEquiv_sheafPullbackCompSheafFiberIso_inv :
    conjugateEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
      Ψ.skyscraperSheafAdjunction (Φ.sheafPullbackCompSheafFiberIso F e A).inv =
      (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso F e A).hom := by
  simp [sheafPullbackCompSheafFiberIso]

/-- Under the inverse of `sheafPullbackCompSheafFiberIso`, the germ at `Ψ` of a section of `G` over
`X` maps to the germ at `Φ` of its pullback along the adjunction unit. -/
@[simp]
lemma toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app
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
  let idΦ : Φ.presheafFiber.obj ((F.sheafPullback A J K).obj G).obj ⟶
      (F.sheafPullback A J K ⋙ Φ.sheafFiber).obj G := 𝟙 _
  have hrhs : (Ψ.skyscraperSheafAdjunction.unit.app G ≫ Ψ.skyscraperSheafFunctor.map α).hom =
      Ψ.skyscraperPresheafHomEquiv α := by
    rw [← Ψ.skyscraperSheafAdjunction.homEquiv_unit G _ α]
    exact Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom α
  have hlhs : (Φ.skyscraperSheafAdjunction.unit.app ((F.sheafPullback A J K).obj G)).hom =
      Φ.skyscraperPresheafHomEquiv idΦ := by
    rw [← Φ.skyscraperSheafAdjunction.homEquiv_id ((F.sheafPullback A J K).obj G)]
    exact Φ.skyscraperSheafAdjunction_homEquiv_apply_hom idΦ
  have h1 := congrArg (fun f : G ⟶ _ ↦ f.hom.app (op X) ≫ Pi.π _ y) h.symm
  -- `erw` crosses the semireducible `Point.sheafFiber` / `Point.skyscraperSheafFunctor` boundaries.
  erw [hrhs, Ψ.skyscraperPresheafHomEquiv_app_π] at h1
  refine h1.trans ?_
  simp only [Adjunction.comp_unit_app]
  erw [Category.assoc,
    Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π, Category.assoc]
  congr 1
  erw [congrArg (·.app (op (F.obj X))) hlhs, Φ.skyscraperPresheafHomEquiv_app_π, Category.comp_id]
  rfl

@[simp]
lemma toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app_assoc
    (G : Sheaf J A) (X : C) (y : Ψ.fiber.obj X) {Z : A}
    (h : Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G) ⟶ Z) :
    Ψ.toPresheafFiber X y G.obj ≫ (Φ.sheafPullbackCompSheafFiberIso F e A).inv.app G ≫ h =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) (e.inv.app X y) ((F.sheafPullback A J K).obj G).obj ≫ h := by
  erw [← Category.assoc, Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app, Category.assoc]
  rfl

/-- Under `sheafPullbackCompSheafFiberIso`, the germ at `Φ` of the pullback of a section of `G`
over `X` along the adjunction unit maps to its germ at `Ψ`. -/
@[simp]
lemma unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app
    (G : Sheaf J A) (X : C) (x : Φ.fiber.obj (F.obj X)) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj ≫
          (Φ.sheafPullbackCompSheafFiberIso F e A).hom.app G =
      Ψ.toPresheafFiber X (e.hom.app X x) G.obj := by
  have h := Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app_assoc F e A G X
    (e.hom.app X x) ((Φ.sheafPullbackCompSheafFiberIso F e A).hom.app G)
  rw [Iso.hom_inv_id_app_apply] at h
  erw [← h, (Φ.sheafPullbackCompSheafFiberIso F e A).inv_hom_id_app G, Category.comp_id]

@[simp]
lemma unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app_assoc
    (G : Sheaf J A) (X : C) (x : Φ.fiber.obj (F.obj X)) {Z : A} (h : Ψ.sheafFiber.obj G ⟶ Z) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X) ≫
        Φ.toPresheafFiber (F.obj X) x ((F.sheafPullback A J K).obj G).obj ≫
          (Φ.sheafPullbackCompSheafFiberIso F e A).hom.app G ≫ h =
      Ψ.toPresheafFiber X (e.hom.app X x) G.obj ≫ h := by
  rw [← Φ.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app]
  symm
  erw [Category.assoc, Category.assoc]
  rfl

end Skyscraper

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
  have hrefl : Φ.sheafPullbackCompSheafFiberIso F (Ψ := Φ.comap F hF) e₀ A =
      (Φ.sheafFiberComapIso F hF A).symm := by
    refine Iso.symm_eq_iff.mp (Iso.ext ((conjugateEquiv
      ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
      (Φ.comap F hF).skyscraperSheafAdjunction).injective ?_))
    simp only [Iso.symm_hom, Iso.symm_inv, conjugateEquiv_sheafPullbackCompSheafFiberIso_inv,
      sheafFiberComapIso, conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
    ext M ⟨X⟩; apply Pi.hom_ext; intro x
    erw [Φ.skyscraperSheafFunctorCompSheafPushforwardContinuousIso_hom_app_hom_app_π,
      Category.id_comp]
    rfl
  refine Iso.symm_eq_iff.mp (Iso.ext ?_)
  ext G : 2
  refine Ψ.presheafFiber_hom_ext fun X y ↦ ?_
  have h0 := Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app F
    (Ψ := Φ.comap F hF) e₀ A G X (e.inv.app X y)
  rw [hrefl] at h0
  simp only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, sheafFiberIso_inv]
  erw [Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app, ← h0]
  symm
  erw [NatTrans.comp_app, Functor.whiskerLeft_app, Hom.presheafFiber_app,
    Ψ.toPresheafFiber_presheafFiberDesc_assoc _ _ X y, comapIsoOfFiberIso_hom_hom]
  rfl

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
