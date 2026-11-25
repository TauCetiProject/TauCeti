/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Comma.Presheaf.OverYoneda
public import TauCeti.CategoryTheory.Sites.Over.Basic

/-!
# Sheaves over a representable sheaf

Let `J` be a Grothendieck topology on `C` and `X` an object of `C` whose representable presheaf
is a sheaf. A presheaf of types `F` on `C` lying over `yoneda.obj X` corresponds, under
`TauCeti.overYonedaEquivPresheafOver X`, to a presheaf on `Over X`. The first is a sheaf for `J`
exactly when the second is a sheaf for the induced topology `J.over X`. The proof identifies
`F` with the presheaf `T ↦ Σ (h : T ⟶ X), F (T, h)` of `CategoryTheory.Over.sigmaPresheaf` and
applies `CategoryTheory.Over.isSheaf_over_iff_isSheaf_sigmaPresheaf`.

## Main declarations

* `CategoryTheory.Over.sigmaPresheafOverYonedaEquivPresheafOverIso F`: the presheaf on `C`
  assembled from the presheaf on `Over X` attached to `F` is isomorphic to `F.left`.
* `CategoryTheory.GrothendieckTopology.isSheaf_overYonedaEquivPresheafOver_iff`: `F.left` is a
  sheaf for `J` if and only if the attached presheaf on `Over X` is a sheaf for `J.over X`.
-/

public section

universe v u

namespace CategoryTheory

open Opposite TauCeti

variable {C : Type u} [Category.{v} C] {X : C}

namespace Over

/-- The presheaf `T ↦ Σ (h : T ⟶ X), P (T, h)` on `C` built from the presheaf `P` on `Over X`
attached to a presheaf `F` over `yoneda.obj X` is isomorphic to `F.left`: a section of `F.left`
over `T` determines its image `h` in `yoneda.obj X`. -/
noncomputable def sigmaPresheafOverYonedaEquivPresheafOverIso (F : Over (yoneda.obj X)) :
    Over.sigmaPresheaf ((overYonedaEquivPresheafOver X).functor.obj F) ≅ F.left :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun x := x.2.val
      invFun y := ⟨F.hom.app T y, ⟨y, ⟨(yonedaEquiv_yoneda_map _).symm⟩⟩⟩
      left_inv x := Sigma.subtype_ext (β := F.left.obj T)
        (x.2.app_val.trans (yonedaEquiv_yoneda_map _)) rfl
      right_inv _ := rfl })
    -- Naturality holds by definition: both sides send a pair `⟨h, u⟩` to `F.left.map f u.val`,
    -- since `Over.sigmaPresheaf` maps `u` by `OverPresheafAux.OverArrows.map₂`, whose value is
    -- `F.left.map f u.val` by definition (`OverPresheafAux.OverArrows.map₂_val`).
    (fun _ ↦ rfl)

/-- The isomorphism `sigmaPresheafOverYonedaEquivPresheafOverIso F` forgets the morphism to `X`
of a pair. -/
@[simp]
lemma sigmaPresheafOverYonedaEquivPresheafOverIso_hom_app_apply (F : Over (yoneda.obj X))
    (T : Cᵒᵖ) (x : (Over.sigmaPresheaf ((overYonedaEquivPresheafOver X).functor.obj F)).obj T) :
    (sigmaPresheafOverYonedaEquivPresheafOverIso F).hom.app T x = x.2.val :=
  (rfl)

/-- The inverse of `sigmaPresheafOverYonedaEquivPresheafOverIso F` pairs a section `y` of `F.left`
with its image in `yoneda.obj X`. -/
@[simp]
lemma sigmaPresheafOverYonedaEquivPresheafOverIso_inv_app_apply_fst (F : Over (yoneda.obj X))
    (T : Cᵒᵖ) (y : F.left.obj T) :
    ((sigmaPresheafOverYonedaEquivPresheafOverIso F).inv.app T y).1 = F.hom.app T y :=
  (rfl)

end Over

/-- If `yoneda.obj X` is a sheaf for `J`, then a presheaf `F` over `yoneda.obj X` is a sheaf for
`J` exactly when the corresponding presheaf on `Over X` is a sheaf for `J.over X`. -/
theorem GrothendieckTopology.isSheaf_overYonedaEquivPresheafOver_iff (J : GrothendieckTopology C)
    (hX : Presieve.IsSheaf J (CategoryTheory.yoneda.obj X))
    (F : Over (CategoryTheory.yoneda.obj X)) :
    Presieve.IsSheaf (J.over X) ((overYonedaEquivPresheafOver X).functor.obj F) ↔
      Presieve.IsSheaf J F.left :=
  (Over.isSheaf_over_iff_isSheaf_sigmaPresheaf J hX).trans
    ⟨Presieve.isSheaf_iso J (Over.sigmaPresheafOverYonedaEquivPresheafOverIso F),
      Presieve.isSheaf_iso J (Over.sigmaPresheafOverYonedaEquivPresheafOverIso F).symm⟩

end CategoryTheory
