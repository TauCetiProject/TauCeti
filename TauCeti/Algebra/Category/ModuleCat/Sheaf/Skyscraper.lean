/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Skyscraper
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs

/-!
# Skyscraper sheaves of modules

Let `R` be a sheaf of commutative rings on a topological space `X`, `x` a point of `X` and `T` a
module over the stalk `R_x`. The skyscraper presheaf of modules
`TauCeti.PresheafOfModules.skyscraper` at `x` with value `T` is a sheaf; this file packages it as a
sheaf of modules `TauCeti.SheafOfModules.skyscraper R x T`, right adjoint to the stalk at `x`:
morphisms `M ⟶ x_* T` of sheaves of modules correspond to `R_x`-linear maps `M_x → T`.

## Main declarations

* `TauCeti.SheafOfModules.skyscraper`: the skyscraper sheaf of modules at `x` with value `T`;
* `TauCeti.SheafOfModules.skyscraperHomEquiv`: `(M_x →ₗ[R_x] T) ≃ (M ⟶ x_* T)`, natural in `M`
  (`TauCeti.SheafOfModules.skyscraperHomEquiv_naturality_left`).
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)
  (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk R.obj x) T]

/-- The skyscraper presheaf of modules is a sheaf: compatible local values at `x` all agree with
the value of any member of the cover containing `x`. -/
theorem isSheaf_skyscraper :
    TopCat.Presheaf.IsSheaf (PresheafOfModules.skyscraper R.obj x T).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf ↦ ?_
  have key (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j) : sf i ⟨hi⟩ = sf j ⟨hj⟩ :=
    congrFun (hsf i j) ⟨⟨hi, hj⟩⟩
  refine ⟨fun p ↦ sf (Opens.mem_iSup.mp p.down).choose ⟨(Opens.mem_iSup.mp p.down).choose_spec⟩,
    fun i ↦ funext fun p ↦ key _ _ _ _, fun s hs ↦ funext fun p ↦ ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp p.down
  exact (congrFun (hs i) ⟨hi⟩ :).trans (key _ _ _ _)

/-- The skyscraper sheaf of modules at `x` with value the `R_x`-module `T`: its sections over `U`
are `T` when `x ∈ U` and `0` otherwise. Its body is exposed so that sections compute as those of
`TauCeti.PresheafOfModules.skyscraper`. -/
@[expose] def skyscraper : _root_.SheafOfModules.{u} (ringCatSheaf R) where
  val := PresheafOfModules.skyscraper R.obj x T
  isSheaf := isSheaf_skyscraper R x T

/-- The underlying presheaf of modules of the skyscraper sheaf is the skyscraper presheaf. -/
@[simp]
lemma skyscraper_val : (skyscraper R x T).val = PresheafOfModules.skyscraper R.obj x T :=
  rfl

variable {R} (M : _root_.SheafOfModules.{u} (ringCatSheaf R))

/-- The skyscraper at `x` is right adjoint to the stalk at `x`: `R_x`-linear maps `M_x → T`
correspond to morphisms `M ⟶ x_* T` of sheaves of modules. -/
def skyscraperHomEquiv :
    (↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T) ≃
      (M ⟶ skyscraper R x T) :=
  (PresheafOfModules.skyscraperHomEquiv (S := R.obj) x T M.val).trans
    ((_root_.SheafOfModules.fullyFaithfulForget (ringCatSheaf R)).homEquiv
      (X := M) (Y := skyscraper R x T)).symm

/-- The morphism into the skyscraper attached to `g` sends a section `m` over `U ∋ x` to
`g (m_x)`. -/
@[simp]
lemma skyscraperHomEquiv_apply_val_app_apply
    (g : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T)
    (U : (Opens X)ᵒᵖ) (m : M.val.obj U) (p : PLift (x ∈ U.unop)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      skyscraper_val]
    ((skyscraperHomEquiv x T M g).val.app U m p =
      g (TopCat.Presheaf.germ M.val.presheaf U.unop x p.down m)) :=
  (PresheafOfModules.skyscraperHomEquiv_apply_app_apply (S := R.obj) x T M.val g U m p :)

/-- The linear map attached to a morphism `α` into the skyscraper sends the germ of `m` to the
value of `α m` at `x`. -/
@[simp]
lemma skyscraperHomEquiv_symm_apply_germ (α : M ⟶ skyscraper R x T) (U : Opens X)
    (hx : x ∈ U) (m : M.val.obj (op U)) :
    dsimp% only [sheafCompose_obj_obj, _root_.PresheafOfModules.presheaf_obj_coe,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((skyscraperHomEquiv x T M).symm α (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      α.val.app (op U) m ⟨hx⟩) := (
  PresheafOfModules.skyscraperHomEquiv_symm_apply_germ (S := R.obj) x T M.val α.val U hx m :)

/-- Naturality of `skyscraperHomEquiv` in the source: precomposing with `β : M' ⟶ M` corresponds
to precomposing with the stalk map of `β`. -/
lemma skyscraperHomEquiv_naturality_left {M' : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    (β : M' ⟶ M)
    (g : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] T) :
    skyscraperHomEquiv x T M' (g ∘ₗ PresheafOfModules.stalkMapCommRing (S := R.obj) x β.val) =
      β ≫ skyscraperHomEquiv x T M g :=
  _root_.SheafOfModules.Hom.ext
    (PresheafOfModules.skyscraperHomEquiv_naturality_left (S := R.obj) x T M.val β.val g)

end SheafOfModules

end

end TauCeti
