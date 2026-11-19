/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Skyscraper
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Stalk

/-!
# Skyscraper sheaves of modules

Let `R` be a sheaf of commutative rings on a topological space `X`, `x` a point of `X` and `T` a
module over the stalk `R_x`. The skyscraper presheaf of modules
`TauCeti.PresheafOfModules.skyscraper` at `x` with value `T` is a sheaf; this file packages it as a
sheaf of modules `TauCeti.SheafOfModules.skyscraper R x T`, right adjoint to the stalk at `x`:
morphisms `M ⟶ x_* T` of sheaves of modules correspond to `R_x`-linear maps `M_x → T`.

For a morphism of ringed spaces `(f, φ) : Y → X`, a point `y` of `Y` and an `𝒪_{Y,y}`-module `T`,
the pushforward along `φ` of the skyscraper at `y` with value `T` is the skyscraper at `f y` with
value `T`, an `𝒪_{X,f(y)}`-module by restriction of scalars along the stalk map of `(f, φ)`
(`TauCeti.SheafOfModules.pushforwardSkyscraperIso`). Together with the adjunction between
pullback and pushforward, this computes linear maps out of the stalks of a pulled-back module.

## Main declarations

* `TauCeti.SheafOfModules.skyscraper`: the skyscraper sheaf of modules at `x` with value `T`;
* `TauCeti.SheafOfModules.skyscraperHomEquiv`: `(M_x →ₗ[R_x] T) ≃ (M ⟶ x_* T)`, natural in `M`
  (`TauCeti.SheafOfModules.skyscraperHomEquiv_naturality_left`);
* `TauCeti.SheafOfModules.pushforwardSkyscraperIso`: `f_* (y_* T) ≅ (f y)_* T`.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

section Skyscraper

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
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
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

end Skyscraper

section Pushforward

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  (y : Y) (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) T]
  [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) T]

/-- The pushforward along `(f, φ)` of the skyscraper at `y` with value `T` is the skyscraper at
`f y` with value `T`, for any `𝒪_{X,f(y)}`-module structure on `T` that is restriction of scalars
along the stalk map `ringStalkMap φ y`. On sections over `U` both sides are `T` when `f y ∈ U` and
`0` otherwise. -/
def pushforwardSkyscraperIso (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T),
      a • t = ringStalkMap φ y a • t) :
    (_root_.SheafOfModules.pushforward φ).obj (skyscraper 𝒪Y y T) ≅ skyscraper 𝒪X (f y) T :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (_root_.PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
      (R := (ringCatSheaf 𝒪X).obj.obj U)
      (X₁ := ((_root_.SheafOfModules.pushforward φ).obj (skyscraper 𝒪Y y T)).val.obj U)
      (m₁ := ModuleCat.isModule _)
      (X₂ := (skyscraper 𝒪X (f y) T).val.obj U) (m₂ := ModuleCat.isModule _)
      { toFun s p := s ⟨p.down⟩
        invFun s p := s ⟨p.down⟩
        map_add' _ _ := rfl
        map_smul' r s := funext fun p ↦ by
          refine (congrArg (· • s ⟨p.down⟩) (ringStalkMap_germ φ y U.unop p.down r).symm).trans ?_
          exact (hT _ _).symm
        left_inv _ := rfl
        right_inv _ := rfl }) (fun _ _ _ ↦ rfl))

/-- On sections, `pushforwardSkyscraperIso` is the identity of the values at `y`. -/
@[simp]
lemma pushforwardSkyscraperIso_hom_val_app_apply
    (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T), a • t = ringStalkMap φ y a • t)
    (U : (Opens X)ᵒᵖ)
    (s : (skyscraper 𝒪Y y T).val.obj (op ((Opens.map f).obj U.unop))) (p : PLift (f y ∈ U.unop)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((pushforwardSkyscraperIso φ y T hT).hom.val.app U s p = s ⟨p.down⟩) :=
  (rfl)

end Pushforward

end SheafOfModules

end

end TauCeti
