/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import TauCeti.Topology.Sheaves.Stalks

/-!
# Linear maps from stalks of presheaves of modules

Mathlib endows the stalk of a presheaf of modules with a module structure over the stalk of
its ring presheaf, without requiring commutativity. This file gives its linear universal property:
compatible additive maps on sections that respect scalar multiplication by germs induce a linear
map from the stalk. Over commutative coefficients, `germSemilinear` bundles the germ map of
sections as a map semilinear along the ring germ map, and `stalkMapCommRing` is the stalk map of a
morphism, linear over the commutative-ring stalk.
It also constructs the stalk map of a morphism defined on a neighborhood, for use with
local morphisms such as sections of an internal Hom.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

universe u

noncomputable section

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}}
  (M : PresheafOfModules.{u} R) (x : X)
  {T : Type u} [AddCommGroup T]

variable [Module (R.stalk x) T]

/-- Compatible section maps that are linear for the ring germ maps induce a linear map from
the module stalk. -/
def stalkLift
    (f : ∀ (U : Opens X), x ∈ U → M.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : M.obj (op V)),
      f U hx (M.map i.op m) = f V (i.le hx) m)
    (hs : ∀ (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)),
      f U hx (r • m) = R.germ U x hx r • f U hx m) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[R.stalk x] T where
  toFun := TopCat.Presheaf.stalkLiftAddHom M.presheaf x f hf
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := R.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m hxU
    rw [← R.germ_res_apply (homOfLE hVU) x hxV r,
      ← M.germ_ringCat_smul (R := R) x V hxV (R.map (homOfLE hVU).op r) m]
    exact (TopCat.Presheaf.stalkLiftAddHom_germ M.presheaf x f hf V hxV _).trans
      ((hs V hxV (R.map (homOfLE hVU).op r) m).trans
        (congrArg (fun t : T ↦ R.germ V x hxV (R.map (homOfLE hVU).op r) • t)
          (TopCat.Presheaf.stalkLiftAddHom_germ M.presheaf x f hf V hxV m).symm))

/-- The linear map induced from compatible section maps takes a germ to its prescribed value. -/
theorem stalkLift_germ
    (f : ∀ (U : Opens X), x ∈ U → M.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : M.obj (op V)),
      f U hx (M.map i.op m) = f V (i.le hx) m)
    (hs : ∀ (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)),
      f U hx (r • m) = R.germ U x hx r • f U hx m)
    (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    M.stalkLift x f hf hs (TopCat.Presheaf.germ M.presheaf U x hx m) = f U hx m :=
  TopCat.Presheaf.stalkLiftAddHom_germ M.presheaf x f hf U hx m

section CommRing

variable {S : X.Presheaf CommRingCat.{u}}
  (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u}))
  [Module (S.stalk x) T]

/-- Compatible section maps linear for the original commutative-ring germs induce a linear
map from the module stalk. This retains the commutative-ring stalk carrier, which differs
from the stalk of the presheaf obtained by forgetting commutativity. -/
def stalkLiftCommRing
    (f : ∀ (U : Opens X), x ∈ U → N.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : N.obj (op V)),
      f U hx (N.map i.op m) = f V (i.le hx) m)
    (hs : ∀ (U : Opens X) (hx : x ∈ U) (r : S.obj (op U)) (m : N.obj (op U)),
      f U hx (r • m) = S.germ U x hx r • f U hx m) :
    ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] T where
  toFun := TopCat.Presheaf.stalkLiftAddHom N.presheaf x f hf
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := S.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf m hxU
    rw [← S.germ_res_apply (homOfLE hVU) x hxV r,
      ← N.germ_smul (R := S) x V hxV (S.map (homOfLE hVU).op r) m]
    exact (TopCat.Presheaf.stalkLiftAddHom_germ N.presheaf x f hf V hxV _).trans
      ((hs V hxV (S.map (homOfLE hVU).op r) m).trans
        (congrArg (fun t : T ↦ S.germ V x hxV (S.map (homOfLE hVU).op r) • t)
          (TopCat.Presheaf.stalkLiftAddHom_germ N.presheaf x f hf V hxV m).symm))

/-- The commutative-ring linear stalk lift takes a germ to its prescribed value. -/
theorem stalkLiftCommRing_germ
    (f : ∀ (U : Opens X), x ∈ U → N.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : N.obj (op V)),
      f U hx (N.map i.op m) = f V (i.le hx) m)
    (hs : ∀ (U : Opens X) (hx : x ∈ U) (r : S.obj (op U)) (m : N.obj (op U)),
      f U hx (r • m) = S.germ U x hx r • f U hx m)
    (U : Opens X) (hx : x ∈ U) (m : N.obj (op U)) :
    N.stalkLiftCommRing x f hf hs (TopCat.Presheaf.germ N.presheaf U x hx m) = f U hx m :=
  TopCat.Presheaf.stalkLiftAddHom_germ N.presheaf x f hf U hx m

/-- The germ map of a presheaf of modules over a presheaf of commutative rings, as a map
semilinear along the ring germ map. -/
def germSemilinear (U : Opens X) (hx : x ∈ U) :
    N.obj (op U) →ₛₗ[(S.germ U x hx).hom] ↑(TopCat.Presheaf.stalk N.presheaf x) where
  toFun := TopCat.Presheaf.germ N.presheaf U x hx
  map_add' := map_add _
  map_smul' r m := N.germ_smul x U hx r m

/-- The semilinear germ map is the germ map. -/
@[simp]
theorem germSemilinear_apply (U : Opens X) (hx : x ∈ U) (m : N.obj (op U)) :
    N.germSemilinear x U hx m = TopCat.Presheaf.germ N.presheaf U x hx m :=
  (rfl)

variable {N} {N' : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u})}

private def stalkMapCommRingSection (f : N ⟶ N') (U : Opens X) (hx : x ∈ U) :
    N.obj (op U) →+ ↑(TopCat.Presheaf.stalk N'.presheaf x) :=
  (N'.germSemilinear x U hx).toAddMonoidHom.comp (f.app (op U)).hom.toAddMonoidHom

private theorem stalkMapCommRingSection_res (f : N ⟶ N') {U V : Opens X} (i : U ⟶ V)
    (hx : x ∈ U) (m : N.obj (op V)) :
    stalkMapCommRingSection x f U hx (N.map i.op m) =
      stalkMapCommRingSection x f V (i.le hx) m :=
  (congrArg (TopCat.Presheaf.germ N'.presheaf _ x hx) (naturality_apply f i.op m)).trans
    (TopCat.Presheaf.germ_res_apply N'.presheaf i x hx _)

private theorem stalkMapCommRingSection_smul (f : N ⟶ N') (U : Opens X) (hx : x ∈ U)
    (r : S.obj (op U)) (m : N.obj (op U)) :
    stalkMapCommRingSection x f U hx (r • m) =
      S.germ U x hx r • stalkMapCommRingSection x f U hx m :=
  (congrArg (TopCat.Presheaf.germ N'.presheaf U x hx) ((f.app (op U)).hom.map_smul r m)).trans
    (N'.germ_smul x U hx r _)

/-- A morphism of presheaves of modules over a presheaf of commutative rings induces a map on
stalks, linear over the commutative-ring stalk. -/
def stalkMapCommRing (f : N ⟶ N') :
    ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[S.stalk x] ↑(TopCat.Presheaf.stalk N'.presheaf x) :=
  N.stalkLiftCommRing x (stalkMapCommRingSection x f)
    (stalkMapCommRingSection_res x f) (stalkMapCommRingSection_smul x f)

/-- The stalk map of a morphism sends a germ to the germ of its image. -/
@[simp]
theorem stalkMapCommRing_germ (f : N ⟶ N') (U : Opens X) (hx : x ∈ U) (m : N.obj (op U)) :
    dsimp% only [presheaf_obj_coe]
    (stalkMapCommRing x f (TopCat.Presheaf.germ N.presheaf U x hx m) =
      TopCat.Presheaf.germ N'.presheaf U x hx (f.app (op U) m)) :=
  N.stalkLiftCommRing_germ x (stalkMapCommRingSection x f)
    (stalkMapCommRingSection_res x f) (stalkMapCommRingSection_smul x f) U hx m

end CommRing

variable {N : PresheafOfModules.{u} R}

variable (U : Opens X)
  (φ : (pushforward₀ (Over.forget U) R).obj M ⟶
    (pushforward₀ (Over.forget U) R).obj N)

private def stalkMapOverSection (hxU : x ∈ U) :
    ∀ (V : Opens X), x ∈ V → M.obj (op V) →+ ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  fun V hxV ↦ AddMonoidHom.mk'
      (fun m ↦ TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))
          (M.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)))
      (fun a b ↦ (congrArg (fun t ↦ TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U))) t))
          ((M.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op).hom.map_add a b)).trans
            ((congrArg (TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩)
              ((φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom.map_add _ _)).trans
                ((TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩).hom.map_add _ _)))

private theorem stalkMapOverSection_res (hxU : x ∈ U) :
    ∀ {V W : Opens X} (i : V ⟶ W) (hxV : x ∈ V) (m : M.obj (op W)),
      stalkMapOverSection M x U φ hxU V hxV (M.map i.op m) =
        stalkMapOverSection M x U φ hxU W (i.le hxV) m :=
  fun {V W} i hxV m ↦ by
      let j : V ⊓ U ⟶ W ⊓ U := homOfLE (inf_le_inf i.le le_rfl)
      let k : Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U) ⟶
          Over.mk (homOfLE inf_le_right : W ⊓ U ⟶ U) := Over.homMk j
      have hm : M.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op (M.map i.op m) =
          M.map j.op (M.map (homOfLE inf_le_left : W ⊓ U ⟶ W).op m) := by
        simp only [← map_comp_apply]
        congr 1
      exact (congrArg (fun t ↦ TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U))) t)) hm).trans
          ((congrArg (TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩)
            (naturality_apply φ k.op _)).trans
              (TopCat.Presheaf.germ_res_apply N.presheaf j x ⟨hxV, hxU⟩ _))

private theorem stalkMapOverSection_smul (hxU : x ∈ U) :
    ∀ (V : Opens X) (hxV : x ∈ V) (r : R.obj (op V)) (m : M.obj (op V)),
      stalkMapOverSection M x U φ hxU V hxV (r • m) =
        R.germ V x hxV r • stalkMapOverSection M x U φ hxU V hxV m :=
  fun V hxV r m ↦ by
      refine (congrArg (fun t ↦ TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U))) t))
          (M.map_smul (homOfLE inf_le_left : V ⊓ U ⟶ V).op r m)).trans ?_
      refine (congrArg (TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩)
        ((φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom.map_smul _ _)).trans ?_
      exact (N.germ_ringCat_smul (R := R) x (V ⊓ U) ⟨hxV, hxU⟩ _ _).trans
        (congrArg (fun t ↦ t • TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
          (φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))
            (M.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)))
          (R.germ_res_apply (homOfLE inf_le_left) x ⟨hxV, hxU⟩ r))

/-- A morphism defined on the slice over a neighborhood induces a map on stalks at every
point of that neighborhood. -/
def stalkMapOver (hxU : x ∈ U) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[R.stalk x]
      ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  M.stalkLift x (stalkMapOverSection M x U φ hxU)
    (stalkMapOverSection_res M x U φ hxU) (stalkMapOverSection_smul M x U φ hxU)

/-- The stalk map of a local morphism is computed on any representative inside its domain. -/
theorem stalkMapOver_germ (hxU : x ∈ U) (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V)
    (m : M.obj (op V)) :
    stalkMapOver M x U φ hxU (TopCat.Presheaf.germ M.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.presheaf V x hxV (φ.app (op (Over.mk i)) m) := by
  let k : Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U) ⟶ Over.mk i :=
    Over.homMk (homOfLE inf_le_left)
  have hg : stalkMapOver M x U φ hxU (TopCat.Presheaf.germ M.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))
          (M.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)) := by
    exact M.stalkLift_germ x (stalkMapOverSection M x U φ hxU)
      (stalkMapOverSection_res M x U φ hxU) (stalkMapOverSection_smul M x U φ hxU) V hxV m
  exact hg.trans ((congrArg (TopCat.Presheaf.germ N.presheaf (V ⊓ U) x ⟨hxV, hxU⟩)
      (naturality_apply φ k.op m)).trans
        (TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE inf_le_left) x ⟨hxV, hxU⟩ _))

end PresheafOfModules
