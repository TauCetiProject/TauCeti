/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Additive maps from stalks

Compatible additive maps on sections of an additive-group-valued presheaf induce an additive
map from each stalk. Its value on a germ is the prescribed value of the section map.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u}) (x : X)
  {T : Type u} [AddCommGroup T]

/-- The additive universal property of a presheaf stalk, using maps compatible with restriction. -/
def stalkLiftAddHom
    (f : ∀ (U : Opens X), x ∈ U → F.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : F.obj (op V)),
      f U hx (F.map i.op m) = f V (i.le hx) m) :
    ↑(TopCat.Presheaf.stalk F x) →+ T :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ F)
    { pt := AddCommGrpCat.of T
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom (f U.unop.1 U.unop.2)
          naturality := fun {U V} i ↦ by
            ext m
            exact hf i.unop V.unop.2 m } }).hom

/-- The additive map induced from compatible section maps takes a germ to its prescribed value. -/
@[simp]
theorem stalkLiftAddHom_germ
    (f : ∀ (U : Opens X), x ∈ U → F.obj (op U) →+ T)
    (hf : ∀ {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : F.obj (op V)),
      f U hx (F.map i.op m) = f V (i.le hx) m)
    (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    F.stalkLiftAddHom x f hf (TopCat.Presheaf.germ F U x hx m) = f U hx m :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ F) _ (op ⟨U, hx⟩)) m

end TopCat.Presheaf
