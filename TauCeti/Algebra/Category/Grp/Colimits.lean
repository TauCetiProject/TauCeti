/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Images of the legs of a colimit of groups

The images of the legs `c.ι.app j` of a colimit cocone `c` in `GrpCat` generate its apex: a
subgroup containing all of them receives a cocone, so by the universal property its inclusion has
a right inverse. Over a filtered index category, the images form a directed family of subgroups,
so every finite subset of the apex already lies in the image of a single leg. This is how
properties defined by finitely many elements at a time pass to filtered colimits of groups.

## Main declarations

* `TauCeti.GrpCat.iSup_range_eq_top_of_isColimit`: the images of the legs of a colimit cocone
  generate its apex.
* `TauCeti.GrpCat.range_le_range`: the image of the leg at `j` is contained in the image of the
  leg at any object receiving a morphism from `j`.
* `TauCeti.GrpCat.directed_range`: over a filtered index category, the images of the legs of a
  cocone form a directed family of subgroups.
* `TauCeti.GrpCat.exists_subset_range_of_isColimit`: over a filtered index category, every finite
  subset of the apex of a colimit cocone lies in the image of a single leg.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

namespace GrpCat

variable {J : Type*} [Category* J] {F : J ⥤ _root_.GrpCat.{u}}

/-- The images of the legs of a colimit cocone in `GrpCat` generate its apex. -/
theorem iSup_range_eq_top_of_isColimit {c : Cocone F} (hc : IsColimit c) :
    ⨆ j, MonoidHom.range (N := c.pt) (c.ι.app j).hom = ⊤ := by
  set S : Subgroup c.pt := ⨆ j, MonoidHom.range (N := c.pt) (c.ι.app j).hom
  have hS (j : J) (x : F.obj j) : (c.ι.app j).hom x ∈ S :=
    le_iSup (fun j => MonoidHom.range (N := c.pt) (c.ι.app j).hom) j ⟨x, rfl⟩
  -- Corestricting the legs to `S` gives a cocone with apex `S`.
  let d : Cocone F :=
    { pt := .of S
      ι :=
        { app j := _root_.GrpCat.ofHom ((c.ι.app j).hom.codRestrict S (hS j))
          naturality j k f := by
            ext x
            exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) x) } }
  -- The inclusion of `S` is split by the map out of the colimit, so it is surjective.
  have hd : hc.desc d ≫ _root_.GrpCat.ofHom S.subtype = 𝟙 c.pt :=
    hc.hom_ext fun j => by ext x; simp [d]
  have hd' : S.subtype.comp (hc.desc d).hom = MonoidHom.id c.pt := by
    simpa using congr(($hd).hom)
  have hsurj : Function.Surjective S.subtype := fun x =>
    ⟨(hc.desc d).hom x, DFunLike.congr_fun hd' x⟩
  rw [← S.range_subtype]
  exact S.subtype.range_eq_top_of_surjective hsurj

/-- The image of the leg at `j` of a cocone in `GrpCat` is contained in the image of the leg at
any object receiving a morphism from `j`. -/
theorem range_le_range (c : Cocone F) {j k : J} (f : j ⟶ k) :
    (c.ι.app j).hom.range ≤ (c.ι.app k).hom.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(F.map f).hom x, ConcreteCategory.congr_hom (c.w f) x⟩

/-- Over a filtered index category, the images of the legs of a cocone in `GrpCat` form a directed
family of subgroups. -/
theorem directed_range [IsFilteredOrEmpty J] (c : Cocone F) :
    Directed (· ≤ ·) fun j => MonoidHom.range (N := c.pt) (c.ι.app j).hom := fun j k =>
  ⟨IsFiltered.max j k, range_le_range c (IsFiltered.leftToMax j k),
    range_le_range c (IsFiltered.rightToMax j k)⟩

/-- Over a filtered index category, every finite subset of the apex of a colimit cocone in
`GrpCat` lies in the image of a single leg. -/
theorem exists_subset_range_of_isColimit [IsFiltered J] {c : Cocone F} (hc : IsColimit c)
    (s : Finset c.pt) : ∃ j, (s : Set c.pt) ⊆ Set.range (c.ι.app j).hom := by
  have := IsFiltered.nonempty (C := J)
  have hdir :
      Directed (· ⊆ ·) fun j => (MonoidHom.range (N := c.pt) (c.ι.app j).hom : Set c.pt) :=
    (directed_range c).mono_comp _ fun _ _ => SetLike.coe_subset_coe.2
  obtain ⟨j, hj⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion (s := s) <| by
    rw [← Subgroup.coe_iSup_of_directed (directed_range c), iSup_range_eq_top_of_isColimit hc]
    exact Set.subset_univ _
  exact ⟨j, by simpa using hj⟩

end GrpCat

end TauCeti
