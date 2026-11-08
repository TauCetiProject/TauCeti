/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Exactness of sheaves of abelian groups on a basis

A sequence `F₁ ⟶ F₂ ⟶ F₃` of sheaves of abelian groups on a topological space is exact as soon as
the sequences of sections `F₁(V) ⟶ F₂(V) ⟶ F₃(V)` are exact for the members `V` of a basis of the
topology (`TopCat.Sheaf.exact_of_isBasis`). Exactness of sheaves is exactness on stalks
(`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`), and every stalk is a filtered colimit of
sections over basic open neighbourhoods. The converse fails: exactness of sheaves only says that
a section of `F₂` killed by `F₂ ⟶ F₃` comes from `F₁` locally.

This is how a sheaf defined as the homology of a complex of sheaves is shown to vanish, for
instance a higher direct image computed from an injective resolution: it suffices that the
complexes of sections are exact over a basis, where they compute sheaf cohomology.

In the other direction, an epimorphism of sheaves is only locally surjective on sections: a section
of the target lifts near every point, on a member of any set of opens which contains a basis inside
each of its members (`TopCat.Sheaf.exists_mem_lift_of_epi`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercise II.1.2.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
  {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  {B : Set (Opens X)}

/-- A sequence of sheaves of abelian groups is exact when the sequences of its sections over the
members of a basis of the topology are exact: every section of `F₂` over a basic open killed by
`F₂ ⟶ F₃` comes from a section of `F₁`. -/
theorem exact_of_isBasis (hB : Opens.IsBasis B)
    (h : ∀ V ∈ B, ∀ s : S.X₂.obj.obj (op V), S.g.hom.app (op V) s = 0 →
      ∃ t : S.X₁.obj.obj (op V), S.f.hom.app (op V) t = s) :
    S.Exact := by
  refine (exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{u}) (X := X) S).2 fun x ↦ ?_
  rw [ShortComplex.ab_exact_iff]
  -- `S.map` is taken in `TopCat.Sheaf`, a type synonym of the category of sheaves on the site of
  -- opens; unfold the mapped differentials to the stalk maps of the underlying presheaves
  change ∀ y, (Presheaf.stalkFunctor _ x).map S.g.hom y = 0 →
    ∃ z, (Presheaf.stalkFunctor _ x).map S.f.hom z = y
  intro y hy
  obtain ⟨U, hxU, hU, s, rfl⟩ := Presheaf.exists_mem_germ_eq_of_isBasis hB S.X₂.obj x y
  -- the image of `s` in `F₃` has zero germ at `x`, so it vanishes on a basic neighbourhood `W`
  have hgs : Presheaf.germ S.X₃.obj U x hxU (S.g.hom.app (op U) s) =
      Presheaf.germ S.X₃.obj U x hxU 0 := by
    rw [map_zero, ← Presheaf.stalkFunctor_map_germ_apply]
    exact hy
  obtain ⟨W, hxW, hW, hWU, hWU', hWs⟩ := Presheaf.germ_eq_of_isBasis hB _ x hxU hxU hgs
  -- on `W` the restriction of `s` comes from a section of `F₁`
  obtain ⟨t, ht⟩ := h W hW (S.X₂.obj.map (homOfLE hWU).op s) <| by
    rw [← ConcreteCategory.comp_apply, S.g.hom.naturality, ConcreteCategory.comp_apply, hWs,
      map_zero]
  refine ⟨Presheaf.germ S.X₁.obj W x hxW t, ?_⟩
  rw [Presheaf.stalkFunctor_map_germ_apply, ht, Presheaf.germ_res_apply]

/-- Let `B` be a set of opens containing, inside each of its members, a basis of the topology of
that member. Along an epimorphism of sheaves `π : F ⟶ G`, a section of `G` over a member `Y` of `B`
lifts, near every point of `Y`, on a member of `B` contained in `Y`. -/
theorem exists_mem_lift_of_epi
    (hbasis : ∀ U ∈ B, ∀ V : Opens X, V ≤ U → ∀ x ∈ V, ∃ W ∈ B, x ∈ W ∧ W ≤ V)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (π : F ⟶ G)
    [Epi π]
    {Y : Opens X} (hY : Y ∈ B) (s : G.obj.obj (op Y)) (x : X) (hx : x ∈ Y) :
    ∃ V ∈ B, x ∈ V ∧ ∃ h : V ≤ Y, ∃ t : F.obj.obj (op V),
      π.hom.app (op V) t = G.obj.map (homOfLE h).op s := by
  have : CategoryTheory.Sheaf.IsLocallySurjective π :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ :=
    CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X) π.hom s x hx
  obtain ⟨W, hW, hxW, hWV⟩ := hbasis Y hY V f.le x hxV
  refine ⟨W, hW, hxW, hWV.trans f.le, F.obj.map (homOfLE hWV).op t, ?_⟩
  rw [← ConcreteCategory.comp_apply, π.hom.naturality, ConcreteCategory.comp_apply, ht,
    ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
  rfl

end TopCat.Sheaf
