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
each of its members (`TopCat.Sheaf.exists_mem_lift_of_epi`). Consequently, any morphism intertwined
under an epimorphism with a morphism that vanishes on all opens inside `V` also vanishes on all
opens inside `V` (`TopCat.Sheaf.app_eq_zero_of_epi_comp`). This file also records sectionwise
evaluation of `∑ i ∈ s, η i - 𝟙 F` (`TopCat.Sheaf.sum_sub_id_app_eq_zero_iff`) and gluing of
locally finite sums of sections (`TopCat.Sheaf.exists_gluing_finset_sum`).

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
  obtain ⟨U, hxU, _, s, rfl⟩ := Presheaf.exists_mem_germ_eq_of_isBasis hB S.X₂.obj x y
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

/-- If `π₁ : G₁ ⟶ Z₁` is an epimorphism of sheaves of abelian groups and `π₁ ≫ ζ = φ ≫ π₂`,
where `φ : G₁ ⟶ G₂` vanishes on all opens inside `V`, then `ζ : Z₁ ⟶ Z₂` also vanishes on all
opens inside `V`. -/
theorem app_eq_zero_of_epi_comp {G₁ G₂ Z₁ Z₂ : X.Sheaf AddCommGrpCat.{u}}
    (π₁ : G₁ ⟶ Z₁) [Epi π₁] (π₂ : G₂ ⟶ Z₂) (φ : G₁ ⟶ G₂) (ζ : Z₁ ⟶ Z₂)
    (hcomm : π₁ ≫ ζ = φ ≫ π₂) {V : Opens X}
    (hφ : ∀ ⦃W : Opens X⦄, W ≤ V → φ.hom.app (op W) = 0) ⦃W : Opens X⦄ (hW : W ≤ V) :
    ζ.hom.app (op W) = 0 := by
  refine AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun z ↦ ?_
  rw [AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  choose U _ hxU hUW t ht using fun x : W ↦
    exists_mem_lift_of_epi (B := Set.univ)
      (fun _ _ U' _ y hy ↦ ⟨U', Set.mem_univ _, hy, le_rfl⟩)
      π₁ (Set.mem_univ W) z x.1 x.2
  have hcov : W ≤ ⨆ x : W, U x := fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  refine Z₂.eq_of_locally_eq' U W (fun x ↦ homOfLE (hUW x)) hcov _ _ fun x ↦ ?_
  rw [map_zero, ← NatTrans.naturality_apply ζ.hom, ← ht x,
    ← ConcreteCategory.comp_apply, ← TopCat.Sheaf.comp_app, hcomm,
    TopCat.Sheaf.comp_app, hφ ((hUW x).trans hW), zero_comp]
  simp

/-- For a finite family of endomorphisms `η` of a sheaf `F` valued in a preadditive category,
`(∑ i ∈ s, η i) - 𝟙 F` vanishes on `W` if and only if `∑ i ∈ s, (η i).hom.app (op W)` is the
identity on `F(W)`. -/
theorem sum_sub_id_app_eq_zero_iff {C : Type*} [Category* C] [Preadditive C]
    {Y : TopCat} {F : Y.Sheaf C} {ι : Type*} (s : Finset ι) (η : ι → (F ⟶ F))
    (W : Opens Y) :
    ((∑ i ∈ s, η i) - 𝟙 F).hom.app (op W) = 0 ↔
      ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W)) := by
  rw [← InducedCategory.homAddEquiv_apply, map_sub, map_sum]
  simp [sub_eq_zero]

/-- Gluing a locally finite sum of sections of an abelian sheaf `G` over `U`: if each `a i`
vanishes on opens inside `V i`, and `N` covers `U` with `N k ≤ V i` for all `i ∉ S k`, then the
finite sums `∑ i ∈ S k, a i|_{N k}` glue to a section `b` over `U`. -/
theorem exists_gluing_finset_sum (G : X.Sheaf AddCommGrpCat.{u}) {U : Opens X} {ι κ : Type*}
    (V : ι → Opens X) (a : ι → G.obj.obj (op U))
    (ha : ∀ i ⦃W : Opens X⦄ (hWU : W ≤ U), W ≤ V i → G.obj.map (homOfLE hWU).op (a i) = 0)
    (N : κ → Opens X) (hNU : ∀ k, N k ≤ U) (hN : U ≤ ⨆ k, N k) (S : κ → Finset ι)
    (hSV : ∀ k i, i ∉ S k → N k ≤ V i) :
    ∃ b : G.obj.obj (op U), ∀ k,
      G.obj.map (homOfLE (hNU k)).op b =
        ∑ i ∈ S k, G.obj.map (homOfLE (hNU k)).op (a i) := by
  classical
  let sf : ∀ k : κ, G.obj.obj (op (N k)) :=
    fun k ↦ ∑ i ∈ S k, G.obj.map (homOfLE (hNU k)).op (a i)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj N sf := by
    intro k₁ k₂
    let W := N k₁ ⊓ N k₂
    have hWU : W ≤ U := inf_le_left.trans (hNU k₁)
    have hrestrict (k : κ) (hWN : W ≤ N k) (hs : S k ⊆ S k₁ ∪ S k₂) :
        G.obj.map (homOfLE hWN).op (sf k) =
          ∑ i ∈ S k₁ ∪ S k₂, G.obj.map (homOfLE hWU).op (a i) := by
      simp only [sf, map_sum]
      have hterm (i : ι) :
          G.obj.map (homOfLE hWN).op (G.obj.map (homOfLE (hNU k)).op (a i)) =
            G.obj.map (homOfLE hWU).op (a i) := by
        rw [← Functor.map_comp_apply]
        exact congrArg (fun f : W ⟶ U ↦ G.obj.map f.op (a i)) (Subsingleton.elim _ _)
      simp_rw [hterm]
      exact Finset.sum_subset hs fun i _ hi ↦ ha i hWU (hWN.trans (hSV k i hi))
    exact (hrestrict k₁ inf_le_left Finset.subset_union_left).trans
      (hrestrict k₂ inf_le_right Finset.subset_union_right).symm
  obtain ⟨b, hb, -⟩ := G.existsUnique_gluing' N U (fun k ↦ homOfLE (hNU k)) hN sf hcompat
  exact ⟨b, hb⟩

end TopCat.Sheaf
