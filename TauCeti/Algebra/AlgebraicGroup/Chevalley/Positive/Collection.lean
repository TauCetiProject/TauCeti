/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2

/-!
# Positive-root product collection for a Chevalley datum

For **any** Chevalley datum `D` of **any** valid Dynkin type, every element of the positive-root
subgroup is a product with one factor from each positive root subgroup, in any enumeration without
repetition. This holds on the base-changed admissible lattice (`D.positiveSubgroup A`) and inside
the datum's point group (`D.positivePoints A`) over every commutative ring, without restriction on
lacing, isogeny type, reducedness, or characteristic. It is the existence half of positive-root
coordinates; uniqueness is proved in `TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct` and
combined with collection in `TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.positiveSubgroup_eq_iSup` and
  `TauCeti.DynkinType.ChevalleyDatum.positivePoints_eq_iSup`: the positive lattice and point
  subgroups are the suprema of the positive root subgroups.
* `TauCeti.DynkinType.ChevalleyDatum.mem_positiveSubgroup_iff_exists_prod`: every positive lattice
  automorphism factors as an ordered product along any duplicate-free cover of positive roots.
* `TauCeti.DynkinType.ChevalleyDatum.mem_positivePoints_iff_exists_prod`: every positive point of
  `D` over a commutative ring `A` factors as an ordered product of positive root points.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, §5.3.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

/-- The positive lattice subgroup is the supremum of the ranges of the positive root maps. -/
theorem positiveSubgroup_eq_iSup (A : CommAlgCat.{v} ℤ) :
    D.positiveSubgroup A =
      ⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator γ A).range := by
  apply le_antisymm
  · exact D.positiveSubgroup_le_iff.mpr fun γ hγ u =>
      Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ ⟨u, rfl⟩)
  · exact iSup₂_le fun γ hγ => by
      rintro _ ⟨u, rfl⟩
      exact D.chevalleyRootSubgroup_mem_positiveSubgroup A hγ u

/-- The positive point subgroup is the supremum of the ranges of the positive root-point maps. -/
theorem positivePoints_eq_iSup (A : Type v) [CommRing A] :
    D.positivePoints A =
      ⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        (D.rootSubgroupPoints γ A).range := by
  apply le_antisymm
  · exact D.positivePoints_le_iff.mpr fun γ hγ u =>
      Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ ⟨u, rfl⟩)
  · exact iSup₂_le fun γ hγ => by
      rintro _ ⟨u, rfl⟩
      exact D.rootSubgroupPoints_mem_positivePoints A hγ u

private theorem exists_fin6_list_of_posRoots_g2 {ht : G2.Valid}
    {l : List (Fin G2.numRoots)} (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht)) :
    ∃ l₆ : List (Fin 6), l₆.Nodup ∧ (∀ i, i ∈ l₆) ∧
      l₆.map (Fin.castAdd 6 : Fin 6 → Fin G2.numRoots) = l := by
  let emb : Fin 6 → Fin G2.numRoots := Fin.castAdd 6
  let l₆ : List (Fin 6) := l.attach.map fun ⟨γ, hγ⟩ =>
    ⟨γ.val, (mem_posRoots_rational_g2_iff ht γ).mp ((hcover γ).mp hγ)⟩
  have hmap : l₆.map emb = l := by
    dsimp only [l₆]
    rw [List.map_map]
    refine Eq.trans (List.map_congr_left ?_) l.attach_map_subtype_val
    rintro ⟨γ, hγ⟩ _
    rfl
  refine ⟨l₆, List.Nodup.of_map emb (hmap.symm ▸ hl), fun i => ?_, hmap⟩
  have hi : emb i ∈ l :=
    (hcover _).mpr ((mem_posRoots_rational_g2_iff ht _).mpr i.isLt)
  obtain ⟨j, hj, hji⟩ := List.mem_map.mp (hmap.symm ▸ hi)
  exact Fin.castAdd_injective 6 _ hji ▸ hj

/-- Every element of the positive lattice subgroup of a Chevalley datum has an ordered
root-product expression along any duplicate-free enumeration of all positive roots, over every
commutative `ℤ`-algebra and in every valid Dynkin type. -/
theorem mem_positiveSubgroup_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat.{v} ℤ)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)) :
    g ∈ D.positiveSubgroup A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A (u γ)).prod =
        g := by
  rw [D.positiveSubgroup_eq_iSup A]
  by_cases hG2 : t = .G2
  · subst hG2
    obtain ⟨l₆, hl₆, hall, hmap⟩ := exists_fin6_list_of_posRoots_g2 hl hcover
    have hF (F : Fin G2.numRoots → LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)) :
        (l.map F).prod = (l₆.map fun i => F (Fin.castAdd 6 i)).prod := by
      rw [← hmap]
      exact congrArg List.prod List.map_map
    rw [mem_biSup_posRoots_g2_iff_exists_list_prod_map D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A l₆ hl₆ hall g]
    constructor
    · rintro ⟨f, hf⟩
      refine ⟨fun γ => if h : γ.val < 6 then Multiplicative.ofAdd (f ⟨γ.val, h⟩) else 1, ?_⟩
      rw [hF]
      refine Eq.trans (congrArg List.prod (List.map_congr_left fun i _ => ?_)) hf
      exact congrArg _ (by simp [i.isLt])
    · rintro ⟨u, hu⟩
      refine ⟨fun i => (u (Fin.castAdd 6 i)).toAdd, ?_⟩
      rw [hF] at hu
      simpa only [ofAdd_toAdd] using hu
  · have := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) hG2
    rw [mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A l hl hcover g]
    exact ⟨fun ⟨u, hu⟩ => ⟨fun γ => Multiplicative.ofAdd (u γ), hu⟩,
      fun ⟨u, hu⟩ => ⟨fun γ => (u γ).toAdd, by simpa only [ofAdd_toAdd] using hu⟩⟩

/-- Every element of the positive point subgroup of a Chevalley datum factors as an ordered
product of positive root points along any duplicate-free enumeration of all positive roots, over
every commutative ring and in every valid Dynkin type. -/
theorem mem_positivePoints_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : Fin t.numRoots → A,
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod = g := by
  constructor
  · intro hg
    obtain ⟨h, hh, hmat⟩ := D.mem_positivePoints_iff.mp hg
    obtain ⟨u, rfl⟩ := (D.mem_positiveSubgroup_iff_exists_prod l hl hcover
      (CommAlgCat.of ℤ A) h).mp hh
    refine ⟨fun γ => (u γ).toAdd, (D.points A).subtype_injective ?_⟩
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.coe_subtype,
      D.coe_rootSubgroupPoints, ofAdd_toAdd, MulEquiv.toMonoidHom_eq_coe] using hmat
  · rintro ⟨u, rfl⟩
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    exact D.rootSubgroupPoints_mem_positivePoints A ((hcover γ).mp hγ) _

end TauCeti.DynkinType.ChevalleyDatum
