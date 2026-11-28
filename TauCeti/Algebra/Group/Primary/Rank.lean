/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Basic
public import TauCeti.GroupTheory.PGroup
public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Generator rank of finite abelian `p`-groups

For a finite abelian `p`-group `G` (`IsAddPGroup p G` with `p` prime), the Frattini / Burnside
reduction identifies the minimal number of generators `AddGroup.rank G` with the `ZMod p`-dimension
of `ModN G p = G / pG`. Because `ModN · p` distributes `ZMod p`-linearly over products
(`ModN.prodLinearEquiv`, `ModN.piLinearEquiv`), generator rank is **additive** on products of finite
abelian `p`-groups, and hence on `p`-primary components of binary products of finite abelian groups.

## Main definitions and statements

* `IsAddPGroup.eq_top_of_map_mkQ_eq_top`: a subgroup of a finite abelian `p`-group is `⊤` if
  its image in `ModN G p` is `⊤`.
* `IsAddPGroup.rank_eq_finrank_modN`: `AddGroup.rank G = finrank (ZMod p) (ModN G p)` for a finite
  abelian `p`-group `G`.
* `IsAddPGroup.rank_prod`, `IsAddPGroup.rank_pi`: generator rank is additive on products of finite
  abelian `p`-groups.
* `AddGroup.rank_primaryComponent_prod`: additivity of `l(A_p)` on binary products of finite
  abelian groups.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace IsAddPGroup

/-- An additive subgroup of a finite abelian `p`-group is `⊤` if its image under `ModN.mkQ p` is
`⊤`. -/
theorem eq_top_of_map_mkQ_eq_top {p : ℕ} {G : Type*} [AddCommGroup G] [Finite G]
    (hG : IsAddPGroup p G) {H : AddSubgroup G} (hmap : H.map (ModN.mkQ p) = ⊤) :
    H = ⊤ := by
  have hstep (g : G) : ∃ h ∈ H, ∃ g' : G, g = h + p • g' := by
    have hmem : ModN.mkQ p g ∈ H.map (ModN.mkQ p) := hmap ▸ trivial
    obtain ⟨h, hh, hgh⟩ := hmem
    have hsub : g - h ∈ LinearMap.range (LinearMap.lsmul ℤ G (p : ℤ)) :=
      (Submodule.Quotient.eq _).mp hgh.symm
    obtain ⟨g', hg'⟩ := hsub
    refine ⟨h, hh, g', ?_⟩
    calc g = h + (g - h) := (add_sub_cancel h g).symm
      _ = h + p • g' := by
        rw [← hg', LinearMap.lsmul_apply, natCast_zsmul]
  have hiter (k : ℕ) : ∀ g : G, ∃ h ∈ H, ∃ g' : G, g = h + p ^ k • g' := by
    induction k with
    | zero =>
        intro g
        exact ⟨0, H.zero_mem, g, by simp⟩
    | succ k ih =>
        intro g
        obtain ⟨h₁, hh₁, g₁, rfl⟩ := ih g
        obtain ⟨h₂, hh₂, g₂, rfl⟩ := hstep g₁
        refine ⟨h₁ + p ^ k • h₂, H.add_mem hh₁ (H.nsmul_mem hh₂ _), g₂, ?_⟩
        rw [nsmul_add, add_assoc, smul_smul, ← pow_succ]
  obtain ⟨K, hkill⟩ := isAddPGroup_iff_exists_pow_nsmul_eq_zero.mp hG
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨h, hh, g', rfl⟩ := hiter K x
  simpa [hkill g'] using hh

/-- **Burnside basis theorem for finite abelian `p`-groups**: for prime `p`, the minimal number of
generators `AddGroup.rank G` of a finite abelian `p`-group `G` equals
`finrank (ZMod p) (ModN G p)`. -/
theorem rank_eq_finrank_modN {p : ℕ} (hp : p.Prime) {G : Type*} [AddCommGroup G] [Finite G]
    (hG : IsAddPGroup p G) :
    AddGroup.rank G = Module.finrank (ZMod p) (ModN G p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hsurj : Function.Surjective (ModN.mkQ (G := G) p) := Submodule.mkQ_surjective _
  rw [← AddGroup.rank_eq_finrank_zmod (ModN G p)]
  refine le_antisymm ?_ (AddGroup.rank_le_of_surjective (ModN.mkQ p) hsurj)
  -- Any lift of a generating set of `G / pG` generates `G` modulo `p • G`, hence modulo `p ^ k • G`
  -- for every `k`, and `p ^ k • G = 0` for large `k`.
  obtain ⟨S, hScard, hS⟩ := AddGroup.rank_spec (ModN G p)
  let T : Finset G := S.image (Function.surjInv hsurj)
  have hmap : (AddSubgroup.closure (T : Set G)).map (ModN.mkQ p) = ⊤ := by
    dsimp only [T]
    rw [AddMonoidHom.map_closure, Finset.coe_image, ← Set.image_comp,
      Function.comp_surjInv hsurj, Set.image_id, hS]
  exact (AddGroup.rank_le (S := T) (hG.eq_top_of_map_mkQ_eq_top hmap)).trans
    (Finset.card_image_le.trans_eq hScard)

/-- Generator rank is additive on binary products of finite abelian `p`-groups. -/
theorem rank_prod {p : ℕ} (hp : p.Prime) {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Finite G] [Finite H] (hG : IsAddPGroup p G) (hH : IsAddPGroup p H) :
    AddGroup.rank (G × H) = AddGroup.rank G + AddGroup.rank H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite (ZMod p) (ModN G p) := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (ModN H p) := Module.Finite.of_finite
  rw [(IsAddPGroup.prod hG hH).rank_eq_finrank_modN hp, hG.rank_eq_finrank_modN hp,
    hH.rank_eq_finrank_modN hp, (ModN.prodLinearEquiv G H p).finrank_eq, Module.finrank_prod]

/-- Generator rank is additive on finite indexed products of finite abelian `p`-groups. -/
theorem rank_pi {p : ℕ} (hp : p.Prime) {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Finite (G i)] (hG : ∀ i, IsAddPGroup p (G i)) :
    AddGroup.rank (∀ i, G i) = ∑ i, AddGroup.rank (G i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : ∀ i, Module.Finite (ZMod p) (ModN (G i) p) := fun _ ↦ Module.Finite.of_finite
  rw [(IsAddPGroup.pi hG).rank_eq_finrank_modN hp, (ModN.piLinearEquiv G p).finrank_eq,
    Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ ((hG i).rank_eq_finrank_modN hp).symm

end IsAddPGroup

namespace AddGroup

/-- On any binary product of finite abelian groups, the generator rank of the `p`-primary component
is additive for prime `p`. -/
theorem rank_primaryComponent_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B] {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (AddCommGroup.primaryComponent (A × B) p) =
      AddGroup.rank (AddCommGroup.primaryComponent A p) +
        AddGroup.rank (AddCommGroup.primaryComponent B p) := by
  rw [AddGroup.rank_congr (AddCommGroup.primaryComponentProdAddEquiv A B p),
    (AddCommGroup.primaryComponent.isAddPGroup A p).rank_prod hp
      (AddCommGroup.primaryComponent.isAddPGroup B p)]

end AddGroup
