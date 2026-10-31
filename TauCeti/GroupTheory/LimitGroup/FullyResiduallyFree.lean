/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.MarkedGroup
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree

/-!
# Fully residually free groups as limits of marked free groups

A finite marking of a fully residually free group is a limit of free markings. To see this,
index approximations by finite subsets of the group. At each index choose a homomorphism to a
free group that preserves the nonidentity elements in that subset. For every fixed word, its
image under the marking is either the identity under every approximation, or is eventually
nonidentity. Thus the corresponding kernels converge pointwise in the space of marked groups.

This is one direction of the identification of finitely generated fully residually free groups
with limit groups. The converse uses equational Noetherianity to reduce all relations of a
marking to finitely many equations before extracting a homomorphism from a nearby free marking.

## Reference

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §3, especially Corollary 3.10.
-/

public section

open Filter Topology

namespace TauCeti.LimitGroup

universe u

variable {G : Type u} [Group G]

/-- Every marking of a fully residually free group is a limit of free markings. A net of free
markings is indexed by finite sets of group elements to be kept nontrivial. -/
theorem IsFullyResiduallyFree.ofMarking_mem_closure_freeMarkings
    (h : IsFullyResiduallyFree G) {n : ℕ} (S : Fin n → G) :
    MarkedGroup.ofMarking S ∈ closure (MarkedGroup.freeMarkings n) := by
  classical
  have hφ (s : Finset G) :
      ∃ φ : G →* FreeGroup (Fin 2), ∀ g ∈ s, g ≠ 1 → φ g ≠ 1 := by
    obtain ⟨φ, hφ⟩ := isFullyResiduallyFree_iff_fin_two.mp h (s.erase 1)
      (by intro g hg; exact (Finset.mem_erase.mp hg).1)
    exact ⟨φ, fun g hg hne => hφ g (Finset.mem_erase.mpr ⟨hne, hg⟩)⟩
  choose φ hφ using hφ
  have hlim : Tendsto (fun s : Finset G => MarkedGroup.ofMarking (φ s ∘ S)) atTop
      (𝓝 (MarkedGroup.ofMarking S)) := by
    rw [MarkedGroup.tendsto_nhds_iff]
    intro w
    have hlift (s : Finset G) : FreeGroup.lift (φ s ∘ S) =
        (φ s).comp (FreeGroup.lift S) :=
      FreeGroup.ext_hom _ _ fun i => by simp
    by_cases hw : FreeGroup.lift S w = 1
    · exact Eventually.of_forall fun s => by
        simp [MarkedGroup.mem_ofMarking_ker, hlift, hw]
    · filter_upwards [eventually_ge_atTop ({FreeGroup.lift S w} : Finset G)] with s hs
      simp only [MarkedGroup.mem_ofMarking_ker, hlift, MonoidHom.comp_apply]
      constructor
      · intro heq
        exact ((hφ s (FreeGroup.lift S w) (Finset.singleton_subset_iff.mp hs) hw) heq).elim
      · intro heq
        exact (hw heq).elim
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun s =>
    MarkedGroup.ofMarking_mem_freeMarkings (φ s ∘ S))

/-- A finitely generated fully residually free group is a limit group. -/
theorem IsFullyResiduallyFree.isLimitGroup (h : IsFullyResiduallyFree G)
    [Group.FG G] : IsLimitGroup G := by
  obtain ⟨n, S, hS⟩ := Group.fg_iff_exists_fin_generating_family.mp ‹Group.FG G›
  exact isLimitGroup_def.mpr ⟨n, S, hS, h.ofMarking_mem_closure_freeMarkings S⟩

end TauCeti.LimitGroup
