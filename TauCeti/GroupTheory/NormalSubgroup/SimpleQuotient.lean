/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Surjecting onto products of simple quotients

Let `f i : G →* H i` be surjections from a group `G` onto a finite family of groups, each of
which is simple or trivial. The image of `G` in `∏ i, H i` need not be the whole product (two of
the `f i` may have the same kernel), but it is the whole product over a suitable subfamily that
already sees all of `G ⧸ ⨅ i, ker (f i)`. This file proves that statement. It is the group
theory behind the description of the Galois group of a compositum of Galois extensions with
simple Galois groups as a product of copies of those groups.

The key step is the two-factor case: for surjections `f : G →* A` and `g : G →* B` with `B`
simple, the pair `(f, g) : G →* A × B` is surjective exactly when `ker f` is not contained in
`ker g`. The image of `ker f` under `g` is then a nontrivial normal subgroup of `B`, hence all of
`B`. This is the simple-group case of Goursat's lemma.

## Main results

* `MonoidHom.surjective_prod_iff_not_ker_le`: for surjections `f : G →* A` and `g : G →* B` with
  `B` simple, `f.prod g` is surjective if and only if `ker f` is not contained in `ker g`.
* `MonoidHom.surjective_pi_insert_of_not_iInf_ker_le`: a simple factor whose kernel does not
  contain the kernel intersection of a subfamily can be added to that subfamily, keeping `G`
  surjecting onto the product.
* `MonoidHom.exists_set_iInf_ker_eq_and_surjective_pi`: surjections onto a finite family of
  simple or trivial groups admit a subfamily of nontrivial targets with the same kernel
  intersection, onto whose product `G` surjects.
-/

public section

namespace MonoidHom

variable {G A B : Type*} [Group G] [Group A] [Group B]

/-- **Surjecting onto a product with a simple factor.** For surjections `f : G →* A` and
`g : G →* B` with `B` simple, the pair `(f, g) : G →* A × B` is surjective if and only if
`ker f` is not contained in `ker g`. -/
theorem surjective_prod_iff_not_ker_le [IsSimpleGroup B] {f : G →* A} {g : G →* B}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (f.prod g) ↔ ¬f.ker ≤ g.ker := by
  refine ⟨fun h hle ↦ ?_, fun h ⟨a, b⟩ ↦ ?_⟩
  · -- A preimage of `(1, b)` with `b ≠ 1` lies in `ker f` but not in `ker g`.
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    obtain ⟨x, hx⟩ := h (1, b)
    simp only [prod_apply, Prod.mk.injEq] at hx
    exact hb (hx.2 ▸ hle hx.1)
  · -- The image of `ker f` is a nontrivial normal subgroup of `B`, so it is all of `B`.
    have hmap : f.ker.map g = ⊤ :=
      ((f.normal_ker.map g hg).eq_bot_or_eq_top).resolve_left
        fun h' ↦ h ((Subgroup.map_eq_bot_iff _).1 h')
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_top ((g x)⁻¹ * b))
    exact ⟨x * y, by simp [mem_ker.1 hy, hgy]⟩

variable {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)]

/-- **Adding a simple factor.** Let `G` surject onto `∏ j ∈ J, H j` via the `f j`, and let
`f i : G →* H i` be a surjection onto a simple group. If `ker (f i)` does not contain the
intersection of the kernels of the `f j`, `j ∈ J`, then `G` also surjects onto
`∏ j ∈ insert i J, H j`. -/
theorem surjective_pi_insert_of_not_iInf_ker_le {f : ∀ i, G →* H i} {J : Set ι} {i : ι}
    [IsSimpleGroup (H i)] (hi : Function.Surjective (f i))
    (hJ : Function.Surjective (MonoidHom.pi fun j : J ↦ f j))
    (hle : ¬(⨅ j ∈ J, (f j).ker) ≤ (f i).ker) :
    Function.Surjective (MonoidHom.pi fun j : ↥(insert i J) ↦ f j) := by
  rw [← iInf_subtype'' J fun j ↦ (f j).ker, ← ker_pi] at hle
  intro t
  obtain ⟨x, hx⟩ := (surjective_prod_iff_not_ker_le hJ hi).2 hle
    (fun j ↦ t ⟨j, Set.mem_insert_of_mem i j.property⟩, t ⟨i, Set.mem_insert i J⟩)
  simp only [prod_apply, Prod.mk.injEq, funext_iff] at hx
  refine ⟨x, funext fun ⟨j, hj⟩ ↦ ?_⟩
  rcases hj with rfl | hj
  · exact hx.2
  · exact hx.1 ⟨j, hj⟩

/-- **Surjecting onto a product of simple quotients.** Let `f i : G →* H i` be surjections onto a
finite family of groups, each simple or trivial. Then there is a set `J` of indices with every
`H j`, `j ∈ J`, nontrivial, such that the kernels of the `f j` with `j ∈ J` have the same
intersection as all the kernels, and `G` surjects onto `∏ j ∈ J, H j`. -/
theorem exists_set_iInf_ker_eq_and_surjective_pi [Finite ι] (f : ∀ i, G →* H i)
    (hf : ∀ i, Function.Surjective (f i)) (hH : ∀ i, Subsingleton (H i) ∨ IsSimpleGroup (H i)) :
    ∃ J : Set ι, (∀ j ∈ J, Nontrivial (H j)) ∧ (⨅ j ∈ J, (f j).ker) = ⨅ i, (f i).ker ∧
      Function.Surjective (MonoidHom.pi fun j : J ↦ f j) := by
  -- Take `J` maximal among the sets of nontrivial indices onto whose product `G` surjects.
  let S : Set (Set ι) :=
    {J | (∀ j ∈ J, Nontrivial (H j)) ∧ Function.Surjective (MonoidHom.pi fun j : J ↦ f j)}
  obtain ⟨J, hJ⟩ := S.toFinite.exists_maximal
    ⟨∅, fun _ h ↦ h.elim, fun _ ↦ ⟨1, funext fun j ↦ j.property.elim⟩⟩
  refine ⟨J, hJ.prop.1, le_antisymm (le_iInf fun i ↦ ?_) (le_iInf₂ fun j _ ↦ iInf_le _ j),
    hJ.prop.2⟩
  rcases hH i with hi | hi
  · -- A homomorphism to a trivial group has kernel `⊤`.
    exact fun x _ ↦ mem_ker.2 (Subsingleton.elim _ _)
  · -- Otherwise `insert i J` would be a larger such set, by
    -- `surjective_pi_insert_of_not_iInf_ker_le`.
    by_contra hle
    have hiJ : insert i J ∈ S :=
      ⟨Set.forall_mem_insert.2 ⟨inferInstance, hJ.prop.1⟩,
        surjective_pi_insert_of_not_iInf_ker_le (hf i) hJ.prop.2 hle⟩
    exact hle (iInf₂_le i (hJ.mem_of_prop_insert hiJ))

end MonoidHom
