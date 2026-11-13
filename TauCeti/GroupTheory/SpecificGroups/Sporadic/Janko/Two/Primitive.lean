/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Janko.Two.Orbits
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitivity of the second Janko group's canonical action

The canonical ATLAS model `TauCeti.Sporadic.J2` acts primitively on its 100 points.
The stabilizer of `0` has orbits of sizes `1`, `63` and `36`. A block containing `0`
is a union of these orbits, so has size `1`, `64`, `37` or `100`. Since its size
must divide `100`, it is trivial.

The 36-point orbit is certified by explicit words in the canonical generators. Their
point images are checked by the kernel. This concerns the permutation model, not
recognition of an abstract presentation.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  representation `J2G1-p100B0`, <https://brauer.maths.qmul.ac.uk/Atlas/v3/>.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.5, for blocks and primitivity.
-/

public section

namespace TauCeti.Sporadic

namespace J2

open MulAction
open scoped Pointwise

private def fourPoint (i : Fin 36) : Fin 100 :=
  (#[4, 5, 7, 10, 11, 16, 18, 20, 21, 26, 33, 36, 38, 44, 46, 48, 50, 51, 52, 53, 54, 55,
    59, 60, 61, 65, 68, 71, 78, 79, 80, 83, 84, 87, 91, 92] : Array (Fin 100)).getD i.val 0

private def fourPoints : Finset (Fin 100) := Finset.univ.image fourPoint

-- Breadth-first search on ordered pairs supplies words carrying `(0, 4)` to `(0, x)`.
-- Lists multiply left to right; the rightmost permutation acts first.
private def witness (i : Fin 36) : J2 :=
  let words : Array (List (Fin 2)) := #[
    [],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0,
      1, 0, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0,
      1, 0, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]]
  ((words.getD i.val []).map fun j ↦
    (![⟨a, a_mem⟩, ⟨b, b_mem⟩] : Fin 2 → J2) j).prod

private theorem witness_spec : ∀ i,
    (witness i : Equiv.Perm (Fin 100)) 0 = 0 ∧
      (witness i : Equiv.Perm (Fin 100)) 4 = fourPoint i := by
  decide +kernel

private theorem fourPoints_subset_orbit :
    (fourPoints : Set (Fin 100)) ⊆ orbit (J2.stabilizerChain basePoint 1) 4 := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hw := witness_spec i
  refine mem_orbit_iff.mpr ⟨⟨(witness i : Equiv.Perm (Fin 100)), ?_⟩, ?_⟩
  · rw [Subgroup.stabilizerChain_succ, Subgroup.stabilizerChain_zero]
    exact ⟨(witness i).2, by simpa [mem_stabilizer_iff, basePoint_def] using hw.1⟩
  · simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using hw.2

private theorem mem_fourPoints (x : Fin 100) :
    x ∈ fourPoints ↔ x ≠ 0 ∧
      x ∉ orbit (J2.stabilizerChain basePoint 1) (basePoint 1) := by
  rw [orbit_stabilizer_zero_one]
  revert x
  decide +kernel

private theorem orbit_four_eq :
    orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100) = fourPoints := by
  apply Set.Subset.antisymm ?_ fourPoints_subset_orbit
  intro x hx
  apply (mem_fourPoints x).2
  have h4 : (4 : Fin 100) ∈ fourPoints := by decide +kernel
  refine ⟨?_, fun h ↦ (mem_fourPoints 4).mp h4 |>.2 ?_⟩
  · rintro rfl
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hx
    have hfix := (Subgroup.mem_stabilizerChain_iff J2 basePoint).mp g.2
    have hz : g • (0 : Fin 100) = 0 := by
      simpa [basePoint_def, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hfix.2 0 (by decide)
    exact (by decide : (4 : Fin 100) ≠ 0) ((MulAction.injective g) (hg.trans hz.symm))
  · exact mem_orbit_trans (mem_orbit_symm.mp hx) h

/-- The complementary nontrivial orbit of the stabilizer of `0` in the canonical model. -/
theorem orbit_stabilizer_zero_four :
    orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100) =
      ({4, 5, 7, 10, 11, 16, 18, 20, 21, 26, 33, 36, 38, 44, 46, 48, 50, 51, 52, 53, 54, 55,
        59, 60, 61, 65, 68, 71, 78, 79, 80, 83, 84, 87, 91, 92} : Finset (Fin 100)) := by
  rw [orbit_four_eq]
  congr 1

/-- The complementary stabilizer orbit has 36 points. -/
@[simp]
theorem ncard_orbit_stabilizer_zero_four :
    (orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100)).ncard = 36 := by
  rw [orbit_stabilizer_zero_four, Set.ncard_coe_finset]
  decide +kernel

private theorem orbit_subset_block {B : Set (Fin 100)} (hB : IsBlock J2 B)
    (h0 : 0 ∈ B) {x : Fin 100} (hx : x ∈ B) :
    orbit (J2.stabilizerChain basePoint 1) x ⊆ B := by
  rintro y ⟨g, rfl⟩
  have hg := (Subgroup.mem_stabilizerChain_iff J2 basePoint).mp g.2
  let g' : J2 := ⟨g, hg.1⟩
  have hfix : g' ∈ stabilizer J2 (0 : Fin 100) := by
    simpa [mem_stabilizer_iff, basePoint_def, g', Subgroup.smul_def] using
      hg.2 0 (by decide)
  have hset := hB.stabilizer_le h0 hfix
  rw [mem_stabilizer_iff] at hset
  exact hset ▸ Set.smul_mem_smul_set hx

private theorem block_ncard {B : Set (Fin 100)} (hB : IsBlock J2 B) (h0 : 0 ∈ B) :
    B.ncard = 1 ∨ B.ncard = 37 ∨ B.ncard = 64 ∨ B.ncard = 100 := by
  classical
  let O₁ := orbit (J2.stabilizerChain basePoint 1) (basePoint 1)
  let O₄ := orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100)
  have hpartition (x : Fin 100) : x = 0 ∨ x ∈ O₁ ∨ x ∈ O₄ := by
    dsimp only [O₄]
    rw [orbit_four_eq]
    by_cases hx : x = 0
    · exact Or.inl hx
    · by_cases h : x ∈ O₁
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((mem_fourPoints x).2 ⟨hx, h⟩))
  have hsat {x y : Fin 100} (hx : x ∈ B)
      (hy : y ∈ orbit (J2.stabilizerChain basePoint 1) x) : y ∈ B :=
    orbit_subset_block hB h0 hx hy
  have hset : B = {0} ∪ (if (basePoint 1) ∈ B then O₁ else ∅) ∪
      (if (4 : Fin 100) ∈ B then O₄ else ∅) := by
    ext x
    constructor
    · intro hx
      rcases hpartition x with rfl | hx₁ | hx₄
      · simp
      · have h1 := hsat hx (mem_orbit_symm.mp hx₁)
        simp [h1, hx₁]
      · have h4 := hsat hx (mem_orbit_symm.mp hx₄)
        simp [h4, hx₄]
    · intro hx
      simp only [Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | hx₁) | hx₄
      · exact h0
      · split_ifs at hx₁ with h1
        · exact hsat h1 hx₁
        · exact hx₁.elim
      · split_ifs at hx₄ with h4
        · exact hsat h4 hx₄
        · exact hx₄.elim
  rw [hset]
  dsimp only [O₁, O₄]
  rw [orbit_stabilizer_zero_one, orbit_stabilizer_zero_four]
  split_ifs <;>
    simp only [← Finset.coe_singleton, ← Finset.coe_empty, ← Finset.coe_union,
      Set.ncard_coe_finset] <;> decide +kernel

end J2

/-- The canonical 100-point action of the second Janko group is primitive. -/
instance isPreprimitive_J2 : MulAction.IsPreprimitive J2 (Fin 100) := by
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (0 : Fin 100)
  intro B h0 hB
  have hdvd := hB.ncard_dvd_card ⟨0, h0⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
  rcases J2.block_ncard hB h0 with h | h | h | h
  · exact Or.inl (Set.ncard_le_one_iff_subsingleton.mp h.le)
  · norm_num [h] at hdvd
  · norm_num [h] at hdvd
  · exact Or.inr ((Set.eq_univ_iff_ncard B).2 (by simpa using h))

end TauCeti.Sporadic
