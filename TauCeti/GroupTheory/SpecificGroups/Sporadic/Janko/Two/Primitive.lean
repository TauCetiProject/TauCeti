/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Janko.Two.Orbits
public import TauCeti.GroupTheory.GroupAction.Primitive

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

open _root_.MulAction

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
  have h0 : basePoint 0 = 0 := by rw [basePoint_def]; decide
  rw [Subgroup.stabilizerChain_succ, Subgroup.stabilizerChain_zero, h0]
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hfix, himage⟩ := witness_spec i
  have hmem :
      (witness i : Equiv.Perm (Fin 100)) ∈ stabilizer (Equiv.Perm (Fin 100)) (0 : Fin 100) := by
    simpa only [mem_stabilizer_iff, Equiv.Perm.smul_def] using hfix
  refine mem_orbit_iff.mpr ⟨⟨witness i, (witness i).property, hmem⟩, ?_⟩
  simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using himage

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
    have h0 : basePoint 0 = 0 := by rw [basePoint_def]; decide
    rw [Subgroup.stabilizerChain_succ, Subgroup.stabilizerChain_zero, h0] at hx
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hx
    have hz : g • (0 : Fin 100) = 0 := by
      simpa only [Subgroup.smul_def] using mem_stabilizer_iff.mp g.property.2
    exact (by decide : (4 : Fin 100) ≠ 0) ((MulAction.injective g) (hg.trans hz.symm))
  · exact mem_orbit_trans (mem_orbit_symm.mp hx) h

/-- The complementary nontrivial orbit of the stabilizer of `0` in the canonical model. -/
theorem orbit_stabilizer_zero_four :
    orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100) =
      ({4, 5, 7, 10, 11, 16, 18, 20, 21, 26, 33, 36, 38, 44, 46, 48, 50, 51, 52, 53, 54, 55,
        59, 60, 61, 65, 68, 71, 78, 79, 80, 83, 84, 87, 91, 92} : Finset (Fin 100)) := by
  rw [orbit_four_eq, Finset.coe_inj]
  decide +kernel

/-- The complementary stabilizer orbit has 36 points. -/
@[simp]
theorem ncard_orbit_stabilizer_zero_four :
    (orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100)).ncard = 36 := by
  rw [orbit_stabilizer_zero_four, Set.ncard_coe_finset]
  decide +kernel

private theorem orbit_stabilizer_zero_cover (x : Fin 100) :
    x = 0 ∨ x ∈ orbit (J2.stabilizerChain basePoint 1) (basePoint 1) ∨
      x ∈ orbit (J2.stabilizerChain basePoint 1) (4 : Fin 100) := by
  rw [orbit_four_eq]
  by_cases hx : x = 0
  · exact Or.inl hx
  · by_cases h : x ∈ orbit (J2.stabilizerChain basePoint 1) (basePoint 1)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((mem_fourPoints x).2 ⟨hx, h⟩))

end J2

/-- The canonical 100-point action of the second Janko group is primitive. -/
instance isPreprimitive_J2 : MulAction.IsPreprimitive J2 (Fin 100) := by
  have hbridge (x : Fin 100) :
      MulAction.orbit (MulAction.stabilizer J2 (J2.basePoint 0)) x =
        MulAction.orbit (J2.stabilizerChain J2.basePoint 1) x := by
    exact (congrArg (fun H : Subgroup (Equiv.Perm (Fin 100)) ↦
      MulAction.orbit (MulAction.stabilizer H (J2.basePoint 0)) x)
      (Subgroup.stabilizerChain_zero J2 J2.basePoint)).symm.trans
      (Subgroup.orbit_stabilizerChain_succ J2 J2.basePoint 0 x).symm
  have h0 : J2.basePoint 0 = 0 := by rw [J2.basePoint_def]; decide
  apply MulAction.IsPreprimitive.of_two_orbit_stabilizer
    (J2.basePoint 0) (J2.basePoint 1) (4 : Fin 100)
  · intro x
    rw [hbridge, hbridge, h0]
    exact J2.orbit_stabilizer_zero_cover x
  · rw [hbridge, J2.ncard_orbit_stabilizer_zero_one]
    norm_num
  · rw [hbridge, J2.ncard_orbit_stabilizer_zero_four]
    norm_num

end TauCeti.Sporadic
