/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Orbits
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitivity of the Higman--Sims action

The canonical ATLAS Higman--Sims model acts primitively on its 100 points. The stabilizer of
`0` has three orbits, of lengths 1, 22 and 77. A block containing `0` is a union of these
orbits, so its size is 1, 23, 78 or 100. Since a block size divides the degree, only the
trivial blocks occur. This supplies the primitive action used in studying normal subgroups
of the model; it does not identify the abstract Higman--Sims presentation with this model.

The 22-point orbit is certified by explicit words in the existing ATLAS generators, using
Mathlib's convention that the last letter acts first. Its upper bound follows from the
already established 77-point orbit and disjointness of orbits.

The stabilizer of `0` acts doubly transitively on the 22-point orbit: further explicit words fix
`0` and `4` and carry `8` to each of the other 20 points of the orbit.

## Main results

* `TauCeti.Sporadic.HS.orbit_stabilizerChain_one_four`: the 22-point orbit of the stabilizer
  of `0`.
* `TauCeti.Sporadic.HS.isPreprimitive`: the action of the model on its 100 points is primitive.
* `TauCeti.Sporadic.HS.isMultiplyPretransitive_stabilizer_orbit`: the stabilizer of `0` acts
  doubly transitively on its 22-point orbit.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `HSG1-p100B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/HSG1-p100B0>.
* D. G. Higman and C. C. Sims, *A simple group of order 44,352,000*, Math. Z. **105** (1968),
  110–113, for the rank-three action with suborbits of lengths 1, 22 and 77.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.5 (blocks and primitivity).
-/

public section

namespace TauCeti.Sporadic.HS

open MulAction
open scoped Pointwise

local notation "S" => HS.stabilizerChain pointSequence 1

private def smallOrbit : Finset (Fin 100) :=
  {4, 8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44, 47, 49, 50, 52, 66, 67, 70, 71, 91}

private def orbitPoints : Fin 22 → Fin 100 :=
  ![4, 8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44, 47, 49, 50, 52, 66, 67, 70, 71, 91]

private abbrev aa : HS := ⟨a, a_mem⟩
private abbrev bb : HS := ⟨b, b_mem⟩

-- Breadth-first paths on ordered pairs, from (0, 4) to (0, orbitPoints i).
private def orbitWords : Fin 22 → List HS :=
  ![[],
    [aa, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb],
    [aa, bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa],
    [aa, bb, bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb],
    [bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, aa, bb, bb, bb],
    [bb, bb, aa, bb, bb, aa, bb, bb, aa, bb, aa, bb, bb, aa, bb],
    [bb, bb, aa, bb, bb, bb],
    [bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, aa],
    [bb, bb, bb, aa, bb, aa, bb, aa, bb, aa, bb, aa, bb, bb, aa],
    [aa, bb, aa, bb, bb, aa, bb, aa, bb, aa, bb, aa, bb, aa, bb, aa],
    [bb, aa, bb, aa, bb, bb, aa, bb, bb, aa, bb, aa, bb, aa],
    [aa, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa],
    [bb, aa, bb, aa, bb, bb, bb, aa, bb, aa, bb, bb, aa],
    [bb, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, aa, bb],
    [bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, bb, bb, aa, bb, bb, aa, bb],
    [bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, bb],
    [bb, bb, bb, aa, bb, bb, aa, bb, bb, aa, bb, aa, bb, aa, bb, aa, bb, aa, bb],
    [bb, bb, aa, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, aa, bb],
    [aa, bb, aa, bb, bb, aa, bb, bb, aa, bb, bb, aa, bb, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, aa, bb, bb, aa, bb],
    [bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, aa]]

private theorem orbitWords_apply : ∀ i,
    ((orbitWords i).prod : Equiv.Perm (Fin 100)) 0 = 0 ∧
      ((orbitWords i).prod : Equiv.Perm (Fin 100)) 4 = orbitPoints i := by
  decide +kernel

private theorem mem_smallOrbit : ∀ x, x ∈ smallOrbit ↔ ∃ i, orbitPoints i = x := by
  decide +kernel

private theorem mem_largeOrbit : ∀ x : Fin 100,
    x ∈ orbit S (1 : Fin 100) ↔ x ≠ 0 ∧ x ∉ smallOrbit := by
  simp only [orbit_stabilizerChain_one]
  decide +kernel

private theorem mem_stabilizerChain_one_iff {g : Equiv.Perm (Fin 100)} :
    g ∈ S ↔ g ∈ HS ∧ g 0 = 0 := by
  simp [Subgroup.stabilizerChain_succ, pointSequence_apply]

private theorem orbit_stabilizerChain_one_four_eq :
    orbit S (4 : Fin 100) = (↑smallOrbit : Set (Fin 100)) := by
  ext x
  rw [Finset.mem_coe]
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by
      intro h
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp (mem_orbit_symm.mp (h ▸ hx))
      have hg0 := (mem_stabilizerChain_one_iff.mp g.property).2
      rw [Subgroup.smul_def, Equiv.Perm.smul_def, hg0] at hg
      exact (by decide : (0 : Fin 100) ≠ 4) hg
    by_contra hn
    have hx1 := (mem_largeOrbit x).mpr ⟨hx0, hn⟩
    have h41 := mem_orbit_trans (mem_orbit_symm.mp hx) hx1
    exact ((mem_largeOrbit 4).mp h41).2 (by decide +kernel)
  · intro hx
    obtain ⟨i, rfl⟩ := (mem_smallOrbit x).mp hx
    obtain ⟨h0, h4⟩ := orbitWords_apply i
    apply mem_orbit_iff.mpr
    refine ⟨⟨((orbitWords i).prod : Equiv.Perm (Fin 100)), ?_⟩, ?_⟩
    · exact mem_stabilizerChain_one_iff.mpr ⟨(orbitWords i).prod.property, h0⟩
    · simpa only [Subgroup.mk_smul, Equiv.Perm.smul_def] using h4

/-- The other nontrivial orbit of the stabilizer of `0` in the canonical Higman--Sims model. -/
theorem orbit_stabilizerChain_one_four :
    orbit S (4 : Fin 100) =
      (↑({4, 8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44, 47, 49, 50, 52, 66, 67, 70,
        71, 91} : Finset (Fin 100)) : Set (Fin 100)) := by
  simpa only [smallOrbit] using orbit_stabilizerChain_one_four_eq

/-- The stabilizer of `0` has a 22-point orbit containing `4`. -/
@[simp]
theorem ncard_orbit_stabilizerChain_one_four :
    (orbit S (4 : Fin 100)).ncard = 22 := by
  rw [orbit_stabilizerChain_one_four, Set.ncard_coe_finset]
  decide +kernel

-- A block through zero is invariant under its point stabilizer.
private theorem orbit_subset_block (B : Set (Fin 100)) (h0 : 0 ∈ B) (hB : IsBlock HS B)
    {x : Fin 100} (hx : x ∈ B) : orbit S x ⊆ B := by
  intro y hy
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hy
  have hg := mem_stabilizerChain_one_iff.mp g.property
  let g' : HS := ⟨g, hg.1⟩
  have hg' : g' ∈ stabilizer HS (0 : Fin 100) := by
    simpa only [mem_stabilizer_iff, g', Subgroup.mk_smul, Equiv.Perm.smul_def] using hg.2
  have hfix := mem_stabilizer_iff.mp (hB.stabilizer_le h0 hg')
  rw [Subgroup.smul_def, ← Subgroup.mk_smul _ hg.1, ← hfix]
  exact Set.smul_mem_smul_set hx

-- Membership is constant on each of the two nontrivial stabilizer orbits.
private theorem mem_block_iff (B : Set (Fin 100)) (h0 : 0 ∈ B) (hB : IsBlock HS B)
    (x : Fin 100) :
    x ∈ B ↔ x = 0 ∨ (x ∈ orbit S (1 : Fin 100) ∧ 1 ∈ B) ∨
      (x ∈ smallOrbit ∧ 4 ∈ B) := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    by_cases hxs : x ∈ smallOrbit
    · have hx4 : x ∈ orbit S (4 : Fin 100) := by
        rw [orbit_stabilizerChain_one_four_eq, Finset.mem_coe]
        exact hxs
      exact Or.inr (Or.inr ⟨hxs, orbit_subset_block B h0 hB hx (mem_orbit_symm.mp hx4)⟩)
    · have hx1 := (mem_largeOrbit x).mpr ⟨hx0, hxs⟩
      exact Or.inr (Or.inl ⟨hx1, orbit_subset_block B h0 hB hx (mem_orbit_symm.mp hx1)⟩)
  · rintro (rfl | ⟨hx1, h1⟩ | ⟨hxs, h4⟩)
    · exact h0
    · exact orbit_subset_block B h0 hB h1 hx1
    · apply orbit_subset_block B h0 hB h4
      rw [orbit_stabilizerChain_one_four_eq, Finset.mem_coe]
      exact hxs

/-- The canonical 100-point action of the Higman--Sims model is primitive. -/
instance isPreprimitive : IsPreprimitive HS (Fin 100) := by
  apply IsPreprimitive.of_isTrivialBlock_base (0 : Fin 100)
  intro B h0 hB
  -- The two intermediate unions have sizes 78 and 23, neither dividing the degree.
  have hdvd : B.ncard ∣ 100 := by
    simpa using hB.ncard_dvd_card ⟨0, h0⟩
  by_cases h1 : (1 : Fin 100) ∈ B <;> by_cases h4 : (4 : Fin 100) ∈ B
  · right
    apply Set.eq_univ_of_forall
    intro x
    rw [mem_block_iff B h0 hB, mem_largeOrbit]
    tauto
  · have hEq : B = (↑(Finset.univ \ smallOrbit) : Set (Fin 100)) := by
      ext x
      rw [mem_block_iff B h0 hB]
      simp only [mem_largeOrbit, h1, h4, and_true, and_false, or_false,
        Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and]
      have : (0 : Fin 100) ∉ smallOrbit := by decide +kernel
      grind
    have hcard : B.ncard = 78 := by
      rw [hEq, Set.ncard_coe_finset]
      decide +kernel
    norm_num [hcard] at hdvd
  · have hEq : B = (↑(insert 0 smallOrbit) : Set (Fin 100)) := by
      ext x
      rw [mem_block_iff B h0 hB]
      simp [h1, h4]
    have hcard : B.ncard = 23 := by
      rw [hEq, Set.ncard_coe_finset]
      decide +kernel
    norm_num [hcard] at hdvd
  · left
    have hEq : B = {0} := by
      ext x
      rw [mem_block_iff B h0 hB]
      simp [h1, h4]
    rw [hEq]
    exact Set.subsingleton_singleton

-- The points other than 4 in the 22-point orbit of the stabilizer of 0.
private def restPoints : Fin 21 → Fin 100 :=
  ![8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44, 47, 49, 50, 52, 66, 67, 70, 71, 91]

-- Breadth-first paths on ordered triples, from (0, 4, 8) to (0, 4, restPoints i). A word is
-- read in Mathlib's product convention: its last letter acts first.
private def restWords : Fin 21 → List HS :=
  ![[],
    [bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [aa, bb, bb, aa, bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, aa, bb, aa, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa,
      bb, bb, aa, bb, aa],
    [aa, bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, aa, bb, aa],
    [bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb,
      bb, bb, bb],
    [bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb],
    [aa, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa],
    [bb, aa, bb, aa, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa,
      bb],
    [bb, bb, bb, aa, bb, aa, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, bb, aa, bb,
      bb, aa, bb, bb, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [bb, aa, bb, aa, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb]]

private theorem restWords_apply : ∀ i,
    ((restWords i).prod : Equiv.Perm (Fin 100)) 0 = 0 ∧
      ((restWords i).prod : Equiv.Perm (Fin 100)) 4 = 4 ∧
      ((restWords i).prod : Equiv.Perm (Fin 100)) 8 = restPoints i := by
  decide +kernel

private theorem exists_restPoints_eq : ∀ x ∈ ({4, 8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44,
    47, 49, 50, 52, 66, 67, 70, 71, 91} : Finset (Fin 100)), x ≠ 4 → ∃ i, restPoints i = x := by
  decide +kernel

/-- The stabilizer of `0` in the Higman--Sims model has the same orbits as the second member of
the stabilizer chain of the model along `pointSequence`. -/
theorem orbit_stabilizer_zero (x : Fin 100) :
    orbit (stabilizer HS (0 : Fin 100)) x = orbit S x := by
  have h0 : pointSequence 0 = 0 := by
    rw [pointSequence_apply]
    decide
  rw [Subgroup.orbit_stabilizerChain_succ, Subgroup.stabilizerChain_zero, h0]

/-- The stabilizer of `0` in the Higman--Sims model acts doubly transitively on its 22-point
orbit, the orbit of `4`. -/
instance isMultiplyPretransitive_stabilizer_orbit :
    IsMultiplyPretransitive (stabilizer HS (0 : Fin 100))
      (orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100)) 2 := by
  have h8 : (8 : Fin 100) ∈ orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100) := by
    rw [orbit_stabilizer_zero, orbit_stabilizerChain_one_four]
    decide
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (a := (⟨4, mem_orbit_self 4⟩ : orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100)))).mpr
  apply is_one_pretransitive_iff.mpr
  have h84 : (8 : Fin 100) ≠ 4 := by decide
  refine IsPretransitive.of_orbit (x₀ := ⟨⟨8, h8⟩,
    (SubMulAction.mem_ofStabilizer_iff _ _).mpr fun h ↦ h84 (congrArg Subtype.val h)⟩) fun c ↦ ?_
  have hc : c.val.val ∈ orbit S (4 : Fin 100) := orbit_stabilizer_zero 4 ▸ c.val.property
  rw [orbit_stabilizerChain_one_four, Finset.mem_coe] at hc
  have hc4 : c.val.val ≠ 4 := fun h ↦ (SubMulAction.mem_ofStabilizer_iff _ _).mp c.property
      (Subtype.ext h)
  obtain ⟨i, hi⟩ := exists_restPoints_eq _ hc hc4
  obtain ⟨h0, h4, h8'⟩ := restWords_apply i
  -- The word fixes `0` and `4`, so it lies in the stabilizer of `4` in the stabilizer of `0`.
  have hg0 : (restWords i).prod ∈ stabilizer HS (0 : Fin 100) := by
    simpa only [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] using h0
  have hg4 : (⟨(restWords i).prod, hg0⟩ : stabilizer HS (0 : Fin 100)) ∈
      stabilizer (stabilizer HS (0 : Fin 100))
        (⟨4, mem_orbit_self 4⟩ : orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100)) := by
    simpa only [mem_stabilizer_iff, Subtype.ext_iff, orbit.coe_smul, Subgroup.smul_def,
      Equiv.Perm.smul_def] using h4
  refine ⟨⟨⟨(restWords i).prod, hg0⟩, hg4⟩, ?_⟩
  simpa only [Subtype.ext_iff, SubMulAction.val_smul, orbit.coe_smul, Subgroup.smul_def,
    Equiv.Perm.smul_def] using h8'.trans hi

end TauCeti.Sporadic.HS
