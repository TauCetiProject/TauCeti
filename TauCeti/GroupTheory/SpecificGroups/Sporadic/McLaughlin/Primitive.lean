/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.McLaughlin.Orbits
public import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Data.Nat.Bits
import Mathlib.NumberTheory.Divisors

/-!
# Primitivity of the McLaughlin permutation model

The stabilizer of `0` in the canonical degree-275 ATLAS model has orbits of lengths
`1`, `112` and `162`. The 112-point orbit is supplied by `McLaughlin.Orbits`;
this file certifies the complementary 162-point orbit by explicit words in the
same generators. A block through `0` contains any stabilizer orbit it meets.
Its cardinality divides 275, whose proper divisors are all at most 55, so no
non-singleton proper block exists. This gives primitivity without assuming an
order or simplicity theorem for the group.

The word witnesses were found by breadth-first search on ordered pairs. Only
their kernel-checked evaluations are used. In a word's binary encoding the
least significant bit is the leftmost factor, and the final 1-bit is a sentinel;
thus list products use Mathlib's right-to-left permutation composition.

## References

* ATLAS of Finite Group Representations, version 3, representation `McLG1-p275B0`;
  the generator tables and point numbering are those of `McLaughlin.Basic`.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Springer, 1996, §1.5
  (blocks and primitive actions).
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti.Sporadic.McL

/- Bit i records membership of point i. A filter avoids a deeply nested insertion expression
when elaborating membership proofs; the following theorem checks its precise meaning. -/
private def farPoints : Finset (Fin 275) :=
  Finset.univ.filter fun x ↦ Nat.testBit
    3360744548305178561915033061133623370228496632925262544093607510845232363228427016 x.val

private theorem mem_farPoints (x : Fin 275) :
    x ∈ farPoints ↔ x ≠ 0 ∧
      x ∉ orbit ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275)) (1 : Fin 275) := by
  rw [orbit_stabilizer_zero_one]
  revert x
  decide +kernel

private def farWords (i : Fin 275) : ℕ :=
  (#[
    #[1, 1, 1, 1, 1, 1, 1, 1, 112478, 899951, 1, 1, 122330, 12015479, 12442334, 29089242,
      1, 1, 14333813, 49208687, 28375, 8084954, 7042423, 1, 1],
    #[11905883, 253679, 56023, 1406397, 895709, 440150, 1, 980847, 1, 16440798, 8216282, 1, 1,
      1, 750966, 1, 1, 15685053, 14342075, 515005, 1, 48054, 4111323, 372142, 1],
    #[113630, 1, 4111034, 2866650, 1, 1, 43870, 5618397, 443, 223989, 224187, 900055, 1,
      55963055, 1, 1, 5691307, 3923435, 1431483, 31582, 1, 1758647, 1, 1, 193885],
    #[14063, 1, 12442299, 7010135, 14073181, 11988667, 113397, 224222, 1, 7257431, 1, 1,
      3599851, 22902127, 1, 1, 1, 3495670, 1, 1, 28794555, 749303, 5699038, 4110167, 56290671],
    #[1, 128437, 1, 1, 14016218, 5683031, 2026842, 1, 1, 1, 1, 44907, 31383002, 7003479,
      109533, 1, 11236789, 1, 1, 1, 1, 2059227, 1, 3845806, 1930614],
    #[2845659, 1011445, 1948535, 1, 1431285, 1, 1, 2026461, 2812789, 1, 54717, 219061,
      177589, 488797, 875, 11988702, 1, 1423221, 1, 28794330, 777046, 448363, 1, 5487, 1],
    #[46830, 1, 87, 1437399, 1, 22261, 4126174, 2848685, 1, 16439213, 54970, 1, 3648213,
      1013181, 1486510, 2872765, 1, 121782, 5591, 718575, 32881515, 1, 2874071, 1, 2022238],
    #[122555, 1, 1, 1, 1, 7264187, 1, 1, 1, 14019927, 2026357, 1, 1, 1, 61582190, 14003163,
      3585495, 1, 961966, 8084406, 1, 1, 1, 7270103, 1],
    #[4108154, 1, 64714426, 1, 1, 29087470, 1, 16214967, 7203701, 3951, 4126139, 1, 113595,
      478, 109429, 1, 32954102, 1, 1, 1, 1, 11466077, 7846750, 6010587, 48602],
    #[2808670, 1, 1, 1, 1956694, 3861174, 109914, 977589, 1, 28666843, 1, 22932149, 28138171,
      22459, 906677, 30857134, 1, 879543, 1, 24833514, 1, 5681018, 3602106, 1, 1],
    #[2009773, 1, 357847, 768887, 64347613, 16117, 7187157, 1013434, 1404661, 32339293, 88797,
      1, 351191, 1, 12434907, 1, 1, 1, 1496438, 64221, 387765, 1, 1, 1, 1]] : Array (Array ℕ))
    |>.getD (i.val / 25) #[]
    |>.getD (i.val % 25) 0

/- Evaluate directly in the canonical subgroup, so membership needs no separate word proof. -/
private def farWordValue (w : ℕ) : McL :=
  (w.bits.dropLast.map (fun t ↦ if t then (⟨b, b_mem⟩ : McL) else ⟨a, a_mem⟩)).prod

private theorem farWords_apply : ∀ x : Fin 275, x ∈ farPoints →
    farWordValue (farWords x) • (0 : Fin 275) = 0 ∧
      farWordValue (farWords x) • (3 : Fin 275) = x := by
  decide +kernel

/-- The third orbit of the stabilizer of `0` is exactly the complement of its fixed point
and its 112-point orbit. In particular, these three orbits exhaust the 275-point set. -/
theorem orbit_stabilizer_zero_three :
    orbit ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275)) (3 : Fin 275) =
      ({0} ∪ orbit ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275))
        (1 : Fin 275))ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
  constructor
  · intro hx
    constructor
    · obtain ⟨g, rfl⟩ := hx
      have h0 : (g : Equiv.Perm (Fin 275)) 0 = 0 := g.property.2
      simpa only [subgroup_smul_def, Equiv.Perm.smul_def, h0] using
        (g : Equiv.Perm (Fin 275)).injective.ne (by decide : (3 : Fin 275) ≠ 0)
    · intro hx1
      have h31 := mem_orbit_trans (mem_orbit_symm.mp hx) hx1
      exact ((mem_farPoints 3).mp (by decide)).2 h31
  · intro hx
    obtain ⟨h0, h3⟩ := farWords_apply x ((mem_farPoints x).mpr hx)
    exact ⟨⟨(farWordValue (farWords x) : Equiv.Perm (Fin 275)),
      (farWordValue (farWords x)).property, h0⟩, h3⟩

/-- The complementary orbit of the point stabilizer has length 162. -/
@[simp] theorem ncard_orbit_stabilizer_zero_three :
    (orbit ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275))
      (3 : Fin 275)).ncard = 162 := by
  have hset : orbit ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275))
      (3 : Fin 275) = (farPoints : Set (Fin 275)) := by
    ext x
    rw [orbit_stabilizer_zero_three, Finset.mem_coe, mem_farPoints]
    simp
  rw [hset, Set.ncard_coe_finset]
  decide +kernel

private theorem orbit_subset_block {B : Set (Fin 275)} (hB : IsBlock McL B)
    (h0 : (0 : Fin 275) ∈ B) {x : Fin 275} (hx : x ∈ B) :
    orbit ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275)) x ⊆ B := by
  rintro _ ⟨g, rfl⟩
  let g' : McL := ⟨g.val, g.property.1⟩
  have hg' : g' ∈ stabilizer McL (0 : Fin 275) := g.property.2
  have hfix := hB.stabilizer_le h0 hg'
  rw [← hfix]
  exact Set.smul_mem_smul_set hx

/-- The canonical degree-275 ATLAS McLaughlin action is primitive. -/
instance : IsPreprimitive McL (Fin 275) := by
  apply IsPreprimitive.of_isTrivialBlock_base (0 : Fin 275)
  intro B h0 hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  · -- A non-singleton block contains a nonzero point and its entire stabilizer orbit.
    have hnot : ¬ B ⊆ {0} := fun h ↦ hsub (Set.subsingleton_of_subset_singleton h)
    obtain ⟨x, hx, hx0⟩ := Set.not_subset.mp hnot
    have hx0 : x ≠ 0 := by simpa using hx0
    have hlarge : 112 ≤ B.ncard := by
      by_cases hx1 : x ∈ orbit
          ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275)) (1 : Fin 275)
      · have h1 := (mem_orbit_symm.mp hx1)
        have hinc := orbit_subset_block hB h0 hx
        have hB1 := hinc h1
        simpa using Set.ncard_le_ncard (orbit_subset_block hB h0 hB1)
      · have hx3 : x ∈ orbit
            ↥(McL ⊓ stabilizer (Equiv.Perm (Fin 275)) (0 : Fin 275)) (3 : Fin 275) := by
          rw [orbit_stabilizer_zero_three]
          simpa using And.intro hx0 hx1
        have hB3 := orbit_subset_block hB h0 hx (mem_orbit_symm.mp hx3)
        have hcard := Set.ncard_le_ncard (orbit_subset_block hB h0 hB3)
        rw [ncard_orbit_stabilizer_zero_three] at hcard
        omega
    -- Every proper divisor of 275 is at most 55, contradicting the orbit bound.
    have hdiv : B.ncard ∣ 275 := by
      simpa using hB.ncard_dvd_card (Set.nonempty_of_mem h0)
    have hmem : B.ncard ∈ (275 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    have hds : (275 : ℕ).divisors = {1, 5, 11, 25, 55, 275} := by decide
    rw [hds] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    exact Or.inr (B.eq_univ_iff_ncard.mpr (by simpa using (by omega : B.ncard = 275)))

end TauCeti.Sporadic.McL
