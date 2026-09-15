/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Topology.MetricSpace.Infsep
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Minimum Hamming distance

The minimum distance of a set of words is the least Hamming distance between distinct
words, with value zero for a set containing at most one word. It agrees with `Set.infsep`
after transport to Mathlib's `Hamming` metric space. For an additive code it is also the
least weight of a nonzero word, so the same API applies to linear codes through their
underlying additive subgroups.

The coordinate type is finite; the alphabet and the code need not be finite. The attained
minimum and its lower-bound characterization support parameter computations for explicit
codes, while invariance under distance-preserving maps handles changes of coordinates.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*,
§§1.2–1.6. The metric comparison uses Mathlib's `Set.Nontrivial.le_infsep_iff`.
-/

public section

namespace TauCeti

variable {ι κ A B : Type*} [Fintype ι] [DecidableEq A]

/-- The least distance between distinct words of `C`, or zero if there are no such words. -/
noncomputable def hammingMinDist (C : Set (ι → A)) : ℕ :=
  sInf {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d}

variable {C D : Set (ι → A)}

/-- A code with at most one word has minimum distance zero. -/
theorem hammingMinDist_eq_zero_of_subsingleton (hC : C.Subsingleton) :
    hammingMinDist C = 0 := by
  have h : {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d} = ∅ := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, hx, y, hy, hxy, _⟩
    exact hxy (hC hx hy)
  simp [hammingMinDist, h]

@[simp]
theorem hammingMinDist_empty : hammingMinDist (∅ : Set (ι → A)) = 0 :=
  hammingMinDist_eq_zero_of_subsingleton Set.subsingleton_empty

@[simp]
theorem hammingMinDist_singleton (x : ι → A) : hammingMinDist {x} = 0 :=
  hammingMinDist_eq_zero_of_subsingleton Set.subsingleton_singleton

/-- The minimum distance is bounded by the distance between any two distinct codewords. -/
theorem hammingMinDist_le {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    hammingMinDist C ≤ hammingDist x y :=
  csInf_le' ⟨x, hx, y, hy, hxy, rfl⟩

/-- Every code with two distinct words attains its minimum distance. -/
theorem exists_hammingDist_eq_hammingMinDist (hC : C.Nontrivial) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = hammingMinDist C := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hC
  exact csInf_mem (s := {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d})
    ⟨_, x, hx, y, hy, hxy, rfl⟩

/-- Lower bounds for minimum distance are exactly lower bounds for all distinct pairs. -/
theorem le_hammingMinDist_iff (hC : C.Nontrivial) {d : ℕ} :
    d ≤ hammingMinDist C ↔ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  constructor
  · intro hd x hx y hy hxy
    exact hd.trans (hammingMinDist_le hx hy hxy)
  · intro hd
    obtain ⟨x, hx, y, hy, hxy, hdist⟩ := exists_hammingDist_eq_hammingMinDist hC
    exact hdist ▸ hd x hx y hy hxy

@[simp]
theorem hammingMinDist_pos_iff : 0 < hammingMinDist C ↔ C.Nontrivial := by
  constructor
  · contrapose!
    intro hC
    simp [hammingMinDist_eq_zero_of_subsingleton hC]
  · intro hC
    exact (le_hammingMinDist_iff hC).2 fun x _ y _ hxy => (hammingDist_pos).2 hxy

@[simp]
theorem hammingMinDist_eq_zero_iff : hammingMinDist C = 0 ↔ C.Subsingleton := by
  simpa only [Nat.pos_iff_ne_zero, not_not, Set.not_nontrivial_iff] using
    (not_congr (hammingMinDist_pos_iff (C := C)))

/-- The minimum distance never exceeds the number of coordinates. -/
theorem hammingMinDist_le_card : hammingMinDist C ≤ Fintype.card ι := by
  by_cases hC : C.Nontrivial
  · obtain ⟨x, hx, y, hy, hxy⟩ := hC
    exact (hammingMinDist_le hx hy hxy).trans hammingDist_le_card_fintype
  · simp [hammingMinDist_eq_zero_of_subsingleton (Set.not_nontrivial_iff.mp hC)]

/-- Inclusion reverses minimum distance when the smaller code has two distinct words. -/
theorem hammingMinDist_anti (hC : C.Nontrivial) (hCD : C ⊆ D) :
    hammingMinDist D ≤ hammingMinDist C := by
  obtain ⟨x, hx, y, hy, hxy, hdist⟩ := exists_hammingDist_eq_hammingMinDist hC
  exact hdist ▸ hammingMinDist_le (hCD hx) (hCD hy) hxy

/-- The natural-number minimum distance equals metric infimum separation in Hamming space. -/
theorem hammingMinDist_eq_infsep :
    (hammingMinDist C : ℝ) = (Hamming.toHamming '' C).infsep := by
  by_cases hC : C.Nontrivial
  · have himage := hC.image Hamming.toHamming.injective
    apply le_antisymm
    · apply himage.le_infsep
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      simp only [Hamming.dist_eq_hammingDist, Hamming.ofHamming_toHamming, Nat.cast_le]
      exact hammingMinDist_le hx hy (fun h => hxy (congrArg _ h))
    · obtain ⟨x, hx, y, hy, hxy, hdist⟩ := exists_hammingDist_eq_hammingMinDist hC
      have h := Set.infsep_le_dist_of_mem (Set.mem_image_of_mem Hamming.toHamming hx)
        (Set.mem_image_of_mem Hamming.toHamming hy)
        (Hamming.toHamming.injective.ne hxy)
      simpa only [Hamming.dist_eq_hammingDist, Hamming.ofHamming_toHamming, hdist] using h
  · have hs := Set.not_nontrivial_iff.mp hC
    rw [hammingMinDist_eq_zero_of_subsingleton hs, Nat.cast_zero, (hs.image _).infsep_zero]

/-- A distance-preserving map on a code preserves its minimum distance. -/
theorem hammingMinDist_image [Fintype κ] [DecidableEq B] (f : (ι → A) → (κ → B))
    (hf : ∀ x ∈ C, ∀ y ∈ C, hammingDist (f x) (f y) = hammingDist x y) :
    hammingMinDist (f '' C) = hammingMinDist C := by
  unfold hammingMinDist
  congr 1
  ext d
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy, hd⟩
    exact ⟨x, hx, y, hy, fun h => hxy (congrArg f h), (hf x hx y hy).symm.trans hd⟩
  · rintro ⟨x, hx, y, hy, hxy, hd⟩
    refine ⟨f x, Set.mem_image_of_mem f hx, f y, Set.mem_image_of_mem f hy, ?_,
      (hf x hx y hy).trans hd⟩
    intro heq
    have hz : hammingDist x y = 0 := by rw [← hf x hx y hy, heq, hammingDist_self]
    exact hxy (hammingDist_eq_zero.mp hz)

section Additive

variable [AddGroup A] {E : AddSubgroup (ι → A)}

/-- For an additive code, minimum distance is the least nonzero weight.
For the zero code the indexing set is empty and both sides are zero. -/
theorem hammingMinDist_eq_sInf_hammingNorm :
    hammingMinDist (E : Set (ι → A)) =
      sInf {d | ∃ x ∈ E, x ≠ 0 ∧ hammingNorm x = d} := by
  unfold hammingMinDist
  congr 1
  ext d
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hd⟩
    refine ⟨-x + y, E.add_mem (E.neg_mem hx) hy, ?_, ?_⟩
    · exact fun h => hxy (neg_add_eq_zero.mp h)
    · simpa only [hammingDist_eq_hammingNorm] using hd
  · rintro ⟨x, hx, hzero, hd⟩
    exact ⟨0, E.zero_mem, x, hx, hzero.symm, by simpa using hd⟩

/-- A nonzero additive code attains its minimum distance at a nonzero codeword. -/
theorem exists_hammingNorm_eq_hammingMinDist (hE : E ≠ ⊥) :
    ∃ x ∈ E, x ≠ 0 ∧ hammingNorm x = hammingMinDist (E : Set (ι → A)) := by
  rw [hammingMinDist_eq_sInf_hammingNorm]
  have hex : ∃ x ∈ E, x ≠ 0 := by
    by_contra! h
    exact hE ((AddSubgroup.eq_bot_iff_forall E).mpr h)
  obtain ⟨x, hx, hzero⟩ := hex
  exact csInf_mem (s := {d | ∃ x ∈ E, x ≠ 0 ∧ hammingNorm x = d})
    ⟨_, x, hx, hzero, rfl⟩

/-- A nonzero weight in an additive code bounds its minimum distance. -/
theorem hammingMinDist_le_hammingNorm {x : ι → A} (hx : x ∈ E) (hzero : x ≠ 0) :
    hammingMinDist (E : Set (ι → A)) ≤ hammingNorm x := by
  simpa only [hammingDist_zero_left] using hammingMinDist_le E.zero_mem hx hzero.symm

/-- Weight lower bounds characterize the minimum distance of a nonzero additive code. -/
theorem le_hammingMinDist_iff_hammingNorm (hE : E ≠ ⊥) {d : ℕ} :
    d ≤ hammingMinDist (E : Set (ι → A)) ↔ ∀ x ∈ E, x ≠ 0 → d ≤ hammingNorm x := by
  constructor
  · intro hd x hx hzero
    exact hd.trans (hammingMinDist_le_hammingNorm hx hzero)
  · intro hd
    obtain ⟨x, hx, hzero, hdist⟩ := exists_hammingNorm_eq_hammingMinDist hE
    exact hdist ▸ hd x hx hzero

end Additive

end TauCeti
