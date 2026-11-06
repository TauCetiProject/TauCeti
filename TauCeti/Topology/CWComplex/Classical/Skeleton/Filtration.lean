/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# The skeletal filtration of a space over a relative CW complex

For a map `p : Y → B` into a relative CW complex `C ⊆ B`, the preimages `p⁻¹(Bᵠ)` of the
skeleta form an increasing filtration of `Y` indexed by `ℤ` (`TauCeti.skeletalFiltration`), with
the preimage of the base in every negative degree. For a CW complex the negative stages are
empty (`TauCeti.skeletalFiltration_eq_empty`).

A compact subset of a relative CW complex lies in a finite skeleton
(`TauCeti.exists_subset_skeletonLT_of_isCompact`), so for continuous `p` every compact subset of
`Y` lies in a finite stage of the filtration
(`TauCeti.exists_subset_skeletalFiltration_of_isCompact`). No finiteness or finite-dimensionality
of the CW complex is needed. Filtering the total space of a fibration over a CW complex in this
way gives the Serre spectral sequence; the compactness statement is what makes the filtration of
its singular chains exhaustive.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Appendix, Proposition A.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapter 5.
-/

public section

open Topology Topology.RelCWComplex

namespace TauCeti

variable {Y : Type*} {B : Type*} [TopologicalSpace B] [T2Space B] (C : Set B) {D : Set B}
  [RelCWComplex C D] (p : Y → B)

/-- **The skeletal filtration of a space over a relative CW complex.** For a map `p : Y → B`, the
stage `q ≥ 0` is the preimage `p⁻¹(Bᵠ)` of the `q`-skeleton, made of the base and the cells of
dimension at most `q`; every negative stage is the preimage of the base. For a CW complex the
negative stages are empty (`TauCeti.skeletalFiltration_eq_empty`). -/
def skeletalFiltration (q : ℤ) : Set Y :=
  p ⁻¹' (skeletonLT C (q + 1).toNat : Set B)

/-- The defining equality of the skeletal filtration at an arbitrary integer stage. -/
lemma skeletalFiltration_def (q : ℤ) :
    skeletalFiltration C p q = p ⁻¹' (skeletonLT C (q + 1).toNat : Set B) :=
  (rfl)

/-- Membership in the skeletal filtration at an arbitrary integer stage. -/
@[simp]
lemma mem_skeletalFiltration_iff {q : ℤ} {y : Y} :
    y ∈ skeletalFiltration C p q ↔ p y ∈ skeletonLT C (q + 1).toNat :=
  (Iff.rfl)

/-- The stage `n ≥ 0` of the skeletal filtration is the preimage of the `n`-skeleton. -/
@[simp]
lemma skeletalFiltration_natCast (n : ℕ) :
    skeletalFiltration C p n = p ⁻¹' (skeleton C n : Set B) := by
  simp [skeletalFiltration, skeleton]

/-- The stage `0` of the skeletal filtration is the preimage of the `0`-skeleton. -/
@[simp]
lemma skeletalFiltration_zero : skeletalFiltration C p 0 = p ⁻¹' (skeleton C 0 : Set B) := by
  simpa using skeletalFiltration_natCast C p 0

/-- The stage `1` of the skeletal filtration is the preimage of the `1`-skeleton. -/
@[simp]
lemma skeletalFiltration_one : skeletalFiltration C p 1 = p ⁻¹' (skeleton C 1 : Set B) := by
  simpa using skeletalFiltration_natCast C p 1

/-- A numeral stage of the skeletal filtration is the preimage of the corresponding skeleton. -/
@[simp]
lemma skeletalFiltration_ofNat (n : ℕ) [n.AtLeastTwo] :
    skeletalFiltration C p ofNat(n) = p ⁻¹' (skeleton C ofNat(n) : Set B) :=
  skeletalFiltration_natCast C p n

/-- The negative stages of the skeletal filtration are the preimage of the base. -/
@[simp]
lemma skeletalFiltration_of_neg {q : ℤ} (hq : q < 0) : skeletalFiltration C p q = p ⁻¹' D := by
  rw [skeletalFiltration, Int.toNat_of_nonpos (by lia), Nat.cast_zero, skeletonLT_zero_eq_base]

/-- The negative stages of the skeletal filtration of a space over a CW complex are empty. -/
lemma skeletalFiltration_eq_empty {C : Set B} [CWComplex C] {q : ℤ} (hq : q < 0) :
    skeletalFiltration C p q = ∅ := by
  rw [skeletalFiltration_of_neg C p hq, Set.preimage_empty]

/-- The skeletal filtration is increasing. -/
lemma monotone_skeletalFiltration : Monotone (skeletalFiltration C p) :=
  fun _ _ h ↦ Set.preimage_mono (skeletonLT_mono (by gcongr; lia))

/-- **Compact subsets lie in a finite stage of the skeletal filtration.** If a map `p : Y → B`
is continuous on a compact set `K` and maps it into a relative CW complex, then `K` lies in the
preimage of some skeleton. This holds for every relative CW complex, also when it has infinitely
many cells or is infinite-dimensional. -/
theorem exists_subset_skeletalFiltration_of_isCompact [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) (hp : ContinuousOn p K) (hpK : Set.MapsTo p K C) :
    ∃ q, K ⊆ skeletalFiltration C p q := by
  obtain ⟨n, hn⟩ := exists_subset_skeletonLT_of_isCompact (hK.image_of_continuousOn hp)
    hpK.image_subset
  refine ⟨n, fun y hy ↦ skeletonLT_mono ?_ (hn (Set.mem_image_of_mem p hy))⟩
  simp

end TauCeti
