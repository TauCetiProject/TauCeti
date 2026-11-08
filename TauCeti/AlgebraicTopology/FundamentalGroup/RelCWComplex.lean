/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression

import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv

/-!
# Attaching cells of dimension other than one creates no loops

Let `C` be a relative CW complex over a base `D` in a Hausdorff space, all of whose cells are
attached directly along the base: the frontier of every cell lies in `D`. If `C` has no `1`-cells
and every loop in `D` is nullhomotopic, then every loop in `C` is nullhomotopic
(`TauCeti.subsingleton_fundamentalGroup_of_isEmpty_cell_one`). The `0`-cells are isolated points
of `C`, while cells of dimension at least `2` cannot carry new loops.

This is the form in which the cell attachment theorem of Morse theory controls the fundamental
group of a sublevel set: crossing a critical level attaches one cell along the lower sublevel for
each critical point, of dimension its index, so critical points of index one are the only ones
that can create loops.

The proof compresses loops into the `1`-skeleton. Every point of `C` is joined by a path to the
`1`-skeleton (`TauCeti.exists_joined_skeletonLT`), and a loop based in the `1`-skeleton is
homotopic, relative to its basepoint, to a loop in the `1`-skeleton
(`TauCeti.exists_path_homotopic_skeletonLT`). Without `1`-cells the `1`-skeleton equals the
`0`-skeleton `skeletonLT C 1`, the union of `D` with the `0`-cells. Since the cells are attached
along `D`, every subset of the `0`-skeleton meeting `D` in a closed set is closed
(`TauCeti.isClosed_of_subset_skeletonLT_one`). So a loop in the `1`-skeleton stays in `D` when its
basepoint lies in `D`, where it is nullhomotopic, and is constant at a `0`-cell otherwise.

## Main results

* `TauCeti.subsingleton_fundamentalGroup_of_isEmpty_cell_one`: attaching cells of dimension other
  than one along a base with trivial fundamental groups gives trivial fundamental groups.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.2, Proposition 1.26, and Section 4.1, Corollary 4.12.
-/

public section

open Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- A path in the `0`-skeleton of a complex attached along its base stays in any part `B` of the
`0`-skeleton which, like its complement there, meets the base in a closed set. -/
private theorem forall_mem_of_subset_skeletonLT_one
    (hfr : ∀ n (j : cell C n), cellFrontier n j ⊆ D) {B : Set X}
    (hB : B ⊆ skeletonLT C 1) (hBD : IsClosed (B ∩ D))
    (hBD' : IsClosed (((skeletonLT C 1 : Set X) \ B) ∩ D)) (γ : C(I, X))
    (hγ : ∀ t, γ t ∈ skeletonLT C 1) (h₀ : γ 0 ∈ B) (t : I) : γ t ∈ B := by
  have hclosed := (isClosed_of_subset_skeletonLT_one hfr hB hBD).preimage γ.continuous
  have hopen : IsOpen (γ ⁻¹' B) := by
    have h := (isClosed_of_subset_skeletonLT_one hfr sdiff_subset hBD').preimage γ.continuous
    rw [← isClosed_compl_iff]
    convert h using 1
    ext s
    exact ⟨fun hs ↦ ⟨hγ s, hs⟩, fun hs ↦ hs.2⟩
  have huniv := (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left
    (nonempty_of_mem (show (0 : I) ∈ γ ⁻¹' B from h₀)).ne_empty
  exact (huniv ▸ mem_univ t : t ∈ γ ⁻¹' B)

/-- **Attaching cells of dimension other than one creates no loops.** Let `C` be a relative CW
complex over `D` in a Hausdorff space, with no `1`-cells, all of whose cells are attached along
the base, in that the frontier of every cell lies in `D`. If the fundamental group of `D` is
trivial at every basepoint, then so is the fundamental group of `C`. -/
theorem subsingleton_fundamentalGroup_of_isEmpty_cell_one (h₁ : IsEmpty (cell C 1))
    (hfr : ∀ n (j : cell C n), cellFrontier n j ⊆ D)
    (hD : ∀ x : D, Subsingleton (FundamentalGroup D x)) (x : C) :
    Subsingleton (FundamentalGroup C x) := by
  set A : Set X := (skeletonLT C (((1 : ℕ) : ℕ∞) + 1) : Set X) with hA
  have hAC : A ⊆ C := (skeletonLT C _).subset_complex
  -- Without `1`-cells, the `1`-skeleton is the `0`-skeleton `skeletonLT C 1`.
  have hA₁ : A ⊆ skeletonLT C 1 := by
    intro y hy
    rw [hA, SetLike.mem_coe, mem_skeletonLT_iff] at hy
    rw [SetLike.mem_coe, mem_skeletonLT_iff]
    obtain hy | ⟨m, hm, j, hy⟩ := hy
    · exact .inl hy
    obtain rfl | rfl : m = 0 ∨ m = 1 := by norm_cast at hm; omega
    · exact .inr ⟨0, by norm_num, j, hy⟩
    · exact h₁.elim j
  have hD₁ : D ⊆ skeletonLT C 1 := fun y hy ↦ mem_skeletonLT_iff.2 (.inl hy)
  have hDC : D ⊆ C := base_subset_complex
  -- Move the basepoint to a point `a` of the `1`-skeleton.
  obtain ⟨a, ha⟩ := exists_joined_skeletonLT (n := 1) rfl hAC x
  suffices Subsingleton (FundamentalGroup C (inclusion hAC a)) from
    (FundamentalGroup.fundamentalGroupMulEquivOfPath ha.somePath).symm.injective.subsingleton
  refine subsingleton_fundamentalGroup_iff.2 fun γ ↦ ?_
  -- Compress the loop into the `1`-skeleton.
  obtain ⟨γ', hγ'⟩ := exists_path_homotopic_skeletonLT one_pos rfl hAC γ
  have hγ'₁ (t : I) : ((γ' t : A) : X) ∈ skeletonLT C 1 := hA₁ (γ' t).2
  let γ'X : C(I, X) := ⟨fun t ↦ γ' t, by fun_prop⟩
  by_cases haD : (a : X) ∈ D
  · -- The compressed loop stays in `D`, where it is nullhomotopic.
    have hmem := forall_mem_of_subset_skeletonLT_one hfr hD₁ (by simpa using isClosedBase C)
      (by simp) γ'X hγ'₁ (by simpa [γ'X] using haD)
    -- Inside `C`, the base `D` is homeomorphic to `D` itself, so its loops are nullhomotopic.
    let e := (IsEmbedding.inclusion hDC).toHomeomorph
    let b : range (inclusion hDC) := ⟨inclusion hAC a, ⟨a, haD⟩, rfl⟩
    have := hD (e.symm b)
    have : Subsingleton (FundamentalGroup (range (inclusion hDC)) b) :=
      (e.symm.toHomotopyEquiv.fundamentalGroupMulEquiv b).injective.subsingleton
    exact hγ'.symm.trans (Path.Homotopic.refl_of_forall_mem_of_subsingleton (x := b) _
      fun t ↦ ⟨⟨_, hmem t⟩, rfl⟩)
  · -- The basepoint is a `0`-cell, an isolated point of the `1`-skeleton.
    have hD' : ((skeletonLT C 1 : Set X) \ {↑a}) ∩ D = D :=
      inter_eq_right.2 fun y hy ↦ ⟨hD₁ hy, fun h ↦ haD (h ▸ hy)⟩
    have hmem := forall_mem_of_subset_skeletonLT_one (B := {↑a}) hfr
      (singleton_subset_iff.2 (hA₁ a.2)) (by simp [haD]) (by rw [hD']; exact isClosedBase C)
      γ'X hγ'₁ (by simp [γ'X])
    have hconst : γ'.map (continuous_inclusion hAC) = Path.refl _ := by
      ext t
      exact hmem t
    exact hγ'.symm.trans (by rw [hconst])

end TauCeti
