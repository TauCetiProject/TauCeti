/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression

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
(`TauCeti.exists_path_homotopic_skeletonLT`). Without `1`-cells the `1`-skeleton is the union of
`D` with the `0`-cells, and since the cells are attached along `D`, every subset of the
`1`-skeleton meeting `D` in a closed set is closed
(`TauCeti.isClosed_of_subset_skeletonLT_one`). So a loop in the `1`-skeleton stays in `D` when its
basepoint lies in `D`, where it is nullhomotopic, and is constant at a `0`-cell otherwise.

## Main results

* `TauCeti.isClosed_of_subset_skeletonLT_one`: when the cells are attached along `D`, a subset of
  the `1`-skeleton is closed as soon as its intersection with `D` is.
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

/-- **Closed subsets of the `1`-skeleton of a complex attached along its base.** If the frontier of
every cell of `C` lies in the base `D`, then a subset `A` of the `1`-skeleton `skeletonLT C 1`,
which consists of `D` and the `0`-cells, is closed as soon as `A ∩ D` is closed. -/
theorem isClosed_of_subset_skeletonLT_one (hfr : ∀ n (j : cell C n), cellFrontier n j ⊆ D)
    {A : Set X} (hA : A ⊆ skeletonLT C 1) (hAD : IsClosed (A ∩ D)) : IsClosed A := by
  refine (RelCWComplex.closed C A (hA.trans (skeletonLT C 1).subset_complex)).2
    ⟨fun n j ↦ ?_, hAD⟩
  cases n with
  | zero =>
    -- A `0`-cell is a single point.
    rw [closedCell_zero_eq_singleton]
    exact (subsingleton_singleton.anti inter_subset_right).isClosed
  | succ n =>
    -- A point of the `1`-skeleton in a cell of positive dimension lies on its frontier.
    have hsub : A ∩ closedCell (n + 1) j ⊆ D := by
      rintro x ⟨hxA, hx⟩
      rw [← cellFrontier_union_openCell_eq_closedCell] at hx
      refine hx.elim (fun hx ↦ hfr _ j hx) fun hx ↦ absurd hx ?_
      exact disjoint_left.1 (disjoint_skeletonLT_openCell (by norm_cast; omega)) (hA hxA)
    have : A ∩ closedCell (n + 1) j = (A ∩ D) ∩ closedCell (n + 1) j := by
      ext x
      exact ⟨fun hx ↦ ⟨⟨hx.1, hsub hx⟩, hx.2⟩, fun hx ↦ ⟨hx.1.1, hx.2⟩⟩
    rw [this]
    exact hAD.inter isClosed_closedCell

/-- A path in the `1`-skeleton of a complex attached along its base stays in any part `B` of the
`1`-skeleton which, like its complement there, meets the base in a closed set. -/
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
    let δ : Path (⟨a, haD⟩ : D) ⟨a, haD⟩ :=
      { toFun t := ⟨γ' t, hmem t⟩
        continuous_toFun := by fun_prop
        source' := by ext; simp
        target' := by ext; simp }
    have hδ := (subsingleton_fundamentalGroup_iff.1 (hD _) δ).map
      ⟨_, continuous_inclusion hDC⟩
    have hδγ' : δ.map (continuous_inclusion hDC) = γ'.map (continuous_inclusion hAC) := by
      ext; rfl
    have hrefl : (Path.refl (⟨a, haD⟩ : D)).map (continuous_inclusion hDC) =
        Path.refl (inclusion hAC a) := by
      ext; rfl
    rw [hδγ', hrefl] at hδ
    exact hγ'.symm.trans hδ
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
