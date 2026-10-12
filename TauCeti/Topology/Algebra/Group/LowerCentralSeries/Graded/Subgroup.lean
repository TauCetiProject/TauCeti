/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.BracketSpan

/-!
# The graded pieces of a subgroup along the lower `p`-series

Let `G` be a topological group with lower `p`-series `λ_k = λ_k(G)` and graded pieces
`gr_k(G) = λ_k ⧸ λ_{k+1}`, and let `K ≤ G` be a subgroup. The filtration `K_k := K ∩ λ_k(G)`
induced on `K` has graded pieces `K_k ⧸ K_{k+1}`, and since `K_{k+1} = K_k ∩ λ_{k+1}(G)` these
inject into `gr_k(G)`. This file works with their images: the **graded piece of `K`** in degree `k`
(`TauCeti.gradedPieceOf`) is the `𝔽_p`-subspace `gr_k(K) ≤ gr_k(G)` of the classes of the elements
of `K ∩ λ_k(G)`. When `K` is normal, `gr(K) = ⨁_k gr_k(K)` is an ideal of the graded Lie algebra
`gr(G)`: it is stable under the `p`-power operator `π` and under the bracket with any class of
`gr(G)` (`TauCeti.gradedPow_mem_gradedPieceOf`, `TauCeti.gradedBracket_mem_gradedPieceOf_left`,
`TauCeti.gradedBracket_mem_gradedPieceOf_right`). If `K` contains the commutator subgroup, then
`gr(K)` contains every bracket, so the bracket span `C_{k+1}(G)` of `Graded/BracketSpan.lean`
lies in `gr_{k+1}(K)` (`TauCeti.gradedBracketSpan_le_gradedPieceOf`).

This is the graded Lie algebra `gr(X)` of the kernel `X` of a character of a free pro-`p` group
that Labute's classification of Demushkin groups with `q = 2` runs on, identified with its image in
`gr(F)`.

## Main definitions

* `TauCeti.gradedPieceOf`: the graded piece `gr_k(K) ≤ gr_k(G)` of a subgroup `K`.

## Main results

* `TauCeti.mem_gradedPieceOf_iff`: the elements of `gr_k(K)` are the classes of the elements of
  `K ∩ λ_k(G)`.
* `TauCeti.gradedPow_mem_gradedPieceOf`, `TauCeti.gradedPowIter_gradedMkZero_mem_gradedPieceOf`:
  `π gr_k(K) ≤ gr_{k+1}(K)`, and `π^j` of the class of an element of `K` lies in `gr_j(K)`.
* `TauCeti.gradedBracket_mem_gradedPieceOf_left`, `TauCeti.gradedBracket_mem_gradedPieceOf_right`:
  for `K` normal, `[gr_j(K), gr_k(G)]` and `[gr_j(G), gr_k(K)]` lie in `gr_{j+k+1}(K)`.
* `TauCeti.gradedBracket_mem_gradedPieceOf_of_commutator_le`,
  `TauCeti.gradedBracketSpan_le_gradedPieceOf`: when `K` contains the commutator subgroup, every
  bracket lies in `gr(K)`, and `C_{k+1}(G) ≤ gr_{k+1}(K)`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §4, Lemma 1.
-/

public section

namespace TauCeti

open Subgroup Submodule
open scoped commutatorElement

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (p) in
/-- **The graded piece of a subgroup**: for `K ≤ G`, the `𝔽_p`-subspace `gr_k(K) ≤ gr_k(G)` of the
classes of the elements of `K ∩ λ_k(G)`, the image of `K_k ⧸ K_{k+1}` for the induced filtration
`K_k = K ∩ λ_k(G)` of `K`. Its elements are characterized by `TauCeti.mem_gradedPieceOf_iff`. -/
def gradedPieceOf (K : Subgroup G) (k : ℕ) : Submodule (ZMod p) (gradedPiece p G k) :=
  AddSubgroup.toZModSubmodule p <|
    (Subgroup.toAddSubgroup (K.subgroupOf (pLowerCentralSeries p G k))).map
      (MonoidHom.toAdditive
        (QuotientGroup.mk' ((pLowerCentralSeries p G (k + 1)).subgroupOf
          (pLowerCentralSeries p G k))))

/-- **The elements of `gr_k(K)`** are the classes in `gr_k(G)` of the elements of `K ∩ λ_k(G)`. -/
theorem mem_gradedPieceOf_iff {K : Subgroup G} {k : ℕ} {z : gradedPiece p G k} :
    z ∈ gradedPieceOf p K k ↔
      ∃ x : pLowerCentralSeries p G k, (x : G) ∈ K ∧ gradedMk p G k x = z := by
  simp only [gradedPieceOf, AddSubgroup.mem_toZModSubmodule, AddSubgroup.mem_map,
    Additive.mem_toAddSubgroup, MonoidHom.toAdditive_apply_apply, QuotientGroup.mk'_apply,
    gradedMk_def]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.toMul, mem_subgroupOf.1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Additive.ofMul x, mem_subgroupOf.2 hx, rfl⟩

/-- The class of an element of `K ∩ λ_k(G)` lies in `gr_k(K)`. -/
theorem gradedMk_mem_gradedPieceOf {K : Subgroup G} {k : ℕ} {x : pLowerCentralSeries p G k}
    (hx : (x : G) ∈ K) : gradedMk p G k x ∈ gradedPieceOf p K k :=
  mem_gradedPieceOf_iff.2 ⟨x, hx, rfl⟩

theorem gradedPieceOf_mono {K L : Subgroup G} (h : K ≤ L) (k : ℕ) :
    gradedPieceOf p K k ≤ gradedPieceOf p L k := by
  rintro z hz
  obtain ⟨x, hx, rfl⟩ := mem_gradedPieceOf_iff.1 hz
  exact gradedMk_mem_gradedPieceOf (h hx)

@[simp]
theorem gradedPieceOf_top (k : ℕ) : gradedPieceOf p (⊤ : Subgroup G) k = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨x, rfl⟩ := gradedMk_surjective k z
  exact gradedMk_mem_gradedPieceOf (mem_top _)

/-- **`π` preserves the graded pieces of a subgroup**: `π gr_k(K) ≤ gr_{k+1}(K)`. -/
theorem gradedPow_mem_gradedPieceOf {K : Subgroup G} {k : ℕ} {z : gradedPiece p G k}
    (hz : z ∈ gradedPieceOf p K k) : gradedPow p G k z ∈ gradedPieceOf p K (k + 1) := by
  obtain ⟨x, hx, rfl⟩ := mem_gradedPieceOf_iff.1 hz
  rw [gradedPow_gradedMk]
  exact gradedMk_mem_gradedPieceOf (K.pow_mem hx p)

/-- The iterated `p`-power `π^j` of the class of an element of `K` lies in `gr_j(K)`. -/
theorem gradedPowIter_gradedMkZero_mem_gradedPieceOf {K : Subgroup G} {g : G} (hg : g ∈ K)
    (j : ℕ) : gradedPowIter p G j (gradedMkZero p G g) ∈ gradedPieceOf p K j := by
  rw [gradedPowIter_gradedMkZero]
  exact gradedMk_mem_gradedPieceOf (K.pow_mem hg _)

/-- **The graded pieces of a normal subgroup form a left ideal**: for `K` normal,
`[gr_j(K), gr_k(G)] ≤ gr_{j+k+1}(K)`. -/
theorem gradedBracket_mem_gradedPieceOf_left {K : Subgroup G} [K.Normal] {j k : ℕ}
    {x : gradedPiece p G j} (hx : x ∈ gradedPieceOf p K j) (y : gradedPiece p G k) :
    gradedBracket p G j k x y ∈ gradedPieceOf p K (j + k + 1) := by
  obtain ⟨x, hxK, rfl⟩ := mem_gradedPieceOf_iff.1 hx
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk]
  exact gradedMk_mem_gradedPieceOf
    (commutator_le_left K ⊤ (commutator_mem_commutator hxK (mem_top (y : G))))

/-- **The graded pieces of a normal subgroup form a right ideal**: for `K` normal,
`[gr_j(G), gr_k(K)] ≤ gr_{j+k+1}(K)`. -/
theorem gradedBracket_mem_gradedPieceOf_right {K : Subgroup G} [K.Normal] {j k : ℕ}
    (x : gradedPiece p G j) {y : gradedPiece p G k} (hy : y ∈ gradedPieceOf p K k) :
    gradedBracket p G j k x y ∈ gradedPieceOf p K (j + k + 1) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, hyK, rfl⟩ := mem_gradedPieceOf_iff.1 hy
  rw [gradedBracket_gradedMk]
  exact gradedMk_mem_gradedPieceOf
    (commutator_le_right ⊤ K (commutator_mem_commutator (mem_top (x : G)) hyK))

/-- **The iterated `p`-powers of brackets lie in `gr(K)` when `K` contains the commutator
subgroup**: `π^m [ξ_g, ξ_h] ∈ gr_{m+1}(K)`. -/
theorem gradedPowIterBracket_mem_gradedPieceOf {K : Subgroup G} (hK : commutator G ≤ K) (m : ℕ)
    (g h : G) : gradedPowIterBracket p G m g h ∈ gradedPieceOf p K (m + 1) := by
  rw [gradedPowIterBracket_def]
  exact gradedMk_mem_gradedPieceOf
    (K.pow_mem (hK (commutator_mem_commutator (mem_top g) (mem_top h))) _)

/-- **Every bracket lies in `gr(K)` when `K` contains the commutator subgroup.** -/
theorem gradedBracket_mem_gradedPieceOf_of_commutator_le {K : Subgroup G} (hK : commutator G ≤ K)
    {j k : ℕ} (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedBracket p G j k x y ∈ gradedPieceOf p K (j + k + 1) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk]
  exact gradedMk_mem_gradedPieceOf (hK (commutator_mem_commutator (mem_top _) (mem_top _)))

/-- **The bracket span lies in `gr(K)` when `K` contains the commutator subgroup**:
`C_{k+1}(G) ≤ gr_{k+1}(K)`. -/
theorem gradedBracketSpan_le_gradedPieceOf {K : Subgroup G} (hK : commutator G ≤ K) (k : ℕ) :
    gradedBracketSpan p G k ≤ gradedPieceOf p K (k + 1) :=
  gradedBracketSpan_le_iff.2 fun x y ↦ gradedBracket_mem_gradedPieceOf_of_commutator_le hK x y

end TauCeti
