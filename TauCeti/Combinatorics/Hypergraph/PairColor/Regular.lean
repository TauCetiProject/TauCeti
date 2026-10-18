/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Density
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Regularity of pair colors and of the lower skeleton

For a pair-color system `S` and two vertex sets `s` and `t`, `S.IsRegularPair ε s t` says that
the density of every palette color on `(s, t)` is within `ε` of its density on every pair of
subsets `s' ⊆ s`, `t' ⊆ t` with `ε * #s ≤ #s'` and `ε * #t ≤ #t'`. The condition is
coordinatewise: each color is controlled separately. Densities are taken among ordered
*distinct* pairs, so the condition is meaningful also when `s = t`.

A `PairSkeleton3` bundles a partition of the host into vertex cells with a pair-color system.
It is the lower skeleton over which triple densities and their regularity are measured.
`PairSkeleton3.IsPairColorRegular S ε` asks for `ε`-regularity of every ordered pair of vertex
cells, diagonal pairs included; `PairSkeleton3.LowerSkeletonRegular S F` evaluates an error
schedule `F : ℕ → ℝ` at the lower complexity, the number of vertex cells plus the palette size.

## Main declarations

* `TauCeti.PairColorSystem.IsRegularPair`: coordinatewise `ε`-regularity of a pair of sets.
* `TauCeti.PairColorSystem.isRegularPair_comm`: regularity is symmetric in the two sets.
* `TauCeti.PairSkeleton3`: vertex cells together with a pair-color system.
* `TauCeti.PairSkeleton3.IsPairColorRegular`: every pair of vertex cells is regular.
* `TauCeti.PairSkeleton3.isPairColorRegular_bot`: the partition into singletons is regular.
* `TauCeti.PairSkeleton3.LowerSkeletonRegular`: regularity at the lower complexity.

## References

* V. Rödl, M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* C. Terry, *Growth of regular partitions 4: strong regularity and the pairs partition*,
  arXiv:2404.02030.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*}

namespace PairColorSystem

/-- A pair `(s, t)` of vertex sets is `ε`-regular for the pair-color system `S` when, for every
color, its density on any `s' ⊆ s` and `t' ⊆ t` with `ε * #s ≤ #s'` and `ε * #t ≤ #t'` is within
`ε` of its density on `(s, t)`. Each color is controlled separately. -/
def IsRegularPair (S : PairColorSystem κ V) (ε : ℝ) (s t : Finset V) : Prop :=
  ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, ε * #s ≤ #s' → ε * #t ≤ #t' →
    |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| ≤ ε

variable {S : PairColorSystem κ V} {ε ε' : ℝ} {s t : Finset V}

/-- Unfolded form of `PairColorSystem.IsRegularPair`. -/
theorem isRegularPair_iff : S.IsRegularPair ε s t ↔
    ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, ε * #s ≤ #s' → ε * #t ≤ #t' →
      |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| ≤ ε :=
  Iff.rfl

/-- Regularity is monotone in its parameter. -/
theorem IsRegularPair.mono (h : S.IsRegularPair ε s t) (hε : ε ≤ ε') :
    S.IsRegularPair ε' s t := by
  intro c s' hs' t' ht' hs ht
  refine (h c s' hs' t' ht' ?_ ?_).trans hε
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans hs
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans ht

/-- Every pair is `ε`-regular once `1 ≤ ε`, since densities lie in `[0, 1]`. -/
theorem isRegularPair_of_one_le (hε : 1 ≤ ε) : S.IsRegularPair ε s t := by
  intro c s' _ t' _ _ _
  have h₀ : (0 : ℝ) ≤ pairColorDensity S c s' t' := mod_cast pairColorDensity_nonneg S c s' t'
  have h₁ : (pairColorDensity S c s' t' : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s' t'
  have h₀' : (0 : ℝ) ≤ pairColorDensity S c s t := mod_cast pairColorDensity_nonneg S c s t
  have h₁' : (pairColorDensity S c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s t
  exact (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩).trans hε

/-- Exchanging the two sets preserves regularity. -/
theorem IsRegularPair.symm (h : S.IsRegularPair ε s t) : S.IsRegularPair ε t s := by
  intro c t' ht' s' hs' ht hs
  have hc := h (S.rev c) s' hs' t' ht' hs ht
  rwa [← pairColorDensity_swap S (S.rev c) s' t', ← pairColorDensity_swap S (S.rev c) s t,
    rev_rev] at hc

/-- Regularity is symmetric in the two sets. -/
theorem isRegularPair_comm : S.IsRegularPair ε s t ↔ S.IsRegularPair ε t s :=
  ⟨IsRegularPair.symm, IsRegularPair.symm⟩

/-- Two singletons form an `ε`-regular pair for every `ε > 0`. -/
theorem isRegularPair_singleton (hε : 0 < ε) (u v : V) : S.IsRegularPair ε {u} {v} := by
  intro c s' hs' t' ht' hs ht
  rw [card_singleton, Nat.cast_one, mul_one] at hs ht
  obtain rfl | rfl := subset_singleton_iff.mp hs'
  · exact absurd hs (by simpa using hε)
  obtain rfl | rfl := subset_singleton_iff.mp ht'
  · exact absurd ht (by simpa using hε)
  simpa using hε.le

end PairColorSystem

/-- The lower skeleton of an arity-three complex: a partition of the host into vertex cells,
together with a coherent coloring of the ordered distinct vertex pairs. -/
@[ext]
structure PairSkeleton3 (κ : Type*) (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The partition of the host into vertex cells. -/
  vertexPart : Finpartition (univ : Finset V)
  /-- The coloring of ordered distinct vertex pairs. -/
  pairColors : PairColorSystem κ V

namespace PairSkeleton3

variable [Fintype V] [DecidableEq V] (S : PairSkeleton3 κ V) {ε ε' : ℝ}

/-- The lower skeleton is `ε`-regular when every ordered pair of its vertex cells, including a
cell paired with itself, is `ε`-regular for its pair colors. The test subsets range over the
subsets of the actual cells, tying pair regularity to the skeleton. -/
def IsPairColorRegular (ε : ℝ) : Prop :=
  ∀ A ∈ S.vertexPart.parts, ∀ B ∈ S.vertexPart.parts, S.pairColors.IsRegularPair ε A B

variable {S}

/-- Unfolded form of `PairSkeleton3.IsPairColorRegular`: for every color and every ordered pair
of vertex cells, the color density is stable on all large enough subcells. -/
theorem isPairColorRegular_iff : S.IsPairColorRegular ε ↔
    ∀ c, ∀ A ∈ S.vertexPart.parts, ∀ B ∈ S.vertexPart.parts, ∀ A' ⊆ A, ∀ B' ⊆ B,
      ε * #A ≤ #A' → ε * #B ≤ #B' →
        |(pairColorDensity S.pairColors c A' B' : ℝ) - pairColorDensity S.pairColors c A B| ≤
          ε :=
  ⟨fun h c A hA B hB => h A hA B hB c, fun h A hA B hB c => h c A hA B hB⟩

/-- In a regular lower skeleton, every ordered pair of vertex cells is a regular pair. -/
theorem IsPairColorRegular.isRegularPair (h : S.IsPairColorRegular ε) {A B : Finset V}
    (hA : A ∈ S.vertexPart.parts) (hB : B ∈ S.vertexPart.parts) :
    S.pairColors.IsRegularPair ε A B :=
  h A hA B hB

/-- Pair-color regularity is monotone in its parameter. -/
theorem IsPairColorRegular.mono (h : S.IsPairColorRegular ε) (hε : ε ≤ ε') :
    S.IsPairColorRegular ε' :=
  fun A hA B hB => (h A hA B hB).mono hε

/-- Every lower skeleton is `ε`-regular once `1 ≤ ε`. -/
theorem isPairColorRegular_of_one_le (hε : 1 ≤ ε) : S.IsPairColorRegular ε :=
  fun _ _ _ _ => PairColorSystem.isRegularPair_of_one_le hε

/-- A regular lower skeleton on a nonempty host with a nonempty palette has a nonnegative
parameter. -/
theorem IsPairColorRegular.nonneg [Nonempty κ] [Nonempty V] (h : S.IsPairColorRegular ε) :
    0 ≤ ε := by
  refine le_of_not_gt fun hε => ?_
  obtain ⟨A, hA⟩ := S.vertexPart.parts_nonempty univ_nonempty.ne_empty
  have hA' : ε * #A ≤ (#(∅ : Finset V) : ℝ) := by
    rw [card_empty, Nat.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hε.le (Nat.cast_nonneg _)
  have h0 := h A hA A hA (Classical.arbitrary κ) ∅ (empty_subset _) ∅ (empty_subset _) hA' hA'
  linarith [abs_nonneg ((pairColorDensity S.pairColors (Classical.arbitrary κ) ∅ ∅ : ℝ) -
    pairColorDensity S.pairColors (Classical.arbitrary κ) A A)]

/-- A lower skeleton whose vertex cells are the singletons is `ε`-regular for every `ε > 0`. -/
theorem isPairColorRegular_bot (hε : 0 < ε) (C : PairColorSystem κ V) :
    (⟨⊥, C⟩ : PairSkeleton3 κ V).IsPairColorRegular ε := by
  intro A hA B hB
  obtain ⟨u, -, rfl⟩ := Finpartition.mem_bot_iff.mp hA
  obtain ⟨v, -, rfl⟩ := Finpartition.mem_bot_iff.mp hB
  exact PairColorSystem.isRegularPair_singleton hε u v

variable (S) in
/-- Lower-skeleton regularity for an error schedule `F : ℕ → ℝ`: pair-color regularity at the
parameter `F` takes at the lower complexity, the number of vertex cells plus the palette size. -/
def LowerSkeletonRegular [Fintype κ] (F : ℕ → ℝ) : Prop :=
  S.IsPairColorRegular (F (#S.vertexPart.parts + Fintype.card κ))

/-- Unfolded form of `PairSkeleton3.LowerSkeletonRegular`. -/
theorem lowerSkeletonRegular_iff [Fintype κ] {F : ℕ → ℝ} :
    S.LowerSkeletonRegular F ↔ S.IsPairColorRegular (F (#S.vertexPart.parts + Fintype.card κ)) :=
  Iff.rfl

/-- A lower skeleton regular for a schedule is regular at every parameter dominating the
scheduled one. -/
theorem LowerSkeletonRegular.isPairColorRegular [Fintype κ] {F : ℕ → ℝ}
    (h : S.LowerSkeletonRegular F) (hε : F (#S.vertexPart.parts + Fintype.card κ) ≤ ε) :
    S.IsPairColorRegular ε :=
  IsPairColorRegular.mono h hε

end PairSkeleton3

end TauCeti
