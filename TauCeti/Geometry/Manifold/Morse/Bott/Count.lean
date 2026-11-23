/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.BettiNumber
import TauCeti.Geometry.Manifold.Morse.Bott.Index.Basic

/-!
# The indices of the pieces of a Morse–Bott function and the Morse–Bott count

Let a family of embeddings `i a : S a → M` exhibit `f` as a Morse–Bott function
(`TauCeti.IsMorseBottFamily`). The Morse index of `f` is locally constant along each piece
(`IsNondegenerateCriticalSubmanifold.isLocallyConstant_manifoldMorseIndex`, in the namespace
`TauCeti.SmoothEmbedding`) and each piece is connected, so `f` has the same Morse index `λ_a` at
every point of the piece `S a`: the **index of the piece** (`TauCeti.IsMorseBottFamily.index`,
`TauCeti.IsMorseBottFamily.manifoldMorseIndex_eq_index`). It is the rank of the negative normal
bundle of the piece. The index of the piece for `-f` is its coindex, and index, coindex and the
dimension of the piece add up to the dimension of `M`
(`TauCeti.IsMorseBottFamily.index_add_index_neg_add_finrank`).

The **Morse–Bott count** in degree `j` with coefficients in a ring `k` is

`cⱼ = ∑ₐ b_{j - λ_a}(S a; k)`,

the sum over the pieces of index at most `j` of the Betti numbers of the pieces, shifted by their
indices (`TauCeti.IsMorseBottFamily.morseBottCount`). It is the coefficient of `tʲ` in
`∑ₐ t^{λ_a} P_{S a}(t)`, where `P_{S a}` is the Poincaré polynomial of `S a`. This is the left side
of Bott's inequalities: crossing a critical level attaches the negative disc bundles of the pieces
on that level, whose Thom isomorphism shifts the homology of each piece by its index. With
coefficients in `𝔽₂`, or when the negative normal bundles are orientable, the Morse–Bott
inequalities compare the counts `cⱼ` with the Betti numbers of `M`; in general the Betti numbers of
`S a` must be twisted by the orientation system of its negative normal bundle. The count takes
values in `ℕ∞`, as the critical count `TauCeti.criticalCount` does, so that infinitely many
contributing pieces give `⊤`; with finitely many pieces, as on a compact manifold
(`TauCeti.IsMorseBottFamily.finite`), it is a finite sum
(`TauCeti.IsMorseBottFamily.morseBottCount_eq_sum`).

For a Morse function every piece is a point, of index the Morse index of `f` there, and a point
has Betti numbers `1, 0, 0, …`. So each piece contributes `t^{λ_a}` and the Morse–Bott count is the
number of critical points of index `j`
(`TauCeti.IsMorseBottFamily.morseBottCount_eq_criticalCount`), for every Morse–Bott family
exhibiting the Morse function and over every ring with the strong rank condition. On a compact
manifold the Morse–Bott count therefore satisfies the Morse polynomial identity
`∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)`
(`TauCeti.IsMorseBottFamily.exists_morseBottCount_eq_bettiNumber_add_coeff_of_isMorse`): the
Morse–Bott count of a Morse function recovers the ordinary Morse formula.

## Main definitions

* `TauCeti.IsMorseBottFamily.index`: the Morse index of a piece of a Morse–Bott family.
* `TauCeti.IsMorseBottFamily.morseBottCount`: the Morse–Bott count `∑ₐ b_{j - λ_a}(S a; k)`.

## Main results

* `TauCeti.IsMorseBottFamily.manifoldMorseIndex_eq_index`: the Morse index of `f` at every point of
  a piece is the index of the piece.
* `TauCeti.IsMorseBottFamily.index_add_index_neg_add_finrank`: index plus coindex plus the
  dimension of a piece is the dimension of `M`.
* `TauCeti.IsMorseBottFamily.morseBottCount_eq_sum`: with finitely many pieces the Morse–Bott count
  is a finite sum of shifted Betti numbers.
* `TauCeti.IsMorseBottFamily.morseBottCount_eq_criticalCount`: for a Morse function the Morse–Bott
  count is the critical count.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.6 and 15.7.
-/

public section

noncomputable section

open Function Module Set
open Polynomial (X)
open scoped ContDiff Manifold Polynomial

universe u

namespace TauCeti

namespace IsMorseBottFamily

section Index

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  {S : ι → Type*} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
  {n : ℕ∞ω} {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {f : M → ℝ}
  (h : IsMorseBottFamily i f)
include h

/-- The **index of a piece** of a Morse–Bott family: the Morse index of `f` at a point of the
piece. It does not depend on the point (`TauCeti.IsMorseBottFamily.manifoldMorseIndex_eq_index`),
and it is the rank of the negative normal bundle of the piece. -/
def index (a : ι) : ℕ :=
  manifoldMorseIndex I f (i a (h.nonempty a).some)

theorem index_def (a : ι) : h.index a = manifoldMorseIndex I f (i a (h.nonempty a).some) :=
  (rfl)

variable [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 2 M] (hn : n ≠ 0)
include hn

/-- **The Morse index is constant on each piece.** At every point of a piece of a Morse–Bott
family, the Morse index of `f` is the index of the piece: it is locally constant along the piece,
which is connected. -/
theorem manifoldMorseIndex_eq_index (a : ι) (s : S a) :
    manifoldMorseIndex I f (i a s) = h.index a := by
  have := h.preconnectedSpace a
  exact ((h.isNondegenerateCriticalSubmanifold a).isLocallyConstant_manifoldMorseIndex
    hn).apply_eq_of_preconnectedSpace s _

/-- **Index plus coindex is the codimension.** For each piece of a Morse–Bott family modelled on
`E' a`, its indices for `f` and for `-f` and its dimension add up to the dimension of `M`. -/
theorem index_add_index_neg_add_finrank (a : ι) :
    h.index a + h.neg.index a + finrank ℝ (E' a) = finrank ℝ E :=
  (h.isNondegenerateCriticalSubmanifold a).manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank
    hn _

end Index

section Count

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  {S : ι → Type u} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
  {n : ℕ∞ω} {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {f : M → ℝ}
  (h : IsMorseBottFamily i f) (k : Type u) [Ring k]
include h

/-- The **Morse–Bott count** of a Morse–Bott family in degree `j`, with coefficients in `k`: the
sum `∑ₐ b_{j - λ_a}(S a; k)` over the pieces `S a` of index `λ_a ≤ j` of their Betti numbers
shifted by their indices, that is, the coefficient of `tʲ` in `∑ₐ t^{λ_a} P_{S a}(t)`. It is the
cardinality of the disjoint union of `b_{j - λ_a}(S a; k)` points over these pieces, so that it is
`⊤` when infinitely many pieces contribute. For a Morse function it is the number of critical
points of index `j` (`TauCeti.IsMorseBottFamily.morseBottCount_eq_criticalCount`). -/
def morseBottCount (j : ℕ) : ℕ∞ :=
  ENat.card (Σ a : {a // h.index a ≤ j}, Fin (bettiNumber k (S a) (j - h.index a)))

theorem morseBottCount_def (j : ℕ) :
    h.morseBottCount k j =
      ENat.card (Σ a : {a // h.index a ≤ j}, Fin (bettiNumber k (S a) (j - h.index a))) :=
  (rfl)

/-- With finitely many pieces, for instance on a compact manifold, the Morse–Bott count is the
finite sum `∑ₐ b_{j - λ_a}(S a; k)` over the pieces of index at most `j`. -/
theorem morseBottCount_eq_sum [Fintype ι] (j : ℕ) :
    h.morseBottCount k j = ∑ a with h.index a ≤ j, bettiNumber k (S a) (j - h.index a) := by
  classical
  rw [morseBottCount_def, ENat.card_eq_coe_natCard, Nat.card_sigma,
    ← Finset.sum_subtype (Finset.univ.filter fun a ↦ h.index a ≤ j) (fun _ ↦ by simp)
      fun a ↦ Nat.card (Fin (bettiNumber k (S a) (j - h.index a)))]
  simp

variable [StrongRankCondition k] [IsManifold I 1 M]

/-- **The Morse–Bott count of a Morse function is its critical count.** For any Morse–Bott family
exhibiting a Morse function `f`, the Morse–Bott count in degree `j` is the number of critical
points of `f` of index `j`, over every ring with the strong rank condition: each piece is a point of
index `λ_a` and contributes `t^{λ_a}`. -/
theorem morseBottCount_eq_criticalCount (hf : IsMorse I f) (j : ℕ) :
    h.morseBottCount k j = criticalCount I f j := by
  have hb (a : ι) (ha : h.index a ≤ j) :
      bettiNumber k (S a) (j - h.index a) = if h.index a = j then 1 else 0 := by
    have := h.subsingleton_of_isMorse hf a
    have := h.nonempty a
    rw [bettiNumber_of_contractibleSpace]
    exact if_congr (by omega) rfl rfl
  -- A summand of the disjoint union is nonempty exactly for a piece of index `j`, and then it is a
  -- single point.
  let φ : (Σ a : {a // h.index a ≤ j}, Fin (bettiNumber k (S a) (j - h.index a))) →
      {a // h.index a = j} := fun x ↦
    ⟨x.1, by
      have hx := x.2.pos
      rw [hb x.1 x.1.property] at hx
      by_contra hne
      simp [hne] at hx⟩
  have hφ : Bijective φ := by
    refine ⟨fun ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb'⟩, y⟩ hxy ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
    · obtain rfl : a = b := congrArg Subtype.val hxy
      have hsub : Subsingleton (Fin (bettiNumber k (S a) (j - h.index a))) := by
        rw [Fin.subsingleton_iff_le_one, hb a ha]
        split_ifs <;> simp
      rw [Subsingleton.elim x y]
    · have hpos : 0 < bettiNumber k (S a) (j - h.index a) := by
        rw [hb a ha.le]
        simp [ha]
      exact ⟨⟨⟨a, ha.le⟩, ⟨0, hpos⟩⟩, rfl⟩
  -- A piece of index `j` is a critical point of index `j`, and every such point is one piece.
  let g : {a // h.index a = j} → M := fun a ↦ i a (h.nonempty a).some
  have hg : Injective g := fun a b hab ↦ Subtype.ext <| by
    by_contra hne
    exact disjoint_left.1 (h.pairwise_disjoint_range hne) (mem_range_self _) ⟨_, hab.symm⟩
  have hrange : range g = {x ∈ criticalPoints I f | manifoldMorseIndex I f x = j} := by
    ext x
    refine ⟨?_, fun ⟨hx, hxj⟩ ↦ ?_⟩
    · rintro ⟨a, rfl⟩
      exact ⟨h.range_subset_criticalPoints a (mem_range_self _), a.property⟩
    · obtain ⟨a, s, rfl⟩ := h.mem_criticalPoints_iff.1 hx
      obtain rfl : s = (h.nonempty a).some := (h.subsingleton_of_isMorse hf a).elim _ _
      exact ⟨⟨a, hxj⟩, rfl⟩
  rw [morseBottCount_def, criticalCount_def, ← hrange, hg.encard_range]
  exact ENat.card_congr (Equiv.ofBijective φ hφ)

end Count

section Polynomial

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  {S : ι → Type u} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
  {n : ℕ∞ω} {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {f : M → ℝ}

/-- **The Morse–Bott count of a Morse function satisfies the Morse polynomial identity.** For a
Morse–Bott family exhibiting a Morse function `f` on a compact boundaryless manifold `M` of
dimension `m`, and a division ring `k`, the Morse–Bott counts `cⱼ` and the Betti numbers `bⱼ` of
`M` satisfy `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)` for a polynomial `Q` with natural number coefficients
and degree below `m`. -/
theorem exists_morseBottCount_eq_bettiNumber_add_coeff_of_isMorse (h : IsMorseBottFamily i f)
    (hf : IsMorse I f) (k : Type u) [DivisionRing k] :
    ∃ Q : ℕ[X], Q.degree < finrank ℝ E ∧
      ∀ j, h.morseBottCount k j = (bettiNumber k M j + ((1 + X) * Q).coeff j : ℕ) := by
  simpa only [← h.morseBottCount_eq_criticalCount k hf] using
    hf.exists_criticalCount_eq_bettiNumber_add_coeff k

end Polynomial

end IsMorseBottFamily

end TauCeti
