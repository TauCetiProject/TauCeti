/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Character
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Odd.Exact

/-!
# The orientation image pins the odd dyadic normal form

Labute's normal form for a Demushkin group `G` at `p = 2` of odd rank `n` says that `G` is
presented on `n` generators by `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`, the level `f = ∞`, or by
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` for some finite level `f ≥ 2`
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Odd.Exact`). The level is not
a free parameter: the canonical character of the presented group at level `f` has image
`{±1} × U^(f)`, at level `f = ∞` it has image `{±1}`, and these closed subgroups of `ℤ₂ˣ` are
pairwise distinct (`TauCeti.unitsPlusMinus_inj`, `TauCeti.unitsPlusMinus_ne_zpowers_neg_one`).
Since the image of the canonical character is an isomorphism invariant, the image of `G`
determines the level of its normal form. This file draws the two consequences.

First, the **image pins the normal form**: a Demushkin group of odd rank `n` whose canonical
character has image `{±1} × U^(f)` is presented by the level-`f` word, and one whose canonical
character has image `{±1}` is presented by the level-`∞` word; in relator form, an automorphism of
the free pro-`2` group carries any relator in `Φ(F)` with that image to that word. The finite-level
statements carry the hypothesis `3 ≤ n`, because at rank one the image is `{±1}` whatever the
level, the word `x₁² x₂^{2^f}` reading `x₁²` when the second generator is out of range.

Second, the **necessity half of the existence theorem for odd rank** (Labute, Theorem 1 with
Remark 2; Serre, Theorem 3.2): the image of the canonical character of a Demushkin group of odd
rank is `{±1}`, or the rank is at least `3` and the image is `{±1} × U^(f)` for some `f ≥ 2`. With
the realization half of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Existence`, the existence theorem
for odd rank becomes an equivalence: a subgroup `A ≤ ℤ₂ˣ` is the image of the canonical
character of a Demushkin group of odd rank `n` exactly when `A = {±1}`, or `n ≥ 3` and
`A = {±1} × U^(f)` for some `f ≥ 2`. The uniqueness and marked forms of the odd-rank
classification are drawn from the pinned normal form in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Uniqueness` and
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Marked`.

## Main results

* `TauCeti.freeProP.range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd` and its
  intrinsic form
  `IsDemushkin.range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd_demushkinRank`:
  **the necessity half of the existence theorem for odd rank**, the image of the canonical
  character of a Demushkin group of odd rank is `{±1}`, or the rank is at least `3` and the image
  is `{±1} × U^(f)` for some `f ≥ 2`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordTwoOdd_of_range_eq`,
  `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordTwoOddTop_of_range_eq`: **the
  image pins the normal form, relator form**: an automorphism of the free pro-`2` group on an odd
  number of generators carries a relator in `Φ(F)` presenting a Demushkin group with image
  `{±1} × U^(f)`, respectively `{±1}`, to the odd word at level `f`, respectively at level `∞`.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOdd_of_range_eq`
  and `IsDemushkin.nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOddTop_of_range_eq`:
  **the image pins the normal form, intrinsic form**.
* `TauCeti.exists_isDemushkin_range_demushkinCharacter_eq_iff_of_odd`: **the existence theorem of
  the classification for odd rank, as an equivalence**.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorems 1, 3 and 4 and their corollaries, and Remark 2.
* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 252
  (1962/63), Theorem 3.2.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

open Subgroup

universe u

section Intrinsic

namespace IsDemushkin

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (hG : IsDemushkin 2 G)
include hG

/-- **The image `{±1}` pins the odd normal form at level `f = ∞`.** A Demushkin group at `p = 2`
of odd rank `n` whose canonical character has image `{±1}` is topologically isomorphic to
`⟨x₁, …, x_n ∣ x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩`; at rank one this is `ℤ/2 = ⟨x₁ ∣ x₁²⟩`. -/
theorem nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOddTop_of_range_eq
    (hn : Odd (demushkinRank hG))
    (hrange : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    Nonempty (G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
      {demushkinWordTwoOddTop (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))}) := by
  rcases hG.exists_continuousMulEquiv_presentedProP_demushkinWordTwoOdd_of_odd_demushkinRank hn with
    h | ⟨f, hf, ⟨e⟩⟩
  · exact h
  rcases le_or_gt (demushkinRank hG) 1 with hn₁ | hn₁
  · -- At rank one the level-`f` word is `x₁²`, the level-`∞` word.
    rw [demushkinWordTwoOdd_eq_demushkinWordTwoOddTop f _
      (by rw [freeProPGen_eq_one_of_le 2 hn₁, one_pow])] at e
    exact ⟨e⟩
  · have hn₂ : 2 < demushkinRank hG := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact absurd (hrange.symm.trans
      (range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd hG hf hn hn₂ e)).symm
      (unitsPlusMinus_ne_zpowers_neg_one f)

/-- **The image `{±1} × U^(f)` pins the odd normal form at level `f`.** A Demushkin group at
`p = 2` of odd rank `n ≥ 3` whose canonical character has image `{±1} × U^(f)`, with `f ≥ 2`, is
topologically isomorphic to `⟨x₁, …, x_n ∣ x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)⟩`. -/
theorem nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOdd_of_range_eq
    (hn : Odd (demushkinRank hG)) (hn₃ : 3 ≤ demushkinRank hG) {f : ℕ} (hf : 2 ≤ f)
    (hrange : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
      {demushkinWordTwoOdd f (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))}) := by
  rcases hG.exists_continuousMulEquiv_presentedProP_demushkinWordTwoOdd_of_odd_demushkinRank hn with
    h | ⟨f', hf', ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    exact absurd (hrange.symm.trans
      (range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop hG hn e))
      (unitsPlusMinus_ne_zpowers_neg_one f)
  · obtain rfl := (unitsPlusMinus_inj hf hf').1 <| hrange.symm.trans <|
      range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd hG hf' hn (by omega) e
    exact ⟨e⟩

/-- **The necessity half of the existence theorem for odd rank** (Labute, Theorem 1 and Remark 2;
Serre, Theorem 3.2). The image of the canonical character of a Demushkin group of odd rank is
`{±1}`, or the rank is at least `3` and the image is `{±1} × U^(f)` for some `f ≥ 2`. -/
theorem range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd_demushkinRank
    (hn : Odd (demushkinRank hG)) :
    (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) ∨
      3 ≤ demushkinRank hG ∧
        ∃ f, 2 ≤ f ∧ (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f := by
  rcases hG.exists_continuousMulEquiv_presentedProP_demushkinWordTwoOdd_of_odd_demushkinRank hn with
    h | ⟨f, hf, ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    exact Or.inl
      (range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop hG hn e)
  rcases le_or_gt (demushkinRank hG) 1 with hn₁ | hn₁
  · -- At rank one the level-`f` word is `x₁²`, the level-`∞` word.
    rw [demushkinWordTwoOdd_eq_demushkinWordTwoOddTop f _
      (by rw [freeProPGen_eq_one_of_le 2 hn₁, one_pow])] at e
    exact Or.inl
      (range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop hG hn e)
  · have hn₂ : 2 < demushkinRank hG := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact Or.inr ⟨hn₂, f, hf,
      range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd hG hf hn hn₂ e⟩

end IsDemushkin

end Intrinsic

section Relator

variable {n : ℕ}

namespace freeProP

/-- **The image `{±1} × U^(f)` pins the odd normal form at level `f`, relator form.** Let
`r ∈ Φ(F)` be a relator of the free pro-`2` group on an odd number `n ≥ 3` of generators
presenting a Demushkin group whose canonical character has image `{±1} × U^(f)`, with `f ≥ 2`.
Then a continuous automorphism of `F` carries `r` to `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordTwoOdd_of_range_eq (hn : Odd n)
    (hn₃ : 3 ≤ n) {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) {f : ℕ} (hf : 2 ≤ f)
    (hrange : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      e r = demushkinWordTwoOdd f n (freeProPGen 2 n) := by
  obtain ⟨e, he | ⟨f', hf', he⟩⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordTwoOdd_of_odd hn hr hG
  · exact absurd (hrange.symm.trans
      (range_demushkinCharacter_eq_zpowers_neg_one_of_equiv_demushkinWordTwoOddTop hG hn
        (presentedProP.congrSingleton e he))) (unitsPlusMinus_ne_zpowers_neg_one f)
  · obtain rfl := (unitsPlusMinus_inj hf hf').1 <| hrange.symm.trans <|
      range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd hG hf' hn (by omega)
        (presentedProP.congrSingleton e he)
    exact ⟨e, he⟩

/-- **The image `{±1}` pins the odd normal form at level `f = ∞`, relator form.** Let `r ∈ Φ(F)` be
a relator of the free pro-`2` group on an odd number `n` of generators presenting a Demushkin group
whose canonical character has image `{±1}`. Then a continuous automorphism of `F` carries `r` to
`x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)`. At rank one this is the relator `x₁²` of `ℤ/2`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordTwoOddTop_of_range_eq (hn : Odd n)
    {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}))
    (hrange : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      e r = demushkinWordTwoOddTop n (freeProPGen 2 n) := by
  obtain ⟨e, he | ⟨f, hf, he⟩⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordTwoOdd_of_odd hn hr hG
  · exact ⟨e, he⟩
  rcases le_or_gt n 1 with hn₁ | hn₁
  · -- At rank one the level-`f` word is `x₁²`, the level-`∞` word.
    exact ⟨e, he.trans (demushkinWordTwoOdd_eq_demushkinWordTwoOddTop f n
      (by rw [freeProPGen_eq_one_of_le 2 hn₁, one_pow]))⟩
  · have hn₂ : 2 < n := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact absurd (hrange.symm.trans
      (range_demushkinCharacter_eq_unitsPlusMinus_of_equiv_demushkinWordTwoOdd hG hf hn hn₂
        (presentedProP.congrSingleton e he))).symm (unitsPlusMinus_ne_zpowers_neg_one f)

/-- **The necessity half of the existence theorem for odd rank, relator form** (Labute, Theorem 1
and Remark 2). Let `r ∈ Φ(F)` be a relator of the free pro-`2` group on an odd number `n` of
generators presenting a Demushkin group. Then the image of the canonical character of `⟨X ∣ r⟩` is
`{±1}`, or `n ≥ 3` and the image is `{±1} × U^(f)` for some `f ≥ 2`. At rank one the image is
`{±1}`, the odd word at every level reading `x₁²` there. -/
theorem range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd (hn : Odd n)
    {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) :
    (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) ∨
      3 ≤ n ∧ ∃ f, 2 ≤ f ∧ (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f := by
  have hrank : demushkinRank hG = n := by
    rw [demushkinRank_presentedProP (Set.singleton_subset_iff.2 hr) hG, Nat.card_fin]
  rcases hG.range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd_demushkinRank
    (by rwa [hrank]) with h | ⟨hn₃, hf⟩
  · exact Or.inl h
  · exact Or.inr ⟨by omega, hf⟩

end freeProP

end Relator

/-- **The existence theorem of the classification for odd rank, as an equivalence** (Labute,
Theorem 1 and Remark 2; Serre, Theorem 3.2). Let `n` be odd and let `A ≤ ℤ₂ˣ` be a subgroup. Then
`(n, A)` is the pair of invariants of a Demushkin group, presented on `n` generators by one relator,
exactly when `A = {±1}`, or `n ≥ 3` and `A = {±1} × U^(f)` for some `f ≥ 2`. At `n = 1` the only
admissible image is `{±1}`, the image of the canonical character of `ℤ/2`. Every such `A` is
closed and pro-`2`, so no hypothesis on `A` is needed. -/
theorem exists_isDemushkin_range_demushkinCharacter_eq_iff_of_odd {n : ℕ} (hn : Odd n)
    {A : Subgroup ℤ_[2]ˣ} :
    (∃ r : freeProP 2 (Fin n), ∃ hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}),
        demushkinRank hG = n ∧ (demushkinCharacter hG).toMonoidHom.range = A) ↔
      A = zpowers (-1 : ℤ_[2]ˣ) ∨ 3 ≤ n ∧ ∃ f, 2 ≤ f ∧ A = unitsPlusMinus f := by
  constructor
  · rintro ⟨r, hG, hrank, rfl⟩
    rcases hG.range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd_demushkinRank
      (by rwa [hrank]) with h | ⟨hn₃, hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hf⟩
  · rintro (rfl | ⟨hn₃, f, hf, rfl⟩)
    · obtain ⟨r, hG, hrank, -, hrange⟩ := exists_isDemushkin_range_eq_zpowers_neg_one_of_odd hn
      exact ⟨r, hG, hrank, hrange _ (hasPrescriptionProperty_demushkinCharacter hG)⟩
    · obtain ⟨r, hG, hrank, -, hrange⟩ :=
        exists_isDemushkin_range_eq_unitsPlusMinus_of_odd hn hn₃ hf
      exact ⟨r, hG, hrank, hrange _ (hasPrescriptionProperty_demushkinCharacter hG)⟩

end TauCeti
