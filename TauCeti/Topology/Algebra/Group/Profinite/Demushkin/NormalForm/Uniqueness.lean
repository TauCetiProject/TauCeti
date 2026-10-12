/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.NeTwo
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Odd.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Endpoint
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Twisted
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.UnitsPlusMinus

/-!
# Uniqueness of Demushkin groups

Labute's classification says that a Demushkin group is determined up to topological isomorphism
by its rank `n` and the image of its canonical character `χ : G → ℤ_pˣ`. This file proves that
uniqueness statement in full, in two forms. The relator form is Labute's Theorem 2: two relators
`r, r'` of the free pro-`p` group `F` on `n` generators presenting Demushkin groups whose canonical
characters have the same image are carried to each other by a continuous automorphism of `F`; such
relators lie in `Φ(F)` automatically, since a one-relator presentation of a Demushkin group is
minimal (`TauCeti.IsDemushkin.mem_proPFrattini_of_presentedProP_singleton`). The intrinsic form
follows: two Demushkin groups of the same rank whose canonical characters
have the same image are topologically isomorphic. The relator form is what turns "isomorphic" into
"isomorphic by a change of basis of `F`", so that the normal forms of the classification are a
normalization of the relator and not a choice.

The proof reads the invariants and dispatches to the normal form of each family. The image
determines the `q`-invariant (`TauCeti.demushkinQ_eq_of_range_demushkinCharacter_eq`). For
`q ≠ 2` the normal form is `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`
(`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two`).
For `q = 2`, so `p = 2`, and odd rank, it is `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` at the level
`f` of the image `{±1} × U^(f)`, or `x₁² (x₂, x₃) ⋯ (x_{n-1}, x_n)` when the image is `{±1}`
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Odd.Image`). For `q = 2` and
even rank the image is `{±1}`, `{±1} × U^(f)` or Labute's twisted subgroup `U^[f]`
(`TauCeti.IsDemushkin.range_demushkinCharacter_trichotomy_of_demushkinQ_eq_two`), with normal
forms `x₁² (x₁, x₂)(x₃, x₄) ⋯`, `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯` and
`x₁^{2 + 2^f} (x₁, x₂)(x₃, x₄) ⋯` respectively
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Endpoint`,
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.UnitsPlusMinus`,
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Twisted`); the second does
not occur at rank two, where the image is procyclic
(`TauCeti.IsDemushkin.range_demushkinCharacter_ne_unitsPlusMinus_of_demushkinRank_eq_two`). Two
relators with the same invariants are then compared through their common normal form, and two
groups through presentations by relators in `Φ(F)`.

## Main results

* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_demushkinCharacter_eq`:
  **Labute's Theorem 2**, two relators presenting Demushkin groups whose canonical characters have
  the same image are carried to each other by a continuous automorphism of `F`.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_range_demushkinCharacter_eq`: **uniqueness in
  the classification of Demushkin groups**, two Demushkin groups of the same rank whose canonical
  characters have the same image are topologically isomorphic.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_demushkinQ_eq` and
  `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_demushkinQ_eq`: the two statements for
  `q ≠ 2`, where the image is `1 + qℤ_p` and the invariant may be taken to be `q` itself.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_demushkinCharacter_eq_of_odd`:
  Labute's Theorem 2 for odd rank, the dyadic case proved from the odd normal forms alone.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorems 2 and 3, and §4, Theorems 5 and 6.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

universe u v

open freeProP

variable {p : ℕ} [Fact p.Prime]

section Relator

variable {n : ℕ}

/-- **Labute's Theorem 2 for `q ≠ 2`.** Let `r, r' ∈ Φ(F)` be relators of the free pro-`p` group
on `n` generators whose presented groups are Demushkin groups with the same `q`-invariant `q ≠ 2`.
Then a continuous automorphism of `F` carries `r` to `r'`; in particular the closed normal
closures of `r` and `r'` are carried to each other. -/
theorem freeProP.exists_continuousMulEquiv_apply_eq_of_demushkinQ_eq
    {r r' : freeProP p (Fin n)} (hr : r ∈ proPFrattini p (freeProP p (Fin n)))
    (hr' : r' ∈ proPFrattini p (freeProP p (Fin n)))
    (hG : IsDemushkin p (presentedProP p (Fin n) {r}))
    (hG' : IsDemushkin p (presentedProP p (Fin n) {r'}))
    (hq : demushkinQ hG = demushkinQ hG') (hq2 : demushkinQ hG ≠ 2) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n), e r = r' := by
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two hr hG hq2
  obtain ⟨e', he'⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two hr'
    hG' fun h ↦ hq2 (hq.trans h)
  rw [← hq] at he'
  exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he, ← he', e'.symm_apply_apply]⟩

/-- **Labute's Theorem 2 for odd rank.** Let `r, r' ∈ Φ(F)` be relators of the free pro-`2` group
on an odd number `n` of generators whose presented groups are Demushkin groups whose canonical
characters have the same image. Then a continuous automorphism of `F` carries `r` to `r'`; in
particular the closed normal closures of `r` and `r'` are carried to each other. -/
theorem freeProP.exists_continuousMulEquiv_apply_eq_of_range_demushkinCharacter_eq_of_odd
    (hn : Odd n) {r r' : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hr' : r' ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}))
    (hG' : IsDemushkin 2 (presentedProP 2 (Fin n) {r'}))
    (h : (demushkinCharacter hG).toMonoidHom.range = (demushkinCharacter hG').toMonoidHom.range) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n), e r = r' := by
  rcases range_demushkinCharacter_eq_zpowers_neg_one_or_unitsPlusMinus_of_odd hn hr hG with
    hrange | ⟨hn₃, f, hf, hrange⟩
  · obtain ⟨e, he⟩ :=
      exists_continuousMulEquiv_apply_eq_demushkinWordTwoOddTop_of_range_eq hn hr hG hrange
    obtain ⟨e', he'⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordTwoOddTop_of_range_eq hn hr'
      hG' (h.symm.trans hrange)
    exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he, ← he', e'.symm_apply_apply]⟩
  · obtain ⟨e, he⟩ :=
      exists_continuousMulEquiv_apply_eq_demushkinWordTwoOdd_of_range_eq hn hn₃ hr hG hf hrange
    obtain ⟨e', he'⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordTwoOdd_of_range_eq hn hn₃
      hr' hG' hf (h.symm.trans hrange)
    exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he, ← he', e'.symm_apply_apply]⟩

/-- **Labute's Theorem 2.** Let `r, r'` be relators of the free pro-`p` group `F` on `n`
generators whose presented groups are Demushkin groups whose canonical characters have the same
image. Then a continuous automorphism of `F` carries `r` to `r'`; in particular the closed normal
closures of `r` and `r'` are carried to each other, so two Demushkin relators with the same
invariants differ by a change of basis of `F`. The relators lie in `Φ(F)` and both groups have rank
`n` automatically (`TauCeti.IsDemushkin.mem_proPFrattini_of_presentedProP_singleton`). -/
theorem freeProP.exists_continuousMulEquiv_apply_eq_of_range_demushkinCharacter_eq
    {r r' : freeProP p (Fin n)} (hG : IsDemushkin p (presentedProP p (Fin n) {r}))
    (hG' : IsDemushkin p (presentedProP p (Fin n) {r'}))
    (h : (demushkinCharacter hG).toMonoidHom.range = (demushkinCharacter hG').toMonoidHom.range) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n), e r = r' := by
  have hr := hG.mem_proPFrattini_of_presentedProP_singleton
  have hr' := hG'.mem_proPFrattini_of_presentedProP_singleton
  by_cases hq : demushkinQ hG = 2
  swap
  · exact exists_continuousMulEquiv_apply_eq_of_demushkinQ_eq hr hr' hG hG'
      (demushkinQ_eq_of_range_demushkinCharacter_eq hG hG' h) hq
  -- `q(G) = 2` forces `p = 2`, since `p ∣ q(G)`.
  obtain rfl : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 (hq ▸ hG.prime_dvd_demushkinQ)
  rcases Nat.even_or_odd n with hn | hn
  swap
  · exact exists_continuousMulEquiv_apply_eq_of_range_demushkinCharacter_eq_of_odd hn hr hr' hG hG'
      h
  -- Even rank: the image is `{±1}`, `{±1} × U^(f)` or `U^[f]`, and each pins a normal form.
  rcases hG.range_demushkinCharacter_trichotomy_of_demushkinQ_eq_two hq with
    hA | ⟨f, hf, hA⟩ | ⟨f, u, hf, hu, hA⟩
  · exact exists_continuousMulEquiv_apply_eq_of_range_eq_zpowers_neg_one hn hr hr' hG hG' hA
      (h.symm.trans hA)
  · -- The image `{±1} × U^(f)` is not procyclic, so it does not occur at rank two, and `n ≥ 4`.
    have hn3 : 3 < n := by
      have hn0 : 0 < n := by simpa using hG.card_pos_presentedProP
      have hrank : demushkinRank hG = n := by
        simpa using demushkinRank_presentedProP (Set.singleton_subset_iff.2 hr) hG
      by_contra hn3
      obtain ⟨k, hk⟩ := hn
      exact hG.range_demushkinCharacter_ne_unitsPlusMinus_of_demushkinRank_eq_two
        (hrank.trans (by omega)) hf hA
    obtain ⟨e, he⟩ :=
      exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq hr hG hn hn3 hf hA
    obtain ⟨e', he'⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq hr' hG'
      hn hn3 hf (h.symm.trans hA)
    exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he, ← he', e'.symm_apply_apply]⟩
  · obtain ⟨e, he⟩ :=
      exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq hr hG hn hf hu hA
    obtain ⟨e', he'⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq hr' hG' hn
      hf hu (h.symm.trans hA)
    exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he, ← he', e'.symm_apply_apply]⟩

end Relator

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Uniqueness of Demushkin groups with `q ≠ 2`** (Labute, Theorems 2 and 3). Two Demushkin
groups with the same `q`-invariant `q ≠ 2` and the same rank are topologically isomorphic. -/
theorem IsDemushkin.nonempty_continuousMulEquiv_of_demushkinQ_eq {H : Type v} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hG : IsDemushkin p G) (hH : IsDemushkin p H) (hq : demushkinQ hG = demushkinQ hH)
    (hq2 : demushkinQ hG ≠ 2) (hn : demushkinRank hG = demushkinRank hH) :
    Nonempty (G ≃ₜ* H) := by
  obtain ⟨e⟩ :=
    hG.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two hq2
  obtain ⟨e'⟩ := hH.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two
    fun h ↦ hq2 (hq.trans h)
  rw [hn, hq] at e
  exact ⟨e.trans e'.symm⟩

/-- **Uniqueness in the classification of Demushkin groups** (Labute, Theorems 2 and 3, with
Theorems 5 and 6 for the dyadic groups of even rank). Two Demushkin groups of the same rank whose
canonical characters have the same image are topologically isomorphic. The image determines the
`q`-invariant (`TauCeti.demushkinQ_eq_of_range_demushkinCharacter_eq`), so with the existence
theorems `TauCeti.exists_isDemushkin_range_demushkinCharacter_eq_iff_of_even` and
`TauCeti.exists_isDemushkin_range_demushkinCharacter_eq_iff_of_odd` this classifies the Demushkin
groups by the invariants `(n, Im χ)`. -/
theorem IsDemushkin.nonempty_continuousMulEquiv_of_range_demushkinCharacter_eq {H : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H] (hG : IsDemushkin p G) (hH : IsDemushkin p H)
    (h : (demushkinCharacter hG).toMonoidHom.range = (demushkinCharacter hH).toMonoidHom.range)
    (hn : demushkinRank hG = demushkinRank hH) :
    Nonempty (G ≃ₜ* H) := by
  -- Present both groups by relators in `Φ(F)` on the common rank, and apply Labute's Theorem 2.
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  obtain ⟨r', hr', ⟨e'⟩⟩ : ∃ r' ∈ proPFrattini p (freeProP p (Fin (demushkinRank hG))),
      Nonempty (presentedProP p (Fin (demushkinRank hG)) {r'} ≃ₜ* H) := by
    rw [hn]
    exact hH.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  have : Nonempty (Fin (demushkinRank hG)) := ⟨⟨0, hG.demushkinRank_pos⟩⟩
  have hGr : IsDemushkin p (presentedProP p (Fin (demushkinRank hG)) {r}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _)
      (hG.nondegenerate_degreeOneForm hr e)
  have hHr : IsDemushkin p (presentedProP p (Fin (demushkinRank hG)) {r'}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr' (ContinuousMulEquiv.refl _)
      (hH.nondegenerate_degreeOneForm hr' e')
  obtain ⟨φ, hφ⟩ :=
    freeProP.exists_continuousMulEquiv_apply_eq_of_range_demushkinCharacter_eq hGr hHr
      ((range_demushkinCharacter_of_equiv hG hGr e.symm).trans
        (h.trans (range_demushkinCharacter_of_equiv hH hHr e'.symm).symm))
  exact ⟨e.symm.trans ((presentedProP.congrSingleton φ hφ).trans e')⟩

end TauCeti
