/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.NeTwo

/-!
# Uniqueness of Demushkin groups with `q ≠ 2`

Labute's classification says that a Demushkin group is determined up to topological isomorphism
by its rank `n` and the image of its canonical character, which for `q ≠ 2` is `1 + q ℤ_p` for the
`q`-invariant `q` of the group. This file proves the uniqueness statement in the case `q ≠ 2`, in
intrinsic form: the hypotheses are the rank and the `q`-invariant of the group, and no presentation
is chosen in the statement.

The input is Labute's exact normal form `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` for `q ≠ 2`, in
its intrinsic form: a Demushkin group with `q`-invariant `q ≠ 2` is presented by that word on
`demushkinRank hG` generators, by
`IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two`,
and a relator in `Φ(F)` presenting a Demushkin group with `q`-invariant `q ≠ 2` is carried to that
word by a continuous automorphism of `F`
(`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two`).
Two groups, or two relators, with the same invariants are then compared through their common
normal form.

## Main results

* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_demushkinQ_eq`: Labute's Theorem 2 for
  `q ≠ 2`, two relators in `Φ(F)` presenting Demushkin groups with the same `q`-invariant `q ≠ 2`
  are carried to each other by a continuous automorphism of `F`.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_demushkinQ_eq`: two Demushkin groups with
  the same `q`-invariant `q ≠ 2` and the same rank are topologically isomorphic.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorems 2 and 3.
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

end TauCeti
