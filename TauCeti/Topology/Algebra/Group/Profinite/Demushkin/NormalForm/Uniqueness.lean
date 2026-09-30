/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.OddPrime

/-!
# Uniqueness of Demushkin groups at an odd prime with `q = p`

Labute's classification says that a Demushkin group is determined up to topological isomorphism
by its rank `n` and the image of its canonical character, which for `p` odd is `1 + q ℤ_p` for the
`q`-invariant `q` of the group. This file proves the uniqueness statement in the case `p` odd and
`q = p`, in intrinsic form: the hypotheses are the rank and the `q`-invariant of the group, and no
presentation is chosen in the statement.

The input is Labute's exact normal form `x₁^p (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, in its intrinsic
form: a Demushkin group at an odd prime with `q`-invariant `p` is presented by that word on
`demushkinRank hG` generators
(`TauCeti.IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_eq`),
and a relator in `Φ(F)` presenting a Demushkin group with `q`-invariant `p` is carried to that word
by a continuous automorphism of `F`
(`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_odd`, through
`TauCeti.demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero`). Two groups, or
two relators, with the same invariants are then compared through their common normal form.

## Main results

* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_odd_of_demushkinQ_eq`: Labute's
  Theorem 2 in this case, two relators in `Φ(F)` presenting Demushkin groups with `q = p` are
  carried to each other by a continuous automorphism of `F`.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_odd_of_demushkinQ_eq`: two Demushkin groups
  at an odd prime with `q = p` and the same rank are topologically isomorphic.

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

/-- **Labute's Theorem 2 at an odd prime with `q = p`.** Let `p` be odd and let `r, r' ∈ Φ(F)` be
relators of the free pro-`p` group on `n` generators whose presented groups are Demushkin groups
with `q`-invariant `p`. Then a continuous automorphism of `F` carries `r` to `r'`; in particular
the closed normal closures of `r` and `r'` are carried to each other. -/
theorem freeProP.exists_continuousMulEquiv_apply_eq_of_odd_of_demushkinQ_eq (hp : Odd p)
    {r r' : freeProP p (Fin n)} (hr : r ∈ proPFrattini p (freeProP p (Fin n)))
    (hr' : r' ∈ proPFrattini p (freeProP p (Fin n)))
    (hG : IsDemushkin p (presentedProP p (Fin n) {r}))
    (hG' : IsDemushkin p (presentedProP p (Fin n) {r'}))
    (hq : demushkinQ hG = p) (hq' : demushkinQ hG' = p) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n), e r = r' := by
  obtain ⟨e, he⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_odd hp _
    (hG.nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _))
    ((demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero hr hG).1 hq)
  obtain ⟨e', he'⟩ := exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_odd hp _
    (hG'.nondegenerate_degreeOneForm hr' (ContinuousMulEquiv.refl _))
    ((demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero hr' hG').1 hq')
  have he₀ : e r = demushkinWordNeTwo p n (freeProPGen p n) := he
  have he₀' : e' r' = demushkinWordNeTwo p n (freeProPGen p n) := he'
  exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he₀, ← he₀', e'.symm_apply_apply]⟩

end Relator

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Uniqueness of Demushkin groups at an odd prime with `q = p`** (Labute, Theorems 2 and 3).
Two Demushkin groups at an odd prime `p` with `q`-invariant `p` and the same rank are
topologically isomorphic. -/
theorem IsDemushkin.nonempty_continuousMulEquiv_of_odd_of_demushkinQ_eq {H : Type v} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hG : IsDemushkin p G) (hH : IsDemushkin p H) (hp : Odd p) (hq : demushkinQ hG = p)
    (hq' : demushkinQ hH = p) (hn : demushkinRank hG = demushkinRank hH) :
    Nonempty (G ≃ₜ* H) := by
  obtain ⟨e⟩ :=
    hG.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_eq hp hq
  obtain ⟨e'⟩ :=
    hH.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_eq hp hq'
  rw [hn] at e
  exact ⟨e.trans e'.symm⟩

end TauCeti
