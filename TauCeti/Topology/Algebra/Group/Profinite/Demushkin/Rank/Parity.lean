/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupForm

/-!
# Parity of the rank of a Demushkin group

When every cup square on `H¹(G, 𝔽_p)` vanishes, the cup form of a Demushkin group
(`LinearMap.cupForm`) is a nondegenerate alternating form, so the Demushkin rank is even. At an odd
prime this is automatic by graded commutativity (`LinearMap.isAlt_cupForm_of_ne_two`); in particular
the rank cannot be one there. This is the parity constraint on the odd-prime normal forms. At
`p = 2` the vanishing of the cup squares is decided by Labute's invariant `q`, in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare`.

## Main results

* `TauCeti.IsDemushkin.even_demushkinRank_of_forall_cupFp_self_eq_zero`: the rank is even when
  every cup square vanishes.
* `TauCeti.IsDemushkin.even_demushkinRank_of_ne_two`: the rank is even at an odd prime.
* `TauCeti.IsDemushkin.demushkinRank_ne_one_of_ne_two`: rank one occurs only at `p = 2`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **A Demushkin group on which every cup square vanishes has even rank**: the cup form is then
a nondegenerate alternating form on `H¹(G, 𝔽_p)`, whose dimension is the rank. -/
theorem IsDemushkin.even_demushkinRank_of_forall_cupFp_self_eq_zero (hG : IsDemushkin p G)
    (h : ∀ a : cohomFp p G 1, cupFp p G a a = 0) : Even (demushkinRank hG) := by
  obtain ⟨e⟩ := hG.nonempty_linearEquiv_cohomFp_two
  exact hG.even_demushkinRank_of_isAlt (DFunLike.ne_iff.2 ⟨e.symm 1, by simp⟩)
    ((e.toLinearMap.isAlt_cupForm_iff_of_injective e.injective).2 h)

/-- At an odd prime, the rank of a Demushkin group is even: every cup square vanishes, because the
cup product is graded-commutative and `2` is invertible. -/
theorem IsDemushkin.even_demushkinRank_of_ne_two (hG : IsDemushkin p G) (hp : p ≠ 2) :
    Even (demushkinRank hG) :=
  hG.even_demushkinRank_of_forall_cupFp_self_eq_zero (cupFp_self_eq_zero_of_ne_two p G hp)

/-- A Demushkin group at an odd prime cannot have rank one. -/
theorem IsDemushkin.demushkinRank_ne_one_of_ne_two (hG : IsDemushkin p G) (hp : p ≠ 2) :
    demushkinRank hG ≠ 1 := by
  intro h
  exact Nat.not_even_one (h ▸ hG.even_demushkinRank_of_ne_two hp)

end TauCeti
