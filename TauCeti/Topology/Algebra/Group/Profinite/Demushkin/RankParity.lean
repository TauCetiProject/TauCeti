/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Parity of the rank of a Demushkin group

When every cup square on `H¹(G, 𝔽_p)` vanishes, the degree-one cup pairing of a Demushkin group is
a nondegenerate alternating form, so the Demushkin rank is even. At an odd prime this is automatic
by graded commutativity; in particular the rank cannot be one there. This is the parity constraint
on the odd-prime normal forms. At `p = 2` the vanishing of the cup squares is decided by Labute's
invariant `q`, in `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare`.

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

/-- **A Demushkin group on which every cup square vanishes has even rank**: the cup pairing is
then a nondegenerate alternating form on `H¹(G, 𝔽_p)`, whose dimension is the rank. -/
theorem IsDemushkin.even_demushkinRank_of_forall_cupFp_self_eq_zero (hG : IsDemushkin p G)
    (h : ∀ a : cohomFp p G 1, cupFp p G a a = 0) : Even (demushkinRank hG) := by
  have : Module.Finite (ZMod p) (cohomFp p G 1) := hG.finite_cohomFp_one
  let τ : cohomFp p G 2 ≃ₗ[ZMod p] ZMod p :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one hG.finrank_cohomFp_two).some.symm
  let B : LinearMap.BilinForm (ZMod p) (cohomFp p G 1) :=
    (cupFp p G).compr₂ τ.toLinearMap
  have halt : B.IsAlt := fun a ↦ by simp [B, h a]
  have hB : B.Nondegenerate := by
    apply (@LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (ZMod p) (cohomFp p G 1) (ZMod p) _ _ _ _ Semiring.toModule B halt.isRefl).mpr
    intro a ha
    by_contra hne
    obtain ⟨b, hb⟩ := hG.cup_separatingLeft a hne
    have hab : τ (cupFp p G a b) = 0 := by
      calc
        τ (cupFp p G a b) = B a b := by
          simp only [B, LinearMap.compr₂_apply, LinearEquiv.coe_toLinearMap]
        _ = 0 := ha b
    exact hb (τ.injective (by simpa using hab))
  rw [← hG.finrank_cohomFp_one]
  exact halt.even_finrank hB

/-- At an odd prime, the rank of a Demushkin group is even: every cup square vanishes, because the
cup product is graded-commutative and `2` is invertible. -/
theorem IsDemushkin.even_demushkinRank_of_ne_two (hG : IsDemushkin p G) (hp : p ≠ 2) :
    Even (demushkinRank hG) := by
  refine hG.even_demushkinRank_of_forall_cupFp_self_eq_zero fun a ↦ ?_
  have htwo : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two hp
  have hsmul : (2 : ZMod p) • cupFp p G a a = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr (cupFp_gradedComm p G a a)
  exact (smul_eq_zero.mp hsmul).resolve_left htwo

/-- A Demushkin group at an odd prime cannot have rank one. -/
theorem IsDemushkin.demushkinRank_ne_one_of_ne_two (hG : IsDemushkin p G) (hp : p ≠ 2) :
    demushkinRank hG ≠ 1 := by
  intro h
  exact Nat.not_even_one (h ▸ hG.even_demushkinRank_of_ne_two hp)

end TauCeti
