/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# A symmetry criterion for reduced root pairings

A root pairing over a domain in which `2 ≠ 0`, with torsion-free weight module, is reduced as
soon as its pairing is symmetric on roots and coroots. Indeed, if the roots indexed by `i` and
`j` are linearly dependent, then `P.pairing j i • P.root i = 2 • P.root j` and
`P.pairing i j • P.root j = 2 • P.root i`. Symmetry makes these two pairing values equal, so
their common value squares to `4` and is `2` or `-2`; cancelling the factor `2` then identifies
the two roots up to sign. No finiteness of the index type is needed.

This criterion is useful for root data presented in dual coordinate bases. Their roots and
coroots need not be equal as coordinate vectors, while the pairing can still visibly be the
symmetric form of a simply-laced Cartan matrix.

## Main result

* `RootPairing.isReduced_of_pairing_comm`: a root pairing with symmetric pairings is reduced.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- A root pairing whose root--coroot pairing is symmetric is reduced. -/
theorem isReduced_of_pairing_comm
    (hcomm : ∀ i j, P.pairing i j = P.pairing j i) : P.IsReduced := by
  refine ⟨fun i j hdependent => ?_⟩
  have hi := P.pairing_smul_root_eq_of_not_linearIndependent hdependent
  have hj := P.pairing_smul_root_eq_of_not_linearIndependent
    (by rwa [LinearIndependent.pair_symm_iff] at hdependent)
  rw [hcomm] at hj
  have hsquare : P.pairing j i * P.pairing j i = 2 * 2 := by
    refine smul_left_injective R (P.ne_zero i) ?_
    simp only [mul_smul, hi, hj, smul_comm (P.pairing j i) (2 : R)]
  rcases mul_self_eq_mul_self_iff.mp hsquare with htwo | hnegTwo
  · exact .inl (smul_right_injective M two_ne_zero (htwo ▸ hi))
  · rw [hnegTwo, neg_smul, neg_eq_iff_eq_neg, ← smul_neg] at hi
    exact .inr (smul_right_injective M two_ne_zero hi)

end RootPairing
