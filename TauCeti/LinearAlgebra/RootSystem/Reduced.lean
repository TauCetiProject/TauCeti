/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.Tactic.Module

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

## Main results

* `RootPairing.isReduced_of_pairing_comm`: a root pairing with symmetric pairings is reduced.
* `RootPairing.ne_neg_of_root_eq_add_nsmul`: in a reduced root pairing, a root string through a
  root `j ≠ -s` in the direction `s` never reaches `-s`.
* `RootPairing.root_ne_and_root_ne_neg_of_root_eq_add`: in a reduced root pairing, a summand of a
  root that is a sum of two roots is neither that root nor its negative.
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

omit [IsDomain R] [NeZero (2 : R)] [Module.IsTorsionFree R M] in
/-- A root `k = j + n • s` with `j ≠ -s` is not `-s`: otherwise `-j` would be a positive multiple
of `s`, which a reduced root pairing excludes. -/
lemma ne_neg_of_root_eq_add_nsmul [CharZero R] [HasUniqueDiv M] [P.IsReduced] (s : ι) {j k : ι}
    (hj : let _i := P.indexNeg; j ≠ -s) {n : ℕ} (hkroot : P.root k = P.root j + n • P.root s) :
    let _i := P.indexNeg; k ≠ -s := by
  intro _i
  rintro rfl
  replace hkroot : P.root (-j) = (n + 1) • P.root s := by
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self,
      neg_eq_iff_add_eq_zero, add_smul, one_smul] at hkroot ⊢
    rw [← hkroot]
    module
  rcases n.eq_zero_or_pos with rfl | hn
  · apply hj
    rw [zero_add, one_smul, EmbeddingLike.apply_eq_iff_eq] at hkroot
    simp [← hkroot, -indexNeg_neg]
  · have _i : (n + 1).AtLeastTwo := ⟨by omega⟩
    exact P.nsmul_notMem_range_root (n := n + 1) (i := s) ⟨-j, hkroot⟩

section Sum

variable [P.IsReduced]

omit [Module.IsTorsionFree R M] in
/-- If a root is the sum of two roots, then each summand is neither that root nor its negative. -/
theorem root_ne_and_root_ne_neg_of_root_eq_add [CharZero R] {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    P.root i ≠ P.root k ∧ P.root i ≠ -P.root k := by
  have hadd : P.root i + P.root j ∈ Set.range P.root := ⟨k, hk⟩
  have hlin := P.linearIndependent_of_add_mem_range_root' hadd
  refine ⟨fun h ↦ P.ne_zero j (by simpa [hk] using h), fun h ↦ ?_⟩
  have hrel : (2 : R) • P.root i + (1 : R) • P.root j = 0 := by
    rw [one_smul, two_smul, add_assoc, ← hk, h, neg_add_cancel]
  exact one_ne_zero (hlin.eq_zero_of_pair hrel).2

end Sum

end RootPairing
