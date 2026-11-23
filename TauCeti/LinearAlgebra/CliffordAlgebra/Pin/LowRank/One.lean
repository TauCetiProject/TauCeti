/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.FullCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Real
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import TauCeti.Algebra.Order.Ring.Square

/-!
# The real Pin groups in rank one

The normalized full Clifford covers of the real signature forms of rank one, `Cliff(0, 1)` and
`Cliff(1, 0)`, are groups of order four. Mathlib's Pin group, of `star` norm `1`, is all of the
first but only `{±1}` in the second.

* In `Cliff(0, 1)`, where `e ^ 2 = -1`, the generator has `e * star e = -e ^ 2 = 1`, and the form
  takes no positive value, so the Pin group is the whole full cover.
* In `Cliff(1, 0)`, where `e ^ 2 = 1`, the Pin image in `O(1)` is the trivial group `SO(1)`, so the
  Pin group is the kernel `{±1}` of the full-cover action.

## Main results

* `CliffordAlgebra.pinToCliffordFullCover_surjective_realCliffordForm_zero_one`: the Pin group of
  `Cliff(0, 1)` is the whole full cover.
* `CliffordAlgebra.range_pinToCliffordFullCover_realCliffordForm_one_zero` and
  `CliffordAlgebra.card_range_pinToCliffordFullCover_realCliffordForm_one_zero`: the Pin group of
  `Cliff(1, 0)` is `{±1}`, of order two.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

/-- **The Pin group of `Cliff(0, 1)` is the whole full cover**: the generator `e` has
`e * star e = -e ^ 2 = 1`. -/
theorem pinToCliffordFullCover_surjective_realCliffordForm_zero_one :
    Function.Surjective (pinToCliffordFullCover (realCliffordForm 0 1)) := by
  refine (pinToCliffordFullCover_surjective_iff _ (nondegenerate_realCliffordForm 0 1)).2 fun v ↦ ?_
  rw [realCliffordForm_apply]
  refine Finset.sum_nonpos fun i _ ↦ ?_
  rw [realCliffordWeight_of_le (Nat.zero_le _)]
  nlinarith [mul_self_nonneg (v i)]

/-- **The Pin group of `Cliff(1, 0)` is only `{±1}`**: its image `SO(1)` is trivial, so it is the
kernel of the full-cover action. -/
theorem range_pinToCliffordFullCover_realCliffordForm_one_zero :
    (pinToCliffordFullCover (realCliffordForm 1 0)).range =
      (cliffordFullCoverToOrthogonal (realCliffordForm 1 0)).ker := by
  have hQ := nondegenerate_realCliffordForm 1 0
  have hbot : (pinToOrthogonal (realCliffordForm 1 0)).range = ⊥ := by
    have h := Subgroup.card_mul_index (pinToOrthogonal (realCliffordForm 1 0)).range
    rw [index_range_pinToOrthogonal _ hQ ⟨Pi.single 0 1, by simp⟩,
      QuadraticMap.card_orthogonalGroup_of_finrank_eq_one hQ.ne_zero (by simp)] at h
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  rw [← comap_range_pinToOrthogonal hQ not_isSquare_neg_one, hbot,
    MonoidHom.comap_bot]

/-- The Pin group of `Cliff(1, 0)` has order two. -/
theorem card_range_pinToCliffordFullCover_realCliffordForm_one_zero :
    Nat.card (pinToCliffordFullCover (realCliffordForm 1 0)).range = 2 := by
  have : Nontrivial (Fin (1 + 0) → ℝ) :=
    Module.nontrivial_of_finrank_eq_succ (R := ℝ) (n := 0) (by simp)
  rw [range_pinToCliffordFullCover_realCliffordForm_one_zero,
    card_ker_cliffordFullCoverToOrthogonal (nondegenerate_realCliffordForm 1 0)
      not_isSquare_neg_one]

end CliffordAlgebra
