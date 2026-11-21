/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import Mathlib.FieldTheory.IsRealClosed.Real
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.RankOne

/-!
# The real full Clifford covers in rank one

The normalized full Clifford covers of the real signature forms of rank one, `Cliff(0, 1)` and
`Cliff(1, 0)`, are both extensions of `O(1) = {±1}` by `{±1}`, groups of order four, but they are
not isomorphic.

* In `Cliff(0, 1)`, where `e ^ 2 = -1`, the full cover is `{±1, ±e}`, cyclic of order four.
* In `Cliff(1, 0)`, where `e ^ 2 = 1`, the full cover is not cyclic: `1`, `-1` and `e` all square
  to `1`.

## Main results

* `CliffordAlgebra.card_cliffordFullCover_realCliffordForm`: the full covers in rank one have order
  four.
* `CliffordAlgebra.isCyclic_cliffordFullCover_realCliffordForm_zero_one` and
  `CliffordAlgebra.not_isCyclic_cliffordFullCover_realCliffordForm_one_zero`: the full cover of
  `Cliff(0, 1)` is cyclic and that of `Cliff(1, 0)` is not.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

/-- **The full covers in rank one have order four**: those of `Cliff(1, 0)` and `Cliff(0, 1)` are
both extensions of `O(1) = {±1}` by `{±1}`. -/
theorem card_cliffordFullCover_realCliffordForm {p q : ℕ} (hpq : p + q = 1) :
    Nat.card (cliffordFullCover (realCliffordForm p q)) = 4 :=
  card_cliffordFullCover_of_finrank_eq_one (nondegenerate_realCliffordForm p q)
    (by rw [Module.finrank_fin_fun, hpq]) (fun h ↦ absurd h.nonneg (by norm_num))
    IsRealClosed.isSquare_or_isSquare_neg

/-- **The full cover of `Cliff(0, 1)` is cyclic**: the generator `e`, with `e ^ 2 = -1`, has order
four. -/
theorem isCyclic_cliffordFullCover_realCliffordForm_zero_one :
    IsCyclic (cliffordFullCover (realCliffordForm 0 1)) :=
  (isCyclic_cliffordFullCover_iff_of_finrank_eq_one (nondegenerate_realCliffordForm 0 1)
    (by simp) (fun h ↦ absurd h.nonneg (by norm_num))
    IsRealClosed.isSquare_or_isSquare_neg).2 ⟨Pi.single 0 1, by simp⟩

/-- **The full cover of `Cliff(1, 0)` is not cyclic**: `1`, `-1` and the generator `e`, with
`e ^ 2 = 1`, all square to `1`. -/
theorem not_isCyclic_cliffordFullCover_realCliffordForm_one_zero :
    ¬IsCyclic (cliffordFullCover (realCliffordForm 1 0)) := by
  rw [isCyclic_cliffordFullCover_iff_of_finrank_eq_one (nondegenerate_realCliffordForm 1 0)
    (by simp) (fun h ↦ absurd h.nonneg (by norm_num)) IsRealClosed.isSquare_or_isSquare_neg]
  rintro ⟨v, hv⟩
  linarith [(posDef_realCliffordForm_zero 1).nonneg v]

end CliffordAlgebra
