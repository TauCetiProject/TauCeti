/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.LinearlyReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.AdditiveSubgroup
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Linear reductivity of general linear groups detects characteristic zero

For `n ≥ 2`, the group `GLₙ` over a field is linearly reductive exactly in characteristic
zero. Its additive transvection subgroup gives the obstruction in positive characteristic;
complete reducibility in characteristic zero is proved in `GeneralLinear.LinearlyReductive.Basic`.
This gives reductive groups that are not linearly reductive in every positive characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.g and Chapter 22.
-/

public section

namespace TauCeti.GeneralLinear

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- For `n ≥ 2`, `GLₙ` is linearly reductive exactly when the field has characteristic zero. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra_iff (hn : 2 ≤ n) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) ↔ CharZero k := by
  constructor
  · intro h
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by simp [i, j]
    apply HopfAlgebra.charZero_of_isLinearlyReductive_of_injective_additiveHom
      ((linearlyReductiveCommHopfAlgProperty_iff k _).mp h)
      ((pointsMulEquiv (R := k) n).symm.toMonoidHom.comp (transvectionHom (A := k) hij))
    exact (pointsMulEquiv (R := k) n).symm.injective.comp (transvectionHom_injective hij)
  · intro h
    let _ := h
    exact linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra k n

/-- In positive characteristic, `GLₙ` is not linearly reductive for `n ≥ 2`. -/
theorem not_linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra
    (p : ℕ) [NeZero p] [CharP k p] (hn : 2 ≤ n) :
    ¬ linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  intro h
  let _ := (linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra_iff k n hn).mp h
  exact (Nat.cast_ne_zero.mpr (NeZero.ne p)) (CharP.cast_eq_zero k p)

end TauCeti.GeneralLinear
