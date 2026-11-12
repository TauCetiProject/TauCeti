/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.LinearlyReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.AdditiveSubgroup
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Linear reductivity of special linear groups detects characteristic zero

For `n ≥ 2`, the group `SLₙ` over a field is linearly reductive exactly in characteristic
zero. The elementary transvections embed the additive group of the field in its rational
points, giving the positive-characteristic obstruction. Thus these smooth connected
reductive groups distinguish reductivity from linear reductivity in positive characteristic.
The characteristic-zero direction is the complete reducibility theorem in
`SpecialLinear.LinearlyReductive.Basic`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.g and Chapter 22.
-/

public section

namespace TauCeti.SpecialLinear

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- For `n ≥ 2`, `SLₙ` is linearly reductive exactly when the field has characteristic zero. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra_iff (hn : 2 ≤ n) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) ↔ CharZero k := by
  constructor
  · intro h
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by simp [i, j]
    let f := Matrix.SpecialLinearGroup.transvectionHom (A := k) hij
    apply HopfAlgebra.charZero_of_isLinearlyReductive_of_injective_additiveHom
      ((linearlyReductiveCommHopfAlgProperty_iff k _).mp h)
      ((pointsMulEquiv (A := k) k n).symm.toMonoidHom.comp f)
    refine (pointsMulEquiv (A := k) k n).symm.injective.comp fun a b hab ↦ ?_
    apply Multiplicative.toAdd.injective
    apply Matrix.SpecialLinearGroup.transvection_injective hij
    simpa only [f, Matrix.SpecialLinearGroup.transvectionHom_apply] using hab
  · intro h
    let _ := h
    exact linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra k n

/-- In positive characteristic, `SLₙ` is not linearly reductive for `n ≥ 2`. -/
theorem not_linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra
    (p : ℕ) [NeZero p] [CharP k p] (hn : 2 ≤ n) :
    ¬ linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  intro h
  let _ := (linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra_iff k n hn).mp h
  exact (Nat.cast_ne_zero.mpr (NeZero.ne p)) (CharP.cast_eq_zero k p)

end TauCeti.SpecialLinear
