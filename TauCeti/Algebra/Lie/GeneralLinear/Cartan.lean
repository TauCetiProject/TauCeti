/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
public import TauCeti.Algebra.Lie.Matrix.NegTranspose

import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.SpecialLinear.Cartan.Killing

/-!
# Cartan involutions of the general linear Lie algebra

The negative-transpose automorphism `TauCeti.negTransposeLieEquiv n K` is a reductive Cartan
involution of `gl n K` over every ordered field `K`, because it is involutive and restricts on the
derived algebra `[gl n K, gl n K] = sl n K` to `LieAlgebra.SpecialLinear.cartanInvolution`
(`TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv`).

## Main results

* `TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv`: `X ↦ -Xᵀ` is a reductive Cartan
  involution of `gl n K`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–2 and Chapter VII, §2.
-/

public section

namespace TauCeti

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Negative transpose is a reductive Cartan involution of `gl n K`** over every ordered field
`K`, since its restriction to `[gl n K, gl n K] = sl n K` is
`LieAlgebra.SpecialLinear.cartanInvolution`. -/
theorem isReductiveCartanInvolution_negTransposeLieEquiv
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (negTransposeLieEquiv n K).IsReductiveCartanInvolution := by
  rw [LieEquiv.isReductiveCartanInvolution_iff]
  refine ⟨fun X ↦ by simp, ?_⟩
  let e : derivedSeries K (Matrix n n K) 1 ≃ₗ⁅K⁆ LieAlgebra.SpecialLinear.sl n K :=
    LieEquiv.ofEq (derivedSeries K (Matrix n n K) 1).toLieSubalgebra
      (LieAlgebra.SpecialLinear.sl n K)
      (by rw [derivedSeries_one_toLieSubalgebra_eq_sl])
  refine (LieEquiv.isCartanInvolution_iff_of_intertwine e
    (θ' := LieAlgebra.SpecialLinear.cartanInvolution n K) fun x ↦ ?_).mp ?_
  · apply Subtype.ext
    have he (y : derivedSeries K (Matrix n n K) 1) : (e y : Matrix n n K) = y :=
      LieEquiv.ofEq_apply (derivedSeries K (Matrix n n K) 1).toLieSubalgebra
        (LieAlgebra.SpecialLinear.sl n K)
        (by rw [derivedSeries_one_toLieSubalgebra_eq_sl]) y
    rw [LieAlgebra.SpecialLinear.coe_cartanInvolution, he, he,
      LieEquiv.coe_derivedSeriesCongr, negTransposeLieEquiv_apply]
  · exact LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution

end TauCeti
