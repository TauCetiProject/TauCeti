/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Dynamic parabolics in characteristic zero

Let `λ : 𝔾ₘ → G` be a cocharacter of a connected affine group of finite type over an
algebraically closed field of characteristic zero. The Lie algebra of the dynamic parabolic
`P(λ)` is the sum of the nonnegative weight spaces of `λ`. If `λ` has no negative weights, then
`Lie P(λ) = Lie G`. Cartier's theorem makes both `G` and `P(λ)` smooth, and a smooth closed
subgroup of a smooth connected group with the full Lie algebra is the whole group. Hence
`P(λ) = G`.

## Main declarations

* `BialgHom.parabolicDefiningHopfIdeal_eq_bot_of_adjointWeightSpace_neg_eq_bot`: a cocharacter
  with no negative adjoint weights has the whole group as its dynamic parabolic.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Over an algebraically closed field of characteristic zero, a cocharacter of a connected
affine group with no negative adjoint weights has the whole group as its dynamic parabolic.** -/
theorem parabolicDefiningHopfIdeal_eq_bot_of_adjointWeightSpace_neg_eq_bot
    [ConnectedSpace (PrimeSpectrum H)] (l : H →ₐc[k] LaurentPolynomial k)
    (hneg : ∀ n : ℤ, n < 0 →
      Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n) = ⊥) :
    parabolicDefiningHopfIdeal l = ⊥ := by
  set π := (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l
  -- Cartier's theorem makes the group and its dynamic parabolic smooth.
  have : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj)
  have : Algebra.Smooth k (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k
      (CommHopfAlgCat.quotient H.obj (parabolicDefiningHopfIdeal l)))
  -- The weight decomposition was stated with classical decidable equality on the characters.
  let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
  apply HopfIdeal.eq_bot_of_lieSubalgebra_eq_top
  apply LieSubalgebra.toSubmodule_injective
  rw [lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule,
    LieSubalgebra.top_toSubmodule, Submodule.map_eq_top_iff, eq_top_iff,
    ← (Derivation.isInternal_adjointWeightSpace π).submodule_iSup_eq_top]
  refine iSup_le fun α ↦ ?_
  rcases lt_or_ge α.toAdd 0 with hn | hn
  · rw [← ofAdd_toAdd α, hneg _ hn]
    exact bot_le
  · exact le_iSup₂_of_le α.toAdd hn le_rfl

end BialgHom
