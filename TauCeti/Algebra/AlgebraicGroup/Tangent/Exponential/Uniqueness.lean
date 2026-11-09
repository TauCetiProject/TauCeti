/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.OneParameter.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter

/-!
# Uniqueness of intrinsic exponential curves

The exponential of a tangent vector with locally nilpotent invariant derivation is the unique
polynomial one-parameter subgroup through its value at parameter one. Consequently these
exponential points determine their tangent vectors. These results concern the intrinsic
coordinate algebra, without choosing a faithful matrix representation.

Together with the matrix comparison for invariant-vector-field exponentials, uniqueness
identifies polynomial exponential curves constructed in different faithful realizations.
It applies to all affine monoids over a rational domain, without finite-type or smoothness
hypotheses, provided the indicated invariant derivations are locally nilpotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
-/

public section

open Polynomial WithConv TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [IsDomain R]
  [CommRing H] [_root_.Bialgebra R H] [Algebra ℚ H]

namespace AlgHom

/-- An intrinsic exponential curve is the unique polynomial one-parameter subgroup through
its exponential point at parameter one. -/
theorem eq_expPointPolynomial_of_aeval_one_comp_eq
    (γ : H →ₐ[R] R[X])
    (hγ : ∀ s t : R, toConv ((aeval (s + t)).comp γ) =
      toConv ((aeval s).comp γ) * toConv ((aeval t).comp γ))
    (d : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    (h : (aeval (1 : R)).comp γ = expPoint d hd) :
    γ = expPointPolynomial d hd := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  have : CharZero R := Algebra.charZero_of_charZero ℚ R
  apply γ.eq_of_aeval_one_comp_eq _ hγ
    (aeval_comp_expPointPolynomial_add d hd)
  exact h.trans (aeval_one_comp_expPointPolynomial d hd).symm

end AlgHom

namespace Derivation

/-- Intrinsic exponential points determine their tangent vectors when both invariant
vector fields are locally nilpotent. No matrix realization is involved. -/
theorem eq_of_expPoint_eq
    (d e : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    (he : ∀ x, ∃ n, (leftInvariantDerivation e)^[n] x = 0)
    (h : expPoint d hd = expPoint e he) : d = e := by
  have hcurve : expPointPolynomial d hd = expPointPolynomial e he := by
    apply AlgHom.eq_expPointPolynomial_of_aeval_one_comp_eq _
      (aeval_comp_expPointPolynomial_add d hd) e he
    exact (aeval_one_comp_expPointPolynomial d hd).trans h
  rw [← curveVelocity_expPointPolynomial d hd
    (hzero := aeval_zero_comp_expPointPolynomial d hd)]
  simp only [hcurve, curveVelocity_expPointPolynomial]

end Derivation
