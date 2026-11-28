/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.MvPolynomial.JetPairing.Basic
import TauCeti.RingTheory.MvPolynomial.LinearSubst
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Linear substitution in the jet pairing

`MvPolynomial.jetPairing_subst_toMvPolynomial` moves a linear substitution from a formal
power series to its polynomial differential operator by transposing the coefficient matrix.
It uses the chain rule `Matrix.pderiv_subst_toMvPolynomial` and the adjunction
`MvPolynomial.jetPairing_mul_X`.

The identity corresponds to `New.jet_subst_linearSeries` as used in
`New.norm_jet_columnDetProd_subst` in `grh/src/New/Derivatives/Divisibility/Count.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`
(Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace MvPolynomial

/-- For a linear substitution with coefficient matrix `A` on a power series, the adjoint
substitution on the polynomial side of the jet pairing has matrix `Aᵀ`.
The matrix may be rectangular or singular. -/
theorem jetPairing_subst_toMvPolynomial {σ τ R : Type*} [CommRing R] [Fintype σ] [Fintype τ]
    (p : MvPolynomial τ R) (A : Matrix σ τ R) (f : MvPowerSeries σ R) :
    jetPairing p (MvPowerSeries.subst (fun i ↦ (A.toMvPolynomial i : MvPowerSeries τ R)) f) =
      jetPairing (aeval A.transpose.toMvPolynomial p) f := by
  induction p using MvPolynomial.induction_on generalizing f with
  | C c =>
    -- Both operators read the constant coefficient, which linear substitution preserves.
    rw [aeval_C, algebraMap_eq, jetPairing_C, jetPairing_C,
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero A.hasSubst_toMvPolynomial
        (fun i ↦ by rw [MvPolynomial.constantCoeff_coe, A.toMvPolynomial_constantCoeff]),
      Algebra.algebraMap_self, RingHom.id_apply]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p j hp =>
    -- Expand both sides along the same column of `A` to use the induction hypothesis termwise.
    rw [jetPairing_mul_X, A.pderiv_subst_toMvPolynomial, map_mul, aeval_X,
      A.transpose.toMvPolynomial_eq_sum_smul_X, Finset.mul_sum]
    simp only [Matrix.transpose_apply, map_sum, map_smul, hp, mul_smul_comm, LinearMap.sum_apply,
      LinearMap.smul_apply, jetPairing_mul_X]

end MvPolynomial
