/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.MvPolynomial.JetPairing.Basic
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Linear substitution in the jet pairing

`MvPolynomial.jetPairing_subst_toMvPolynomial` moves a linear substitution from a formal
power series to its polynomial differential operator by transposing the coefficient matrix.
It combines `MvPowerSeries.pderiv_subst` with the adjunction `MvPolynomial.jetPairing_mul_X`.

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
  classical
  set a : σ → MvPowerSeries τ R := fun i ↦ A.toMvPolynomial i
  have hzero (i : σ) : MvPowerSeries.constantCoeff (a i) = 0 := by
    simpa only [a, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coe,
      constantCoeff_eq] using A.toMvPolynomial_constantCoeff i
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero hzero
  have hderiv (i : σ) (j : τ) : MvPowerSeries.pderiv j (a i) = MvPowerSeries.C (A i j) := by
    simp only [a, MvPowerSeries.pderiv_coe, Matrix.toMvPolynomial, ← C_mul_X_eq_monomial,
      map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, coe_C]
  have hchain (g : MvPowerSeries σ R) (j : τ) :
      MvPowerSeries.pderiv j (MvPowerSeries.subst a g) =
        ∑ i, A i j • MvPowerSeries.subst a (MvPowerSeries.pderiv i g) := by
    simp only [MvPowerSeries.pderiv_subst ha, hderiv, MvPowerSeries.smul_eq_C_mul, mul_comm]
  induction p using MvPolynomial.induction_on generalizing f with
  | C c =>
    -- Both operators read the constant coefficient, which linear substitution preserves.
    rw [aeval_C, algebraMap_eq, jetPairing_C, jetPairing_C,
      MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero ha hzero, Algebra.algebraMap_self,
      RingHom.id_apply]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p j hp =>
    -- The column of `A` from the chain rule is the row used in the adjoint substitution.
    have hform : A.transpose.toMvPolynomial j = ∑ i, A i j • X i := by
      simp only [Matrix.toMvPolynomial, Matrix.transpose_apply, ← C_mul_X_eq_monomial,
        smul_eq_C_mul]
    -- Expand both sides along this column so the induction hypothesis applies termwise.
    rw [jetPairing_mul_X, hchain, map_mul, aeval_X, hform, Finset.mul_sum]
    simp only [map_sum, map_smul, hp, mul_smul_comm, LinearMap.sum_apply,
      LinearMap.smul_apply, jetPairing_mul_X]

end MvPolynomial
