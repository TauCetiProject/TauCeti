/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Norm
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Characteristic polynomials and the norm of divisors

Let `F' / F` be a finite extension of an algebraic function field `F / k`, and let `z ∈ F'` have
its poles bounded by an effective divisor `D` of `F'`. The coefficients of the characteristic
polynomial of `z` over `F` are functions on the curve of `F`; this file bounds their poles by the
norm `N(D)` of `D` (`TauCeti.Divisor.norm`):

`z ∈ L(D) → every coefficient of charpoly_{F'/F}(z) lies in L(N(D))`.

For the constant term this is the statement `N_{F'/F}(z) ∈ L(N(D))`, which follows from the
order-of-a-norm formula. The other coefficients are not norms, and the bound for them is local.
At a place `P` of `F`, take `w ∈ F'` with `ord_{P'} w = D(P')` at every place `P'` above `P`. Then
`w` and `w z` are integral over `𝒪_P`, and in a basis of the free `𝒪_P`-module `𝒪'_P` the identity
`det (w) · det (X - z) = det (X · w - w z)` exhibits `N(w) · charpoly(z)` as a polynomial with
coefficients in `𝒪_P`. Since `ord_P N(w) = N(D)(P)`, every coefficient has order at least
`-N(D)(P)` at `P`.

This is the device behind the monotonicity of the gonality along finite extensions: a
transcendental `z ∈ F'` has a coefficient transcendental over `k`, which then has at most
`deg N(D) = [k' : k] · deg D` poles, that is `deg D` poles when `k' = k`.

## Main results

* `TauCeti.Place.norm_mul_coeff_charpoly_mem_integers`: if `w` and `w z` are integral over `𝒪_P`,
  then `N_{F'/F}(w)` times each coefficient of the characteristic polynomial of `z` lies in `𝒪_P`.
* `TauCeti.Divisor.coeff_charpoly_mem_riemannRochSpace_norm`: for an effective `D` and
  `z ∈ L(D)`, every coefficient of the characteristic polynomial of `z` over `F` lies in
  `L(N(D))`.

## References

* B. Poonen, *Gonality of modular curves in characteristic `p`*, Math. Res. Lett. 14 (2007),
  Appendix A, Proposition A.1(vii).
-/

public section

open Polynomial
open scoped nonZeroDivisors

namespace TauCeti

open AlgebraicGeometry

namespace Place

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **Clearing the denominators of a characteristic polynomial at a place.** Let `P` be a place of
`F / k` whose local model `𝒪'_P`, the integral closure of `𝒪_P` in `F'`, is a finite `𝒪_P`-module.
If `w` and `w z` are integral over `𝒪_P`, then `N_{F'/F}(w)` times every coefficient of the
characteristic polynomial of `z` over `F` lies in `𝒪_P`.

The finiteness hypothesis holds for every finite extension of an algebraic function field
(`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`). -/
theorem norm_mul_coeff_charpoly_mem_integers [FiniteDimensional F F'] (P : Place k F)
    [Module.Finite P.integers (integralClosure P.integers F')]
    {w z : F'} (hw : w ∈ integralClosure P.integers F')
    (hwz : w * z ∈ integralClosure P.integers F') (i : ℕ) :
    Algebra.norm F w * (Algebra.lmul F F' z).charpoly.coeff i ∈ P.integers := by
  classical
  let A := integralClosure P.integers F'
  have : IsLocalization (Algebra.algebraMapSubmonoid A (P.integers)⁰) F' :=
    isLocalization_integralClosure F' P
  -- `𝒪'_P` is finite and torsion-free over the discrete valuation ring `𝒪_P`, hence free; a basis
  -- of it is an `F`-basis of `F'` in which integral elements have integral matrices.
  have : Module.IsTorsionFree P.integers A := IsIntegralClosure.isTorsionFree P.integers F'
  let ι := Module.Free.ChooseBasisIndex P.integers A
  let c := Module.Free.chooseBasis P.integers A
  let b := c.localizationLocalization F (P.integers)⁰ F'
  let φ := algebraMap P.integers F
  let Mw := Algebra.leftMulMatrix c ⟨w, hw⟩
  let My := Algebra.leftMulMatrix c ⟨w * z, hwz⟩
  have hMw : φ.mapMatrix Mw = Algebra.leftMulMatrix b w :=
    Algebra.map_leftMulMatrix_localization P.integers (P.integers)⁰ c ⟨w, hw⟩
  have hMy : φ.mapMatrix My = Algebra.leftMulMatrix b (w * z) :=
    Algebra.map_leftMulMatrix_localization P.integers (P.integers)⁰ c ⟨w * z, hwz⟩
  set Q : P.integers[X] :=
    (Matrix.scalar ι X * (C : P.integers →+* _).mapMatrix Mw -
      (C : P.integers →+* _).mapMatrix My).det with hQ
  have hmul : Algebra.leftMulMatrix b w * Algebra.leftMulMatrix b z =
      Algebra.leftMulMatrix b (w * z) := (map_mul _ _ _).symm
  have hC (M : Matrix ι ι P.integers) : (mapRingHom φ).mapMatrix ((C : _ →+* _).mapMatrix M) =
      (C : F →+* _).mapMatrix (φ.mapMatrix M) := by
    ext; simp
  have hX : (mapRingHom φ).mapMatrix (Matrix.scalar ι (X : P.integers[X])) =
      Matrix.scalar ι X := by
    ext i j; by_cases h : i = j <;> simp [h]
  -- `w · (X - z) = X · w - w z` as matrices over `F[X]`, and the right side comes from `𝒪_P[X]`.
  have hmat : (C : F →+* F[X]).mapMatrix (Algebra.leftMulMatrix b w) *
      (Algebra.leftMulMatrix b z).charmatrix =
      (mapRingHom φ).mapMatrix (Matrix.scalar ι X * (C : P.integers →+* _).mapMatrix Mw -
        (C : P.integers →+* _).mapMatrix My) := by
    rw [Matrix.charmatrix, Matrix.mul_sub, ← RingHom.map_mul, hmul, ← hMw, ← hMy, map_sub,
      map_mul, hC, hC, hX, (Matrix.scalar_commute X commute_X _).eq]
  -- Taking determinants: `det (w) · det (X - z) = det (X · w - w z)`.
  have key : C (Algebra.norm F w) * (Algebra.lmul F F' z).charpoly = Q.map φ :=
    calc C (Algebra.norm F w) * (Algebra.lmul F F' z).charpoly
        = C (Algebra.leftMulMatrix b w).det * (Algebra.leftMulMatrix b z).charmatrix.det := by
          rw [Algebra.norm_eq_matrix_det b, ← LinearMap.charpoly_toMatrix _ b,
            ← Algebra.leftMulMatrix_apply, Matrix.charpoly]
      _ = ((C : F →+* F[X]).mapMatrix (Algebra.leftMulMatrix b w) *
            (Algebra.leftMulMatrix b z).charmatrix).det := by
          rw [Matrix.det_mul, RingHom.map_det]
      _ = Q.map φ := by
          rw [hmat, ← RingHom.map_det, hQ, Polynomial.coe_mapRingHom]
  have := congrArg (fun p ↦ p.coeff i) key
  simp only [coeff_C_mul, coeff_map] at this
  rw [this]
  exact (Q.coeff i).property

end Place

namespace Divisor

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Algebra.IsIntegral k k']

/-- **The coefficients of a characteristic polynomial lie in the Riemann–Roch space of the norm**
(Poonen, Proposition A.1(vii)): for a finite extension `F' / F` of an algebraic function field
`F / k`, an effective divisor `D` of `F' / k'` and `z ∈ L(D)`, every coefficient of the
characteristic polynomial of `z` over `F` lies in `L(N(D))`. No separability hypothesis is
needed. -/
theorem coeff_charpoly_mem_riemannRochSpace_norm (hF : IsFunctionField k F) {D : Divisor k' F'}
    (hD : 0 ≤ D) {z : F'} (hz : z ∈ riemannRochSpace D) (i : ℕ) :
    (Algebra.lmul F F' z).charpoly.coeff i ∈ riemannRochSpace (norm k F D) := by
  rw [mem_riemannRochSpace_iff]
  intro P
  have hfin := Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  have hs : ∀ P' : Place k' F', P' ∈ hfin.toFinset ↔ P'.restrict k F = P :=
    fun _ ↦ Set.Finite.mem_toFinset _
  -- A function `w` with `ord_{P'} w = D(P')` above `P` clears the poles of `z` there.
  obtain ⟨w, hw0, hw⟩ := Place.exists_ne_zero_forall_mem_ord_eq hfin.toFinset D.coeff
  have hvw (P' : Place k' F') (hP' : P'.restrict k F = P) :
      P'.valuation w = WithZero.exp (-D.coeff P') := by
    rw [P'.valuation_eq_exp_neg_ord hw0, hw P' ((hs P').mpr hP')]
  have hwI : w ∈ integralClosure P.integers F' :=
    (Place.mem_integralClosure_iff_forall_restrict_eq_mem_integers k' P).mpr fun P' hP' ↦ by
      rw [Place.mem_integers_iff, hvw P' hP', ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact neg_nonpos.mpr (WeilDivisor.coeff_nonneg hD P')
  have hwzI : w * z ∈ integralClosure P.integers F' :=
    (Place.mem_integralClosure_iff_forall_restrict_eq_mem_integers k' P).mpr fun P' hP' ↦ by
      rw [Place.mem_integers_iff, map_mul, hvw P' hP']
      calc WithZero.exp (-D.coeff P') * P'.valuation z
          ≤ WithZero.exp (-D.coeff P') * WithZero.exp (D.coeff P') :=
            mul_le_mul_right (mem_riemannRochSpace_iff.mp hz P') _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have := Place.moduleFinite_integralClosure_of_isFunctionField F' P hF
  have hmem := P.mem_integers_iff.mp (P.norm_mul_coeff_charpoly_mem_integers hwI hwzI i)
  -- The order of `N(w)` at `P` is the coefficient of `N(D)` at `P`.
  have hNw : P.valuation (Algebra.norm F w) = WithZero.exp (-(norm k F D).coeff P) := by
    rw [P.valuation_eq_exp_neg_ord (Algebra.norm_ne_zero_iff.mpr hw0),
      Place.ord_norm_of_isFunctionField hF P hs, coeff_norm k F D P hs]
    congr 2
    exact Finset.sum_congr rfl fun P' hP' ↦ by rw [hw P' hP']
  rw [map_mul, hNw, WithZero.exp_neg] at hmem
  -- `(exp n)⁻¹ · v ≤ 1` means `v ≤ exp n`.
  exact (inv_mul_le_one₀ WithZero.exp_pos).mp hmem

end Divisor

end TauCeti
