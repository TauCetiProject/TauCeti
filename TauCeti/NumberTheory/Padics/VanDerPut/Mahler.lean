/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.VanDerPut.Basic
public import TauCeti.NumberTheory.Padics.MahlerBasis.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Changing between Mahler and van der Put coordinates

`PadicInt.mahlerToVanDerPut` changes coordinates on the native null-sequence space. It is an
isometry, linear over any additional continuous scalar action on the coefficient module.
Its inverse changes van der Put coordinates to Mahler coordinates.

The images of coordinate vectors are computed explicitly in both directions. In the
output-first matrix convention, columns are null by
`ContinuousLinearMap.tendsto_matrixCoeff_cofinite`. For the `ℤ_[p]`-valued matrices, every entry
has norm at most one by `PadicInt.norm_le_one`. The matrix action is an unconditionally
convergent sum, also for module coefficients.
Neither change of coordinates is asserted to preserve finite support: a polynomial can have
infinitely many nonzero van der Put coefficients, and a locally constant function can have
infinitely many nonzero Mahler coefficients.

The construction uses `PadicInt.mahlerLinearIsometryEquiv` and `PadicInt.vanDerPutEquiv`.
The inverse-column formula is Mathlib's `fwdDiff_iter_eq_sum_shift` applied to a clopen-ball
indicator.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, §I.3.
* W. H. Schikhof, *Ultrametric Calculus*, §62.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]
variable (S E : Type*) [Semiring S] [NormedAddCommGroup E] [Module ℤ_[p] E]
  [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  [Module S E] [ContinuousConstSMul S E]

variable (p) in
/-- The isometric change from Mahler coefficients to van der Put coefficients.
The inverse changes van der Put coefficients to Mahler coefficients. -/
noncomputable def mahlerToVanDerPut : C₀(ℕ, E) ≃ₗᵢ[S] C₀(ℕ, E) :=
  (mahlerLinearIsometryEquiv (p := p) S E).symm.trans (vanDerPutEquiv S E)

variable {S E}

/-- Recover the function from its Mahler coefficients and take its van der Put coefficients. -/
@[simp]
theorem mahlerToVanDerPut_apply (a : C₀(ℕ, E)) :
    mahlerToVanDerPut p S E a =
      vanDerPutEquiv S E ((mahlerEquiv (p := p) E).symm a) := by
  simp [mahlerToVanDerPut]

/-- Recover the function from its van der Put coefficients and take its Mahler coefficients. -/
@[simp]
theorem mahlerToVanDerPut_symm_apply (a : C₀(ℕ, E)) :
    (mahlerToVanDerPut p S E).symm a =
      mahlerEquiv E ((vanDerPutEquiv (p := p) S E).symm a) := by
  simp [mahlerToVanDerPut]

/-- The forward column at `j`: row `0` is `a` if `j = 0`, and `0` otherwise. For `i ≠ 0`,
it is the difference of binomial coefficients at `i` and at `i` with its leading base-`p`
digit deleted, acting on `a`. -/
theorem mahlerToVanDerPut_single_apply (j : ℕ) (a : E) (i : ℕ) :
    mahlerToVanDerPut p S E (single j a) i =
      if i = 0 then (if j = 0 then a else 0)
      else i.choose j • a - (i % p ^ Nat.log p i).choose j • a := by
  rw [mahlerToVanDerPut_apply, mahlerEquiv_symm_single, vanDerPutEquiv_apply]
  rcases eq_or_ne i 0 with rfl | hi
  · cases j <;> simp [mahlerTerm_apply, mahler_apply]
  · simp [vanDerPutCoeff_of_ne_zero _ hi, hi, mahlerTerm_apply, mahler_natCast_eq,
      Nat.cast_smul_eq_nsmul]

/-- The inverse column at `j`: finite differences of the indicator of the `j`-th van der Put
ball. -/
theorem mahlerToVanDerPut_symm_single_apply (j : ℕ) (a : E) (i : ℕ) :
    (mahlerToVanDerPut p S E).symm (single j a) i =
      ∑ k ∈ Finset.range (i + 1), ((-1 : ℤ) ^ (i - k) * i.choose k) •
        (if k % p ^ (p.digits j).length = j then a else 0) := by
  simp [mahlerEquiv_apply, fwdDiff_iter_eq_sum_shift, vanDerPutTerm_natCast]

/-- The forward matrix action converges unconditionally, with module-valued coefficients. -/
theorem hasSum_mahlerToVanDerPut_apply (a : C₀(ℕ, E)) (i : ℕ) :
    HasSum (fun j ↦ if i = 0 then (if j = 0 then a j else 0)
      else i.choose j • a j - (i % p ^ Nat.log p i).choose j • a j)
      (mahlerToVanDerPut p S E a i) := by
  simpa only [evalCLM_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, mahlerToVanDerPut_single_apply] using
    ((hasSum_single a).mapL
      (mahlerToVanDerPut p S E).toContinuousLinearEquiv.toContinuousLinearMap).mapL
      (evalCLM S i)

/-- The inverse matrix action converges unconditionally, with module-valued coefficients. -/
theorem hasSum_mahlerToVanDerPut_symm_apply (a : C₀(ℕ, E)) (i : ℕ) :
    HasSum (fun j ↦ ∑ k ∈ Finset.range (i + 1),
      ((-1 : ℤ) ^ (i - k) * i.choose k) •
        (if k % p ^ (p.digits j).length = j then a j else 0))
      ((mahlerToVanDerPut p S E).symm a i) := by
  simpa only [evalCLM_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, mahlerToVanDerPut_symm_single_apply] using
    ((hasSum_single a).mapL
      (mahlerToVanDerPut p S E).symm.toContinuousLinearEquiv.toContinuousLinearMap).mapL
        (evalCLM S i)

variable {R : Type*} [NormedRing R] [Module ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- The output-first matrix of the change from Mahler to van der Put coordinates. -/
@[simp]
theorem matrixCoeff_mahlerToVanDerPut (i j : ℕ) :
    ContinuousLinearMap.matrixCoeff
      (mahlerToVanDerPut p R R : C₀(ℕ, R) →L[R] C₀(ℕ, R)) i j =
      if i = 0 then (if j = 0 then 1 else 0)
      else (i.choose j : R) - ((i % p ^ Nat.log p i).choose j : R) := by
  simp only [ContinuousLinearMap.matrixCoeff_apply, LinearIsometryEquiv.coe_coe'',
    mahlerToVanDerPut_single_apply]
  simp [nsmul_eq_mul]

/-- The output-first matrix of the inverse change of coordinates. -/
@[simp]
theorem matrixCoeff_mahlerToVanDerPut_symm (i j : ℕ) :
    ContinuousLinearMap.matrixCoeff
      ((mahlerToVanDerPut p R R).toContinuousLinearEquiv.symm :
        C₀(ℕ, R) →L[R] C₀(ℕ, R)) i j =
      ∑ k ∈ Finset.range (i + 1), ((-1 : R) ^ (i - k) * i.choose k) *
        (if k % p ^ (p.digits j).length = j then 1 else 0) := by
  simp only [ContinuousLinearMap.matrixCoeff_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, mahlerToVanDerPut_symm_single_apply]
  simp [zsmul_eq_mul]

end PadicInt
