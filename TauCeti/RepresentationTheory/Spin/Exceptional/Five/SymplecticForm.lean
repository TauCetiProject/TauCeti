/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import TauCeti.RepresentationTheory.Spin.Exceptional.Four.RootOperators

import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# The symplectic form on the four-dimensional spinor module

The spinor module associated to an isotropic summand of rank two is its exterior algebra. This
file equips that four-dimensional module with the bilinear form obtained by taking the oriented
top coefficient of

`CliffordAlgebra.reverse s * t`.

The sign and coordinate order matter. We use the order

`1, e₀, e₀e₁, e₁`,

so the form has matrix `Matrix.J (Fin 2)`. Thus its coordinate expression is exactly
`stdSymplecticBilinForm`, rather than merely an unspecified equivalent alternating form. The
construction consequently gives a nondegenerate alternating form intrinsic to Clifford reversal.

This is the form used to realize the four-dimensional spin representation as a symplectic
representation.

## Main definitions and results

* `TauCeti.spinFiveExteriorBasis`: the rank-two exterior basis in standard symplectic order.
* `TauCeti.spinFiveBilinForm`: the reversal-induced top-coefficient pairing.
* `TauCeti.spinFiveBilinForm_basis`: the matrix of the pairing is `Matrix.J (Fin 2)`.
* `TauCeti.spinFiveBilinForm_apply`: the pairing is the standard symplectic form in coordinates.
* `TauCeti.isAlt_spinFiveBilinForm`: the pairing is alternating.
* `TauCeti.spinFiveBilinForm_nondegenerate`: the pairing is nondegenerate.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

open CliffordAlgebra Module QuadraticMap

namespace TauCeti

universe u v

/-- The reindexing from the exterior subsets of `Fin 2` to standard symplectic coordinates.

The first summand contains the vacuum and the first generator; the second contains the oriented
top wedge and the second generator. -/
private def spinFiveIndexEquiv : Finset (Fin 2) ≃ Fin 2 ⊕ Fin 2 where
  toFun s := if s = ∅ then Sum.inl 0 else if s = {0} then Sum.inl 1
    else if s = {1} then Sum.inr 1 else Sum.inr 0
  invFun i := match i with
    | Sum.inl 0 => ∅
    | Sum.inl 1 => {0}
    | Sum.inr 0 => {0, 1}
    | Sum.inr 1 => {1}
  left_inv s := by fin_cases s <;> decide
  right_inv i := by rcases i with i | i <;> fin_cases i <;> decide

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The oriented rank-two exterior basis in the coordinate order of the standard symplectic
form: `1, e₀, e₀e₁, e₁`. -/
noncomputable def spinFiveExteriorBasis (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    Basis (Fin 2 ⊕ Fin 2) K (ExteriorAlgebra K P.W) :=
  (spinFourExteriorBasis P b).reindex spinFiveIndexEquiv

/-- The reversal pairing on rank-two spinors, normalized as the negative oriented top
coefficient of `reverse s * t`. -/
noncomputable def spinFiveBilinForm (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    LinearMap.BilinForm K (ExteriorAlgebra K P.W) :=
  LinearMap.mk₂ K
    (fun s t => -(spinFourExteriorBasis P b).repr
      (CliffordAlgebra.reverse s * t) {0, 1})
    (fun _ _ _ => by simp [add_mul]; abel)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp [mul_add]; abel)
    (fun _ _ _ => by simp)

/-- The vacuum is the first coordinate of the standard symplectic basis. -/
@[simp]
theorem spinFiveExteriorBasis_inl_zero (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    spinFiveExteriorBasis P b (Sum.inl 0) = 1 := by
  simp [spinFiveExteriorBasis, spinFiveIndexEquiv]

/-- The first exterior generator is the second coordinate of the standard symplectic basis. -/
@[simp]
theorem spinFiveExteriorBasis_inl_one (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    spinFiveExteriorBasis P b (Sum.inl 1) = ExteriorAlgebra.ι K (b 0) := by
  simp [spinFiveExteriorBasis, spinFiveIndexEquiv]

/-- The oriented top wedge is the third coordinate of the standard symplectic basis. -/
@[simp]
theorem spinFiveExteriorBasis_inr_zero (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    spinFiveExteriorBasis P b (Sum.inr 0) =
      ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1) := by
  simp [spinFiveExteriorBasis, spinFiveIndexEquiv]

/-- The second exterior generator is the fourth coordinate of the standard symplectic basis. -/
@[simp]
theorem spinFiveExteriorBasis_inr_one (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    spinFiveExteriorBasis P b (Sum.inr 1) = ExteriorAlgebra.ι K (b 1) := by
  simp [spinFiveExteriorBasis, spinFiveIndexEquiv]

@[simp]
private theorem spinFiveTopCoord_one (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    (spinFourExteriorBasis P b).repr 1 {0, 1} = 0 := by
  have h : (∅ : Finset (Fin 2)) ≠ {0, 1} := by decide
  simpa only [spinFourExteriorBasis_empty, h, ite_false] using
    (spinFourExteriorBasis P b).repr_self_apply (∅ : Finset (Fin 2)) {0, 1}

@[simp]
private theorem spinFiveTopCoord_zero (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    (spinFourExteriorBasis P b).repr (ExteriorAlgebra.ι K (b 0)) {0, 1} = 0 := by
  have h : ({0} : Finset (Fin 2)) ≠ {0, 1} := by decide
  rw [← spinFourExteriorBasis_zero P b]
  simpa only [h, ite_false] using
    (spinFourExteriorBasis P b).repr_self_apply ({0} : Finset (Fin 2)) {0, 1}

@[simp]
private theorem spinFiveTopCoord_one' (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    (spinFourExteriorBasis P b).repr (ExteriorAlgebra.ι K (b 1)) {0, 1} = 0 := by
  have h : ({1} : Finset (Fin 2)) ≠ {0, 1} := by decide
  rw [← spinFourExteriorBasis_one P b]
  simpa only [h, ite_false] using
    (spinFourExteriorBasis P b).repr_self_apply ({1} : Finset (Fin 2)) {0, 1}

@[simp]
private theorem spinFiveTopCoord_pair (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    (spinFourExteriorBasis P b).repr
      (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) {0, 1} = 1 := by
  simpa only [spinFourExteriorBasis_pair, ite_true] using
    (spinFourExteriorBasis P b).repr_self_apply ({0, 1} : Finset (Fin 2)) {0, 1}

/-- The reversal pairing has the standard symplectic matrix in the oriented exterior basis. -/
@[simp]
theorem spinFiveBilinForm_basis (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) (i j : Fin 2 ⊕ Fin 2) :
    spinFiveBilinForm P b (spinFiveExteriorBasis P b i) (spinFiveExteriorBasis P b j) =
      Matrix.J (Fin 2) K i j := by
  have hswap : ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0) =
      -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) :=
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (QuadraticMap.IsOrtho.all (b 1) (b 0))
  have hzero0 : ExteriorAlgebra.ι K (b 0) *
      (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  have hzero1 : ExteriorAlgebra.ι K (b 1) *
      (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) = 0 := by
    calc
      _ = (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0)) *
          ExteriorAlgebra.ι K (b 1) := (mul_assoc _ _ _).symm
      _ = -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) *
          ExteriorAlgebra.ι K (b 1) := by rw [hswap]
      _ = 0 := by rw [neg_mul, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, neg_zero]
  have htop0 : (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) *
      ExteriorAlgebra.ι K (b 0) = 0 := by
    rw [mul_assoc, hswap, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul,
      neg_zero]
  have htop1 : (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) *
      ExteriorAlgebra.ι K (b 1) = 0 := by
    rw [mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]
  have htoptop : (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) *
      (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) = 0 := by
    calc
      _ = ((ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) *
          ExteriorAlgebra.ι K (b 0)) * ExteriorAlgebra.ι K (b 1) :=
        (mul_assoc _ _ _).symm
      _ = 0 := by rw [htop0, zero_mul]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spinFiveBilinForm, Matrix.J, Matrix.fromBlocks, Matrix.of_apply,
      Matrix.zero_apply, CliffordAlgebra.reverse.map_mul, hswap, hzero0, hzero1, htop0,
      htop1, htoptop]

/-- In the oriented exterior coordinates, the reversal pairing is the standard symplectic
bilinear form. -/
theorem spinFiveBilinForm_apply (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) (s t : ExteriorAlgebra K P.W) :
    spinFiveBilinForm P b s t = stdSymplecticBilinForm K 2
      ((spinFiveExteriorBasis P b).equivFun s)
      ((spinFiveExteriorBasis P b).equivFun t) := by
  suffices spinFiveBilinForm P b =
      (stdSymplecticBilinForm K 2).comp
        (spinFiveExteriorBasis P b).equivFun.toLinearMap
        (spinFiveExteriorBasis P b).equivFun.toLinearMap by
    exact LinearMap.congr_fun (LinearMap.congr_fun this s) t
  rw [LinearMap.ext_iff_basis (spinFiveExteriorBasis P b) (spinFiveExteriorBasis P b)]
  intro i j
  rw [spinFiveBilinForm_basis]
  simp only [LinearMap.BilinForm.comp_apply]
  have hsingle : stdSymplecticBilinForm K 2 (Pi.single i 1) (Pi.single j 1) =
      Matrix.J (Fin 2) K i j := by
    rw [stdSymplecticBilinForm_apply]
    simpa only [Matrix.toBilin'_apply'] using
      Matrix.toBilin'_single (Matrix.J (Fin 2) K) i j
  calc
    _ = stdSymplecticBilinForm K 2 (Pi.single i 1) (Pi.single j 1) := hsingle.symm
    _ = _ := by
      congr 2 <;> ext k <;> simp [Basis.equivFun_self, Pi.single_apply, eq_comm]

/-- The reversal-induced form on the rank-two spinor module is alternating. -/
theorem isAlt_spinFiveBilinForm (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) : (spinFiveBilinForm P b).IsAlt := by
  intro s
  rw [spinFiveBilinForm_apply]
  exact isAlt_stdSymplecticBilinForm K 2 _

/-- The reversal-induced form on the rank-two spinor module is nondegenerate. -/
theorem spinFiveBilinForm_nondegenerate (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) : (spinFiveBilinForm P b).Nondegenerate := by
  let e := (spinFiveExteriorBasis P b).equivFun
  have hstd := stdSymplecticBilinForm_nondegenerate K 2
  constructor
  · intro s hs
    have hes : e s = 0 := hstd.1 (e s) fun y => by
      rw [← e.apply_symm_apply y, ← spinFiveBilinForm_apply]
      exact hs _
    apply e.injective
    simpa only [map_zero] using hes
  · intro t ht
    have het : e t = 0 := hstd.2 (e t) fun y => by
      rw [← e.apply_symm_apply y, ← spinFiveBilinForm_apply]
      exact ht _
    apply e.injective
    simpa only [map_zero] using het

end TauCeti
