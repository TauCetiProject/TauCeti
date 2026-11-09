/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MahlerBasis.Basic
import TauCeti.Algebra.Group.ForwardDiff

/-!
# Products in Mahler coordinates

The Mahler coefficients of a pointwise product are not the pointwise products of the
coefficient sequences. The discrete Leibniz rule gives a finite triangular formula: the
coefficient of order `n` uses only coefficients of orders at most `n` in both inputs.
The same formula applies to a scalar-valued function acting on a module-valued function.

`ZeroAtInftyContinuousMap.mahlerProduct` transports pointwise multiplication through Mathlib's
`PadicInt.mahlerEquiv`. Thus it preserves cofinite decay, is associative and distributive,
and satisfies the submultiplicative sup-norm estimate. Its unit is `single 0 1`, not the
constant sequence. No new multiplication instance on `C₀` is installed: that space already
has a different, pointwise multiplication.

The construction uses Mathlib's Mahler isometry and Gregory–Newton formula
`shift_eq_sum_fwdDiff_iter`. For background on Mahler expansions and the algebra of continuous
functions, see P. Colmez, *Fonctions d'une variable p-adique*, §I.3.
-/

public section

open scoped ZeroAtInfty fwdDiff
open ZeroAtInftyContinuousMap

variable {p : ℕ} [Fact p.Prime]

namespace ContinuousMap

/-- Mahler coefficients of a scalar product, expressed entirely in the coefficients of its
inputs. Both coefficient indices on the right are at most `n`. -/
theorem mahlerEquiv_smul_apply {R E : Type*} [NormedRing R] [Module ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] [Module R E] [ContinuousSMul R E]
    (f : C(ℤ_[p], R)) (g : C(ℤ_[p], E)) (n : ℕ) :
    PadicInt.mahlerEquiv E (f • g) n =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
        (n.choose i * i.choose j) •
          (PadicInt.mahlerEquiv R f i • PadicInt.mahlerEquiv E g (n - i + j)) := by
  simpa only [PadicInt.mahlerEquiv_apply, ContinuousMap.coe_smul'] using
    TauCeti.fwdDiff_iter_smul_eq_sum_range_sum_range (1 : ℤ_[p]) f g n 0

/-- Mahler coefficients of a pointwise product. The formula works for noncommutative
coefficient rings, keeping the input factors in their original order. -/
theorem mahlerEquiv_mul_apply {R : Type*} [NormedRing R] [Module ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (f g : C(ℤ_[p], R)) (n : ℕ) :
    PadicInt.mahlerEquiv R (f * g) n =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
        (n.choose i * i.choose j) •
          (PadicInt.mahlerEquiv R f i * PadicInt.mahlerEquiv R g (n - i + j)) := by
  simpa only [smul_eq_mul] using f.mahlerEquiv_smul_apply g n

end ContinuousMap

namespace ZeroAtInftyContinuousMap

variable {R : Type*} [NormedRing R] [Module ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

variable (p) in
/-- Multiplication of Mahler coefficient sequences, corresponding to pointwise multiplication
of continuous functions on `ℤ_p`. This is not pointwise multiplication of sequences. -/
noncomputable def mahlerProduct (a b : C₀(ℕ, R)) : C₀(ℕ, R) :=
  PadicInt.mahlerEquiv (p := p) R
    ((PadicInt.mahlerEquiv (p := p) R).symm a * (PadicInt.mahlerEquiv (p := p) R).symm b)

/-- The Mahler series of a Mahler product is the pointwise product of the two series. -/
@[simp]
theorem mahlerEquiv_symm_mahlerProduct (a b : C₀(ℕ, R)) :
    (PadicInt.mahlerEquiv (p := p) R).symm (mahlerProduct p a b) =
      (PadicInt.mahlerEquiv (p := p) R).symm a *
        (PadicInt.mahlerEquiv (p := p) R).symm b := by
  simp [mahlerProduct]

/-- The finite triangular coefficient formula for the Mahler product. -/
theorem mahlerProduct_apply (a b : C₀(ℕ, R)) (n : ℕ) :
    mahlerProduct p a b n = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
      (n.choose i * i.choose j) • (a i * b (n - i + j)) := by
  simp only [mahlerProduct, ContinuousMap.mahlerEquiv_mul_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The constant Mahler coefficient of a product. -/
@[simp]
theorem mahlerProduct_apply_zero (a b : C₀(ℕ, R)) : mahlerProduct p a b 0 = a 0 * b 0 := by
  simp [mahlerProduct_apply]

/-- The Mahler product is submultiplicative for the coefficient sup norm. -/
theorem norm_mahlerProduct_le (a b : C₀(ℕ, R)) : ‖mahlerProduct p a b‖ ≤ ‖a‖ * ‖b‖ := by
  simpa only [mahlerProduct, LinearIsometryEquiv.norm_map] using
    norm_mul_le ((PadicInt.mahlerEquiv (p := p) R).symm a)
      ((PadicInt.mahlerEquiv (p := p) R).symm b)

@[simp]
theorem mahlerProduct_zero_left (a : C₀(ℕ, R)) : mahlerProduct p 0 a = 0 := by
  simp [mahlerProduct]

@[simp]
theorem mahlerProduct_zero_right (a : C₀(ℕ, R)) : mahlerProduct p a 0 = 0 := by
  simp [mahlerProduct]

/-- Additivity in the first factor. -/
theorem mahlerProduct_add_left (a b c : C₀(ℕ, R)) :
    mahlerProduct p (a + b) c = mahlerProduct p a c + mahlerProduct p b c := by
  simp [mahlerProduct, add_mul]

/-- Additivity in the second factor. -/
theorem mahlerProduct_add_right (a b c : C₀(ℕ, R)) :
    mahlerProduct p a (b + c) = mahlerProduct p a b + mahlerProduct p a c := by
  simp [mahlerProduct, mul_add]

/-- Associativity of the Mahler product. -/
theorem mahlerProduct_assoc (a b c : C₀(ℕ, R)) :
    mahlerProduct p (mahlerProduct p a b) c = mahlerProduct p a (mahlerProduct p b c) := by
  apply (PadicInt.mahlerEquiv (p := p) R).symm.injective
  simp [mul_assoc]

/-- The coordinate vector in degree zero is the left unit of the Mahler product. -/
@[simp]
theorem mahlerProduct_single_zero_one_left (a : C₀(ℕ, R)) :
    mahlerProduct p (single 0 1) a = a := by
  apply (PadicInt.mahlerEquiv (p := p) R).symm.injective
  ext x
  simp [PadicInt.mahlerTerm_apply, mahler_apply]

/-- The coordinate vector in degree zero is the right unit of the Mahler product. -/
@[simp]
theorem mahlerProduct_single_zero_one_right (a : C₀(ℕ, R)) :
    mahlerProduct p a (single 0 1) = a := by
  apply (PadicInt.mahlerEquiv (p := p) R).symm.injective
  ext x
  simp [PadicInt.mahlerTerm_apply, mahler_apply]

/-- Over commutative coefficients, the Mahler product is commutative. -/
theorem mahlerProduct_comm {R : Type*} [NormedCommRing R] [Module ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R] (a b : C₀(ℕ, R)) :
    mahlerProduct p a b = mahlerProduct p b a := by
  simp [mahlerProduct, mul_comm]

-- The first coefficient already distinguishes this product from pointwise multiplication.
example (a b : C₀(ℕ, R)) :
    mahlerProduct p a b 1 = a 0 * b 1 + a 1 * b 0 + a 1 * b 1 := by
  simp [mahlerProduct_apply, Finset.sum_range_succ, add_comm, add_assoc]

-- The identity x² = binom(x,1) + 2 binom(x,2), including at p = 2.
example : mahlerProduct p (single 1 (1 : ℤ_[p])) (single 1 1) =
    single 1 1 + single 2 2 := by
  apply (PadicInt.mahlerEquiv (p := p) ℤ_[p]).symm.injective
  simp only [mahlerEquiv_symm_mahlerProduct, map_add, PadicInt.mahlerEquiv_symm_single,
    PadicInt.mahlerTerm_one]
  have h : (mahler 1 : C(ℤ_[p], ℤ_[p])) = ContinuousMap.id ℤ_[p] := by
    ext x
    simp [mahler_apply]
  have hterm : PadicInt.mahlerTerm (2 : ℤ_[p]) 2 = (2 : ℕ) • mahler 2 := by
    apply ContinuousMap.ext
    intro x
    simp only [PadicInt.mahlerTerm_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    exact mul_comm _ _
  rw [hterm]
  simpa [h, add_comm] using TauCeti.id_mul_mahler (p := p) 1

end ZeroAtInftyContinuousMap

namespace ContinuousMap

/-- Taking coefficients turns a pointwise product into the Mahler product. -/
@[simp]
theorem mahlerProduct_mahlerEquiv {R : Type*} [NormedRing R] [Module ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (f g : C(ℤ_[p], R)) :
    mahlerProduct p (PadicInt.mahlerEquiv R f) (PadicInt.mahlerEquiv R g) =
      PadicInt.mahlerEquiv R (f * g) := by
  simp [mahlerProduct]

end ContinuousMap
