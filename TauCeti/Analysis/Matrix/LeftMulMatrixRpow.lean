/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.FiniteSpectrum
import TauCeti.Analysis.SpecialFunctions.Pow.PolynomialIdentity

/-!
# Real powers through the left regular representation

Let `A` be an algebra over `𝕜 = ℝ` or `ℂ` with a finite basis `B`. Left multiplication is the
faithful representation `Algebra.leftMulMatrix B : A →ₐ[𝕜] Matrix ι ι 𝕜`, so an element `a` is
determined by its matrix `M`. When `M` is positive semidefinite, its real powers `M ^ t` from the
continuous functional calculus are again matrices of left multiplication. The spectrum of `M` is a
finite set `S` of nonnegative reals, and Lagrange interpolation on `S` gives

  `M ^ t = ∑ μ ∈ S, μ ^ t • ℓ_μ(M)`,

where the Lagrange basis polynomials `ℓ_μ` do not depend on `t`. So `M ^ t` is the matrix of
`∑ μ ∈ S, μ ^ t • ℓ_μ(a)`, a polynomial in `a`. The real power `Algebra.leftMulMatrixRpow B a t`
is this element, obtained by applying `M ^ t` to the unit.

Because the coefficients `ℓ_μ(a)` are fixed, a bilinear expression `Φ (a ^ t) (a ^ t)` is a
finite sum `∑ (μ ν) ^ t • Φ (ℓ_μ(a)) (ℓ_ν(a))` of real powers. Such a sum is determined by its
values at the natural exponents (`Finset.sum_rpow_smul_eq_of_forall_pow`). Hence a bilinear
identity that holds for all natural powers of `a` holds for all its real powers. This lets real
powers of positive elements stay inside a group cut out by bilinear identities, such as a unitary
group or a Spin group, as needed for polar decompositions.

## Main definitions

* `Algebra.leftMulMatrixRpow`: the real power `a ^ t` of an element, obtained by applying the real
  power of its left multiplication matrix to the unit.

## Main results

* `Algebra.leftMulMatrix_leftMulMatrixRpow`: the matrix of `a ^ t` is the real power `M ^ t` of
  the matrix `M` of `a`, and `Algebra.leftMulMatrixRpow_eq_iff` characterizes `a ^ t` by this.
* `Algebra.leftMulMatrixRpow_mem_adjoin`: `a ^ t` is a polynomial in `a`.
* `Algebra.leftMulMatrixRpow_natCast` and `Algebra.leftMulMatrixRpow_add`: the natural powers and
  the group law.
* `Algebra.bilin_leftMulMatrixRpow_eq_of_forall_pow`: a bilinear identity satisfied by all
  natural powers of an element with positive semidefinite matrix is satisfied by all its real
  powers.
-/

public section

open scoped MatrixOrder ComplexOrder

open Polynomial

namespace Algebra

variable {𝕜 A ι : Type*} [RCLike 𝕜] [Ring A] [Algebra 𝕜 A] [Fintype ι] [DecidableEq ι]
  (B : Module.Basis ι 𝕜 A)

/-- **The real power of an element through its left multiplication matrix.** For a finite basis
`B` of `A`, `leftMulMatrixRpow B a t` is the image of the unit under the real power `M ^ t`, from
the continuous functional calculus, of the matrix `M = leftMulMatrix B a`. Its own matrix is
`M ^ t` (`Algebra.leftMulMatrix_leftMulMatrixRpow`); both are `0` unless `M` is positive
semidefinite. -/
noncomputable def leftMulMatrixRpow (a : A) (t : ℝ) : A :=
  Matrix.toLin B B (leftMulMatrix B a ^ t) 1

/-- An element is the image of the unit under its left multiplication matrix. -/
private theorem toLin_leftMulMatrix_one (y : A) : Matrix.toLin B B (leftMulMatrix B y) 1 = y := by
  rw [leftMulMatrix_apply, Matrix.toLin_toMatrix, coe_lmul_eq_mul, LinearMap.mul_apply', mul_one]

/-- If the matrix of `a` is self-adjoint, every functional calculus of it is the matrix of a fixed
combination `∑ μ ∈ S, f μ • e μ` of polynomials `e μ` in `a`, with `S` the spectrum of the
matrix. -/
private theorem exists_cfc_leftMulMatrix_eq (a : A) (ha : IsSelfAdjoint (leftMulMatrix B a)) :
    ∃ (S : Finset ℝ) (e : ℝ → A), (S : Set ℝ) = spectrum ℝ (leftMulMatrix B a) ∧
      (∀ μ, e μ ∈ adjoin 𝕜 {a}) ∧ ∀ f : ℝ → ℝ,
        cfc f (leftMulMatrix B a) = leftMulMatrix B (∑ μ ∈ S, algebraMap ℝ 𝕜 (f μ) • e μ) := by
  classical
  have hfin := Matrix.finite_real_spectrum (A := leftMulMatrix B a)
  refine ⟨hfin.toFinset,
    fun μ ↦ aeval a ((Lagrange.basis hfin.toFinset _root_.id μ).map (algebraMap ℝ 𝕜)),
    hfin.coe_toFinset, fun μ ↦ aeval_mem_adjoin_singleton 𝕜 a, fun f ↦ ?_⟩
  rw [TauCeti.cfc_eq_sum_smul_aeval_lagrangeBasis f hfin.coe_toFinset.ge ha, map_sum]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [map_smul, ← aeval_algHom_apply, aeval_map_algebraMap, algebraMap_smul]

/-- The real power of an element whose matrix is not positive semidefinite is `0`, because the
functional calculus of `ℝ≥0` is zero off the positive semidefinite matrices. -/
private theorem leftMulMatrixRpow_of_not_nonneg {a : A} (ha : ¬0 ≤ leftMulMatrix B a) (t : ℝ) :
    leftMulMatrixRpow B a t = 0 := by
  rw [leftMulMatrixRpow, CFC.rpow_def, cfc_apply_of_not_predicate _ ha, map_zero,
    LinearMap.zero_apply]

/-- **The matrix of the real power is the real power of the matrix.** For every `a` with matrix
`M = leftMulMatrix B a`, the matrix of `leftMulMatrixRpow B a t` is the real power `M ^ t` of the
continuous functional calculus. Both sides are `0` unless `M` is positive semidefinite. -/
@[simp]
theorem leftMulMatrix_leftMulMatrixRpow (a : A) (t : ℝ) :
    leftMulMatrix B (leftMulMatrixRpow B a t) = leftMulMatrix B a ^ t := by
  by_cases hM : 0 ≤ leftMulMatrix B a
  · obtain ⟨S, e, -, -, he⟩ := exists_cfc_leftMulMatrix_eq B a hM.isSelfAdjoint
    rw [CFC.rpow_eq_cfc_real hM, he, leftMulMatrixRpow, CFC.rpow_eq_cfc_real hM, he,
      toLin_leftMulMatrix_one]
  · rw [leftMulMatrixRpow_of_not_nonneg B hM, map_zero, CFC.rpow_def,
      cfc_apply_of_not_predicate _ hM]

/-- `leftMulMatrixRpow B a t` is the unique element whose matrix is the real power `M ^ t` of the
matrix `M = leftMulMatrix B a`. -/
theorem leftMulMatrixRpow_eq_iff {a y : A} {t : ℝ} :
    leftMulMatrixRpow B a t = y ↔ leftMulMatrix B y = leftMulMatrix B a ^ t := by
  rw [← leftMulMatrix_leftMulMatrixRpow, (leftMulMatrix_injective B).eq_iff, eq_comm]

/-- The real power `leftMulMatrixRpow B a t` is a polynomial in `a`. -/
theorem leftMulMatrixRpow_mem_adjoin (a : A) (t : ℝ) :
    leftMulMatrixRpow B a t ∈ adjoin 𝕜 {a} := by
  by_cases hM : 0 ≤ leftMulMatrix B a
  · obtain ⟨S, e, -, he, hcfc⟩ := exists_cfc_leftMulMatrix_eq B a hM.isSelfAdjoint
    rw [(leftMulMatrixRpow_eq_iff B).2 ((CFC.rpow_eq_cfc_real hM).trans (hcfc _)).symm]
    exact Subalgebra.sum_mem _ fun μ _ ↦ Subalgebra.smul_mem _ (he μ) _
  · rw [leftMulMatrixRpow_of_not_nonneg B hM]
    exact Subalgebra.zero_mem _

variable {B}

/-- For an element `a` with positive semidefinite matrix, the real powers of `a` are fixed
combinations `∑ μ ∈ S, μ ^ t • e μ` over a finite set `S` of nonnegative reals. -/
private theorem exists_leftMulMatrixRpow_eq_sum {a : A} (ha : 0 ≤ leftMulMatrix B a) :
    ∃ (S : Finset ℝ) (e : ℝ → A), (∀ μ ∈ S, 0 ≤ μ) ∧
      ∀ t : ℝ, leftMulMatrixRpow B a t = ∑ μ ∈ S, algebraMap ℝ 𝕜 (μ ^ t) • e μ := by
  obtain ⟨S, e, hS, -, hcfc⟩ := exists_cfc_leftMulMatrix_eq B a ha.isSelfAdjoint
  refine ⟨S, e, fun μ hμ ↦ spectrum_nonneg_of_nonneg ha (hS ▸ Finset.mem_coe.2 hμ),
    fun t ↦ ?_⟩
  rw [leftMulMatrixRpow_eq_iff, ← hcfc, CFC.rpow_eq_cfc_real ha]

/-- At a natural exponent, the real power of an element with positive semidefinite matrix is the
ordinary power. -/
@[simp]
theorem leftMulMatrixRpow_natCast {a : A} (ha : 0 ≤ leftMulMatrix B a) (n : ℕ) :
    leftMulMatrixRpow B a n = a ^ n := by
  rw [leftMulMatrixRpow_eq_iff, CFC.rpow_natCast _ n ha, map_pow]

/-- The real power at exponent `0` of an element with positive semidefinite matrix is `1`. -/
@[simp]
theorem leftMulMatrixRpow_zero {a : A} (ha : 0 ≤ leftMulMatrix B a) :
    leftMulMatrixRpow B a 0 = 1 := by
  simpa using leftMulMatrixRpow_natCast ha 0

/-- The real power at exponent `1` of an element with positive semidefinite matrix is the element
itself. -/
@[simp]
theorem leftMulMatrixRpow_one {a : A} (ha : 0 ≤ leftMulMatrix B a) :
    leftMulMatrixRpow B a 1 = a := by
  simpa using leftMulMatrixRpow_natCast ha 1

/-- **The group law of real powers.** For a unit `a`, `a ^ (s + t) = a ^ s * a ^ t`. This is the
group law of the real powers when the matrix of `a` is positive definite; otherwise all the real
powers are `0`. -/
theorem leftMulMatrixRpow_add {a : A} (ha : IsUnit a) (s t : ℝ) :
    leftMulMatrixRpow B a (s + t) = leftMulMatrixRpow B a s * leftMulMatrixRpow B a t := by
  rw [leftMulMatrixRpow_eq_iff, CFC.rpow_add (ha.map (leftMulMatrix B)), map_mul,
    leftMulMatrix_leftMulMatrixRpow, leftMulMatrix_leftMulMatrixRpow]

/-- **Bilinear identities pass from natural to real powers.** For an element `a` whose matrix is
positive semidefinite, if a bilinear identity `Φ (a ^ n) (a ^ n) = d` holds at every natural
exponent `n`, then `Φ (a ^ t) (a ^ t) = d` holds for the real power at every real exponent `t`. -/
theorem bilin_leftMulMatrixRpow_eq_of_forall_pow {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    {a : A} (ha : 0 ≤ leftMulMatrix B a) (Φ : A →ₗ[𝕜] A →ₗ[𝕜] W) (d : W)
    (h : ∀ n : ℕ, Φ (a ^ n) (a ^ n) = d) (t : ℝ) :
    Φ (leftMulMatrixRpow B a t) (leftMulMatrixRpow B a t) = d := by
  obtain ⟨S, e, hS0, hsum⟩ := exists_leftMulMatrixRpow_eq_sum ha
  -- Expanding `a ^ s`, `Φ (a ^ s) (a ^ s)` is a sum of real powers with fixed coefficients.
  have hexp (s : ℝ) : Φ (leftMulMatrixRpow B a s) (leftMulMatrixRpow B a s) =
      ∑ p ∈ S ×ˢ S, algebraMap ℝ 𝕜 ((p.1 * p.2) ^ s) • Φ (e p.1) (e p.2) := by
    rw [hsum, Finset.sum_product]
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ hμ ↦ Finset.sum_congr rfl fun ν hν ↦ ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, Real.mul_rpow (hS0 μ hμ) (hS0 ν hν),
      map_mul, mul_comm]
  -- View `W` as a real vector space to apply the identity theorem for sums of real powers.
  -- `Module.compHom` defines the real action as the action of the image under `algebraMap`.
  let : Module ℝ W := Module.compHom W (algebraMap ℝ 𝕜)
  have hsmul (r : ℝ) (w : W) : algebraMap ℝ 𝕜 r • w = r • w := rfl
  rw [hexp]
  simp_rw [hsmul]
  refine Finset.sum_rpow_smul_eq_of_forall_pow _ _ _ d (fun n ↦ ?_) t
  have hn := hexp n
  simp only [leftMulMatrixRpow_natCast ha, Real.rpow_natCast, hsmul] at hn
  rw [← hn, h n]

end Algebra
