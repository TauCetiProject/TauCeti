/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
public import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.RingTheory.HahnSeries.Map

/-!
# The classical modular polynomial over `ℤ` and integrality of CM `j`-values

For a positive integer `n`, the cyclic-isogeny polynomial
`TauCeti.ModularForm.cyclicIsogenyPolynomial n j τ` is the monic polynomial

  `∏_{(a b; 0 d)} (X - j((a τ + b) / d))`

over the primitive upper-triangular matrices `(a b; 0 d)` of determinant `n` with `0 < a` and
`0 ≤ b < d` (`FixedDetMatrices.primitiveReps n`). Each coefficient of `X ^ k` is a holomorphic
`SL(2, ℤ)`-invariant function on the upper half-plane. This file proves that these coefficients
are meromorphic at the cusp with integer Laurent `q`-coefficients, descends the polynomial to a
monic integral bivariate polynomial `Φ_n(X, Y) ∈ ℤ[Y][X]`, computes the leading coefficient of the
diagonal specialization `Φ_n(X, X)` when `n` is not a square, and deduces that `j(τ)` is an
algebraic integer at every imaginary quadratic point `τ ∈ ℍ`.

The integrality of the `q`-coefficients follows the classical cyclotomic Galois argument. In the
ramified parameter `q_{1/n} = exp(2 π i τ / n)`, the factor `j((a τ + b) / d)` has Laurent
expansion `J(ζ_n^{a b} q_{1/n}^{a^2})`, where `J ∈ ℤ⸨q⸩` is the `q`-expansion of `j` and
`ζ_n = exp(2 π i / n)`. Every coefficient of the product therefore lies in `ℤ[ζ_n]`, hence is
integral over `ℤ`. An element `σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends `ζ_n` to `ζ_n^c` for some unit
`c ∈ (ℤ / nℤ)ˣ`, and sending `(a b; 0 d)` to `(a, c b mod d; 0, d)` permutes the primitive
representatives of determinant `n`, so `σ` fixes every coefficient of the product. Fixed elements
of `ℚ(ζ_n)` lie in `ℚ`, and algebraic integers in `ℚ` lie in `ℤ`.

When `n` is not a square, no representative `(a b; 0 d)` has `a = d`, so `a^2 ≠ n` for every
factor of `Φ_n(j(τ), j(τ)) = ∏ (j(τ) - j((a τ + b) / d))`. In `q_{1/n}`, the two terms `j(τ)` and
`j((a τ + b) / d)` have distinct pole orders `n` and `a^2` with leading coefficients `1` and
`ζ_n^{-a b}` of absolute value `1`. Each factor therefore has leading coefficient of norm `1`, so
the leading coefficient of `Φ_n(X, X)` is `±1`. Finally, if `τ ∈ ℍ` satisfies a nontrivial
integral quadratic equation `a τ^2 + b τ + c = 0`, dividing by `gcd(a, b, c)` makes `(a, b, c)`
primitive with `D = 4 a c - b^2 ≥ 1`, and for `t = |b| + D` the matrix `(t - b, -c; a, t)` is
primitive of non-square positive determinant `t^2 - b t + a c` and fixes `τ`. Hence `j(τ)` is a
root of `Φ_m(X, X)` with leading coefficient `±1`, and is therefore integral over `ℤ`.

## Main definitions

* `TauCeti.ModularForm.modularPolynomial n`: the classical modular polynomial `Φ_n ∈ ℤ[X][X]`,
  characterized by
  `(modularPolynomial n).map (aeval (R := ℤ) (j τ)) = cyclicIsogenyPolynomial n j τ`.
* `TauCeti.ModularForm.modularPolynomialDiag n`: the diagonal specialization
  `Φ_n(X, X) = (modularPolynomial n).eval X ∈ ℤ[X]`.

## Main results

* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_toGLReal_smul` and
  `TauCeti.UpperHalfPlane.laurentQExpansion_toGLReal_smul`: meromorphy and `q_{1/n}`-expansion of
  `τ ↦ f(A • τ)` for `A ∈ FixedDetMatrices.reps n`.
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial` and
  `TauCeti.ModularForm.laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_range`: meromorphy at
  the cusp and integrality of the Laurent `q`-coefficients of
  `(cyclicIsogenyPolynomial n j ·).coeff k`.
* `TauCeti.ModularForm.map_aeval_j_modularPolynomial`,
  `TauCeti.ModularForm.monic_modularPolynomial`,
  `TauCeti.ModularForm.natDegree_modularPolynomial`, and
  `TauCeti.ModularForm.eq_modularPolynomial_of_map_aeval_j_eq`: basic API and uniqueness of `Φ_n`.
* `TauCeti.ModularForm.isUnit_leadingCoeff_modularPolynomialDiag`: for non-square `n`, the leading
  coefficient of `Φ_n(X, X)` is `±1`.
* `TauCeti.ModularForm.isIntegral_j_of_quadratic`: for `τ ∈ ℍ` satisfying a nontrivial integral
  quadratic equation `a τ^2 + b τ + c = 0`, `j(τ)` is integral over `ℤ`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C, Theorems 11.18 and 11.20.
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §3.
-/

public noncomputable section

open Matrix Polynomial UpperHalfPlane Filter Topology
open scoped MatrixGroups Manifold LaurentSeries

/-! ### Laurent `q`-expansions along upper-triangular representatives -/

namespace TauCeti.UpperHalfPlane

private theorem periodic_vadd_posReal_inv_smul {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (b : ℕ) (d : ℕ+) :
    Function.Periodic
      ((fun τ : ℍ ↦
        f ((⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr (Nat.cast_pos.mpr d.pos)⟩ : {y : ℝ // 0 < y}) •
          ((b : ℝ) +ᵥ τ))) ∘ ofComplex) (d : ℕ) := by
  have hd : 0 < ((d : ℕ) : ℝ) := Nat.cast_pos.mpr d.pos
  let x : {y : ℝ // 0 < y} := ⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr hd⟩
  refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
  have hEq : x • ((b : ℝ) +ᵥ (((d : ℕ) : ℝ) +ᵥ τ)) = (1 : ℝ) +ᵥ (x • ((b : ℝ) +ᵥ τ)) := by
    ext
    simp only [coe_pos_real_smul, coe_vadd, Complex.real_smul, x]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr d.ne_zero]
    ring
  have hw := hfper ↑(x • ((b : ℝ) +ᵥ τ))
  have hadd : (↑(x • ((b : ℝ) +ᵥ τ)) : ℂ) + 1 = ↑((1 : ℝ) +ᵥ (x • ((b : ℝ) +ᵥ τ))) := by
    simp [coe_vadd, add_comm]
  rw [Function.comp_apply, Function.comp_apply, hadd, ofComplex_apply, ofComplex_apply] at hw
  simpa only [x, hEq] using hw

private theorem periodic_pnat_smul_of_periodic {ψ : ℍ → ℂ} {d : ℝ}
    (hψ : Function.Periodic (ψ ∘ ofComplex) d) (a : ℕ+) :
    Function.Periodic
      ((fun τ : ℍ ↦ ψ ((⟨((a : ℕ) : ℝ), Nat.cast_pos.mpr a.pos⟩ : {y : ℝ // 0 < y}) • τ)) ∘
        ofComplex) d := by
  let x : {y : ℝ // 0 < y} := ⟨((a : ℕ) : ℝ), Nat.cast_pos.mpr a.pos⟩
  refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
  have hEq : x • (d +ᵥ τ) = ((a : ℕ) * d) +ᵥ (x • τ) := by
    ext
    simp only [coe_pos_real_smul, coe_vadd, Complex.real_smul, x]
    push_cast
    ring
  have hw := (hψ.nat_mul a) ↑(x • τ)
  have hadd : (↑(x • τ) : ℂ) + (a : ℕ) * (d : ℂ) = ↑(((a : ℕ) * d) +ᵥ (x • τ)) := by
    simp [coe_vadd, add_comm]
  rw [Function.comp_apply, Function.comp_apply, hadd, ofComplex_apply, ofComplex_apply] at hw
  simpa only [x, hEq] using hw

private theorem apply_one_one_pos_of_mem_reps {n : ℕ} [NeZero n]
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ FixedDetMatrices.reps (n : ℤ)) :
    0 < A.1 1 1 := by
  have hprod : A.1 0 0 * A.1 1 1 = (n : ℤ) :=
    FixedDetMatrices.apply_zero_zero_mul_apply_one_one hA.1
  by_contra! hd
  have hle := mul_nonpos_of_nonneg_of_nonpos hA.2.1.le hd
  have hn_pos : (0 : ℤ) < n := Int.natCast_pos.mpr (NeZero.pos n)
  linarith

private theorem toGLReal_smul_eq_posReal_vadd_smul {n : ℕ} [NeZero n]
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ FixedDetMatrices.reps (n : ℤ)) (τ : ℍ) :
    FixedDetMatrices.toGLReal (NeZero.ne (n : ℤ)) A • τ =
      (⟨((A.1 1 1).natAbs : ℝ)⁻¹,
        inv_pos.mpr (Nat.cast_pos.mpr (Int.natAbs_pos.mpr
          (apply_one_one_pos_of_mem_reps hA).ne'))⟩ : {y : ℝ // 0 < y}) •
        (((A.1 0 1).natAbs : ℝ) +ᵥ
          ((⟨((A.1 0 0).natAbs : ℝ), Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA.2.1.ne')⟩ :
            {y : ℝ // 0 < y}) • τ)) := by
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  have hd_pos : 0 < A.1 1 1 := apply_one_one_pos_of_mem_reps hA
  have hdet : 0 < ((FixedDetMatrices.toGLReal hn A).det : ℝ) := by
    rw [FixedDetMatrices.det_toGLReal]; exact_mod_cast NeZero.pos n
  ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, FixedDetMatrices.toGLReal_apply, hA.1,
    coe_pos_real_smul, coe_vadd, Complex.real_smul, Int.cast_zero]
  have ha_eq : (((A.1 0 0).natAbs : ℕ) : ℂ) = A.1 0 0 := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hA.2.1.le]
  have hb_eq : (((A.1 0 1).natAbs : ℕ) : ℂ) = A.1 0 1 := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hA.2.2.1]
  have hd_eq : (((A.1 1 1).natAbs : ℕ) : ℂ) = A.1 1 1 := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hd_pos.le]
  push_cast
  rw [ha_eq, hb_eq, hd_eq]
  field_simp [Int.cast_ne_zero.mpr hd_pos.ne']
  ring

private theorem meromorphicAt_cuspFunction_vadd_posReal_inv_smul {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (hf : MeromorphicAt (cuspFunction 1 f) 0)
    (b : ℕ) (d : ℕ+) :
    MeromorphicAt
      (cuspFunction (d : ℕ) fun τ : ℍ ↦
        f ((⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr (Nat.cast_pos.mpr d.pos)⟩ : {y : ℝ // 0 < y}) •
          ((b : ℝ) +ᵥ τ))) 0 := by
  have hd_real : 0 < ((d : ℕ) : ℝ) := Nat.cast_pos.mpr d.pos
  have hψ₁_per : Function.Periodic
      ((fun τ ↦ f ((⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr hd_real⟩ : {y : ℝ // 0 < y}) • τ)) ∘
        ofComplex) (d : ℕ) := by
    simpa using periodic_vadd_posReal_inv_smul hfper 0 d
  have hψ₁_mer : MeromorphicAt
      (cuspFunction (d : ℕ) fun τ ↦
        f ((⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr hd_real⟩ : {y : ℝ // 0 < y}) • τ)) 0 := by
    simpa [mul_one] using (meromorphicAt_cuspFunction_posReal_mul_iff (h := 1) hd_real f).mpr hf
  exact (meromorphicAt_cuspFunction_vadd_iff hψ₁_per b).mpr hψ₁_mer

/-- For a `1`-periodic function `f` whose cusp function is meromorphic at `0`, composing with an
upper-triangular representative `A ∈ FixedDetMatrices.reps n` gives a function whose width-`n`
cusp function is meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_toGLReal_smul {n : ℕ} [NeZero n] {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (hf : MeromorphicAt (cuspFunction 1 f) 0)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ FixedDetMatrices.reps (n : ℤ)) :
    MeromorphicAt
      (cuspFunction n fun τ ↦ f (FixedDetMatrices.toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 := by
  set a : ℕ+ := (A.1 0 0).natAbs.toPNat (Int.natAbs_pos.mpr hA.2.1.ne')
  set b : ℕ := (A.1 0 1).natAbs
  set d : ℕ+ := (A.1 1 1).natAbs.toPNat (Int.natAbs_pos.mpr (apply_one_one_pos_of_mem_reps hA).ne')
  have hprod : (a : ℕ) * (d : ℕ) = n := by
    simpa [Int.natAbs_mul, a, d, Nat.toPNat] using
      congrArg Int.natAbs (FixedDetMatrices.apply_zero_zero_mul_apply_one_one hA.1)
  have hψ₂_per := periodic_vadd_posReal_inv_smul hfper b d
  have hψ₃_mer := (meromorphicAt_cuspFunction_pnat_smul_iff hψ₂_per a).mpr
    (meromorphicAt_cuspFunction_vadd_posReal_inv_smul hfper hf b d)
  have hEq : (fun τ ↦ f (FixedDetMatrices.toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      fun τ ↦ f ((⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr (Nat.cast_pos.mpr d.pos)⟩ : {y : ℝ // 0 < y}) •
        ((b : ℝ) +ᵥ ((⟨((a : ℕ) : ℝ), Nat.cast_pos.mpr a.pos⟩ : {y : ℝ // 0 < y}) • τ))) :=
    funext fun τ ↦ congrArg f (toGLReal_smul_eq_posReal_vadd_smul hA τ)
  rw [hEq, show (n : ℝ) = (a : ℕ) * ((d : ℕ) : ℝ) by exact_mod_cast hprod.symm]
  exact (meromorphicAt_cuspFunction_pnat_mul_iff
    (periodic_pnat_smul_of_periodic hψ₂_per a) a).mpr hψ₃_mer

/-- **The Laurent `q_{1/n}`-expansion of `τ ↦ f (A • τ)`** for an upper-triangular representative
`A = (a b; 0 d) ∈ FixedDetMatrices.reps n`: substituting `q ↦ ζ_n^{a b} q_{1/n}^{a^2}` into the
Laurent `q`-expansion of `f`. -/
theorem laurentQExpansion_toGLReal_smul {n : ℕ} [NeZero n] {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (hf : MeromorphicAt (cuspFunction 1 f) 0)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ FixedDetMatrices.reps (n : ℤ)) :
    laurentQExpansion n (fun τ ↦ f (FixedDetMatrices.toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ
        (((A.1 0 0).natAbs ^ 2).toPNat (pow_pos (Int.natAbs_pos.mpr hA.2.1.ne') 2))
        (TauCeti.LaurentSeries.rescale
          (Units.mk0
            (Complex.exp (2 * Real.pi * Complex.I / n) ^ ((A.1 0 0).natAbs * (A.1 0 1).natAbs))
            (pow_ne_zero _ (Complex.exp_ne_zero _)))
          (laurentQExpansion 1 f)) := by
  set a : ℕ+ := (A.1 0 0).natAbs.toPNat (Int.natAbs_pos.mpr hA.2.1.ne')
  set b : ℕ := (A.1 0 1).natAbs
  set d : ℕ+ := (A.1 1 1).natAbs.toPNat (Int.natAbs_pos.mpr (apply_one_one_pos_of_mem_reps hA).ne')
  have hprod : (a : ℕ) * (d : ℕ) = n := by
    simpa [Int.natAbs_mul, a, d, Nat.toPNat] using
      congrArg Int.natAbs (FixedDetMatrices.apply_zero_zero_mul_apply_one_one hA.1)
  have hd_real : 0 < ((d : ℕ) : ℝ) := Nat.cast_pos.mpr d.pos
  let ψ₁ : ℍ → ℂ := fun τ ↦ f ((⟨((d : ℕ) : ℝ)⁻¹, inv_pos.mpr hd_real⟩ : {y : ℝ // 0 < y}) • τ)
  have hψ₁_per : Function.Periodic (ψ₁ ∘ ofComplex) (d : ℕ) := by
    simpa [ψ₁] using periodic_vadd_posReal_inv_smul hfper 0 d
  have hψ₁_q : laurentQExpansion (d : ℕ) ψ₁ = laurentQExpansion 1 f := by
    simpa [mul_one] using laurentQExpansion_posReal_mul zero_lt_one hd_real f
  let ψ₂ : ℍ → ℂ := fun τ ↦ ψ₁ ((b : ℝ) +ᵥ τ)
  have hψ₂_per := periodic_vadd_posReal_inv_smul hfper b d
  have hψ₂_mer : MeromorphicAt (cuspFunction (d : ℕ) ψ₂) 0 :=
    meromorphicAt_cuspFunction_vadd_posReal_inv_smul hfper hf b d
  have hψ₃_mer := (meromorphicAt_cuspFunction_pnat_smul_iff hψ₂_per a).mpr hψ₂_mer
  have hEq : (fun τ ↦ f (FixedDetMatrices.toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      fun τ ↦ ψ₂ ((⟨((a : ℕ) : ℝ), Nat.cast_pos.mpr a.pos⟩ : {y : ℝ // 0 < y}) • τ) :=
    funext fun τ ↦ congrArg f (toGLReal_smul_eq_posReal_vadd_smul hA τ)
  have hu : Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * (b : ℝ) / ((d : ℕ) : ℝ)))
      (Complex.exp_ne_zero _) =
      Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n) ^ ((a : ℕ) * b))
        (pow_ne_zero _ (Complex.exp_ne_zero _)) := by
    refine Units.ext ?_
    simp only [Units.val_mk0, ← Complex.exp_nat_mul]
    congr 1
    have hprodC : ((a : ℕ) : ℂ) * (d : ℕ) = n := by exact_mod_cast hprod
    push_cast
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n), Nat.cast_ne_zero.mpr d.ne_zero]
    rw [← hprodC]; ring
  rw [hEq, show (n : ℝ) = (a : ℕ) * ((d : ℕ) : ℝ) by exact_mod_cast hprod.symm,
    laurentQExpansion_pnat_mul (periodic_pnat_smul_of_periodic hψ₂_per a) hψ₃_mer a,
    laurentQExpansion_pnat_smul hd_real hψ₂_per hψ₂_mer a,
    laurentQExpansion_vadd hd_real hψ₁_per b, hψ₁_q,
    LaurentSeries.expand_expand (R := ℂ), hu]
  apply congrArg (fun k : ℕ+ ↦ LaurentSeries.expand ℂ k _)
  exact PNat.eq (by rw [PNat.mul_coe]; simp [sq, a, Nat.toPNat])

private theorem coeff_X_sub_C_mul {R : Type*} [CommRing R] (y : R) (P : R[X]) :
    ∀ k : ℕ, ((X - C y) * P).coeff k =
      (if k = 0 then 0 else P.coeff (k - 1)) - y * P.coeff k
  | 0 => by simp [sub_mul]
  | k + 1 => by simp [sub_mul, coeff_X_mul]

private theorem meromorphicAt_cuspFunction_coeff_prod_X_sub_C {ι : Type*} {h : ℝ}
    (s : Finset ι) {g : ι → ℍ → ℂ}
    (hg : ∀ i ∈ s, MeromorphicAt (cuspFunction h (g i)) 0) :
    ∀ k : ℕ, MeromorphicAt (cuspFunction h fun τ ↦ (∏ i ∈ s, (X - C (g i τ))).coeff k) 0 := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    simpa only [Finset.prod_empty] using
      meromorphicAt_cuspFunction_const (h := h) ((1 : ℂ[X]).coeff k)
  | cons a t hat ih =>
    intro k
    have hEq : (fun τ ↦ (∏ i ∈ Finset.cons a t hat, (X - C (g i τ))).coeff k) =
        (fun τ ↦ if k = 0 then 0 else (∏ i ∈ t, (X - C (g i τ))).coeff (k - 1)) -
          g a * fun τ ↦ (∏ i ∈ t, (X - C (g i τ))).coeff k := by
      funext τ
      simp [Finset.prod_cons, coeff_X_sub_C_mul]
    rw [hEq]
    have hleft : MeromorphicAt
        (cuspFunction h fun τ ↦
          if k = 0 then (0 : ℂ) else (∏ i ∈ t, (X - C (g i τ))).coeff (k - 1)) 0 := by
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simpa [hk] using ih (fun i hi ↦ hg i (Finset.mem_cons_of_mem hi)) (k - 1)
    exact meromorphicAt_cuspFunction_sub hleft
      (meromorphicAt_cuspFunction_mul (hg a (Finset.mem_cons_self a t))
        (ih (fun i hi ↦ hg i (Finset.mem_cons_of_mem hi)) k))

private theorem laurentQExpansion_coeff_prod_X_sub_C {ι : Type*} {h : ℝ}
    (s : Finset ι) {g : ι → ℍ → ℂ}
    (hg : ∀ i ∈ s, MeromorphicAt (cuspFunction h (g i)) 0) :
    ∀ k : ℕ, laurentQExpansion h (fun τ ↦ (∏ i ∈ s, (X - C (g i τ))).coeff k) =
      (∏ i ∈ s, (X - C (laurentQExpansion h (g i)))).coeff k := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    simp only [Finset.prod_empty, laurentQExpansion_const, Polynomial.coeff_one]
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [hk]
  | cons a t hat ih =>
    intro k
    have hgt : ∀ i ∈ t, MeromorphicAt (cuspFunction h (g i)) 0 :=
      fun i hi ↦ hg i (Finset.mem_cons_of_mem hi)
    have hmer := meromorphicAt_cuspFunction_coeff_prod_X_sub_C t hgt
    have hEq : (fun τ ↦ (∏ i ∈ Finset.cons a t hat, (X - C (g i τ))).coeff k) =
        (fun τ ↦ if k = 0 then 0 else (∏ i ∈ t, (X - C (g i τ))).coeff (k - 1)) -
          g a * fun τ ↦ (∏ i ∈ t, (X - C (g i τ))).coeff k := by
      funext τ
      simp [Finset.prod_cons, coeff_X_sub_C_mul]
    have hleft_mer : MeromorphicAt
        (cuspFunction h fun τ ↦
          if k = 0 then (0 : ℂ) else (∏ i ∈ t, (X - C (g i τ))).coeff (k - 1)) 0 := by
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simpa [hk] using hmer (k - 1)
    have hleft_q : laurentQExpansion h
        (fun τ ↦ if k = 0 then (0 : ℂ) else (∏ i ∈ t, (X - C (g i τ))).coeff (k - 1)) =
        if k = 0 then 0
        else (∏ i ∈ t, (X - C (laurentQExpansion h (g i)))).coeff (k - 1) := by
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simpa [hk] using ih hgt (k - 1)
    rw [hEq, Finset.prod_cons, coeff_X_sub_C_mul,
      laurentQExpansion_sub hleft_mer
        (meromorphicAt_cuspFunction_mul (hg a (Finset.mem_cons_self a t)) (hmer k)),
      laurentQExpansion_mul (hg a (Finset.mem_cons_self a t)) (hmer k), hleft_q, ih hgt k]

private theorem meromorphicAt_cuspFunction_prod {ι : Type*} {h : ℝ}
    (s : Finset ι) {g : ι → ℍ → ℂ}
    (hg : ∀ i ∈ s, MeromorphicAt (cuspFunction h (g i)) 0) :
    MeromorphicAt (cuspFunction h fun τ ↦ ∏ i ∈ s, g i τ) 0 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih =>
    have hEq : (fun τ ↦ ∏ i ∈ Finset.cons a t hat, g i τ) = g a * fun τ ↦ ∏ i ∈ t, g i τ :=
      funext fun τ ↦ Finset.prod_cons hat
    rw [hEq]
    exact meromorphicAt_cuspFunction_mul (hg a (Finset.mem_cons_self a t))
      (ih fun i hi ↦ hg i (Finset.mem_cons_of_mem hi))

private theorem laurentQExpansion_prod {ι : Type*} {h : ℝ}
    (s : Finset ι) {g : ι → ℍ → ℂ}
    (hg : ∀ i ∈ s, MeromorphicAt (cuspFunction h (g i)) 0) :
    laurentQExpansion h (fun τ ↦ ∏ i ∈ s, g i τ) = ∏ i ∈ s, laurentQExpansion h (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih =>
    have hgt : ∀ i ∈ t, MeromorphicAt (cuspFunction h (g i)) 0 :=
      fun i hi ↦ hg i (Finset.mem_cons_of_mem hi)
    have hEq : (fun τ ↦ ∏ i ∈ Finset.cons a t hat, g i τ) = g a * fun τ ↦ ∏ i ∈ t, g i τ :=
      funext fun τ ↦ Finset.prod_cons hat
    rw [hEq, Finset.prod_cons, laurentQExpansion_mul (hg a (Finset.mem_cons_self a t))
      (meromorphicAt_cuspFunction_prod t hgt), ih hgt]

end TauCeti.UpperHalfPlane

/-! ### Cyclotomic Galois descent and integrality of `q`-coefficients -/

namespace TauCeti.ModularForm

open FixedDetMatrices

section GaloisDescent

private theorem periodic_j : Function.Periodic (j ∘ ofComplex) 1 :=
  UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by rw [← modular_T_smul, j_smul_SL2Z]

private theorem cyclicIsogenyPolynomial_T_smul (n : ℕ) [NeZero n] {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    cyclicIsogenyPolynomial n f (ModularGroup.T • τ) = cyclicIsogenyPolynomial n f τ := by
  classical
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  have hSL (g : SL(2, ℤ)) (z : ℍ) : Matrix.SpecialLinearGroup.mapGL ℝ g • z = g • z :=
    (MulAction.compHom_smul_def _ _ _).symm
  have hperm {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ primitiveReps (n : ℤ)) :
      X - C (f (toGLReal hn A • ModularGroup.T • τ)) =
        X - C (f (toGLReal hn (repsRightMul hn ModularGroup.T⁻¹ A) • τ)) := by
    have hA' := (mem_primitiveReps.mp hA).1
    have hB := repsRightMul_mem_reps hn ModularGroup.T⁻¹ A
    set γ := repsRightMulFactor hn ModularGroup.T⁻¹ A
    have hγ10 : γ 1 0 = 0 := by
      have h10 : (repsRightMul hn ModularGroup.T⁻¹ A).1 1 0 = 0 := hB.1
      rw [repsRightMul_def, FixedDetMatrices.smul_coe, val_traceFormulaMatrixRight, inv_inv] at h10
      simp_rw [Matrix.mul_apply, Fin.sum_univ_two] at h10
      simp only [ModularGroup.coe_T, hA'.1, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, mul_zero,
        add_zero] at h10
      exact (mul_eq_zero.mp h10).resolve_right hA'.2.1.ne'
    obtain ⟨m, hm⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hγ10
    have heq : toGLReal hn A • ModularGroup.T • τ =
        ModularGroup.T ^ (-m) • (toGLReal hn (repsRightMul hn ModularGroup.T⁻¹ A) • τ) := by
      have hmul := congrArg (· • τ) (toGLReal_repsRightMul hn ModularGroup.T⁻¹ A)
      rw [inv_inv, mul_smul, mul_smul, hSL, hSL, hm] at hmul
      rw [hmul, _root_.zpow_neg, inv_smul_smul]
    have hper_m (z : ℍ) : f (ModularGroup.T ^ (-m) • z) = f z := by
      have hz := hfper.int_mul (-m) z
      rw [Function.comp_apply, Function.comp_apply, mul_one,
        ← ModularGroup.coe_T_zpow_smul_eq, ofComplex_apply, ofComplex_apply] at hz
      exact hz
    rw [heq, hper_m]
  rw [cyclicIsogenyPolynomial_def, cyclicIsogenyPolynomial_def,
    Finset.prod_congr rfl fun A hA ↦ hperm hA,
    ← Finset.prod_image (f := fun A ↦ X - C (f (toGLReal hn A • τ)))
      (repsRightMul_injOn_primitiveReps hn ModularGroup.T⁻¹),
    image_repsRightMul_primitiveReps]

/-- For a `1`-periodic function `f` whose cusp function is meromorphic at `0`, every coefficient of
`cyclicIsogenyPolynomial n f` has a cusp function meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial (n : ℕ) [NeZero n] {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1)
    (hf : MeromorphicAt (cuspFunction 1 f) 0) (k : ℕ) :
    MeromorphicAt (cuspFunction 1 fun τ ↦ (cyclicIsogenyPolynomial n f τ).coeff k) 0 := by
  have hck_per : Function.Periodic
      ((fun τ : ℍ ↦ (cyclicIsogenyPolynomial n f τ).coeff k) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← modular_T_smul]
      exact congrArg (fun P ↦ P.coeff k) (cyclicIsogenyPolynomial_T_smul n hfper τ)
  have hmer_n : MeromorphicAt
      (cuspFunction n fun τ ↦ (cyclicIsogenyPolynomial n f τ).coeff k) 0 := by
    simp only [cyclicIsogenyPolynomial_def]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_coeff_prod_X_sub_C (primitiveReps (n : ℤ))
      (fun A hA ↦ UpperHalfPlane.meromorphicAt_cuspFunction_toGLReal_smul hfper hf
        (mem_primitiveReps.mp hA).1) k
  refine (UpperHalfPlane.meromorphicAt_cuspFunction_pnat_mul_iff (h := 1) hck_per
    (n.toPNat (NeZero.pos n))).mp ?_
  simpa [mul_one, Nat.toPNat] using hmer_n

/-- The permutation of upper-triangular determinant-`n` matrices induced by `u ∈ (ZMod n)ˣ`:
`(a b; 0 d) ↦ (a, u b mod d; 0, d)`. -/
private def permRep {n : ℕ} [NeZero n] (u : (ZMod n)ˣ)
    (A : FixedDetMatrix (Fin 2) ℤ n) : FixedDetMatrix (Fin 2) ℤ n :=
  if h : A.1 1 0 = 0 then
    ⟨!![A.1 0 0, (((u : ZMod n).val : ℤ) * A.1 0 1) % A.1 1 1; 0, A.1 1 1], by
      simpa [det_fin_two] using apply_zero_zero_mul_apply_one_one h⟩
  else A

private theorem permRep_mem_primitiveReps {n : ℕ} [NeZero n] (u : (ZMod n)ˣ)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ primitiveReps (n : ℤ)) :
    permRep u A ∈ primitiveReps (n : ℤ) := by
  obtain ⟨⟨h₁₀, h₀₀, _, _⟩, hprim⟩ := mem_primitiveReps.mp hA
  have hprod : A.1 0 0 * A.1 1 1 = (n : ℤ) := apply_zero_zero_mul_apply_one_one h₁₀
  have hd : 0 < A.1 1 1 := UpperHalfPlane.apply_one_one_pos_of_mem_reps (mem_primitiveReps.mp hA).1
  set c : ℤ := ((u : ZMod n).val : ℤ)
  set c' : ℤ := (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ)
  have hEq : (permRep u A).1 = !![A.1 0 0, (c * A.1 0 1) % A.1 1 1; 0, A.1 1 1] := by
    simp [permRep, h₁₀, c]
  refine mem_primitiveReps.mpr ⟨?_, ?_⟩
  · refine ⟨by rw [hEq]; rfl, by rw [hEq]; exact h₀₀,
      by rw [hEq]; exact Int.emod_nonneg _ hd.ne', ?_⟩
    change |(permRep u A).1 0 1| < |(permRep u A).1 1 1|
    rw [hEq]
    simpa [abs_of_nonneg (Int.emod_nonneg (c * A.1 0 1) hd.ne'), abs_of_pos hd] using
      Int.emod_lt_of_pos (c * A.1 0 1) hd
  · have hcc' : (n : ℤ) ∣ 1 - c * c' := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp [c, c']
    have hdvd_n : A.1 1 1 ∣ (n : ℤ) := ⟨A.1 0 0, by linear_combination -hprod⟩
    obtain ⟨q₁, hq₁⟩ := dvd_trans hdvd_n hcc'
    set q₂ : ℤ := c * A.1 0 1 / A.1 1 1
    have hmod : c * A.1 0 1 % A.1 1 1 = c * A.1 0 1 - A.1 1 1 * q₂ := by
      linarith [Int.emod_add_mul_ediv (c * A.1 0 1) (A.1 1 1)]
    let k : ℤ := q₁ * A.1 0 1 + c' * q₂
    let L : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
      { toFun B := !![B 0 0, c' * B 0 1 + k * B 1 1; B 1 0, B 1 1]
        map_add' _ _ := by ext i j; fin_cases i <;> fin_cases j <;> simp; ring
        map_smul' _ _ := by ext i j; fin_cases i <;> fin_cases j <;> simp; ring }
    have hLA : L (permRep u A).1 = A.1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [L, hEq]
      · simp only [L, hEq, Fin.zero_eta, Fin.mk_one, LinearMap.coe_mk, AddHom.coe_mk, of_apply,
          cons_val_zero, cons_val_one, cons_val_fin_one, k, hmod]
        linear_combination -A.1 0 1 * hq₁
      · simp [L, hEq, h₁₀]
      · simp [L, hEq]
    exact (hLA.symm ▸ hprim).of_map

private theorem permRep_inv_permRep {n : ℕ} [NeZero n] (u : (ZMod n)ˣ)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ primitiveReps (n : ℤ)) :
    permRep u⁻¹ (permRep u A) = A := by
  obtain ⟨⟨h₁₀, _, h₀₁, h₁₁⟩, -⟩ := mem_primitiveReps.mp hA
  have hprod : A.1 0 0 * A.1 1 1 = (n : ℤ) := apply_zero_zero_mul_apply_one_one h₁₀
  have hd : 0 < A.1 1 1 := UpperHalfPlane.apply_one_one_pos_of_mem_reps (mem_primitiveReps.mp hA).1
  have hb_lt : A.1 0 1 < A.1 1 1 := by
    simpa [abs_of_nonneg h₀₁, abs_of_pos hd] using h₁₁
  set c : ℤ := ((u : ZMod n).val : ℤ)
  set c' : ℤ := (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ)
  have hcc' : (n : ℤ) ∣ c' * c - 1 := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp [c, c']
  have hdvd : A.1 1 1 ∣ c' * (c * A.1 0 1) - A.1 0 1 := by
    have hdvd_n : A.1 1 1 ∣ (n : ℤ) := ⟨A.1 0 0, by linear_combination -hprod⟩
    obtain ⟨q, hq⟩ := dvd_trans hdvd_n hcc'
    exact ⟨q * A.1 0 1, by linear_combination A.1 0 1 * hq⟩
  have hmod : (c' * ((c * A.1 0 1) % A.1 1 1)) % A.1 1 1 = A.1 0 1 := by
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod,
      (Int.modEq_iff_dvd.mpr hdvd).symm, Int.emod_eq_of_lt h₀₁ hb_lt]
  apply FixedDetMatrices.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [permRep, h₁₀]
  · simp only [permRep, h₁₀, ↓reduceDIte, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one]
    exact hmod
  · simp [permRep, h₁₀]
  · simp [permRep, h₁₀]

private abbrev cycField (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / n)}

private def cycZeta (n : ℕ) : cycField n :=
  ⟨Complex.exp (2 * Real.pi * Complex.I / n), IntermediateField.mem_adjoin_simple_self ℚ _⟩

private theorem isPrimitiveRoot_cycZeta (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (cycZeta n) n := by
  have hC := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  rw [IsPrimitiveRoot.iff_def] at hC ⊢
  refine ⟨Subtype.ext (by simpa [cycZeta] using hC.1), fun l hl ↦ hC.2 l ?_⟩
  simpa [cycZeta] using congrArg Subtype.val hl

private def cycUnit (n : ℕ) [NeZero n] : (cycField n)ˣ :=
  Units.mk0 (cycZeta n) ((isPrimitiveRoot_cycZeta n).ne_zero (NeZero.ne n))

private theorem cycUnit_zpow_eq_pow_emod (n : ℕ) [NeZero n] (s : ℤ) :
    ((cycUnit n ^ s : (cycField n)ˣ) : cycField n) =
      cycZeta n ^ (s % (n : ℤ)).toNat := by
  have hpow1 : cycUnit n ^ (n : ℤ) = 1 := by
    rw [_root_.zpow_natCast]
    exact Units.ext (isPrimitiveRoot_cycZeta n).pow_eq_one
  have hnonneg : 0 ≤ s % (n : ℤ) := Int.emod_nonneg s (NeZero.ne (n : ℤ))
  have hs : s = (n : ℤ) * (s / (n : ℤ)) + ((s % (n : ℤ)).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hnonneg, add_comm, Int.emod_add_mul_ediv]
  conv_lhs => rw [hs]
  rw [_root_.zpow_add, _root_.zpow_mul, hpow1, _root_.one_zpow, one_mul, _root_.zpow_natCast,
    Units.val_pow_eq_pow_val]
  rfl

private theorem aut_apply_cycUnit_zpow {n : ℕ} [NeZero n] (σ : cycField n ≃ₐ[ℚ] cycField n)
    (s : ℤ) :
    σ ((cycUnit n ^ s : (cycField n)ˣ) : cycField n) =
      ((cycUnit n ^ ((((isPrimitiveRoot_cycZeta n).autToPow ℚ σ : ZMod n).val : ℤ) * s) :
        (cycField n)ˣ) : cycField n) := by
  set c : ℕ := ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ : ZMod n).val
  have hpow1 : cycUnit n ^ (n : ℤ) = 1 := by
    rw [_root_.zpow_natCast]
    exact Units.ext (isPrimitiveRoot_cycZeta n).pow_eq_one
  have hnonneg : 0 ≤ s % (n : ℤ) := Int.emod_nonneg s (NeZero.ne (n : ℤ))
  set k : ℕ := (s % (n : ℤ)).toNat
  have hk : (k : ℤ) = s % (n : ℤ) := Int.toNat_of_nonneg hnonneg
  rw [cycUnit_zpow_eq_pow_emod, map_pow, ← (isPrimitiveRoot_cycZeta n).autToPow_spec ℚ σ,
    ← pow_mul]
  have hval : cycZeta n ^ (c * k) =
      ((cycUnit n ^ ((c * k : ℕ) : ℤ) : (cycField n)ˣ) : cycField n) := by
    rw [_root_.zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  rw [hval]
  apply congrArg Units.val
  have hEq : (c : ℤ) * s = (n : ℤ) * ((c : ℤ) * (s / (n : ℤ))) + ((c * k : ℕ) : ℤ) := by
    push_cast
    rw [hk]
    linear_combination -(c : ℤ) * Int.emod_add_mul_ediv s (n : ℤ)
  rw [hEq, _root_.zpow_add, _root_.zpow_mul, hpow1, _root_.one_zpow, one_mul]

private def factorSeriesAux (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    (a b : ℕ) : LaurentSeries (cycField n) :=
  LaurentSeries.expand (cycField n) ((max (a ^ 2) 1).toPNat (by positivity))
    (TauCeti.LaurentSeries.rescale
      (cycUnit n ^ (a * b))
      (HahnSeries.mapRingHom (Int.castRingHom (cycField n)) jZ))

private def factorSeries (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) : LaurentSeries (cycField n) :=
  factorSeriesAux n jZ (M 0 0).natAbs (M 0 1).natAbs

private theorem map_val_factorSeriesAux (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    {a : ℕ} (ha : 0 < a) (b : ℕ) :
    HahnSeries.mapRingHom (cycField n).val.toRingHom (factorSeriesAux n jZ a b) =
      LaurentSeries.expand ℂ ((a ^ 2).toPNat (pow_pos ha 2))
        (TauCeti.LaurentSeries.rescale
          (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n) ^ (a * b))
            (pow_ne_zero _ (Complex.exp_ne_zero _)))
          (HahnSeries.mapRingHom (Int.castRingHom ℂ) jZ)) := by
  set d : ℕ+ := (a ^ 2).toPNat (pow_pos ha 2)
  have hmax : (max (a ^ 2) 1).toPNat (by positivity) = d :=
    PNat.eq (max_eq_left (pow_pos ha 2))
  rw [factorSeriesAux, hmax]
  ext m
  by_cases hm : ((d : ℕ) : ℤ) ∣ m
  · obtain ⟨r, rfl⟩ := hm
    rw [HahnSeries.coeff_mapRingHom,
      LaurentSeries.coeff_expand_mul (R := cycField n) d,
      LaurentSeries.coeff_expand_mul (R := ℂ) d,
      TauCeti.LaurentSeries.coeff_rescale (R := cycField n),
      TauCeti.LaurentSeries.coeff_rescale (R := ℂ),
      HahnSeries.coeff_mapRingHom, Int.coe_castRingHom, map_mul, map_intCast,
      Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      map_zpow₀, map_pow]
    simp [cycUnit, cycZeta]
  · rw [HahnSeries.coeff_mapRingHom,
      LaurentSeries.coeff_expand_of_not_dvd (R := cycField n) d _ hm,
      LaurentSeries.coeff_expand_of_not_dvd (R := ℂ) d _ hm,
      map_zero]

private theorem map_val_factorSeries {n : ℕ} [NeZero n] {jZ : LaurentSeries ℤ}
    (hjZ : HahnSeries.mapRingHom (Int.castRingHom ℂ) jZ = UpperHalfPlane.laurentQExpansion 1 j)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    HahnSeries.mapRingHom (cycField n).val.toRingHom (factorSeries n jZ A.1) =
      UpperHalfPlane.laurentQExpansion n (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) :=
  (map_val_factorSeriesAux n jZ (Int.natAbs_pos.mpr hA.2.1.ne') (A.1 0 1).natAbs).trans
    (by rw [UpperHalfPlane.laurentQExpansion_toGLReal_smul periodic_j meromorphicAt_cuspFunction_j
          hA, hjZ])

private theorem isIntegral_coeff_factorSeries (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (m : ℤ) :
    IsIntegral ℤ ((factorSeries n jZ M).coeff m) := by
  set a := (M 0 0).natAbs
  set b := (M 0 1).natAbs
  set d : ℕ+ := (max (a ^ 2) 1).toPNat (by positivity)
  change IsIntegral ℤ ((factorSeriesAux n jZ a b).coeff m)
  rw [factorSeriesAux]
  by_cases hm : ((d : ℕ) : ℤ) ∣ m
  · obtain ⟨r, rfl⟩ := hm
    rw [LaurentSeries.coeff_expand_mul (R := cycField n) d,
      TauCeti.LaurentSeries.coeff_rescale (R := cycField n),
      HahnSeries.coeff_mapRingHom, ← _root_.zpow_natCast, ← _root_.zpow_mul,
      cycUnit_zpow_eq_pow_emod]
    exact (((isPrimitiveRoot_cycZeta n).isIntegral (NeZero.pos n)).pow _).mul
      isIntegral_algebraMap
  · rw [LaurentSeries.coeff_expand_of_not_dvd (R := cycField n) d _ hm]
    exact isIntegral_zero

private theorem isIntegral_coeff_prod_factorSeries {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (s : Finset (FixedDetMatrix (Fin 2) ℤ n)) :
    ∀ (k : ℕ) (m : ℤ),
      IsIntegral ℤ (((∏ A ∈ s, (X - C (factorSeries n jZ A.1))).coeff k).coeff m) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k m
    rw [Finset.prod_empty, Polynomial.coeff_one]
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [↓reduceIte]
      rcases eq_or_ne m 0 with rfl | hm
      · simpa using (isIntegral_one : IsIntegral ℤ (1 : cycField n))
      · simp [HahnSeries.coeff_one, hm, isIntegral_zero]
    · simp [hk, isIntegral_zero]
  | cons a t hat ih =>
    intro k m
    rw [Finset.prod_cons, UpperHalfPlane.coeff_X_sub_C_mul, HahnSeries.coeff_sub]
    have hleft : IsIntegral ℤ
        ((if k = 0 then (0 : LaurentSeries (cycField n))
          else (∏ i ∈ t, (X - C (factorSeries n jZ i.1))).coeff (k - 1)).coeff m) := by
      rcases eq_or_ne k 0 with rfl | hk
      · simp [isIntegral_zero]
      · simpa [hk] using ih (k - 1) m
    refine hleft.sub ?_
    rw [HahnSeries.coeff_mul]
    exact IsIntegral.sum _ fun p _ ↦
      (isIntegral_coeff_factorSeries n jZ a.1 p.1).mul (ih k p.2)

private theorem map_aut_factorSeriesAux {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (σ : cycField n ≃ₐ[ℚ] cycField n) (a b b' : ℕ) {q : ℤ}
    (hcong : (((isPrimitiveRoot_cycZeta n).autToPow ℚ σ : ZMod n).val : ℤ) * ((a * b : ℕ) : ℤ) =
      (n : ℤ) * q + ((a * b' : ℕ) : ℤ)) :
    HahnSeries.mapRingHom (σ : cycField n →+* cycField n) (factorSeriesAux n jZ a b) =
      factorSeriesAux n jZ a b' := by
  set d : ℕ+ := (max (a ^ 2) 1).toPNat (by positivity)
  rw [factorSeriesAux, factorSeriesAux]
  ext m : 2
  by_cases hm : ((d : ℕ) : ℤ) ∣ m
  · obtain ⟨r, rfl⟩ := hm
    rw [HahnSeries.coeff_mapRingHom,
      LaurentSeries.coeff_expand_mul (R := cycField n) d,
      LaurentSeries.coeff_expand_mul (R := cycField n) d,
      TauCeti.LaurentSeries.coeff_rescale (R := cycField n),
      TauCeti.LaurentSeries.coeff_rescale (R := cycField n),
      HahnSeries.coeff_mapRingHom, RingHom.coe_coe, Int.coe_castRingHom, map_mul, map_intCast]
    dsimp only
    refine congrArg (· * (jZ.coeff r : cycField n)) ?_
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_natCast, ← _root_.zpow_mul,
      aut_apply_cycUnit_zpow]
    apply congrArg Units.val
    have hpow1 : cycUnit n ^ (n : ℤ) = 1 := by
      rw [_root_.zpow_natCast]; exact Units.ext (isPrimitiveRoot_cycZeta n).pow_eq_one
    have hEq : (((isPrimitiveRoot_cycZeta n).autToPow ℚ σ : ZMod n).val : ℤ) *
        (((a * b : ℕ) : ℤ) * r) = (n : ℤ) * (q * r) + (((a * b' : ℕ) : ℤ) * r) := by
      linear_combination r * hcong
    rw [hEq, _root_.zpow_add, _root_.zpow_mul, hpow1, _root_.one_zpow, one_mul]
  · rw [HahnSeries.coeff_mapRingHom,
      LaurentSeries.coeff_expand_of_not_dvd (R := cycField n) d _ hm,
      LaurentSeries.coeff_expand_of_not_dvd (R := cycField n) d _ hm, map_zero]

private theorem map_aut_factorSeries {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (σ : cycField n ≃ₐ[ℚ] cycField n) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ primitiveReps (n : ℤ)) :
    HahnSeries.mapRingHom (σ : cycField n →+* cycField n) (factorSeries n jZ A.1) =
      factorSeries n jZ (permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ) A).1 := by
  obtain ⟨⟨h₁₀, h₀₀, h₀₁, -⟩, -⟩ := mem_primitiveReps.mp hA
  have hprod : A.1 0 0 * A.1 1 1 = (n : ℤ) := apply_zero_zero_mul_apply_one_one h₁₀
  have hd : 0 < A.1 1 1 := UpperHalfPlane.apply_one_one_pos_of_mem_reps (mem_primitiveReps.mp hA).1
  set u := (isPrimitiveRoot_cycZeta n).autToPow ℚ σ
  have hperm₀₀ : (permRep u A).1 0 0 = A.1 0 0 := by simp [permRep, h₁₀]
  have hperm₀₁ : (permRep u A).1 0 1 = (((u : ZMod n).val : ℤ) * A.1 0 1) % A.1 1 1 := by
    simp [permRep, h₁₀]
  set q := (((u : ZMod n).val : ℤ) * A.1 0 1) / A.1 1 1
  have hdiv := Int.emod_add_mul_ediv (((u : ZMod n).val : ℤ) * A.1 0 1) (A.1 1 1)
  have ha_eq : ((A.1 0 0).natAbs : ℤ) = A.1 0 0 := Int.natAbs_of_nonneg h₀₀.le
  have hb_eq : ((A.1 0 1).natAbs : ℤ) = A.1 0 1 := Int.natAbs_of_nonneg h₀₁
  have hb'_eq : (((permRep u A).1 0 1).natAbs : ℤ) =
      (((u : ZMod n).val : ℤ) * A.1 0 1) % A.1 1 1 :=
    (congrArg (fun x : ℤ ↦ (x.natAbs : ℤ)) hperm₀₁).trans
      (Int.natAbs_of_nonneg (Int.emod_nonneg _ hd.ne'))
  have hcong : ((u : ZMod n).val : ℤ) * (((A.1 0 0).natAbs * (A.1 0 1).natAbs : ℕ) : ℤ) =
      (n : ℤ) * q + (((A.1 0 0).natAbs * ((permRep u A).1 0 1).natAbs : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, ha_eq, hb_eq, hb'_eq]
    linear_combination -A.1 0 0 * hdiv + q * hprod
  exact (map_aut_factorSeriesAux jZ σ (A.1 0 0).natAbs (A.1 0 1).natAbs
    ((permRep u A).1 0 1).natAbs hcong).trans
      (congrArg (fun a ↦ factorSeriesAux n jZ a ((permRep u A).1 0 1).natAbs)
        (congrArg Int.natAbs hperm₀₀.symm))

private theorem map_aut_prod_X_sub_C_factorSeries {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (σ : cycField n ≃ₐ[ℚ] cycField n) :
    (∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.1))).map
        (HahnSeries.mapRingHom (σ : cycField n →+* cycField n)) =
      ∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.1)) := by
  rw [Polynomial.map_prod]
  refine Finset.prod_bij (fun A _ ↦ permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ) A)
    (fun _ hA ↦ permRep_mem_primitiveReps _ hA)
    (fun A₁ hA₁ A₂ hA₂ hEq ↦ by
      have := congrArg (permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ)⁻¹) hEq
      rwa [permRep_inv_permRep _ hA₁, permRep_inv_permRep _ hA₂] at this)
    (fun B hB ↦ ⟨permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ)⁻¹ B,
      permRep_mem_primitiveReps _ hB, by
        simpa using permRep_inv_permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ)⁻¹ hB⟩)
    fun A hA ↦ by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_aut_factorSeries jZ σ hA]

private theorem laurentQExpansion_n_coeff_cyclicIsogenyPolynomial_j_mem_range (n : ℕ) [NeZero n]
    (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m ∈
      (algebraMap ℤ ℂ).range := by
  obtain ⟨jZ, hjZ⟩ : UpperHalfPlane.laurentQExpansion 1 j ∈
      (HahnSeries.mapRingHom (Int.castRingHom ℂ) : LaurentSeries ℤ →+* LaurentSeries ℂ).rangeS :=
    HahnSeries.mem_map_rangeS.mpr fun g ↦
      let ⟨z, hz⟩ := exists_laurentQExpansion_j_coeff_eq_intCast g
      ⟨z, hz.symm⟩
  set ΦK : (LaurentSeries (cycField n))[X] :=
    ∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.1))
  have hΦ_map : ΦK.map (HahnSeries.mapRingHom (cycField n).val.toRingHom) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (X - C (UpperHalfPlane.laurentQExpansion n
          (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun A hA ↦ ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      map_val_factorSeries hjZ (mem_primitiveReps.mp hA).1]
  have hcoeffC : (UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m =
      (cycField n).val (((ΦK.coeff k).coeff m)) := by
    simp only [cyclicIsogenyPolynomial_def]
    rw [UpperHalfPlane.laurentQExpansion_coeff_prod_X_sub_C (primitiveReps (n : ℤ))
        (fun A hA ↦ UpperHalfPlane.meromorphicAt_cuspFunction_toGLReal_smul periodic_j
          meromorphicAt_cuspFunction_j (mem_primitiveReps.mp hA).1) k,
      ← hΦ_map, Polynomial.coeff_map, HahnSeries.coeff_mapRingHom]
    rfl
  have hcyc : IsCyclotomicExtension {n} ℚ (cycField n) :=
    (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).isCyclotomicExtension_adjoin_singleton
  have : IsGalois ℚ (cycField n) := IsCyclotomicExtension.isGalois {n} ℚ (cycField n)
  have : FiniteDimensional ℚ (cycField n) := IsCyclotomicExtension.finite {n} ℚ (cycField n)
  have hfixed : ∀ σ : cycField n ≃ₐ[ℚ] cycField n, σ ((ΦK.coeff k).coeff m) =
      (ΦK.coeff k).coeff m := fun σ ↦ by
    have := congrArg (fun P : (LaurentSeries (cycField n))[X] ↦ (P.coeff k).coeff m)
      (map_aut_prod_X_sub_C_factorSeries jZ σ)
    simpa [ΦK, Polynomial.coeff_map, HahnSeries.coeff_mapRingHom] using this
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hfixed)
  have hint_q : IsIntegral ℤ q := by
    refine isIntegral_ratCast_iff (K := cycField n).mp ?_
    have hint := isIntegral_coeff_prod_factorSeries jZ (primitiveReps (n : ℤ)) k m
    rwa [show ∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.1)) = ΦK from rfl, ← hq]
      at hint
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint_q
  refine ⟨z, ?_⟩
  rw [hcoeffC, ← hq]
  simp

/-- **Every Laurent `q`-coefficient of every coefficient of `cyclicIsogenyPolynomial n j` is an
integer.** -/
theorem laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_range (n : ℕ) [NeZero n]
    (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion 1
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m ∈
      (algebraMap ℤ ℂ).range := by
  have hck_per : Function.Periodic
      ((fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← modular_T_smul]
      exact congrArg (fun P ↦ P.coeff k) (cyclicIsogenyPolynomial_smul (n := n) j_smul_SL2Z _ τ)
  have hmer := meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial n periodic_j
    meromorphicAt_cuspFunction_j k
  have hexp : UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) =
      LaurentSeries.expand ℂ (n.toPNat (NeZero.pos n))
        (UpperHalfPlane.laurentQExpansion 1
          fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) := by
    simpa [mul_one, Nat.toPNat] using
      UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1) hck_per hmer (n.toPNat (NeZero.pos n))
  have hm := laurentQExpansion_n_coeff_cyclicIsogenyPolynomial_j_mem_range n k
    (((n.toPNat (NeZero.pos n) : ℕ) : ℤ) * m)
  rwa [hexp, LaurentSeries.coeff_expand_mul (R := ℂ) (n.toPNat (NeZero.pos n))] at hm

end GaloisDescent

/-! ### The classical modular polynomial `Φ_n(X, Y) ∈ ℤ[Y][X]` -/

section ModularPolynomial

private theorem exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial (n : ℕ) [NeZero n] (k : ℕ) :
    ∃ P : ℤ[X], ∀ τ : ℍ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).coeff k :=
  exists_aeval_j_eq (mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k)
    (fun γ τ ↦ congrArg (fun Q ↦ Q.coeff k)
      (cyclicIsogenyPolynomial_smul (n := n) j_smul_SL2Z γ τ))
    (meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial n periodic_j
      meromorphicAt_cuspFunction_j k)
    fun m _ ↦ laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_range n k m

/-- **The classical modular polynomial** `Φ_n(X, Y) ∈ ℤ[Y][X]`, represented as a polynomial over
`ℤ[X]`: the unique integral bivariate polynomial whose specialization `Y ↦ j(τ)` is
`cyclicIsogenyPolynomial n j τ = ∏_{(a b; 0 d)} (X - j((a τ + b) / d))`. -/
noncomputable def modularPolynomial (n : ℕ) [NeZero n] : ℤ[X][X] :=
  ∑ k ∈ Finset.range ((primitiveReps (n : ℤ)).card + 1),
    Polynomial.monomial k (exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose

/-- Evaluating the `X ^ k`-coefficient of `modularPolynomial n` at `j(τ)` recovers the `X ^ k`
coefficient of `cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem aeval_j_coeff_modularPolynomial (n : ℕ) [NeZero n] (k : ℕ) (τ : ℍ) :
    aeval (j τ) ((modularPolynomial n).coeff k) = (cyclicIsogenyPolynomial n j τ).coeff k := by
  rw [modularPolynomial, Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ (primitiveReps (n : ℤ)).card
  · rw [Finset.sum_eq_single k
      (fun i _ hik ↦ by simp [coeff_monomial, hik.symm])
      (fun hnot ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hnot)]
    simp [(exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose_spec τ]
  · rw [Finset.sum_eq_zero fun i hi ↦ by
        have hi' := Finset.mem_range.mp hi
        have hik : i ≠ k := by omega
        simp [coeff_monomial, hik],
      map_zero, coeff_eq_zero_of_natDegree_lt]
    rw [natDegree_cyclicIsogenyPolynomial]
    omega

/-- Specializing the coefficient ring of `modularPolynomial n` along `Y ↦ j(τ)` recovers
`cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem map_aeval_j_modularPolynomial (n : ℕ) [NeZero n] (τ : ℍ) :
    (modularPolynomial n).map (aeval (R := ℤ) (j τ)) = cyclicIsogenyPolynomial n j τ := by
  ext k
  rw [Polynomial.coeff_map, RingHom.coe_coe]
  exact aeval_j_coeff_modularPolynomial n k τ

/-- **Uniqueness of the modular polynomial**: `modularPolynomial n` is the unique polynomial in
`ℤ[X][X]` whose specialization at `j(τ)` equals `cyclicIsogenyPolynomial n j τ` for all `τ ∈ ℍ`. -/
theorem eq_modularPolynomial_of_map_aeval_j_eq {n : ℕ} [NeZero n] {P : ℤ[X][X]}
    (h : ∀ τ : ℍ, P.map (aeval (R := ℤ) (j τ)) = cyclicIsogenyPolynomial n j τ) :
    P = modularPolynomial n := by
  ext k : 2
  refine aeval_j_injective (Int.cast_injective (α := ℂ)) (funext fun τ ↦ ?_)
  dsimp only
  have hτ := congrArg (fun Q : ℂ[X] ↦ Q.coeff k) (h τ)
  rw [Polynomial.coeff_map, RingHom.coe_coe] at hτ
  exact hτ.trans (aeval_j_coeff_modularPolynomial n k τ).symm

private theorem coeff_modularPolynomial_eq_zero_of_lt {n : ℕ} [NeZero n] {k : ℕ}
    (hk : (primitiveReps (n : ℤ)).card < k) :
    (modularPolynomial n).coeff k = 0 := by
  refine aeval_j_injective (Int.cast_injective (α := ℂ)) (funext fun τ ↦ ?_)
  dsimp only
  rw [aeval_j_coeff_modularPolynomial, map_zero, coeff_eq_zero_of_natDegree_lt]
  rwa [natDegree_cyclicIsogenyPolynomial]

private theorem coeff_modularPolynomial_card (n : ℕ) [NeZero n] :
    (modularPolynomial n).coeff (primitiveReps (n : ℤ)).card = 1 := by
  refine aeval_j_injective (Int.cast_injective (α := ℂ)) (funext fun τ ↦ ?_)
  dsimp only
  rw [aeval_j_coeff_modularPolynomial, map_one, ← natDegree_cyclicIsogenyPolynomial (n := n) j τ]
  exact (monic_cyclicIsogenyPolynomial j τ).leadingCoeff

/-- The degree of `modularPolynomial n` in `X` is the number of cyclic `n`-isogenies. -/
@[simp]
theorem natDegree_modularPolynomial (n : ℕ) [NeZero n] :
    (modularPolynomial n).natDegree = (primitiveReps (n : ℤ)).card :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _ hk ↦ coeff_modularPolynomial_eq_zero_of_lt hk)
    (by rw [coeff_modularPolynomial_card]; exact one_ne_zero)

/-- `modularPolynomial n` is monic in `X`. -/
theorem monic_modularPolynomial (n : ℕ) [NeZero n] : (modularPolynomial n).Monic := by
  rw [Monic, leadingCoeff, natDegree_modularPolynomial, coeff_modularPolynomial_card]

/-- For every primitive integral matrix `A` of determinant `n`, `j(A • τ)` is a root of
`Φ_n(X, j(τ))`. -/
theorem isRoot_map_aeval_j_modularPolynomial {n : ℕ} [NeZero n] {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.1) (τ : ℍ) :
    ((modularPolynomial n).map (aeval (R := ℤ) (j τ))).IsRoot
      (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  rw [map_aeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial j_smul_SL2Z hA τ

/-- The classical modular identity `Φ_n(j(n τ), j(τ)) = 0`. -/
theorem isRoot_map_aeval_j_modularPolynomial_scaleGL_smul (n : ℕ) [NeZero n] (τ : ℍ) :
    ((modularPolynomial n).map (aeval (R := ℤ) (j τ))).IsRoot (j (scaleGL n • τ)) := by
  rw [map_aeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial_scaleGL_smul j_smul_SL2Z τ

end ModularPolynomial

/-! ### The diagonal specialization `Φ_n(X, X)` and its leading coefficient -/

section Diagonal

/-- **The diagonal modular polynomial** `Φ_n(X, X) ∈ ℤ[X]`, obtained by specializing both variables
of `modularPolynomial n` to `X`. -/
noncomputable def modularPolynomialDiag (n : ℕ) [NeZero n] : ℤ[X] :=
  (modularPolynomial n).eval X

/-- The defining equation of `modularPolynomialDiag`. -/
theorem modularPolynomialDiag_def (n : ℕ) [NeZero n] :
    modularPolynomialDiag n = (modularPolynomial n).eval X := by
  unfold modularPolynomialDiag; rfl

/-- Evaluating `modularPolynomialDiag n` at `x ∈ R` evaluates `Φ_n(x, x)`. -/
theorem aeval_modularPolynomialDiag (n : ℕ) [NeZero n] {R : Type*} [CommRing R] (x : R) :
    aeval x (modularPolynomialDiag n) =
      ((modularPolynomial n).map (aeval (R := ℤ) x)).eval x := by
  rw [modularPolynomialDiag_def, eval_eq_sum_range, map_sum, eval_map,
    eval₂_eq_sum_range' (aeval (R := ℤ) x)
      (Nat.lt_succ_self (modularPolynomial n).natDegree) x]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp

/-- Evaluating `modularPolynomialDiag n` at `j(τ)` gives
`(cyclicIsogenyPolynomial n j τ).eval (j τ)`. -/
@[simp]
theorem aeval_j_modularPolynomialDiag (n : ℕ) [NeZero n] (τ : ℍ) :
    aeval (j τ) (modularPolynomialDiag n) = (cyclicIsogenyPolynomial n j τ).eval (j τ) := by
  rw [aeval_modularPolynomialDiag, map_aeval_j_modularPolynomial]

private theorem leadingCoeff_laurentQExpansion_j :
    (UpperHalfPlane.laurentQExpansion 1 j).leadingCoeff = 1 := by
  simpa using Polynomial.leadingCoeff_laurentQExpansion_aeval_j (X : ℤ[X])

private theorem orderTop_rescale_le {R : Type*} [CommRing R] (u : Rˣ) (f : R⸨X⸩) :
    (TauCeti.LaurentSeries.rescale u f).orderTop ≤ f.orderTop := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf]
  refine HahnSeries.orderTop_le_of_coeff_ne_zero ?_
  rw [TauCeti.LaurentSeries.coeff_rescale, ne_eq, Units.mul_right_eq_zero]
  exact HahnSeries.coeff_order_eq_zero.not.mpr hf

private theorem orderTop_rescale {R : Type*} [CommRing R] (u : Rˣ) (f : R⸨X⸩) :
    (TauCeti.LaurentSeries.rescale u f).orderTop = f.orderTop := by
  refine le_antisymm (orderTop_rescale_le u f) ?_
  have hinv : TauCeti.LaurentSeries.rescale u⁻¹ (TauCeti.LaurentSeries.rescale u f) = f := by
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  simpa [hinv] using orderTop_rescale_le u⁻¹ (TauCeti.LaurentSeries.rescale u f)

private theorem leadingCoeff_rescale {R : Type*} [CommRing R] (u : Rˣ) (f : R⸨X⸩) :
    (TauCeti.LaurentSeries.rescale u f).leadingCoeff = ↑(u ^ f.order) * f.leadingCoeff := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have huf : TauCeti.LaurentSeries.rescale u f ≠ 0 := fun h0 ↦
    hf ((TauCeti.LaurentSeries.rescale u).injective (h0.trans (map_zero _).symm))
  have hord : (TauCeti.LaurentSeries.rescale u f).order = f.order :=
    WithTop.coe_injective (by
      rw [HahnSeries.order_eq_orderTop_of_ne_zero huf,
        HahnSeries.order_eq_orderTop_of_ne_zero hf, orderTop_rescale])
  rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord,
    TauCeti.LaurentSeries.coeff_rescale]

private theorem orderTop_and_norm_leadingCoeff_smul_j {n : ℕ} [NeZero n]
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    (UpperHalfPlane.laurentQExpansion n
        (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).orderTop =
      ((-(((A.1 0 0).natAbs ^ 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ∧
    ‖(UpperHalfPlane.laurentQExpansion n
        (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
  set a : ℕ := (A.1 0 0).natAbs
  set b : ℕ := (A.1 0 1).natAbs
  have ha_pos : 0 < a := Int.natAbs_pos.mpr hA.2.1.ne'
  set u : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n) ^ (a * b))
    (pow_ne_zero _ (Complex.exp_ne_zero _))
  have hu_norm : ‖(u : ℂ)‖ = 1 := by
    simp only [u, Units.val_mk0, norm_pow]
    have hEq : 2 * ↑Real.pi * Complex.I / (n : ℂ) = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hEq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hL₂ : UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ ((a ^ 2).toPNat (pow_pos ha_pos 2))
        (TauCeti.LaurentSeries.rescale u (UpperHalfPlane.laurentQExpansion 1 j)) :=
    UpperHalfPlane.laurentQExpansion_toGLReal_smul periodic_j meromorphicAt_cuspFunction_j hA
  have hj_ordTop : (UpperHalfPlane.laurentQExpansion 1 j).orderTop = ((-1 : ℤ) : WithTop ℤ) :=
    orderTop_laurentQExpansion_j
  refine ⟨?_, ?_⟩
  · rw [hL₂, LaurentSeries.orderTop_expand (R := ℂ), orderTop_rescale, hj_ordTop,
      ← WithTop.coe_nsmul]
    exact WithTop.coe_eq_coe.mpr (by simp [Nat.toPNat])
  · have hj_ord : (UpperHalfPlane.laurentQExpansion 1 j).order = -1 := by
      have hj_ne : UpperHalfPlane.laurentQExpansion 1 j ≠ 0 := by
        rw [← HahnSeries.orderTop_ne_top, hj_ordTop]; exact WithTop.coe_ne_top
      exact WithTop.coe_injective (by
        rw [HahnSeries.order_eq_orderTop_of_ne_zero hj_ne, hj_ordTop])
    rw [hL₂, LaurentSeries.leadingCoeff_expand (R := ℂ), leadingCoeff_rescale, hj_ord,
      leadingCoeff_laurentQExpansion_j, mul_one, _root_.zpow_neg_one, Units.val_inv_eq_inv_val,
      norm_inv, hu_norm, inv_one]

private theorem norm_leadingCoeff_factor_diag {n : ℕ} [NeZero n] (hn : ¬ IsSquare n)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ primitiveReps (n : ℤ)) :
    ‖(UpperHalfPlane.laurentQExpansion n j -
        UpperHalfPlane.laurentQExpansion n
          (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
  have hA_rep := (mem_primitiveReps.mp hA).1
  set a : ℕ := (A.1 0 0).natAbs
  have hprod : a * (A.1 1 1).natAbs = n := by
    simpa [Int.natAbs_mul, a] using
      congrArg Int.natAbs (apply_zero_zero_mul_apply_one_one hA_rep.1)
  have hne : a ^ 2 ≠ n := fun hsq ↦ hn ⟨a, by
    have : a * a = a * (A.1 1 1).natAbs := by linarith [sq a]
    rw [← hprod, ← this]⟩
  set L₁ := UpperHalfPlane.laurentQExpansion n j
  set L₂ := UpperHalfPlane.laurentQExpansion n (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))
  have hL₁ : L₁ =
      LaurentSeries.expand ℂ (n.toPNat (NeZero.pos n)) (UpperHalfPlane.laurentQExpansion 1 j) := by
    simpa [mul_one, Nat.toPNat, L₁] using
      UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1) periodic_j meromorphicAt_cuspFunction_j
        (n.toPNat (NeZero.pos n))
  have hj_ordTop : (UpperHalfPlane.laurentQExpansion 1 j).orderTop = ((-1 : ℤ) : WithTop ℤ) :=
    orderTop_laurentQExpansion_j
  have hord₁ : L₁.orderTop = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hL₁, LaurentSeries.orderTop_expand (R := ℂ), hj_ordTop, ← WithTop.coe_nsmul]
    exact WithTop.coe_eq_coe.mpr (by simp [Nat.toPNat])
  have hlc₁ : L₁.leadingCoeff = 1 := by
    rw [hL₁, LaurentSeries.leadingCoeff_expand (R := ℂ), leadingCoeff_laurentQExpansion_j]
  obtain ⟨hord₂, hlc₂⟩ := orderTop_and_norm_leadingCoeff_smul_j hA_rep
  change L₂.orderTop = ((-((a ^ 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) at hord₂
  rw [sub_eq_add_neg]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hord_lt : L₁.orderTop < (-L₂).orderTop := by
      rw [HahnSeries.orderTop_neg, hord₁, hord₂, WithTop.coe_lt_coe]; omega
    rw [HahnSeries.leadingCoeff_add_eq_left hord_lt, hlc₁, norm_one]
  · have hord_gt : (-L₂).orderTop < L₁.orderTop := by
      rw [HahnSeries.orderTop_neg, hord₁, hord₂, WithTop.coe_lt_coe]; omega
    rw [HahnSeries.leadingCoeff_add_eq_right hord_gt, HahnSeries.leadingCoeff_neg, norm_neg, hlc₂]

private theorem leadingCoeff_prod {ι : Type*} (s : Finset ι) (F : ι → ℂ⸨X⸩) :
    (∏ i ∈ s, F i).leadingCoeff = ∏ i ∈ s, (F i).leadingCoeff := by
  induction s using Finset.cons_induction with
  | empty => simp [HahnSeries.leadingCoeff_one]
  | cons a t hat ih => rw [Finset.prod_cons, Finset.prod_cons, HahnSeries.leadingCoeff_mul, ih]

/-- **Kronecker's leading-coefficient theorem for `Φ_n(X, X)`.** When `n` is not a square, the
leading coefficient of `modularPolynomialDiag n` is a unit in `ℤ` (that is, `±1`). -/
theorem isUnit_leadingCoeff_modularPolynomialDiag {n : ℕ} [NeZero n] (hn : ¬ IsSquare n) :
    IsUnit (modularPolynomialDiag n).leadingCoeff := by
  set P := modularPolynomialDiag n
  have hPper : Function.Periodic ((fun τ : ℍ ↦ aeval (j τ) P) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by simp [← modular_T_smul]
  have hEq_fun : (fun τ : ℍ ↦ aeval (j τ) P) =
      fun τ ↦ ∏ A ∈ primitiveReps (n : ℤ),
        (j τ - j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
    funext τ
    rw [aeval_j_modularPolynomialDiag, cyclicIsogenyPolynomial_def, eval_prod]
    exact Finset.prod_congr rfl fun A _ ↦ by simp
  have hj_mer_n : MeromorphicAt (cuspFunction n j) 0 := by
    simpa [mul_one, Nat.toPNat] using (UpperHalfPlane.meromorphicAt_cuspFunction_pnat_mul_iff
      (h := 1) periodic_j (n.toPNat (NeZero.pos n))).mpr meromorphicAt_cuspFunction_j
  have hmer_fac : ∀ A ∈ primitiveReps (n : ℤ),
      MeromorphicAt (cuspFunction n fun τ ↦ j τ - j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
    fun A hA ↦ UpperHalfPlane.meromorphicAt_cuspFunction_sub hj_mer_n
      (UpperHalfPlane.meromorphicAt_cuspFunction_toGLReal_smul periodic_j
        meromorphicAt_cuspFunction_j (mem_primitiveReps.mp hA).1)
  have hq_lhs : (UpperHalfPlane.laurentQExpansion n fun τ ↦ aeval (j τ) P).leadingCoeff =
      (P.leadingCoeff : ℂ) := by
    have hexp : UpperHalfPlane.laurentQExpansion n (fun τ ↦ aeval (j τ) P) =
        LaurentSeries.expand ℂ (n.toPNat (NeZero.pos n))
          (UpperHalfPlane.laurentQExpansion 1 fun τ ↦ aeval (j τ) P) := by
      simpa [mul_one, Nat.toPNat] using UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1) hPper
        (Polynomial.meromorphicAt_cuspFunction_aeval_j P) (n.toPNat (NeZero.pos n))
    rw [hexp, LaurentSeries.leadingCoeff_expand (R := ℂ),
      Polynomial.leadingCoeff_laurentQExpansion_aeval_j,
      Polynomial.leadingCoeff_map_of_injective (Int.cast_injective (α := ℂ))]
    simp
  have hq_rhs : ‖(UpperHalfPlane.laurentQExpansion n fun τ ↦ aeval (j τ) P).leadingCoeff‖ = 1 := by
    rw [hEq_fun, UpperHalfPlane.laurentQExpansion_prod (primitiveReps (n : ℤ)) hmer_fac,
      leadingCoeff_prod, norm_prod]
    refine Finset.prod_eq_one fun A hA ↦ ?_
    have hsub : (fun τ : ℍ ↦ j τ - j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
        j - fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ) := rfl
    rw [hsub, UpperHalfPlane.laurentQExpansion_sub hj_mer_n
      (UpperHalfPlane.meromorphicAt_cuspFunction_toGLReal_smul periodic_j
        meromorphicAt_cuspFunction_j (mem_primitiveReps.mp hA).1)]
    exact norm_leadingCoeff_factor_diag hn hA
  rw [hq_lhs, Complex.norm_intCast] at hq_rhs
  have habs : |P.leadingCoeff| = 1 := by exact_mod_cast hq_rhs
  rcases abs_cases P.leadingCoeff with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact Int.isUnit_iff.mpr (by omega)

/-- When `n` is not a square, `modularPolynomialDiag n` is nonzero. -/
theorem modularPolynomialDiag_ne_zero {n : ℕ} [NeZero n] (hn : ¬ IsSquare n) :
    modularPolynomialDiag n ≠ 0 :=
  leadingCoeff_ne_zero.mp (isUnit_leadingCoeff_modularPolynomialDiag hn).ne_zero

end Diagonal

/-! ### Algebraic integrality of `j(τ)` at imaginary quadratic points -/

section Integrality

private theorem disc_pos_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : 0 < a)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0) :
    0 < 4 * a * c - b ^ 2 := by
  set z : ℂ := 2 * (a : ℂ) * (τ : ℂ) + b
  have hz_sq : z ^ 2 + ((4 * a * c - b ^ 2 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination 4 * (a : ℂ) * hτ
  have hz_im : 0 < z.im := by
    have him : z.im = 2 * (a : ℝ) * τ.im := by simp [z]
    rw [him]
    exact mul_pos (mul_pos zero_lt_two (Int.cast_pos.mpr ha)) τ.im_pos
  have hz_re : z.re = 0 := by
    have him0 : (z ^ 2 + ((4 * a * c - b ^ 2 : ℤ) : ℂ)).im = 0 := by rw [hz_sq]; simp
    have hsq_im : (z ^ 2).im = 2 * z.re * z.im := by
      rw [sq, Complex.mul_im]; ring
    simp only [Complex.add_im, Complex.intCast_im, add_zero, hsq_im] at him0
    nlinarith
  have hre0 : (z ^ 2 + ((4 * a * c - b ^ 2 : ℤ) : ℂ)).re = 0 := by rw [hz_sq]; simp
  have hsq_re : (z ^ 2).re = -z.im ^ 2 := by
    rw [sq, Complex.mul_re, hz_re]; ring
  simp only [Complex.add_re, Complex.intCast_re, hsq_re] at hre0
  have hpos_real : (0 : ℝ) < ((4 * a * c - b ^ 2 : ℤ) : ℝ) := by nlinarith
  exact_mod_cast hpos_real

private theorem exists_primitive_pos_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0) :
    ∃ w : Fin 3 → ℤ, TauCeti.IsPrimitive w ∧ 0 < w 0 ∧
      (w 0 : ℂ) * (τ : ℂ) ^ 2 + w 1 * τ + w 2 = 0 := by
  obtain ⟨g, w, hg, hw, hvw⟩ := TauCeti.exists_eq_zsmul_isPrimitive (v := ![a, b, c])
    fun hv ↦ ha (congrFun hv 0)
  have ha_eq : a = g * w 0 := by simpa using congrFun hvw 0
  have hb_eq : b = g * w 1 := by simpa using congrFun hvw 1
  have hc_eq : c = g * w 2 := by simpa using congrFun hvw 2
  have hw0_ne : w 0 ≠ 0 := fun h0 ↦ ha (by rw [ha_eq, h0, mul_zero])
  have hw_quad : (w 0 : ℂ) * (τ : ℂ) ^ 2 + w 1 * τ + w 2 = 0 := by
    have hgC : (g : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hg.ne'
    refine mul_left_cancel₀ hgC ?_
    calc (g : ℂ) * ((w 0 : ℂ) * (τ : ℂ) ^ 2 + w 1 * τ + w 2)
        = (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c := by
          rw [ha_eq, hb_eq, hc_eq]; push_cast; ring
      _ = 0 := hτ
      _ = (g : ℂ) * 0 := (mul_zero _).symm
  rcases lt_or_gt_of_ne hw0_ne with hlt | hgt
  · refine ⟨-w, hw.neg, by simp; omega, ?_⟩
    simp only [Pi.neg_apply, Int.cast_neg]
    linear_combination -hw_quad
  · exact ⟨w, hw, hgt, hw_quad⟩

private theorem quad_det_pos_and_not_isSquare {a' b' c' : ℤ}
    (hD : 1 ≤ 4 * a' * c' - b' ^ 2) :
    let t : ℤ := |b'| + (4 * a' * c' - b' ^ 2)
    let m : ℤ := t ^ 2 - b' * t + a' * c'
    0 < m ∧ ¬ IsSquare m.natAbs := by
  intro t m
  set D : ℤ := 4 * a' * c' - b' ^ 2
  have h4m : 4 * m = (2 * t - b') ^ 2 + D := by simp only [m, D]; ring
  have hu_ge : 2 * D ≤ 2 * t - b' := by
    have hb1 : b' ≤ |b'| := le_abs_self b'
    have hb2 : 0 ≤ |b'| := abs_nonneg b'
    dsimp only [t, D] at *
    omega
  have hm_pos : 0 < m := by nlinarith
  refine ⟨hm_pos, ?_⟩
  rintro ⟨s, hs⟩
  have hm_sq : m = (s : ℤ) * s := by
    rw [← Int.natAbs_of_nonneg hm_pos.le, hs]; push_cast; rfl
  have hlt1 : 2 * t - b' < 2 * (s : ℤ) := by nlinarith
  have : 2 * t - b' + 1 ≤ 2 * (s : ℤ) := by omega
  nlinarith

private theorem exists_fixedDetMatrix_smul_eq {τ : ℍ} {w : Fin 3 → ℤ}
    (hw : TauCeti.IsPrimitive w) (ha' : 0 < w 0)
    (hquad : (w 0 : ℂ) * (τ : ℂ) ^ 2 + w 1 * τ + w 2 = 0) :
    ∃ (n : ℕ) (_ : NeZero n), ¬ IsSquare n ∧
      ∃ M : FixedDetMatrix (Fin 2) ℤ n,
        TauCeti.IsPrimitive M.1 ∧ toGLReal (NeZero.ne (n : ℤ)) M • τ = τ := by
  set a' := w 0; set b' := w 1; set c' := w 2
  have hD : 1 ≤ 4 * a' * c' - b' ^ 2 := disc_pos_of_quadratic ha' hquad
  obtain ⟨hm_pos, hn_not_sq⟩ := quad_det_pos_and_not_isSquare hD
  set t : ℤ := |b'| + (4 * a' * c' - b' ^ 2)
  set m : ℤ := t ^ 2 - b' * t + a' * c'
  set n : ℕ := m.natAbs
  have hn_cast : (n : ℤ) = m := Int.natAbs_of_nonneg hm_pos.le
  have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp (Int.natAbs_pos.mpr hm_pos.ne')⟩
  let M : FixedDetMatrix (Fin 2) ℤ n :=
    ⟨!![t - b', -c'; a', t], by
      rw [det_fin_two, hn_cast]; dsimp only [m]
      simp only [of_apply, cons_val_zero, cons_val_one, cons_val_fin_one]; ring⟩
  have hM_prim : TauCeti.IsPrimitive M.1 := by
    let g : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] (Fin 3 → ℤ) :=
      { toFun B := ![B 1 0, B 1 1 - B 0 0, -B 0 1]
        map_add' _ _ := by ext i; fin_cases i <;> simp <;> ring
        map_smul' _ _ := by ext i; fin_cases i <;> simp [mul_sub] }
    have hgM : g M.1 = w := by ext i; fin_cases i <;> simp [g, M, a', b', c']
    exact (hgM.symm ▸ hw).of_map
  refine ⟨n, inferInstance, hn_not_sq, M, hM_prim, ?_⟩
  have hdet : 0 < ((toGLReal (NeZero.ne (n : ℤ)) M).det : ℝ) := by
    rw [det_toGLReal]; exact_mod_cast NeZero.pos n
  have hden : (a' : ℂ) * (τ : ℂ) + t ≠ 0 := fun h0 ↦ by
    have him := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im] at him
    exact (mul_pos (Int.cast_pos.mpr ha') τ.im_pos).ne' him
  ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, toGLReal_apply]
  simp only [M, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one]
  push_cast
  rw [div_eq_iff hden]
  linear_combination -hquad

/-- **Algebraic integrality of CM `j`-values.** If `τ ∈ ℍ` satisfies a nontrivial quadratic
equation `a τ^2 + b τ + c = 0` with integer coefficients (`a ≠ 0`), then `j(τ)` is integral over
`ℤ`. -/
theorem isIntegral_j_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0) :
    IsIntegral ℤ (j τ) := by
  obtain ⟨w, hw, ha', hquad⟩ := exists_primitive_pos_quadratic ha hτ
  obtain ⟨n, _, hn_not_sq, M, hM_prim, hfix⟩ := exists_fixedDetMatrix_smul_eq hw ha' hquad
  have hroot : aeval (j τ) (modularPolynomialDiag n) = 0 := by
    rw [aeval_j_modularPolynomialDiag]
    have hr := isRoot_cyclicIsogenyPolynomial j_smul_SL2Z hM_prim τ
    rwa [hfix, IsRoot] at hr
  rcases Int.isUnit_iff.mp (isUnit_leadingCoeff_modularPolynomialDiag hn_not_sq) with h1 | h1
  · simpa [h1] using isIntegral_leadingCoeff_smul (p := modularPolynomialDiag n) (x := j τ) hroot
  · simpa [h1] using
      (isIntegral_leadingCoeff_smul (p := modularPolynomialDiag n) (x := j τ) hroot).neg

end Integrality

end TauCeti.ModularForm
