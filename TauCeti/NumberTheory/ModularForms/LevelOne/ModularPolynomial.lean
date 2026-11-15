/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.Algebra.Polynomial.Bivariate
public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import TauCeti.NumberTheory.ModularForms.QExpansion.Order
import TauCeti.RingTheory.HahnSeries.Map
import TauCeti.RingTheory.HahnSeries.Twist

/-!
# The classical modular polynomial and integrality of `j` at imaginary quadratic points

For a positive integer `n`, the polynomial `cyclicIsogenyPolynomial n j τ` of
`TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial` is the monic polynomial

  `∏_{(a b; 0 d)} (Y - j((a τ + b) / d))`

over the primitive upper-triangular integral matrices `(a b; 0 d)` of determinant `n` with
`0 ≤ b < d` (`FixedDetMatrices.primitiveReps n`). Its coefficients are holomorphic and
`SL(2, ℤ)`-invariant on the upper half-plane. This file proves that each coefficient is a
polynomial in `j(τ)` with **integer** coefficients, assembling the classical **modular polynomial**
`Φ_n(X, Y) : ℤ[X][Y]` (`TauCeti.ModularForm.modularPolynomial`), and deduces that the value `j(τ)`
at every imaginary quadratic point `τ ∈ ℍ` is an algebraic integer.

The integrality of the coefficients of `Φ_n` is proved from the `q`-expansions of the factors at
width `n`. Writing `q_n = e^{2π i τ / n}` and `ζ_n = e^{2π i / n}`, the local parameter at
`(a τ + b) / d` (with `a d = n`) is `ζ_n^{a b} q_n^{a²}`, so the width-`n` Laurent `q`-expansion
of `j((a τ + b) / d)` is obtained from the integral Laurent `q`-expansion of `j` by twisting by
`ζ_n^{a b}` and substituting `X ↦ X^{a²}`. Its coefficients lie in the ring of integers of the
cyclotomic field `ℚ(ζ_n)`. Every automorphism `σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends `ζ_n ↦ ζ_n^k` for a unit
`k` modulo `n`, and `(a, b, d) ↦ (a, k b mod d, d)` permutes `FixedDetMatrices.primitiveReps n`, so
`σ` fixes all Laurent `q`-coefficients of the symmetric functions of the `j((a τ + b) / d)`. Being
both rational and integral over `ℤ`, those coefficients are integers, and the level-one weakly
holomorphic theorem (`TauCeti.ModularForm.exists_aeval_j_eq`) expresses each coefficient as a
unique polynomial in `j` over `ℤ`.

Along the diagonal `Y = X`, `diagModularPolynomial n = Φ_n(X, X) ∈ ℤ[X]` evaluates at `j(τ)` to
`∏ (j(τ) - j(A τ))`. When `n` is not a square, `a d = n` prevents `a² = n`, so in every factor one
of `j(τ)` (order `-n` in `q_n`, leading coefficient `1`) and `-j(A τ)` (order `-a²` in `q_n`,
leading coefficient `-ζ_n^{-a b}`) strictly dominates the other at `i∞`. The product therefore has
leading coefficient of absolute value `1`, forcing `Φ_n(X, X)` to be nonzero with leading
coefficient `±1`, so all of its complex roots are algebraic integers. Every imaginary quadratic
point `τ ∈ ℍ` is fixed by an explicit primitive integral matrix of non-square positive determinant,
making `j(τ)` a root of `Φ_n(X, X)` and hence integral over `ℤ`.

## Main definitions

* `TauCeti.ModularForm.modularPolynomial n`: the classical modular polynomial `Φ_n ∈ ℤ[X][Y]`,
  characterized by `(modularPolynomial n).map (aeval (j τ)) = cyclicIsogenyPolynomial n j τ`.
* `TauCeti.ModularForm.diagModularPolynomial n`: the diagonal specialization `Φ_n(X, X) ∈ ℤ[X]`.

## Main results

* `TauCeti.ModularForm.modularPolynomial_one`: `Φ_1(X, Y) = Y - X` (and `diagModularPolynomial_one`:
  `Φ_1(X, X) = 0`).
* `TauCeti.ModularForm.aevalAeval_j_modularPolynomial`: evaluating `Φ_n(X, Y)` at `(j(τ), w)` gives
  `(cyclicIsogenyPolynomial n j τ).eval w`.
* `TauCeti.ModularForm.aevalAeval_j_modularPolynomial_eq_zero_iff`: `Φ_n(j(τ), j(τ')) = 0` holds
  exactly when `τ' = A • τ` for some primitive integral matrix `A` of determinant `n`.
* `TauCeti.ModularForm.isUnit_leadingCoeff_diagModularPolynomial`: when `n` is not a square, the
  leading coefficient of `Φ_n(X, X)` is a unit in `ℤ` (`±1`), so its complex roots are integral
  over `ℤ` (`isIntegral_of_aeval_diagModularPolynomial_eq_zero`).
* `TauCeti.ModularForm.isIntegral_j_of_quadratic`: if `τ ∈ ℍ` satisfies `a τ² + b τ + c = 0` with
  `a, b, c ∈ ℤ` and `a ≠ 0`, then `j(τ)` is an algebraic integer (`IsIntegral ℤ (j τ)`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C (the modular equation and
  its integer coefficients) and Theorem 11.1 (integrality of singular moduli).
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §§2–3 (the modular equation and `Φ_m(X, X)` for non-square `m`).
-/

public noncomputable section

open Complex Filter Function Matrix Polynomial Topology
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups Polynomial.Bivariate Real

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

open FixedDetMatrices

/-! ### Action and width-`n` `q`-expansion of upper-triangular representatives -/

/-- Natural-number absolute value of the `(i, j)`-entry of a `2 × 2` integral matrix of fixed
determinant. Keeping `FixedDetMatrix` un-projected avoids semireducible coercion mismatches under
`rw`. -/
private def repEntry {m : ℤ} (A : FixedDetMatrix (Fin 2) ℤ m) (i j : Fin 2) : ℕ :=
  (A.1 i j).natAbs

section RepsExpansion

variable {n : ℕ} [NeZero n]

/-- For `n > 0`, a representative `A ∈ reps n` has positive diagonal entries `a, d > 0` with
`a * d = n`, nonnegative upper-right entry `b < d`, and `A = !![a, b; 0, d]`. -/
private theorem mem_reps_nat_entries {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    0 < repEntry A 0 0 ∧ 0 < repEntry A 1 1 ∧ repEntry A 0 0 * repEntry A 1 1 = n ∧
      repEntry A 0 1 < repEntry A 1 1 ∧
      A.1 = !![(repEntry A 0 0 : ℤ), (repEntry A 0 1 : ℤ); 0, (repEntry A 1 1 : ℤ)] := by
  obtain ⟨h₁₀, h₀₀, h₀₁, h₁₁lt⟩ := hA
  have hmul : A.1 0 0 * A.1 1 1 = n := apply_zero_zero_mul_apply_one_one h₁₀
  have hn_pos : (0 : ℤ) < n := Int.natCast_pos.2 (NeZero.pos n)
  have h₁₁ : 0 < A.1 1 1 := pos_of_mul_pos_right (hmul.symm ▸ hn_pos) h₀₀.le
  have ha : (repEntry A 0 0 : ℤ) = A.1 0 0 := Int.natAbs_of_nonneg h₀₀.le
  have hb : (repEntry A 0 1 : ℤ) = A.1 0 1 := Int.natAbs_of_nonneg h₀₁
  have hd : (repEntry A 1 1 : ℤ) = A.1 1 1 := Int.natAbs_of_nonneg h₁₁.le
  refine ⟨Int.natAbs_pos.2 h₀₀.ne', Int.natAbs_pos.2 h₁₁.ne', ?_, ?_, ?_⟩
  · exact Int.natCast_inj.1 (by rw [Nat.cast_mul, ha, hd, hmul])
  · rw [abs_of_nonneg h₀₁, abs_of_pos h₁₁] at h₁₁lt
    exact Int.ofNat_lt.1 (by rwa [hb, hd])
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hd, h₁₀]

/-- The Möbius action of `A ∈ reps n` sends `τ` to `(a τ + b) / d` in `ℂ`. -/
private theorem coe_toGLReal_smul_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (τ : ℍ) :
    ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) =
      ((repEntry A 0 0 : ℂ) * τ + repEntry A 0 1) / repEntry A 1 1 := by
  obtain ⟨-, -, -, -, hmat⟩ := mem_reps_nat_entries hA
  have hdet : 0 < (toGLReal (NeZero.ne (n : ℤ)) A).det.val := by
    rw [det_toGLReal]
    exact_mod_cast NeZero.pos n
  rw [coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom]
  have h00 : (toGLReal (NeZero.ne (n : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = repEntry A 0 0 := by
    rw [toGLReal_apply, hmat]; simp
  have h01 : (toGLReal (NeZero.ne (n : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = repEntry A 0 1 := by
    rw [toGLReal_apply, hmat]; simp
  have h10 : (toGLReal (NeZero.ne (n : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
    rw [toGLReal_apply, hmat]; simp
  have h11 : (toGLReal (NeZero.ne (n : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = repEntry A 1 1 := by
    rw [toGLReal_apply, hmat]; simp
  rw [h00, h01, h10, h11]
  simp

/-- At `(a τ + b) / d` with `a d = n`, the width-one `q`-parameter factors as
`ζ_n^{a b} q_n^{a²}`. -/
private theorem qParam_one_toGLReal_smul_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (τ : ℍ) :
    𝕢 1 ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) =
      cexp (2 * π * I / n) ^ (repEntry A 0 0 * repEntry A 0 1) *
        𝕢 n τ ^ (repEntry A 0 0 ^ 2) := by
  obtain ⟨-, hd, had, -, -⟩ := mem_reps_nat_entries hA
  have hd0 : (repEntry A 1 1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hadC : (repEntry A 0 0 : ℂ) * repEntry A 1 1 = n := by exact_mod_cast had
  rw [coe_toGLReal_smul_of_mem_reps hA]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, Complex.ofReal_natCast, div_one,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  rw [← hadC]
  ring

/-- For `A ∈ reps n`, `τ ↦ toGLReal _ A • τ` sends `atImInfty` to `atImInfty`. -/
private theorem tendsto_toGLReal_smul_atImInfty {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    Tendsto (fun τ : ℍ ↦ toGLReal (NeZero.ne (n : ℤ)) A • τ) atImInfty atImInfty := by
  obtain ⟨ha, hd, -, -, -⟩ := mem_reps_nat_entries hA
  rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
  have him : (UpperHalfPlane.im ∘ fun τ : ℍ ↦ toGLReal (NeZero.ne (n : ℤ)) A • τ) =
      fun τ : ℍ ↦ (repEntry A 0 0 / repEntry A 1 1 : ℝ) * τ.im := by
    ext τ
    have h := congrArg Complex.im (coe_toGLReal_smul_of_mem_reps hA τ)
    simp only [Function.comp_apply, coe_im, ← Complex.ofReal_natCast, Complex.div_ofReal_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      at h ⊢
    rw [h, ← div_mul_eq_mul_div]
  rw [him]
  exact Tendsto.const_mul_atTop (by positivity) Filter.tendsto_comap

/-- Adding `n` on `ℍ` shifts `toGLReal _ A • τ` by the integer `a²`. -/
private theorem toGLReal_smul_vadd_nat {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (τ : ℍ) :
    toGLReal (NeZero.ne (n : ℤ)) A • ((n : ℝ) +ᵥ τ) =
      ((repEntry A 0 0 ^ 2 : ℕ) : ℝ) +ᵥ (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
  obtain ⟨-, hd, had, -, -⟩ := mem_reps_nat_entries hA
  have hd0 : (repEntry A 1 1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hadC : (repEntry A 0 0 : ℂ) * repEntry A 1 1 = n := by exact_mod_cast had
  apply UpperHalfPlane.ext
  rw [coe_vadd, coe_toGLReal_smul_of_mem_reps hA, coe_toGLReal_smul_of_mem_reps hA, coe_vadd]
  push_cast
  field_simp
  rw [← hadC]
  ring

/-- Twisting `j (A • τ)` by `q_n^{a²}` gives a function analytic in `q_n` at `0`. -/
private theorem analyticAt_cuspFunction_qParam_pow_mul_j_toGLReal_smul
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    AnalyticAt ℂ (cuspFunction n fun τ : ℍ ↦
      𝕢 n τ ^ (repEntry A 0 0 ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 := by
  let ζ := cexp (2 * π * I / n)
  let a := repEntry A 0 0
  let b := repEntry A 0 1
  have hζ : ζ ^ (a * b) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hrew : (fun τ : ℍ ↦ 𝕢 n τ ^ (a ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      fun τ : ℍ ↦ (ζ ^ (a * b))⁻¹ *
        (𝕢 1 ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) *
          j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
    ext τ
    rw [qParam_one_toGLReal_smul_of_mem_reps hA, mul_assoc, inv_mul_cancel_left₀ hζ]
  rw [hrew]
  refine UpperHalfPlane.analyticAt_cuspFunction_zero (Nat.cast_pos.2 (NeZero.pos n)) ?_ ?_ ?_
  · refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
    rw [toGLReal_smul_vadd_nat hA]
    set w : ℍ := toGLReal (NeZero.ne (n : ℤ)) A • τ
    have hper := periodic_qParam_mul_j_comp_ofComplex.nat_mul (a ^ 2) (w : ℂ)
    have h1 : ofComplex ((w : ℂ) + (a ^ 2 : ℕ) * (1 : ℂ)) = (((a ^ 2 : ℕ) : ℝ) +ᵥ w) := by
      rw [mul_one, add_comm, ← Complex.ofReal_natCast, ← coe_vadd, ofComplex_apply]
    rw [Function.comp_apply, Function.comp_apply, h1, ofComplex_apply] at hper
    exact congrArg ((ζ ^ (a * b))⁻¹ * ·) hper
  · exact mdifferentiable_const.mul (mdifferentiable_qParam_mul_j.comp
      (mdifferentiable_toGLReal_smul (Int.natCast_pos.2 (NeZero.pos n)) A))
  · exact ((tendsto_qParam_mul_j_atImInfty.comp
      (tendsto_toGLReal_smul_atImInfty hA)).const_mul _).isBigO_one ℝ

/-- If `𝕢 h ^ k * f` has an analytic cusp function at `0` for `h > 0`, then `f` has a meromorphic
cusp function at `0`. -/
private theorem meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul {h : ℝ} (hh : 0 < h)
    {k : ℕ} {f : ℍ → ℂ} (hk : AnalyticAt ℂ (cuspFunction h fun τ ↦ 𝕢 h τ ^ k * f τ) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  refine ((analyticAt_id.pow k).meromorphicAt.inv.mul hk.meromorphicAt).congr ?_
  filter_upwards [UpperHalfPlane.cuspFunction_qParam_pow_mul_eventuallyEq hh k f,
    self_mem_nhdsWithin] with q h₁ hq
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, id_eq, h₁,
    inv_mul_cancel_left₀ (pow_ne_zero k hq)]

/-- For `A ∈ reps n`, `τ ↦ j (A • τ)` has a meromorphic width-`n` cusp function at `0`. -/
private theorem meromorphicAt_cuspFunction_j_toGLReal_smul {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    MeromorphicAt (cuspFunction n fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
  meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul (Nat.cast_pos.2 (NeZero.pos n))
    (analyticAt_cuspFunction_qParam_pow_mul_j_toGLReal_smul hA)

/-- The `q`-expansion coefficients of `q_n^{a²} j(A • τ)` at width `n`. -/
private theorem qExpansion_qParam_pow_mul_j_toGLReal_smul_coeff {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (k : ℕ) :
    (qExpansion n (fun τ : ℍ ↦
      𝕢 n τ ^ (repEntry A 0 0 ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).coeff k =
      if repEntry A 0 0 ^ 2 ∣ k then
        (cexp (2 * π * I / n) ^ (repEntry A 0 0 * repEntry A 0 1)) ^
            ((k / repEntry A 0 0 ^ 2 : ℕ) - 1 : ℤ) *
          (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff (k / repEntry A 0 0 ^ 2)
      else 0 := by
  obtain ⟨ha, -, -, -, -⟩ := mem_reps_nat_entries hA
  let a := repEntry A 0 0
  let b := repEntry A 0 1
  let ζ := cexp (2 * π * I / n)
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have hζ : ζ ^ (a * b) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  let c : ℕ → ℂ := fun r ↦ if a ^ 2 ∣ r then
    (ζ ^ (a * b)) ^ ((r / a ^ 2 : ℕ) - 1 : ℤ) *
      (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff (r / a ^ 2) else 0
  refine (UpperHalfPlane.qExpansion_coeff_unique (c := c) (Nat.cast_pos.2 (NeZero.pos n))
    (analyticAt_cuspFunction_qParam_pow_mul_j_toGLReal_smul hA) (fun τ ↦ ?_) k).symm
  have hsum := (hasSum_qExpansion_qParam_mul_j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).mul_left
    (ζ ^ (a * b))⁻¹
  have hlim : (ζ ^ (a * b))⁻¹ *
      (𝕢 1 ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) *
        j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      𝕢 n τ ^ (a ^ 2) * j (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
    rw [qParam_one_toGLReal_smul_of_mem_reps hA, mul_assoc, inv_mul_cancel_left₀ hζ]
  rw [hlim] at hsum
  have hinj : Injective fun m : ℕ ↦ a ^ 2 * m := fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left ha2 h
  refine (hinj.hasSum_iff fun r hr ↦ ?_).1 (hsum.congr_fun fun m ↦ ?_)
  · have hnd : ¬ a ^ 2 ∣ r := fun ⟨m, hm⟩ ↦ hr ⟨m, hm.symm⟩
    simp [c, hnd]
  · dsimp only [c, Function.comp_apply, smul_eq_mul]
    rw [ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ ha2, zpow_sub₀ hζ, zpow_one,
      zpow_natCast, div_eq_mul_inv, qParam_one_toGLReal_smul_of_mem_reps hA, mul_pow,
      ← pow_mul (𝕢 n τ)]
    dsimp only [ζ, a, b]
    ring

private theorem repEntry_zero_zero_pos {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    0 < repEntry A 0 0 :=
  (mem_reps_nat_entries hA).1

/-- **Width-`n` Laurent `q`-expansion of `j(A • τ)`.** For `A = !![a, b; 0, d] ∈ reps n`, the
width-`n` Laurent `q`-expansion of `j(A • τ)` is the width-one expansion of `j` twisted by
`ζ_n^{a b}` and expanded by `X ↦ X^{a²}`. -/
private theorem laurentQExpansion_j_toGLReal_smul {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    UpperHalfPlane.laurentQExpansion n (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ (⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hA) 2⟩ : ℕ+)
        (HahnSeries.twistEquiv
          (zpowersHom ℂˣ (Units.mk0
            (cexp (2 * π * I / n) ^ (repEntry A 0 0 * repEntry A 0 1))
            (pow_ne_zero _ (Complex.exp_ne_zero _))))
          (UpperHalfPlane.laurentQExpansion 1 j)) := by
  have ha := repEntry_zero_zero_pos hA
  let a := repEntry A 0 0
  set d : ℕ+ := ⟨a ^ 2, pow_pos ha 2⟩
  rw [UpperHalfPlane.laurentQExpansion_eq_of_analyticAt_qParam_pow_mul
    (Nat.cast_pos.2 (NeZero.pos n)) (analyticAt_cuspFunction_qParam_pow_mul_j_toGLReal_smul hA)]
  ext k
  rw [HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  by_cases hdvd : (d : ℤ) ∣ k
  · obtain ⟨r, rfl⟩ := hdvd
    rw [LaurentSeries.coeff_expand_mul, HahnSeries.coeff_twistEquiv]
    rcases lt_or_ge r (-1) with hr | hr
    · have hlt : (d : ℤ) * r - -((a ^ 2 : ℕ) : ℤ) < 0 := by
        have hd_eq : (d : ℤ) = ((a ^ 2 : ℕ) : ℤ) := rfl
        nlinarith [d.pos]
      have h0 : (UpperHalfPlane.laurentQExpansion 1 j).coeff r = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by simpa using WithTop.coe_lt_coe.2 hr)
      rw [ite_eq_left hlt, h0, mul_zero]
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = (m : ℤ) - 1 := ⟨(r + 1).toNat, by omega⟩
      have hdiff : (d : ℤ) * ((m : ℤ) - 1) - -((a ^ 2 : ℕ) : ℤ) = (a ^ 2 * m : ℕ) := by
        have hd_eq : (d : ℤ) = ((a ^ 2 : ℕ) : ℤ) := rfl
        rw [hd_eq]; push_cast; ring
      rw [hdiff, ite_eq_right (not_lt.2 (Nat.cast_nonneg _)), Int.natAbs_natCast,
        qExpansion_qParam_pow_mul_j_toGLReal_smul_coeff hA, ite_eq_left (dvd_mul_right _ _),
        Nat.mul_div_cancel_left _ (pow_pos ha 2), laurentQExpansion_j_coeff_natCast_sub_one]
      simp [zpowersHom_apply, Units.val_zpow_eq_zpow_val]
  · rw [LaurentSeries.coeff_expand_of_not_dvd d _ hdvd]
    split_ifs with hlt
    · rfl
    · rw [qExpansion_qParam_pow_mul_j_toGLReal_smul_coeff hA, ite_eq_right]
      rintro ⟨m, hm⟩
      refine hdvd ⟨(m : ℤ) - 1, ?_⟩
      have habs : ((k - -((a ^ 2 : ℕ) : ℤ)).natAbs : ℤ) = k + (a ^ 2 : ℕ) := by
        rw [Int.natAbs_of_nonneg (not_lt.1 hlt), sub_neg_eq_add]
      have hm' : ((k - -((a ^ 2 : ℕ) : ℤ)).natAbs : ℤ) = ((a ^ 2 : ℕ) : ℤ) * (m : ℤ) := by
        simpa [a] using congrArg (Nat.cast : ℕ → ℤ) hm
      have hd_eq : (d : ℤ) = ((a ^ 2 : ℕ) : ℤ) := rfl
      rw [hd_eq]
      linarith

end RepsExpansion

/-! ### Meromorphy at `i∞` and width-`n` expansion of `cyclicIsogenyPolynomial n j` -/

section CyclicExpansion

variable {n : ℕ} [NeZero n]

/-- For every `A ∈ reps n`, `𝕢 1 τ ^ n * j (A • τ)` is bounded at `i∞`, because `𝕢 1 = 𝕢 n ^ n`
and `a² ≤ n²`. -/
private theorem isBoundedAtImInfty_qParam_pow_mul_j_toGLReal_smul {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
  obtain ⟨-, hd, had, -, -⟩ := mem_reps_nat_entries hA
  let a := repEntry A 0 0
  let b := repEntry A 0 1
  let ζ := cexp (2 * π * I / n)
  have han : a ≤ n := had ▸ Nat.le_mul_of_pos_right a hd
  have ha2 : a ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left han 2
  have hζ : ζ ^ (a * b) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hq1 (τ : ℍ) : 𝕢 1 (τ : ℂ) ^ n = 𝕢 n τ ^ (n ^ 2 - a ^ 2) * 𝕢 n τ ^ (a ^ 2) := by
    have hbase : 𝕢 (n * 1 : ℝ) (τ : ℂ) ^ n = 𝕢 1 (τ : ℂ) :=
      TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne n) (τ : ℂ)
    rw [mul_one] at hbase
    rw [← hbase, ← pow_mul, ← sq, ← pow_add, Nat.sub_add_cancel ha2]
  have hrew : (fun τ : ℍ ↦ 𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      fun τ : ℍ ↦ 𝕢 n τ ^ (n ^ 2 - a ^ 2) * ((ζ ^ (a * b))⁻¹ *
        (𝕢 1 ((toGLReal (NeZero.ne (n : ℤ)) A • τ : ℍ) : ℂ) *
          j (toGLReal (NeZero.ne (n : ℤ)) A • τ))) := by
    ext τ
    rw [hq1, qParam_one_toGLReal_smul_of_mem_reps hA, mul_assoc (ζ ^ (a * b)),
      inv_mul_cancel_left₀ hζ, mul_assoc]
  rw [hrew]
  have h1 : Tendsto (fun τ : ℍ ↦ 𝕢 n τ ^ (n ^ 2 - a ^ 2)) atImInfty (𝓝 (0 ^ (n ^ 2 - a ^ 2))) :=
    (UpperHalfPlane.qParam_tendsto_atImInfty (Nat.cast_pos.2 (NeZero.pos n))).pow _
  have h2 := (tendsto_qParam_mul_j_atImInfty.comp
    (tendsto_toGLReal_smul_atImInfty hA)).const_mul (ζ ^ (a * b))⁻¹
  exact (h1.mul h2).isBigO_one ℝ

/-- Boundedness at `i∞` of the coefficients of `∏ A ∈ s, (q^n Y - q^n j(A • τ))`. -/
private theorem isBoundedAtImInfty_qParam_pow_mul_coeff_prod
    (s : Finset (FixedDetMatrix (Fin 2) ℤ n)) (hs : ∀ A ∈ s, A ∈ reps (n : ℤ)) (k : ℕ) :
    IsBoundedAtImInfty fun τ : ℍ ↦
      (∏ A ∈ s, (C (𝕢 1 τ ^ n) * X - C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).coeff
        k := by
  classical
  let B := UpperHalfPlane.boundedAtImInftySubalgebra ℂ
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty]
    exact B.algebraMap_mem ((1 : ℂ[X]).coeff k)
  | @insert A s hAs ih =>
    have hA : A ∈ reps (n : ℤ) := hs A (Finset.mem_insert_self A s)
    have hs' : ∀ D ∈ s, D ∈ reps (n : ℤ) := fun D hD ↦ hs D (Finset.mem_insert_of_mem hD)
    have hq : (fun τ : ℍ ↦ 𝕢 1 τ ^ n) ∈ B :=
      ((UpperHalfPlane.qParam_tendsto_atImInfty one_pos).pow n).isBigO_one ℝ
    have hjA : (fun τ : ℍ ↦ 𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) ∈ B :=
      isBoundedAtImInfty_qParam_pow_mul_j_toGLReal_smul hA
    cases k with
    | zero =>
      have h0 : (fun τ : ℍ ↦ (∏ D ∈ insert A s, (C (𝕢 1 τ ^ n) * X -
          C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) D • τ)))).coeff 0) =
          -(fun τ : ℍ ↦ 𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) *
            fun τ : ℍ ↦ (∏ D ∈ s, (C (𝕢 1 τ ^ n) * X -
              C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) D • τ)))).coeff 0 := by
        ext τ
        simp only [Finset.prod_insert hAs, mul_coeff_zero, coeff_sub, coeff_X_zero,
          coeff_C_zero, mul_zero, zero_sub, Pi.mul_apply, Pi.neg_apply]
      rw [h0]
      exact B.mul_mem (B.neg_mem hjA) (ih hs' 0)
    | succ k =>
      have hk : (fun τ : ℍ ↦ (∏ D ∈ insert A s, (C (𝕢 1 τ ^ n) * X -
          C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) D • τ)))).coeff (k + 1)) =
          (fun τ : ℍ ↦ 𝕢 1 τ ^ n) * (fun τ : ℍ ↦ (∏ D ∈ s, (C (𝕢 1 τ ^ n) * X -
              C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) D • τ)))).coeff k) -
            (fun τ : ℍ ↦ 𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) *
              fun τ : ℍ ↦ (∏ D ∈ s, (C (𝕢 1 τ ^ n) * X -
                C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) D • τ)))).coeff (k + 1) := by
        ext τ
        rw [Finset.prod_insert hAs, sub_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul,
          coeff_C_mul]
        rfl
      rw [hk]
      exact B.sub_mem (B.mul_mem hq (ih hs' k)) (B.mul_mem hjA (ih hs' (k + 1)))

/-- Scaling every factor `X - C (f i)` by `c` multiplies the `k`-th coefficient of the product over
`s` by `c ^ s.card`. -/
private theorem pow_card_mul_coeff_prod_X_sub_C {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (c : R) (f : ι → R) (k : ℕ) :
    c ^ s.card * (∏ i ∈ s, (X - C (f i))).coeff k =
      (∏ i ∈ s, (C c * X - C (c * f i))).coeff k := by
  have h : C (c ^ s.card) * ∏ i ∈ s, (X - C (f i)) = ∏ i ∈ s, (C c * X - C (c * f i)) := by
    rw [map_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [mul_sub, ← map_mul]
  rw [← coeff_C_mul]
  exact congrArg (fun p ↦ p.coeff k) h

/-- Every coefficient of `cyclicIsogenyPolynomial n j` has a meromorphic width-one cusp function at
`q = 0`. -/
private theorem meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j (k : ℕ) :
    MeromorphicAt (cuspFunction 1 fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) 0 := by
  set M := (primitiveReps (n : ℤ)).card
  refine meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul one_pos (k := n * M) ?_
  have hper_f : Periodic ((fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← UpperHalfPlane.modular_T_smul]
      exact congrArg (fun p : ℂ[X] ↦ p.coeff k) (cyclicIsogenyPolynomial_smul j_smul_SL2Z _ τ)
  refine UpperHalfPlane.analyticAt_cuspFunction_zero one_pos ?_ ?_ ?_
  · have hper_q : Periodic ((fun τ : ℍ ↦ 𝕢 1 τ ^ (n * M)) ∘ ofComplex) 1 :=
      (TauCeti.UpperHalfPlane.periodic_qParam_comp_ofComplex (h := 1)).comp fun z : ℂ ↦ z ^ (n * M)
    exact hper_q.mul hper_f
  · exact ((Function.Periodic.differentiable_qParam.mdifferentiable.comp
      mdifferentiable_coe).pow _).mul
      (mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k)
  · have hrew : (fun τ : ℍ ↦ 𝕢 1 τ ^ (n * M) * (cyclicIsogenyPolynomial n j τ).coeff k) =
        fun τ : ℍ ↦ (∏ A ∈ primitiveReps (n : ℤ),
          (C (𝕢 1 τ ^ n) * X -
            C (𝕢 1 τ ^ n * j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).coeff k := by
      ext τ
      rw [pow_mul, cyclicIsogenyPolynomial_def, pow_card_mul_coeff_prod_X_sub_C]
    rw [hrew]
    exact isBoundedAtImInfty_qParam_pow_mul_coeff_prod _
      (fun _ hA ↦ (mem_primitiveReps.1 hA).1) k

/-- At width `n`, the Laurent `q`-expansion commutes with the coefficients of a `Finset` product of
linear factors `X - C (g A τ)`. -/
private theorem meromorphicAt_and_laurentQExpansion_coeff_prod_X_sub_C
    (s : Finset (FixedDetMatrix (Fin 2) ℤ n)) (hs : ∀ A ∈ s, A ∈ reps (n : ℤ)) (k : ℕ) :
    MeromorphicAt (cuspFunction n fun τ : ℍ ↦
      (∏ A ∈ s, (X - C (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).coeff k) 0 ∧
    UpperHalfPlane.laurentQExpansion n (fun τ : ℍ ↦
      (∏ A ∈ s, (X - C (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).coeff k) =
      (∏ A ∈ s, (X - C (UpperHalfPlane.laurentQExpansion n
        fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_const _, ?_⟩
    simp [Finset.prod_empty, coeff_one]
  | @insert A s hAs ih =>
    have hA : MeromorphicAt (cuspFunction n fun τ : ℍ ↦
        j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
      meromorphicAt_cuspFunction_j_toGLReal_smul (hs A (Finset.mem_insert_self A s))
    have hs' : ∀ B ∈ s, B ∈ reps (n : ℤ) := fun B hB ↦ hs B (Finset.mem_insert_of_mem hB)
    cases k with
    | zero =>
      have hfun : (fun τ : ℍ ↦ (∏ B ∈ insert A s,
          (X - C (j (toGLReal (NeZero.ne (n : ℤ)) B • τ)))).coeff 0) =
          -(fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) *
            fun τ : ℍ ↦ (∏ B ∈ s, (X - C (j (toGLReal (NeZero.ne (n : ℤ)) B • τ)))).coeff 0 := by
        ext τ
        simp only [Finset.prod_insert hAs, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero,
          zero_sub, Pi.mul_apply, Pi.neg_apply]
      rw [hfun]
      refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_mul
        (UpperHalfPlane.meromorphicAt_cuspFunction_neg hA) (ih hs' 0).1, ?_⟩
      rw [UpperHalfPlane.laurentQExpansion_mul (UpperHalfPlane.meromorphicAt_cuspFunction_neg hA)
        (ih hs' 0).1, UpperHalfPlane.laurentQExpansion_neg hA, (ih hs' 0).2,
        Finset.prod_insert hAs, mul_coeff_zero]
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    | succ k =>
      have hfun : (fun τ : ℍ ↦ (∏ B ∈ insert A s,
          (X - C (j (toGLReal (NeZero.ne (n : ℤ)) B • τ)))).coeff (k + 1)) =
          (fun τ : ℍ ↦ (∏ B ∈ s, (X - C (j (toGLReal (NeZero.ne (n : ℤ)) B • τ)))).coeff k) -
          (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) *
            fun τ : ℍ ↦
              (∏ B ∈ s, (X - C (j (toGLReal (NeZero.ne (n : ℤ)) B • τ)))).coeff (k + 1) := by
        ext τ
        rw [Finset.prod_insert hAs, coeff_X_sub_C_mul]
        rfl
      rw [hfun]
      have hm1 := (ih hs' k).1
      have hm2 := UpperHalfPlane.meromorphicAt_cuspFunction_mul hA (ih hs' (k + 1)).1
      refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_sub hm1 hm2, ?_⟩
      rw [UpperHalfPlane.laurentQExpansion_sub hm1 hm2,
        UpperHalfPlane.laurentQExpansion_mul hA (ih hs' (k + 1)).1,
        (ih hs' k).2, (ih hs' (k + 1)).2, Finset.prod_insert hAs, coeff_X_sub_C_mul]

end CyclicExpansion

/-! ### Cyclotomic Galois descent of the `q`-expansion coefficients -/

section GaloisDescent

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Multiplying the upper-right entry of `!![a, b; 0, d]` (`a * d = n`) by `m` coprime to `n`,
reduced modulo `d`, preserves `TauCeti.IsPrimitive`. -/
private theorem isPrimitive_upperTri_mul_mod {a b d m : ℕ} (had : a * d = n) (hm : m.Coprime n)
    (hprim : TauCeti.IsPrimitive !![(a : ℤ), (b : ℤ); 0, (d : ℤ)]) :
    TauCeti.IsPrimitive !![(a : ℤ), ((m * b % d : ℕ) : ℤ); 0, (d : ℤ)] := by
  obtain ⟨f, hf⟩ := isPrimitive_def.1 hprim
  have hmat : !![(a : ℤ), (b : ℤ); (0 : ℤ), (d : ℤ)] =
      (a : ℤ) • !![1, 0; 0, 0] + (b : ℤ) • !![0, 1; 0, 0] + (d : ℤ) • !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmat, map_add, map_add, map_zsmul, map_zsmul, map_zsmul] at hf
  simp only [zsmul_eq_mul] at hf
  set c₀₀ := f !![1, 0; 0, 0]
  set c₀₁ := f !![0, 1; 0, 0]
  set c₁₁ := f !![0, 0; 0, 1]
  have hcop : IsCoprime (m : ℤ) (n : ℤ) := Int.isCoprime_iff_nat_coprime.2 (by simpa using hm)
  obtain ⟨x, y, hxy⟩ := hcop
  set q : ℕ := m * b / d
  have hdiv : ((m * b % d : ℕ) : ℤ) + (d : ℤ) * q = (m : ℤ) * b := by
    exact_mod_cast (Nat.mod_add_div (m * b) d)
  have hadZ : (a : ℤ) * d = n := by exact_mod_cast had
  let g : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] ℤ :=
    c₀₀ • (entryAddMonoidHom ℤ 0 0).toIntLinearMap +
      (c₀₁ * x) • (entryAddMonoidHom ℤ 0 1).toIntLinearMap +
      (c₁₁ + c₀₁ * x * q + c₀₁ * y * b * a) • (entryAddMonoidHom ℤ 1 1).toIntLinearMap
  refine isPrimitive_def.2 ⟨g, ?_⟩
  simp only [g, LinearMap.add_apply, LinearMap.smul_apply, AddMonoidHom.coe_toIntLinearMap,
    entryAddMonoidHom_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
  linear_combination hf + c₀₁ * x * hdiv + c₀₁ * b * hxy + c₀₁ * y * b * hadZ

private def mkFixedDet {m : ℤ} (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = m) :
    FixedDetMatrix (Fin 2) ℤ m :=
  ⟨M, h⟩

private def matOf {m : ℤ} (A : FixedDetMatrix (Fin 2) ℤ m) : Matrix (Fin 2) (Fin 2) ℤ :=
  A.1

open scoped Classical in
/-- A unit `u : (ZMod n)ˣ` acts on `primitiveReps n` by multiplying the upper-right residue `b` of
`(a b; 0 d)` modulo `d`. -/
private def scaleRep (u : (ZMod n)ˣ) (A : FixedDetMatrix (Fin 2) ℤ n) :
    FixedDetMatrix (Fin 2) ℤ n :=
  if hA : A ∈ reps (n : ℤ) then
    mkFixedDet
      !![(repEntry A 0 0 : ℤ), (((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1 : ℕ) : ℤ);
          0, (repEntry A 1 1 : ℤ)]
      (by simp [det_fin_two_of, ← Nat.cast_mul, (mem_reps_nat_entries hA).2.2.1])
  else A

/-- `scaleRep u A` lies in `reps n` whenever `A` does, with upper-right entry `(u.val * b) % d`. -/
private theorem scaleRep_mem_reps_and_entries (u : (ZMod n)ˣ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    scaleRep u A ∈ reps (n : ℤ) ∧
      repEntry (scaleRep u A) 0 0 = repEntry A 0 0 ∧
      repEntry (scaleRep u A) 1 1 = repEntry A 1 1 ∧
      repEntry (scaleRep u A) 0 1 = (u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1 := by
  obtain ⟨ha, hd, -, -, -⟩ := mem_reps_nat_entries hA
  have hcoe : (scaleRep u A).1 =
      !![(repEntry A 0 0 : ℤ), (((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1 : ℕ) : ℤ);
          0, (repEntry A 1 1 : ℤ)] := by
    -- Fold `Subtype.val` into `matOf` so `rw` sees `FixedDetMatrix` at `implicit` transparency.
    change matOf (scaleRep u A) = _
    rw [scaleRep, dite_eq_left_of_eq_true (eq_true hA)]
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hcoe]
  · simp [hcoe, ha]
  · rw [hcoe]
    exact Nat.cast_nonneg _
  · rw [hcoe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    exact Int.ofNat_lt.2 (Nat.mod_lt _ hd)
  · rw [repEntry, hcoe]; simp
  · rw [repEntry, hcoe]; simp
  · rw [repEntry, hcoe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.natAbs_natCast]

/-- `scaleRep u` maps `primitiveReps n` into itself. -/
private theorem scaleRep_mem_primitiveReps (u : (ZMod n)ˣ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ primitiveReps (n : ℤ)) : scaleRep u A ∈ primitiveReps (n : ℤ) := by
  obtain ⟨hAr, hAp⟩ := mem_primitiveReps.1 hA
  obtain ⟨hBr, ha, hd, hb⟩ := scaleRep_mem_reps_and_entries u hAr
  obtain ⟨-, -, had, -, hmatA⟩ := mem_reps_nat_entries hAr
  obtain ⟨-, -, -, -, hmatB⟩ := mem_reps_nat_entries hBr
  refine mem_primitiveReps.2 ⟨hBr, ?_⟩
  rw [hmatB, ha, hb, hd]
  rw [hmatA] at hAp
  exact isPrimitive_upperTri_mul_mod had (ZMod.val_coe_unit_coprime u) hAp

/-- `scaleRep u⁻¹` is a left inverse to `scaleRep u` on `reps n`. -/
private theorem scaleRep_inv_scaleRep (u : (ZMod n)ˣ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) : scaleRep u⁻¹ (scaleRep u A) = A := by
  obtain ⟨hBr, haB, hdB, hbB⟩ := scaleRep_mem_reps_and_entries u hA
  obtain ⟨hCr, haC, hdC, hbC⟩ := scaleRep_mem_reps_and_entries u⁻¹ hBr
  obtain ⟨-, -, had, hb_lt, hmatA⟩ := mem_reps_nat_entries hA
  obtain ⟨-, -, -, -, hmatC⟩ := mem_reps_nat_entries hCr
  apply Subtype.ext
  rw [hmatC, haC, haB, hdC, hbC, hdB, hbB, hmatA]
  have h1 : (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (u : ZMod n)).val = (1 : ZMod n).val := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [ZMod.val_mul, ZMod.val_one_eq_one_mod] at h1
  have hdvd : repEntry A 1 1 ∣ n := ⟨repEntry A 0 0, by rw [mul_comm, had]⟩
  have hmod : (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val *
      ((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1)) % repEntry A 1 1 =
      repEntry A 0 1 := by
    calc (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val *
          ((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1)) % repEntry A 1 1
        = ((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val * (u : ZMod n).val) * repEntry A 0 1) %
            repEntry A 1 1 := by
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
      _ = (1 * repEntry A 0 1) % repEntry A 1 1 :=
          Nat.ModEq.mul_right (repEntry A 0 1) (Nat.ModEq.of_dvd hdvd h1)
      _ = repEntry A 0 1 := by rw [one_mul, Nat.mod_eq_of_lt hb_lt]
  rw [hmod]

open scoped Classical in
/-- `scaleRep u` permutes `primitiveReps n`. -/
private theorem image_scaleRep_primitiveReps (u : (ZMod n)ˣ) :
    (primitiveReps (n : ℤ)).image (scaleRep u) = primitiveReps (n : ℤ) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
    exact scaleRep_mem_primitiveReps u hA
  · rw [Finset.card_image_of_injOn]
    intro A hA B hB hAB
    rw [← scaleRep_inv_scaleRep u (mem_primitiveReps.1 hA).1, hAB,
      scaleRep_inv_scaleRep u (mem_primitiveReps.1 hB).1]

/-- The integral Laurent series lifting the width-one Laurent `q`-expansion of `j`. -/
private def intLaurentJ : LaurentSeries ℤ :=
  ((HahnSeries.mem_map_rangeS (f := Int.castRingHom ℂ)).2 fun g ↦ by
    obtain ⟨m, hm⟩ := exists_laurentQExpansion_j_coeff_eq_intCast g
    exact ⟨m, hm.symm⟩).choose

private theorem map_intLaurentJ :
    HahnSeries.mapRingHom (Int.castRingHom ℂ) intLaurentJ =
      UpperHalfPlane.laurentQExpansion 1 j :=
  ((HahnSeries.mem_map_rangeS (f := Int.castRingHom ℂ)).2 fun g ↦ by
    obtain ⟨m, hm⟩ := exists_laurentQExpansion_j_coeff_eq_intCast g
    exact ⟨m, hm.symm⟩).choose_spec

/-- The cyclotomic subfield `ℚ(e^{2π i / n}) ⊆ ℂ`. -/
private abbrev cyclotomicSubfield (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({cexp (2 * π * I / n)} : Set ℂ)

/-- The canonical `n`-th root of unity `e^{2π i / n}` inside `cyclotomicSubfield n`. -/
private def zetaCyclotomic (n : ℕ) : cyclotomicSubfield n :=
  ⟨cexp (2 * π * I / n), IntermediateField.mem_adjoin_simple_self ℚ _⟩

private theorem isPrimitiveRoot_zetaCyclotomic : IsPrimitiveRoot (zetaCyclotomic n) n :=
  (IsPrimitiveRoot.map_iff_of_injective (f := (cyclotomicSubfield n).val.toRingHom)
    Subtype.val_injective).1 (Complex.isPrimitiveRoot_exp n (NeZero.ne n))

open scoped Classical in
/-- Algebraic lift inside `LaurentSeries (cyclotomicSubfield n)` of the width-`n` Laurent
`q`-expansion of `j (A • τ)`. -/
private def repLaurentSeries (A : FixedDetMatrix (Fin 2) ℤ n) :
    LaurentSeries (cyclotomicSubfield n) :=
  if hA : A ∈ reps (n : ℤ) then
    LaurentSeries.expand (cyclotomicSubfield n)
      (⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hA) 2⟩ : ℕ+)
      (HahnSeries.twistEquiv
        (zpowersHom (cyclotomicSubfield n)ˣ
          (Units.mk0 (zetaCyclotomic n ^ (repEntry A 0 0 * repEntry A 0 1))
            (pow_ne_zero _ (isPrimitiveRoot_zetaCyclotomic.ne_zero (NeZero.ne n)))))
        (HahnSeries.mapRingHom (Int.castRingHom (cyclotomicSubfield n)) intLaurentJ))
  else 0

/-- Under `cyclotomicSubfield n → ℂ`, `repLaurentSeries A` maps to the width-`n` Laurent
`q`-expansion of `j (A • τ)`. -/
private theorem map_val_repLaurentSeries {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    HahnSeries.mapRingHom (cyclotomicSubfield n).val.toRingHom (repLaurentSeries A) =
      UpperHalfPlane.laurentQExpansion n (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  rw [repLaurentSeries, dite_eq_left_of_eq_true (eq_true hA), laurentQExpansion_j_toGLReal_smul hA,
    ← map_intLaurentJ]
  set d : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hA) 2⟩
  ext g
  by_cases hdvd : (d : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [HahnSeries.coeff_mapRingHom, LaurentSeries.coeff_expand_mul, LaurentSeries.coeff_expand_mul,
      HahnSeries.coeff_twistEquiv, HahnSeries.coeff_twistEquiv,
      HahnSeries.coeff_mapRingHom, HahnSeries.coeff_mapRingHom]
    simp only [zpowersHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul, map_zpow₀,
      map_pow]
    simp [zetaCyclotomic]
  · simp [LaurentSeries.coeff_expand_of_not_dvd d _ hdvd]

/-- Every coefficient of `repLaurentSeries A` is integral over `ℤ`. -/
private theorem repLaurentSeries_coeff_isIntegral {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (g : ℤ) :
    IsIntegral ℤ ((repLaurentSeries A).coeff g) := by
  rw [repLaurentSeries, dite_eq_left_of_eq_true (eq_true hA)]
  set d : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hA) 2⟩
  by_cases hdvd : (d : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [LaurentSeries.coeff_expand_mul, HahnSeries.coeff_twistEquiv, HahnSeries.coeff_mapRingHom]
    have hζ : IsPrimitiveRoot (zetaCyclotomic n) n := isPrimitiveRoot_zetaCyclotomic
    have hζ_int : IsIntegral ℤ (zetaCyclotomic n) := hζ.isIntegral (NeZero.pos n)
    have hζ_inv : IsIntegral ℤ (zetaCyclotomic n)⁻¹ := by
      have h1 : zetaCyclotomic n * zetaCyclotomic n ^ (n - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos n), hζ.pow_eq_one]
      rw [inv_eq_of_mul_eq_one_right h1]
      exact hζ_int.pow _
    have hzpow : IsIntegral ℤ (((Units.mk0 (zetaCyclotomic n ^ (repEntry A 0 0 * repEntry A 0 1))
        (pow_ne_zero _ (hζ.ne_zero (NeZero.ne n))) ^ r : (cyclotomicSubfield n)ˣ) :
        cyclotomicSubfield n)) := by
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
      cases r with
      | ofNat l => simpa using (hζ_int.pow _).pow l
      | negSucc l =>
        rw [zpow_negSucc, ← inv_pow, ← inv_pow]
        exact (hζ_inv.pow _).pow (l + 1)
    have hint : IsIntegral ℤ ((intLaurentJ.coeff r : ℤ) : cyclotomicSubfield n) :=
      intCast_mem (integralClosure ℤ (cyclotomicSubfield n)) _
    simpa [zpowersHom_apply] using hzpow.mul hint
  · rw [LaurentSeries.coeff_expand_of_not_dvd d _ hdvd]
    exact isIntegral_zero

/-- Every `σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends `repLaurentSeries A` to
`repLaurentSeries (scaleRep (autToPow ℚ σ) A)`. -/
private theorem map_gal_repLaurentSeries (σ : cyclotomicSubfield n ≃ₐ[ℚ] cyclotomicSubfield n)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    HahnSeries.mapRingHom (σ : cyclotomicSubfield n →+* cyclotomicSubfield n)
        (repLaurentSeries A) =
      repLaurentSeries (scaleRep (isPrimitiveRoot_zetaCyclotomic.autToPow ℚ σ) A) := by
  have hζ : IsPrimitiveRoot (zetaCyclotomic n) n := isPrimitiveRoot_zetaCyclotomic
  set u := hζ.autToPow ℚ σ
  obtain ⟨hBr, haB, -, hbB⟩ := scaleRep_mem_reps_and_entries u hA
  obtain ⟨-, -, had, -, -⟩ := mem_reps_nat_entries hA
  have hpow : σ (zetaCyclotomic n ^ (repEntry A 0 0 * repEntry A 0 1)) =
      zetaCyclotomic n ^ (repEntry (scaleRep u A) 0 0 * repEntry (scaleRep u A) 0 1) := by
    rw [map_pow, ← hζ.autToPow_spec ℚ σ, ← pow_mul, haB, hbB]
    set q := (u : ZMod n).val * repEntry A 0 1 / repEntry A 1 1
    have hdiv := Nat.mod_add_div ((u : ZMod n).val * repEntry A 0 1) (repEntry A 1 1)
    have hexp : (u : ZMod n).val * (repEntry A 0 0 * repEntry A 0 1) =
        repEntry A 0 0 * ((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1) + n * q := by
      calc (u : ZMod n).val * (repEntry A 0 0 * repEntry A 0 1)
          = repEntry A 0 0 * ((u : ZMod n).val * repEntry A 0 1) := by ring
        _ = repEntry A 0 0 * (((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1) +
              repEntry A 1 1 * q) := by rw [hdiv]
        _ = _ := by rw [mul_add, ← mul_assoc, had]
    have hnq : zetaCyclotomic n ^ (n * q) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    rw [hexp, pow_add, hnq, mul_one]
  ext g
  rw [repLaurentSeries, dite_eq_left_of_eq_true (eq_true hA),
    repLaurentSeries, dite_eq_left_of_eq_true (eq_true hBr), HahnSeries.coeff_mapRingHom]
  set dA : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hA) 2⟩
  set dB : ℕ+ := ⟨repEntry (scaleRep u A) 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hBr) 2⟩
  have hdAB : dA = dB := Subtype.ext (by simp [dA, dB, haB])
  by_cases hdvd : (dA : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [LaurentSeries.coeff_expand_mul, hdAB, LaurentSeries.coeff_expand_mul]
    simp [zpowersHom_apply, Units.val_zpow_eq_zpow_val, hpow]
  · rw [LaurentSeries.coeff_expand_of_not_dvd dA _ hdvd,
      LaurentSeries.coeff_expand_of_not_dvd dB _ (hdAB ▸ hdvd), map_zero]

/-- Integrality over `ℤ` of the Laurent coefficients of each polynomial coefficient of
`∏ A ∈ s, (X - C (repLaurentSeries A))`. -/
private theorem coeff_prod_repLaurentSeries_isIntegral
    (s : Finset (FixedDetMatrix (Fin 2) ℤ n)) (hs : ∀ A ∈ s, A ∈ reps (n : ℤ)) (k : ℕ) (g : ℤ) :
    IsIntegral ℤ (((∏ A ∈ s, (X - C (repLaurentSeries A))).coeff k).coeff g) := by
  classical
  have hmul_int {f₁ f₂ : LaurentSeries (cyclotomicSubfield n)}
      (hf₁ : ∀ m, IsIntegral ℤ (f₁.coeff m)) (hf₂ : ∀ m, IsIntegral ℤ (f₂.coeff m)) (m : ℤ) :
      IsIntegral ℤ ((f₁ * f₂).coeff m) := by
    rw [HahnSeries.coeff_mul]
    exact (integralClosure ℤ (cyclotomicSubfield n)).sum_mem fun ij _ ↦ (hf₁ ij.1).mul (hf₂ ij.2)
  induction s using Finset.induction_on generalizing k g with
  | empty =>
    rw [Finset.prod_empty, coeff_one]
    split_ifs with hk
    · rw [HahnSeries.coeff_one]
      split_ifs <;> [exact isIntegral_one; exact isIntegral_zero]
    · simp [isIntegral_zero]
  | @insert A s hAs ih =>
    rw [Finset.prod_insert hAs]
    have hs' : ∀ B ∈ s, B ∈ reps (n : ℤ) := fun B hB ↦ hs B (Finset.mem_insert_of_mem hB)
    have hA := repLaurentSeries_coeff_isIntegral (hs A (Finset.mem_insert_self A s))
    cases k with
    | zero =>
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      exact hmul_int (fun m ↦ by simpa using (hA m).neg) (ih hs' 0) g
    | succ k =>
      rw [coeff_X_sub_C_mul, HahnSeries.coeff_sub]
      exact (ih hs' k g).sub (hmul_int hA (ih hs' (k + 1)) g)

/-- Every `σ ∈ Gal(ℚ(ζ_n) / ℚ)` fixes `∏ A ∈ primitiveReps n, (X - C (repLaurentSeries A))`. -/
private theorem map_gal_prod_repLaurentSeries
    (σ : cyclotomicSubfield n ≃ₐ[ℚ] cyclotomicSubfield n) :
    (∏ A ∈ primitiveReps (n : ℤ), (X - C (repLaurentSeries A))).map
        (HahnSeries.mapRingHom (σ : cyclotomicSubfield n →+* cyclotomicSubfield n)) =
      ∏ A ∈ primitiveReps (n : ℤ), (X - C (repLaurentSeries A)) := by
  classical
  simp only [Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
  rw [Finset.prod_congr rfl fun A hA ↦ by
      rw [map_gal_repLaurentSeries σ (mem_primitiveReps.1 hA).1],
    ← Finset.prod_image (f := fun A ↦ X - C (repLaurentSeries A)) fun A hA B hB h ↦ by
      rw [← scaleRep_inv_scaleRep (isPrimitiveRoot_zetaCyclotomic.autToPow ℚ σ)
          (mem_primitiveReps.1 hA).1, h,
        scaleRep_inv_scaleRep (isPrimitiveRoot_zetaCyclotomic.autToPow ℚ σ)
          (mem_primitiveReps.1 hB).1],
    image_scaleRep_primitiveReps (n := n)]

/-- Every width-one Laurent `q`-coefficient of `(cyclicIsogenyPolynomial n j ·).coeff k` is an
integer. -/
private theorem laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_int (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion 1
      (fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m ∈
      (algebraMap ℤ ℂ).range := by
  let K := cyclotomicSubfield n
  have hζ : IsPrimitiveRoot (cexp (2 * π * I / n)) n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  have : IsCyclotomicExtension {n} ℚ K := hζ.isCyclotomicExtension_adjoin_singleton
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finite_of_singleton n ℚ K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  set PK : (LaurentSeries K)[X] := ∏ A ∈ primitiveReps (n : ℤ), (X - C (repLaurentSeries A))
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  set x : K := (PK.coeff k).coeff ((d : ℤ) * m)
  have hx_fixed : ∀ σ : K ≃ₐ[ℚ] K, σ x = x := fun σ ↦ by
    simpa [x, coeff_map] using
      congrArg (fun p : (LaurentSeries K)[X] ↦ (p.coeff k).coeff ((d : ℤ) * m))
        (map_gal_prod_repLaurentSeries (n := n) σ)
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) x).2 hx_fixed
  have hx_int : IsIntegral ℤ x := coeff_prod_repLaurentSeries_isIntegral _
    (fun _ hA ↦ (mem_primitiveReps.1 hA).1) k ((d : ℤ) * m)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_algebraMap_iff.1 (hq ▸ hx_int))
  refine ⟨z, ?_⟩
  have hper_f : Periodic ((fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← UpperHalfPlane.modular_T_smul]
      exact congrArg (fun p : ℂ[X] ↦ p.coeff k) (cyclicIsogenyPolynomial_smul j_smul_SL2Z _ τ)
  have hexp := UpperHalfPlane.laurentQExpansion_pnat_mul hper_f
    (meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j (n := n) k) d
  have hd_mul : ((d : ℕ) : ℝ) * 1 = n := mul_one _
  rw [hd_mul] at hexp
  have hval_PK : (PK.map (HahnSeries.mapRingHom K.val.toRingHom)).coeff k =
      UpperHalfPlane.laurentQExpansion n
        (fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) := by
    simp only [cyclicIsogenyPolynomial_def]
    rw [(meromorphicAt_and_laurentQExpansion_coeff_prod_X_sub_C _
      (fun _ hA ↦ (mem_primitiveReps.1 hA).1) k).2]
    simp only [PK, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
    exact congrArg (fun p : (LaurentSeries ℂ)[X] ↦ p.coeff k)
      (Finset.prod_congr rfl fun A hA ↦ by rw [map_val_repLaurentSeries (mem_primitiveReps.1 hA).1])
  have hcoeff := congrArg (fun s : LaurentSeries ℂ ↦ s.coeff ((d : ℤ) * m)) (hval_PK.trans hexp)
  simp only [coeff_map, HahnSeries.coeff_mapRingHom, LaurentSeries.coeff_expand_mul] at hcoeff
  have hx_def : (PK.coeff k).coeff ((d : ℤ) * m) = x := rfl
  rw [← hcoeff, hx_def, ← hq, ← hz]
  simp

end GaloisDescent

/-! ### Construction and properties of the modular polynomial `Φ_n(X, Y)` -/

section ModularPolynomial

variable (n : ℕ) [NeZero n]

/-- Each coefficient `(cyclicIsogenyPolynomial n j ·).coeff k` is a polynomial in `j` with integer
coefficients. -/
private theorem exists_int_poly_aeval_j_eq_coeff_cyclicIsogenyPolynomial (k : ℕ) :
    ∃ P : ℤ[X], ∀ τ : ℍ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).coeff k :=
  exists_aeval_j_eq (mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k)
    (fun γ τ ↦ congrArg (fun p : ℂ[X] ↦ p.coeff k)
      (cyclicIsogenyPolynomial_smul j_smul_SL2Z γ τ))
    (meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j k)
    fun m _ ↦ laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_int k m

/-- **The classical modular polynomial `Φ_n(X, Y) ∈ ℤ[X][Y]`**: the unique bivariate polynomial
with integer coefficients such that substituting `X = j(τ)` gives
`cyclicIsogenyPolynomial n j τ = ∏_{A ∈ primitiveReps n} (Y - j(A • τ))`. -/
noncomputable def modularPolynomial : ℤ[X][Y] :=
  ∑ k ∈ Finset.range ((primitiveReps (n : ℤ)).card + 1),
    monomial k (exists_int_poly_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose

/-- Substituting `X = j(τ)` into `modularPolynomial n` recovers `cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem map_aeval_j_modularPolynomial (τ : ℍ) :
    (modularPolynomial n).map ((aeval (j τ) : ℤ[X] →ₐ[ℤ] ℂ) : ℤ[X] →+* ℂ) =
      cyclicIsogenyPolynomial n j τ := by
  ext k
  rw [coeff_map, RingHom.coe_coe, modularPolynomial, finsetSum_coeff]
  simp only [coeff_monomial_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hk
  · exact (exists_int_poly_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose_spec τ
  · rw [map_zero, eq_comm]
    refine coeff_eq_zero_of_natDegree_lt ?_
    rw [natDegree_cyclicIsogenyPolynomial]
    simp only [Finset.mem_range, not_lt] at hk
    omega

/-- Evaluating `modularPolynomial n` at `(j(τ), w)` evaluates `cyclicIsogenyPolynomial n j τ` at
`w`. -/
theorem aevalAeval_j_modularPolynomial (τ : ℍ) (w : ℂ) :
    aevalAeval (j τ) w (modularPolynomial n) = (cyclicIsogenyPolynomial n j τ).eval w := by
  rw [aevalAeval_eq_eval₂, AlgHom.toRingHom_eq_coe, ← eval_map, map_aeval_j_modularPolynomial]

variable {n} in
/-- **Uniqueness of `modularPolynomial n`.** Any `Φ : ℤ[X][Y]` whose evaluation at `X = j(τ)` is
`cyclicIsogenyPolynomial n j τ` for all `τ ∈ ℍ` equals `modularPolynomial n`. -/
theorem eq_modularPolynomial_of_map_aeval_j_eq {Φ : ℤ[X][Y]}
    (hΦ : ∀ τ : ℍ,
      Φ.map ((aeval (j τ) : ℤ[X] →ₐ[ℤ] ℂ) : ℤ[X] →+* ℂ) = cyclicIsogenyPolynomial n j τ) :
    Φ = modularPolynomial n := by
  have hk (k : ℕ) : Φ.coeff k = (modularPolynomial n).coeff k := by
    refine aeval_j_injective Int.cast_injective (funext fun τ ↦ ?_)
    have h := congrArg (fun p : ℂ[X] ↦ p.coeff k)
      ((hΦ τ).trans (map_aeval_j_modularPolynomial n τ).symm)
    rwa [coeff_map, coeff_map, RingHom.coe_coe] at h
  ext k m
  rw [hk k]

/-- At level `n = 1`, the modular polynomial is `Φ_1(X, Y) = Y - X`. -/
@[simp]
theorem modularPolynomial_one : modularPolynomial 1 = Y - C X := by
  symm
  refine eq_modularPolynomial_of_map_aeval_j_eq fun τ ↦ ?_
  let I₁ : FixedDetMatrix (Fin 2) ℤ ((1 : ℕ) : ℤ) := ⟨!![1, 0; 0, 1], by simp⟩
  have hI₁_reps : I₁ ∈ reps ((1 : ℕ) : ℤ) :=
    ⟨by simp [I₁], by simp [I₁], by simp [I₁], by simp [I₁]⟩
  have hreps : primitiveReps ((1 : ℕ) : ℤ) = {I₁} := by
    ext A
    simp only [Finset.mem_singleton]
    refine ⟨fun hA ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨-, -, had, hb, hmat⟩ := mem_reps_nat_entries (n := 1) (mem_primitiveReps.1 hA).1
      have ha1 : repEntry A 0 0 = 1 := Nat.eq_one_of_mul_eq_one_right had
      have hd1 : repEntry A 1 1 = 1 := Nat.eq_one_of_mul_eq_one_left had
      have hb0 : repEntry A 0 1 = 0 := by omega
      exact Subtype.ext (hmat.trans (by rw [ha1, hd1, hb0]; rfl))
    · subst h
      exact mem_primitiveReps.2 ⟨hI₁_reps,
        isPrimitive_def.2 ⟨(entryAddMonoidHom ℤ 0 0).toIntLinearMap, by simp [I₁]⟩⟩
  have hsmul : toGLReal (NeZero.ne ((1 : ℕ) : ℤ)) I₁ • τ = τ := by
    apply UpperHalfPlane.ext
    rw [coe_toGLReal_smul_of_mem_reps (n := 1) hI₁_reps]
    simp [repEntry, I₁]
  rw [cyclicIsogenyPolynomial_def, hreps, Finset.prod_singleton, hsmul]
  simp

/-- `modularPolynomial n` is monic in `Y`. -/
theorem monic_modularPolynomial : (modularPolynomial n).Monic := by
  rw [Monic, leadingCoeff]
  have hdeg : (modularPolynomial n).natDegree = (primitiveReps (n : ℤ)).card := by
    refine le_antisymm ?_ ?_
    · rw [modularPolynomial]
      refine (natDegree_sum_le _ _).trans ?_
      simp only [Finset.fold_max_le, Nat.zero_le, true_and, Finset.mem_range]
      intro k hk
      exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 hk)
    · have h := natDegree_map_le
        (f := ((aeval (j UpperHalfPlane.I) : ℤ[X] →ₐ[ℤ] ℂ) : ℤ[X] →+* ℂ))
        (p := modularPolynomial n)
      rwa [map_aeval_j_modularPolynomial, natDegree_cyclicIsogenyPolynomial] at h
  rw [hdeg]
  refine aeval_j_injective Int.cast_injective (funext fun τ ↦ ?_)
  have h := congrArg (fun p : ℂ[X] ↦ p.coeff (primitiveReps (n : ℤ)).card)
    (map_aeval_j_modularPolynomial n τ)
  rw [coeff_map, ← natDegree_cyclicIsogenyPolynomial j τ,
    ← leadingCoeff, (monic_cyclicIsogenyPolynomial j τ).leadingCoeff] at h
  simpa using h

/-- The `Y`-degree of `modularPolynomial n` is the number of cyclic `n`-isogenies. -/
@[simp]
theorem natDegree_modularPolynomial :
    (modularPolynomial n).natDegree = (primitiveReps (n : ℤ)).card := by
  have h1 := (monic_modularPolynomial n).natDegree_map
    ((aeval (j UpperHalfPlane.I) : ℤ[X] →ₐ[ℤ] ℂ) : ℤ[X] →+* ℂ)
  rw [map_aeval_j_modularPolynomial, natDegree_cyclicIsogenyPolynomial] at h1
  exact h1.symm

variable {n}

/-- For every primitive integral matrix `A` of determinant `n`, `Φ_n(j(τ), j(A • τ)) = 0`. -/
theorem aevalAeval_j_toGLReal_smul_modularPolynomial {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : TauCeti.IsPrimitive A.1) (τ : ℍ) :
    aevalAeval (j τ) (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) (modularPolynomial n) = 0 := by
  rw [aevalAeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial j_smul_SL2Z hA τ

/-- The classical modular equation `Φ_n(j(τ), j(n τ)) = 0`. -/
theorem aevalAeval_j_scaleGL_smul_modularPolynomial (τ : ℍ) :
    aevalAeval (j τ) (j (scaleGL n • τ)) (modularPolynomial n) = 0 := by
  rw [aevalAeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial_scaleGL_smul j_smul_SL2Z τ

/-- **Zero locus of the modular polynomial**: `Φ_n(j(τ), j(τ')) = 0` holds if and only if `τ'` is
the image of `τ` under a primitive integral matrix of determinant `n`. -/
theorem aevalAeval_j_modularPolynomial_eq_zero_iff (τ τ' : ℍ) :
    aevalAeval (j τ) (j τ') (modularPolynomial n) = 0 ↔
      ∃ A : FixedDetMatrix (Fin 2) ℤ n,
        TauCeti.IsPrimitive A.1 ∧ toGLReal (NeZero.ne (n : ℤ)) A • τ = τ' := by
  refine ⟨fun h ↦ ?_, fun ⟨A, hA, hτ⟩ ↦ hτ ▸ aevalAeval_j_toGLReal_smul_modularPolynomial hA τ⟩
  rw [aevalAeval_j_modularPolynomial, ← IsRoot.def,
    ← mem_roots (monic_cyclicIsogenyPolynomial j τ).ne_zero,
    roots_cyclicIsogenyPolynomial, Multiset.mem_map] at h
  obtain ⟨B, hB, hjB⟩ := h
  obtain ⟨γ, hγ⟩ := ModularGroup.j_eq_j_iff.1 hjB
  refine ⟨γ • B, (isPrimitive_smul_iff γ B).2 (mem_primitiveReps.1 hB).2, ?_⟩
  rwa [toGLReal_smul_smul]

end ModularPolynomial

/-! ### The diagonal `Φ_n(X, X)` and integrality of `j` at imaginary quadratic points -/

section DiagonalAndCM

variable (n : ℕ) [NeZero n]

/-- **The diagonal modular polynomial `Φ_n(X, X) ∈ ℤ[X]`**, whose roots are the `j`-invariants of
elliptic curves admitting a cyclic `n`-endomorphism. -/
noncomputable def diagModularPolynomial : ℤ[X] :=
  (modularPolynomial n).eval X

/-- At `n = 1 = 1²`, the diagonal modular polynomial vanishes (`Y - X` evaluated at `Y = X`),
showing that the non-square hypothesis in `diagModularPolynomial_ne_zero` is sharp. -/
@[simp]
theorem diagModularPolynomial_one : diagModularPolynomial 1 = 0 := by
  simp [diagModularPolynomial]

/-- Evaluating `diagModularPolynomial n` at `z` evaluates `modularPolynomial n` at `(z, z)`. -/
@[simp]
theorem aeval_diagModularPolynomial {A : Type*} [CommRing A] (z : A) :
    aeval z (diagModularPolynomial n) = aevalAeval z z (modularPolynomial n) :=
  Polynomial.aeval_eval_X z (modularPolynomial n)

variable {n}

/-- `Φ_n(j(τ), j(τ)) = 0` holds exactly when `τ` is fixed by a primitive integral matrix of
determinant `n`. -/
theorem aeval_j_diagModularPolynomial_eq_zero_iff (τ : ℍ) :
    aeval (j τ) (diagModularPolynomial n) = 0 ↔
      ∃ A : FixedDetMatrix (Fin 2) ℤ n,
        TauCeti.IsPrimitive A.1 ∧ toGLReal (NeZero.ne (n : ℤ)) A • τ = τ := by
  rw [aeval_diagModularPolynomial, aevalAeval_j_modularPolynomial_eq_zero_iff]

/-- The `k`-th power of the width-one Laurent `q`-expansion of `j` has order `-k` and leading
coefficient `1`. -/
private theorem orderTop_and_leadingCoeff_laurentQExpansion_j_pow (k : ℕ) :
    ((UpperHalfPlane.laurentQExpansion 1 j) ^ k).orderTop = (-k : ℤ) ∧
      ((UpperHalfPlane.laurentQExpansion 1 j) ^ k).leadingCoeff = 1 := by
  set J := UpperHalfPlane.laurentQExpansion 1 j
  have hJ_ord : J.orderTop = (-1 : ℤ) := orderTop_laurentQExpansion_j
  have hne : J ≠ 0 := by
    rw [← HahnSeries.orderTop_ne_top, hJ_ord]
    exact WithTop.coe_ne_top
  have hJ_lc : J.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq,
      WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hne).trans hJ_ord),
      laurentQExpansion_j_coeff_neg_one]
  induction k with
  | zero => simp [HahnSeries.leadingCoeff_one]
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul, ih.1, hJ_ord, HahnSeries.leadingCoeff_mul,
      ih.2, hJ_lc, mul_one, ← WithTop.coe_add]
    exact ⟨WithTop.coe_inj.2 (by push_cast; ring), rfl⟩

/-- For a nonzero polynomial `P : ℤ[X]`, the leading coefficient of the width-one Laurent
`q`-expansion of `P(j)` is `(P.leadingCoeff : ℂ)`. -/
private theorem leadingCoeff_laurentQExpansion_aeval_j {P : ℤ[X]} (hP : P ≠ 0) :
    (UpperHalfPlane.laurentQExpansion 1 (fun τ : ℍ ↦ aeval (j τ) P)).leadingCoeff =
      (P.leadingCoeff : ℂ) := by
  rw [Polynomial.laurentQExpansion_aeval_j]
  set J := UpperHalfPlane.laurentQExpansion 1 j
  set ev : ℤ[X] →+* LaurentSeries ℂ := eval₂RingHom (HahnSeries.C.comp (algebraMap ℤ ℂ)) J
  -- Fold `eval₂ (HahnSeries.C.comp (algebraMap ℤ ℂ)) J P` into `ev P` so `map_add`/`map_sum` apply.
  change (ev P).leadingCoeff = (P.leadingCoeff : ℂ)
  set N := P.natDegree
  have hc0 : (P.leadingCoeff : ℂ) ≠ 0 := Int.cast_ne_zero.2 (leadingCoeff_ne_zero.2 hP)
  have htop_lead : (ev (C P.leadingCoeff * X ^ N)).orderTop = (-N : ℤ) ∧
      (ev (C P.leadingCoeff * X ^ N)).leadingCoeff = (P.leadingCoeff : ℂ) := by
    simp only [ev, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow, RingHom.comp_apply]
    have hC_ord : (HahnSeries.C (algebraMap ℤ ℂ P.leadingCoeff) : LaurentSeries ℂ).orderTop =
        (0 : ℤ) := by
      rw [eq_intCast, HahnSeries.C_apply, HahnSeries.orderTop_single hc0]
    rw [HahnSeries.orderTop_mul, hC_ord, (orderTop_and_leadingCoeff_laurentQExpansion_j_pow N).1,
      ← WithTop.coe_add, zero_add, HahnSeries.leadingCoeff_mul, eq_intCast, HahnSeries.C_apply,
      HahnSeries.leadingCoeff_of_single, (orderTop_and_leadingCoeff_laurentQExpansion_j_pow N).2,
      mul_one]
    exact ⟨rfl, rfl⟩
  have herase_ord : ((-N : ℤ) : WithTop ℤ) < (ev P.eraseLead).orderTop := by
    by_cases he0 : P.eraseLead = 0
    · rw [he0, map_zero, HahnSeries.orderTop_zero]
      exact WithTop.coe_lt_top _
    · have hlt : P.eraseLead.natDegree < N :=
        P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right he0
      have hle : ((-(N - 1 : ℕ) : ℤ) : WithTop ℤ) ≤ (ev P.eraseLead).orderTop := by
        rw [P.eraseLead.as_sum_range' N hlt, map_sum]
        refine Finset.sum_induction _ (fun s : LaurentSeries ℂ ↦
          ((-(N - 1 : ℕ) : ℤ) : WithTop ℤ) ≤ s.orderTop)
          (fun x y hx hy ↦ (le_min hx hy).trans HahnSeries.min_orderTop_le_orderTop_add)
          (by simp) fun i hi ↦ ?_
        rw [Finset.mem_range] at hi
        simp only [ev, coe_eval₂RingHom, ← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_C,
          eval₂_X_pow, RingHom.comp_apply]
        rw [eq_intCast]
        by_cases hci : (P.eraseLead.coeff i : ℂ) = 0
        · simp [hci]
        · rw [HahnSeries.orderTop_mul, HahnSeries.C_apply, HahnSeries.orderTop_single hci,
            (orderTop_and_leadingCoeff_laurentQExpansion_j_pow i).1, ← WithTop.coe_add, zero_add]
          exact WithTop.coe_le_coe.2 (by omega)
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by omega)) hle
  conv_lhs => rw [← P.eraseLead_add_C_mul_X_pow]
  rw [map_add, HahnSeries.leadingCoeff_add_eq_right (htop_lead.1 ▸ herase_ord), htop_lead.2]

/-- The width-`n` cusp function of `j` is meromorphic at `0`. -/
private theorem meromorphicAt_cuspFunction_nat_j : MeromorphicAt (cuspFunction n j) 0 := by
  have han := TauCeti.analyticAt_cuspFunction_nat_mul one_ne_zero (NeZero.pos n)
    periodic_qParam_mul_j_comp_ofComplex analyticAt_cuspFunction_qParam_mul_j
  have hq : (fun τ : ℍ ↦ 𝕢 ((n : ℕ) * (1 : ℝ)) τ ^ n * j τ) = fun τ : ℍ ↦ 𝕢 1 τ * j τ := by
    ext τ
    rw [TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne n)]
  rw [← hq, mul_one] at han
  exact meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul (Nat.cast_pos.2 (NeZero.pos n)) han

/-- For `A ∈ reps n`, the width-`n` Laurent `q`-expansion of `j(A • τ)` has order `-a²` and leading
coefficient of norm `1`. -/
private theorem orderTop_and_norm_leadingCoeff_laurentQExpansion_j_toGLReal_smul
    {A : FixedDetMatrix (Fin 2) ℤ n} (hAr : A ∈ reps (n : ℤ)) :
    (UpperHalfPlane.laurentQExpansion n
      (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).orderTop =
        (-(repEntry A 0 0 ^ 2 : ℕ) : ℤ) ∧
    ‖(UpperHalfPlane.laurentQExpansion n
      (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
  let a := repEntry A 0 0
  let b := repEntry A 0 1
  let ζ := cexp (2 * π * I / n)
  let u : ℂˣ := Units.mk0 (ζ ^ (a * b)) (pow_ne_zero _ (Complex.exp_ne_zero _))
  have hJ_ord : (UpperHalfPlane.laurentQExpansion 1 j).orderTop = ((-1 : ℤ) : WithTop ℤ) :=
    orderTop_laurentQExpansion_j
  refine ⟨?_, ?_⟩
  · rw [laurentQExpansion_j_toGLReal_smul hAr]
    set d : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hAr) 2⟩
    have hd : (d : ℕ) = repEntry A 0 0 ^ 2 := rfl
    rw [LaurentSeries.orderTop_expand, HahnSeries.orderTop_twistEquiv, hJ_ord,
      ← WithTop.coe_nsmul, nsmul_eq_mul]
    exact WithTop.coe_inj.2 (by rw [hd]; ring)
  · rw [laurentQExpansion_j_toGLReal_smul hAr]
    set d : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (repEntry_zero_zero_pos hAr) 2⟩
    rw [LaurentSeries.leadingCoeff_expand]
    have htw_ord_top : (HahnSeries.twistEquiv (zpowersHom ℂˣ u)
        (UpperHalfPlane.laurentQExpansion 1 j)).orderTop = ((-1 : ℤ) : WithTop ℤ) :=
      (HahnSeries.orderTop_twistEquiv _ _).trans hJ_ord
    have htw_ne : HahnSeries.twistEquiv (zpowersHom ℂˣ u)
        (UpperHalfPlane.laurentQExpansion 1 j) ≠ 0 :=
      HahnSeries.orderTop_ne_top.1 (htw_ord_top.trans_ne WithTop.coe_ne_top)
    have htw_ord : (HahnSeries.twistEquiv (zpowersHom ℂˣ u)
        (UpperHalfPlane.laurentQExpansion 1 j)).order = -1 :=
      WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero htw_ne).trans htw_ord_top)
    rw [HahnSeries.leadingCoeff_eq, htw_ord, HahnSeries.coeff_twistEquiv,
      laurentQExpansion_j_coeff_neg_one, mul_one]
    have hζ_arg : 2 * (π : ℂ) * I / n = ↑(2 * π / (n : ℝ)) * I := by push_cast; ring
    have hζ1 : ‖ζ‖ = 1 := by dsimp only [ζ]; rw [hζ_arg, Complex.norm_exp_ofReal_mul_I]
    -- Expose the `Multiplicative ℤ` argument of `zpowersHom` before simplifying the unit power.
    change ‖((zpowersHom ℂˣ u (Multiplicative.ofAdd (-1 : ℤ)) : ℂˣ) : ℂ)‖ = 1
    rw [zpowersHom_apply, toAdd_ofAdd, _root_.zpow_neg, zpow_one, Units.val_inv_eq_inv_val,
      Units.val_mk0, norm_inv, norm_pow, hζ1, one_pow, inv_one]

/-- For non-square `n` and `A ∈ reps n`, the width-`n` Laurent `q`-expansion of `j - (j ∘ (A • ·))`
has leading coefficient of norm `1`. -/
private theorem norm_leadingCoeff_laurentQExpansion_j_sub_smul (hn : ¬ IsSquare n)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hAr : A ∈ reps (n : ℤ)) :
    ‖(UpperHalfPlane.laurentQExpansion n
      (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
  rw [UpperHalfPlane.laurentQExpansion_sub meromorphicAt_cuspFunction_nat_j
    (meromorphicAt_cuspFunction_j_toGLReal_smul hAr), sub_eq_add_neg]
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  have hexp_j := UpperHalfPlane.laurentQExpansion_pnat_mul periodic_j_comp_ofComplex
    meromorphicAt_cuspFunction_j d
  have hd_mul : ((d : ℕ) : ℝ) * 1 = n := mul_one _
  rw [hd_mul] at hexp_j
  have hJ_lc := (orderTop_and_leadingCoeff_laurentQExpansion_j_pow 1).2
  rw [pow_one] at hJ_lc
  have hord_j : (UpperHalfPlane.laurentQExpansion n j).orderTop = (-n : ℤ) := by
    rw [hexp_j, LaurentSeries.orderTop_expand, orderTop_laurentQExpansion_j]
    exact WithTop.coe_inj.2 (mul_neg_one _)
  have hlc_j : (UpperHalfPlane.laurentQExpansion n j).leadingCoeff = 1 := by
    rw [hexp_j, LaurentSeries.leadingCoeff_expand, hJ_lc]
  obtain ⟨hord_A, hnorm_A⟩ := orderTop_and_norm_leadingCoeff_laurentQExpansion_j_toGLReal_smul hAr
  have ha2_ne : repEntry A 0 0 ^ 2 ≠ n := fun hsq ↦ hn ⟨repEntry A 0 0, by rw [← sq, hsq]⟩
  rcases lt_or_gt_of_ne ha2_ne with hlt | hgt
  · have hlt' : (UpperHalfPlane.laurentQExpansion n j).orderTop <
        (-UpperHalfPlane.laurentQExpansion n
          fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).orderTop := by
      rw [HahnSeries.orderTop_neg, hord_j, hord_A]
      exact WithTop.coe_lt_coe.2 (by omega)
    rw [HahnSeries.leadingCoeff_add_eq_left hlt', hlc_j, norm_one]
  · have hgt' : (-UpperHalfPlane.laurentQExpansion n
          fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).orderTop <
        (UpperHalfPlane.laurentQExpansion n j).orderTop := by
      rw [HahnSeries.orderTop_neg, hord_j, hord_A]
      exact WithTop.coe_lt_coe.2 (by omega)
    rw [HahnSeries.leadingCoeff_add_eq_right hgt', HahnSeries.leadingCoeff_neg, norm_neg, hnorm_A]

/-- At width `n`, the Laurent `q`-expansion of `∏ A ∈ primitiveReps n, (j(τ) - j(A • τ))` has
leading coefficient of norm `1` whenever `n` is not a square. -/
private theorem norm_leadingCoeff_laurentQExpansion_diag_eq_one (hn : ¬ IsSquare n) :
    ‖(UpperHalfPlane.laurentQExpansion n
      (fun τ : ℍ ↦ aeval (j τ) (diagModularPolynomial n))).leadingCoeff‖ = 1 := by
  classical
  have hfun : (fun τ : ℍ ↦ aeval (j τ) (diagModularPolynomial n)) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
    ext τ
    rw [aeval_diagModularPolynomial, aevalAeval_j_modularPolynomial,
      cyclicIsogenyPolynomial_def, eval_prod, Finset.prod_apply]
    exact Finset.prod_congr rfl fun A _ ↦ by simp
  have hprod : ∀ s : Finset (FixedDetMatrix (Fin 2) ℤ n), (∀ A ∈ s, A ∈ reps (n : ℤ)) →
      MeromorphicAt (cuspFunction n
        (∏ A ∈ s, (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))) 0 ∧
      ‖(UpperHalfPlane.laurentQExpansion n
        (∏ A ∈ s, (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).leadingCoeff‖ = 1 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_const _, ?_⟩
      simp [HahnSeries.leadingCoeff_one]
    | @insert A s hAs ih =>
      have hAr := hs A (Finset.mem_insert_self A s)
      have hs' : ∀ B ∈ s, B ∈ reps (n : ℤ) := fun B hB ↦ hs B (Finset.mem_insert_of_mem hB)
      have hmA := UpperHalfPlane.meromorphicAt_cuspFunction_sub meromorphicAt_cuspFunction_nat_j
        (meromorphicAt_cuspFunction_j_toGLReal_smul hAr)
      rw [Finset.prod_insert hAs]
      refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_mul hmA (ih hs').1, ?_⟩
      rw [UpperHalfPlane.laurentQExpansion_mul hmA (ih hs').1, HahnSeries.leadingCoeff_mul,
        norm_mul, (ih hs').2, mul_one, norm_leadingCoeff_laurentQExpansion_j_sub_smul hn hAr]
  rw [hfun]
  exact (hprod _ fun _ hA ↦ (mem_primitiveReps.1 hA).1).2

/-- When `n` is not a square, `diagModularPolynomial n` is nonzero. -/
theorem diagModularPolynomial_ne_zero (hn : ¬ IsSquare n) :
    diagModularPolynomial n ≠ 0 := by
  intro h0
  have h := norm_leadingCoeff_laurentQExpansion_diag_eq_one hn
  simp [h0] at h

/-- **When `n` is not a square, the leading coefficient of `Φ_n(X, X)` is `±1`**, a unit in `ℤ`. -/
theorem isUnit_leadingCoeff_diagModularPolynomial (hn : ¬ IsSquare n) :
    IsUnit (diagModularPolynomial n).leadingCoeff := by
  set P := diagModularPolynomial n
  have hP : P ≠ 0 := diagModularPolynomial_ne_zero hn
  have hper : Periodic ((fun τ : ℍ ↦ aeval (j τ) P) ∘ ofComplex) 1 :=
    periodic_j_comp_ofComplex.comp fun z : ℂ ↦ aeval z P
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  have hexp := UpperHalfPlane.laurentQExpansion_pnat_mul hper
    (Polynomial.meromorphicAt_cuspFunction_aeval_j P) d
  have hd_mul : ((d : ℕ) : ℝ) * 1 = n := mul_one _
  rw [hd_mul] at hexp
  have hnorm := norm_leadingCoeff_laurentQExpansion_diag_eq_one hn
  rw [hexp, LaurentSeries.leadingCoeff_expand, leadingCoeff_laurentQExpansion_aeval_j hP,
    Complex.norm_intCast] at hnorm
  exact Int.isUnit_iff_abs_eq.2 (by exact_mod_cast hnorm)

/-- **Every root of `Φ_n(X, X)` for non-square `n` is an algebraic integer.** -/
theorem isIntegral_of_aeval_diagModularPolynomial_eq_zero {A : Type*} [CommRing A]
    (hn : ¬ IsSquare n) {x : A} (hx : aeval x (diagModularPolynomial n) = 0) :
    IsIntegral ℤ x := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_diagModularPolynomial hn
  have h := (integralClosure ℤ A).smul_mem
    (isIntegral_leadingCoeff_smul (diagModularPolynomial n) x hx) (↑u⁻¹ : ℤ)
  rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at h

/-- Dividing three integers `(a, b, c)` (`a ≠ 0`) by `g = gcd(a, gcd(b, c))` yields a triple with
an explicit Bézout relation `u * (a / g) + v * (b / g) + w * (c / g) = 1`. -/
private theorem exists_bezout_of_ediv_gcd {a b c : ℤ} (ha : a ≠ 0) :
    let g : ℕ := a.gcd (b.gcd c)
    ∃ u v w : ℤ, u * (a / g) + v * (b / g) + w * (c / g) = 1 := by
  let h : ℕ := b.gcd c
  let g : ℕ := a.gcd h
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.2 ha)
  have hda : (g : ℤ) * (a / g) = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a h)
  have hgh : (g : ℤ) ∣ (h : ℤ) := Int.gcd_dvd_right a h
  have hdb : (g : ℤ) * (b / g) = b := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_left b c))
  have hdc : (g : ℤ) * (c / g) = c := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_right b c))
  have h1 : (g : ℤ) = a * Int.gcdA a h + (h : ℤ) * Int.gcdB a h := Int.gcd_eq_gcd_ab a h
  have h2 : (h : ℤ) = b * Int.gcdA b c + c * Int.gcdB b c := Int.gcd_eq_gcd_ab b c
  refine ⟨Int.gcdA a h, Int.gcdB a h * Int.gcdA b c, Int.gcdB a h * Int.gcdB b c,
    mul_left_cancel₀ (Nat.cast_ne_zero.2 hg_pos.ne') ?_⟩
  linear_combination -h1 - Int.gcdB a h * h2 + Int.gcdA a h * hda +
    Int.gcdB a h * Int.gcdA b c * hdb + Int.gcdB a h * Int.gcdB b c * hdc

/-- Every integral quadratic relation `a τ² + b τ + c = 0` (`a ≠ 0`) for `τ ∈ ℍ` can be divided by
`±gcd(a, b, c)` to obtain a primitive relation with `a' > 0` and `4 a' c' - b'^2 > 0`. -/
private theorem exists_primitive_pos_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    ∃ a' b' c' : ℤ, 0 < a' ∧ (∃ u v w : ℤ, u * a' + v * b' + w * c' = 1) ∧
      0 < 4 * a' * c' - b' ^ 2 ∧ (a' : ℂ) * τ ^ 2 + b' * τ + c' = 0 := by
  wlog ha_pos : 0 < a generalizing a b c
  · exact @this (-a) (-b) (-c) (neg_ne_zero.2 ha) (by push_cast; linear_combination -hτ) (by omega)
  let h : ℕ := b.gcd c
  let g : ℕ := a.gcd h
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.2 ha)
  let a' := a / g; let b' := b / g; let c' := c / g
  have hda : (g : ℤ) * a' = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a h)
  have hgh : (g : ℤ) ∣ (h : ℤ) := Int.gcd_dvd_right a h
  have hdb : (g : ℤ) * b' = b := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_left b c))
  have hdc : (g : ℤ) * c' = c := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_right b c))
  have ha'_pos : 0 < a' := pos_of_mul_pos_right (hda.symm ▸ ha_pos) (by positivity)
  have hτ' : (a' : ℂ) * τ ^ 2 + b' * τ + c' = 0 := by
    have hmul : (g : ℂ) * ((a' : ℂ) * τ ^ 2 + b' * τ + c') = 0 := by
      have haC : (g : ℂ) * a' = a := by exact_mod_cast hda
      have hbC : (g : ℂ) * b' = b := by exact_mod_cast hdb
      have hcC : (g : ℂ) * c' = c := by exact_mod_cast hdc
      linear_combination hτ + τ ^ 2 * haC + τ * hbC + hcC
    exact (mul_eq_zero.1 hmul).resolve_left (Nat.cast_ne_zero.2 hg_pos.ne')
  have hD_pos : 0 < 4 * a' * c' - b' ^ 2 := by
    have him := congrArg Complex.im hτ'
    have hre := congrArg Complex.re hτ'
    simp only [sq, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, coe_re, coe_im, Complex.zero_im] at him
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero, coe_re, coe_im, Complex.zero_re] at hre
    have him_pos : 0 < τ.im := τ.im_pos
    have haR : (0 : ℝ) < a' := Int.cast_pos.2 ha'_pos
    have hlin : (2 * (a' : ℝ) * τ.re + b') * τ.im = 0 := by linarith
    have h2ab : 2 * (a' : ℝ) * τ.re + b' = 0 := (mul_eq_zero.1 hlin).resolve_right him_pos.ne'
    have hDR : (0 : ℝ) < ((4 * a' * c' - b' ^ 2 : ℤ) : ℝ) := by
      push_cast; nlinarith [mul_pos haR him_pos]
    exact Int.cast_pos.1 hDR
  exact ⟨a', b', c', ha'_pos, exists_bezout_of_ediv_gcd ha, hD_pos, hτ'⟩

/-- Every point `τ ∈ ℍ` satisfying a primitive equation `a' τ² + b' τ + c' = 0` (`a' > 0`) is fixed
by a primitive integral matrix of non-square positive determinant. -/
private theorem exists_primitive_fixedDetMatrix_nonsquare_fixing {τ : ℍ} {a' b' c' : ℤ}
    (hbez : ∃ u v w : ℤ, u * a' + v * b' + w * c' = 1) (hD_pos : 0 < 4 * a' * c' - b' ^ 2)
    (hτ' : (a' : ℂ) * τ ^ 2 + b' * τ + c' = 0) :
    ∃ (m : ℕ) (_ : NeZero m), ¬ IsSquare m ∧
      ∃ A : FixedDetMatrix (Fin 2) ℤ m,
        TauCeti.IsPrimitive A.1 ∧ toGLReal (NeZero.ne (m : ℤ)) A • τ = τ := by
  obtain ⟨u₀, v₀, w₀, hbez⟩ := hbez
  set D : ℤ := 4 * a' * c' - b' ^ 2
  set k : ℤ := |b'| + D
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![k - b', -c'; a', k]
  have h4det : 4 * M.det = (2 * k - b') ^ 2 + D := by simp only [M, det_fin_two_of, D]; ring
  have h2k : D < 2 * k - b' := by dsimp only [k]; linarith [le_abs_self b', abs_nonneg b']
  have hdet_pos : 0 < M.det := by nlinarith
  set m : ℕ := M.det.natAbs
  have hm_eq : (m : ℤ) = M.det := Int.natAbs_of_nonneg hdet_pos.le
  have : NeZero m := ⟨Int.natAbs_ne_zero.2 hdet_pos.ne'⟩
  refine ⟨m, inferInstance, ?_, ⟨M, hm_eq.symm⟩, ?_, ?_⟩
  · rintro ⟨r, hm_sq⟩
    have hm_r : M.det = (r : ℤ) * r := by rw [← hm_eq, hm_sq]; push_cast; rfl
    have hr1 : 2 * k - b' < 2 * (r : ℤ) := by nlinarith [hm_r]
    have hr2 : 2 * (r : ℤ) < 2 * k - b' + 1 := by nlinarith [hm_r]
    omega
  · let L : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] ℤ :=
      (-v₀) • (entryAddMonoidHom ℤ 0 0).toIntLinearMap +
        (-w₀) • (entryAddMonoidHom ℤ 0 1).toIntLinearMap +
        u₀ • (entryAddMonoidHom ℤ 1 0).toIntLinearMap +
        v₀ • (entryAddMonoidHom ℤ 1 1).toIntLinearMap
    refine isPrimitive_def.2 ⟨L, ?_⟩
    simp only [L, M, LinearMap.add_apply, LinearMap.smul_apply, AddMonoidHom.coe_toIntLinearMap,
      entryAddMonoidHom_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    linear_combination hbez
  · set A : FixedDetMatrix (Fin 2) ℤ m := ⟨M, hm_eq.symm⟩
    apply UpperHalfPlane.ext
    have hdet : 0 < (toGLReal (NeZero.ne (m : ℤ)) A).det.val := by
      rw [det_toGLReal]; exact_mod_cast Int.natAbs_pos.2 hdet_pos.ne'
    rw [coe_smul_of_det_pos hdet, div_eq_iff (denom_ne_zero _ τ),
      UpperHalfPlane.num, UpperHalfPlane.denom]
    have h00 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (k : ℝ) - b' := by
      rw [toGLReal_apply]; simp [A, M]
    have h01 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(c' : ℝ) := by
      rw [toGLReal_apply]; simp [A, M]
    have h10 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (a' : ℝ) := by
      rw [toGLReal_apply]; simp [A, M]
    have h11 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (k : ℝ) := by
      rw [toGLReal_apply]; simp [A, M]
    rw [h00, h01, h10, h11]
    push_cast
    linear_combination -hτ'

/-- **Integrality of `j` at imaginary quadratic points.** If `τ ∈ ℍ` satisfies an integral quadratic
equation `a τ² + b τ + c = 0` with `a ≠ 0`, then `j(τ)` is integral over `ℤ`. -/
theorem isIntegral_j_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) : IsIntegral ℤ (j τ) := by
  obtain ⟨a', b', c', -, hbez, hD_pos, hτ'⟩ := exists_primitive_pos_quadratic ha hτ
  obtain ⟨m, _, hm_nsq, A, hA_prim, hfix⟩ :=
    exists_primitive_fixedDetMatrix_nonsquare_fixing hbez hD_pos hτ'
  exact isIntegral_of_aeval_diagModularPolynomial_eq_zero hm_nsq
    ((aeval_j_diagModularPolynomial_eq_zero_iff τ).2 ⟨A, hA_prim, hfix⟩)

end DiagonalAndCM

end TauCeti.ModularForm
