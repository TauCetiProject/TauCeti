/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Bivariate
public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
public import TauCeti.RingTheory.HahnSeries.Twist
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import TauCeti.NumberTheory.ModularForms.QExpansion.Order
import TauCeti.RingTheory.HahnSeries.Map

/-!
# The classical modular polynomial

For a positive integer `n`, the polynomial `cyclicIsogenyPolynomial n j τ` of
`TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial` is the monic polynomial

  `∏_{(a b; 0 d)} (Y - j((a τ + b) / d))`

over the primitive upper-triangular integral matrices `(a b; 0 d)` of determinant `n` with
`0 ≤ b < d` (`FixedDetMatrices.primitiveReps n`). Its coefficients are holomorphic and
`SL(2, ℤ)`-invariant on the upper half-plane. This file proves that each coefficient is a
polynomial in `j(τ)` with **integer** coefficients and assembles the classical **modular
polynomial** `Φ_n(X, Y) : ℤ[X][Y]` (`TauCeti.ModularForm.modularPolynomial`).

The integrality of the coefficients of `Φ_n` is proved from the `q`-expansions of the factors at
width `n`. Writing `q_n = e^{2π i τ / n}` and `ζ_n = e^{2π i / n}`, the local parameter at
`(a τ + b) / d` (with `a d = n`) is `ζ_n^{a b} q_n^{a²}`, so the width-`n` Laurent `q`-expansion
of `j((a τ + b) / d)` is obtained from the integral Laurent `q`-expansion of `j` by twisting by
`ζ_n^{a b}` and substituting `X ↦ X^{a²}` (`laurentQExpansion_j_toGLReal_smul`). Its coefficients
lie in the ring of integers of the cyclotomic field `ℚ(ζ_n)`. Every automorphism
`σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends `ζ_n ↦ ζ_n^k` for a unit `k` modulo `n`, and
`(a, b, d) ↦ (a, k b mod d, d)` permutes `FixedDetMatrices.primitiveReps n`, so `σ` fixes all
Laurent `q`-coefficients of the symmetric functions of the `j((a τ + b) / d)`. Being both rational
and integral over `ℤ`, those coefficients are integers, and `TauCeti.ModularForm.exists_aeval_j_eq`
expresses each coefficient as a unique polynomial in `j` over `ℤ`.

## Main definitions

* `TauCeti.ModularForm.modularPolynomial n`: the classical modular polynomial `Φ_n ∈ ℤ[X][Y]`,
  characterized by `(modularPolynomial n).map (aeval (j τ)) = cyclicIsogenyPolynomial n j τ`.

## Main results

* `TauCeti.ModularForm.laurentQExpansion_j_toGLReal_smul`: the width-`n` Laurent `q`-expansion of
  `j(A • τ)` for `A ∈ reps n`.
* `TauCeti.ModularForm.modularPolynomial_one`: `Φ_1(X, Y) = Y - X`.
* `TauCeti.ModularForm.aevalAeval_j_modularPolynomial`: evaluating `Φ_n(X, Y)` at `(j(τ), w)` gives
  `(cyclicIsogenyPolynomial n j τ).eval w`.
* `TauCeti.ModularForm.aevalAeval_j_modularPolynomial_eq_zero_iff`: `Φ_n(j(τ), j(τ')) = 0` holds
  exactly when `τ' = A • τ` for some primitive integral matrix `A` of determinant `n`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C (the modular equation and
  its integer coefficients).
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §2 (the modular equation).
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
  simp [toGLReal_apply, hmat]

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

/-- For `A ∈ reps n`, `τ ↦ j (A • τ)` has a meromorphic width-`n` cusp function at `0`. -/
theorem meromorphicAt_cuspFunction_j_toGLReal_smul {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    MeromorphicAt (cuspFunction n fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
  UpperHalfPlane.meromorphicAt_cuspFunction_qParam_pow_mul_iff.1
    (analyticAt_cuspFunction_qParam_pow_mul_j_toGLReal_smul hA).meromorphicAt

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

/-- **Width-`n` Laurent `q`-expansion of `j(A • τ)`.** For `A = !![a, b; 0, d] ∈ reps n`, the
width-`n` Laurent `q`-expansion of `j(A • τ)` is the width-one expansion of `j` twisted by
`ζ_n^{a b}` and expanded by `X ↦ X^{a²}`. -/
theorem laurentQExpansion_j_toGLReal_smul {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    UpperHalfPlane.laurentQExpansion n (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ
        (⟨(A.1 0 0).natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hA.2.1.ne') 2⟩ : ℕ+)
        (HahnSeries.twistEquiv
          (zpowersHom ℂˣ (Units.mk0
            (cexp (2 * π * I / n) ^ ((A.1 0 0).natAbs * (A.1 0 1).natAbs))
            (pow_ne_zero _ (Complex.exp_ne_zero _))))
          (UpperHalfPlane.laurentQExpansion 1 j)) := by
  have ha : 0 < repEntry A 0 0 := Int.natAbs_pos.2 hA.2.1.ne'
  let a := repEntry A 0 0
  set d : ℕ+ := ⟨(A.1 0 0).natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hA.2.1.ne') 2⟩
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
      simp [repEntry, zpowersHom_apply, Units.val_zpow_eq_zpow_val]
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

/-- Every coefficient of `cyclicIsogenyPolynomial n j` has a meromorphic width-one cusp function at
`q = 0`. -/
private theorem meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j (k : ℕ) :
    MeromorphicAt (cuspFunction 1 fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) 0 := by
  set M := (primitiveReps (n : ℤ)).card
  refine (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_pow_mul_iff (k := n * M)).1
    (AnalyticAt.meromorphicAt ?_)
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
      rw [pow_mul, cyclicIsogenyPolynomial_def, ← coeff_C_mul, C_pow,
        Finset.pow_card_mul_prod]
      simp only [mul_sub, ← C_mul]
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

open scoped Classical in
/-- A unit `u : (ZMod n)ˣ` acts on `primitiveReps n` by multiplying the upper-right residue `b` of
`(a b; 0 d)` modulo `d`. -/
private def scaleRep (u : (ZMod n)ˣ) (A : FixedDetMatrix (Fin 2) ℤ n) :
    FixedDetMatrix (Fin 2) ℤ n :=
  if hA : A ∈ reps (n : ℤ) then
    ⟨!![(repEntry A 0 0 : ℤ), (((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1 : ℕ) : ℤ);
        0, (repEntry A 1 1 : ℤ)],
      by simp [det_fin_two_of, ← Nat.cast_mul, (mem_reps_nat_entries hA).2.2.1]⟩
  else A

open scoped Classical in
/-- For `A ∈ reps n`, the underlying matrix of `scaleRep u A` has upper-right entry
`(u.val * b) % d`. -/
private theorem val_scaleRep_of_mem_reps (u : (ZMod n)ˣ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    (scaleRep u A).1 =
      !![(repEntry A 0 0 : ℤ), (((u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1 : ℕ) : ℤ);
          0, (repEntry A 1 1 : ℤ)] :=
  congrArg Subtype.val (dite_eq_left hA : scaleRep u A = _)

/-- `scaleRep u A` lies in `reps n` whenever `A` does, with upper-right entry `(u.val * b) % d`. -/
private theorem scaleRep_mem_reps_and_entries (u : (ZMod n)ˣ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) :
    scaleRep u A ∈ reps (n : ℤ) ∧
      repEntry (scaleRep u A) 0 0 = repEntry A 0 0 ∧
      repEntry (scaleRep u A) 1 1 = repEntry A 1 1 ∧
      repEntry (scaleRep u A) 0 1 = (u : ZMod n).val * repEntry A 0 1 % repEntry A 1 1 := by
  obtain ⟨ha, hd, -, -, -⟩ := mem_reps_nat_entries hA
  have hcoe := val_scaleRep_of_mem_reps u hA
  refine ⟨⟨by simp [hcoe], by simp [hcoe, ha], hcoe ▸ Nat.cast_nonneg _, ?_⟩,
    by rw [repEntry, hcoe]; simp, by rw [repEntry, hcoe]; simp, ?_⟩
  · rw [hcoe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    exact Int.ofNat_lt.2 (Nat.mod_lt _ hd)
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
  refine Finset.eq_of_subset_of_card_le (fun B hB ↦ ?_) ?_
  · obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
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
      (⟨repEntry A 0 0 ^ 2, pow_pos (Int.natAbs_pos.2 hA.2.1.ne') 2⟩ : ℕ+)
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
  dsimp only [repEntry]
  set d : ℕ+ := ⟨(A.1 0 0).natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hA.2.1.ne') 2⟩
  ext g
  by_cases hdvd : (d : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [HahnSeries.coeff_mapRingHom, LaurentSeries.coeff_expand_mul, LaurentSeries.coeff_expand_mul,
      HahnSeries.coeff_twistEquiv, HahnSeries.coeff_twistEquiv,
      HahnSeries.coeff_mapRingHom, HahnSeries.coeff_mapRingHom]
    simp only [zpowersHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul, map_zpow₀]
    simp [zetaCyclotomic]
  · simp [LaurentSeries.coeff_expand_of_not_dvd d _ hdvd]

/-- Every coefficient of `repLaurentSeries A` is integral over `ℤ`. -/
private theorem repLaurentSeries_coeff_isIntegral {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (g : ℤ) :
    IsIntegral ℤ ((repLaurentSeries A).coeff g) := by
  rw [repLaurentSeries, dite_eq_left_of_eq_true (eq_true hA)]
  set d : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (Int.natAbs_pos.2 hA.2.1.ne') 2⟩
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
  set dA : ℕ+ := ⟨repEntry A 0 0 ^ 2, pow_pos (Int.natAbs_pos.2 hA.2.1.ne') 2⟩
  set dB : ℕ+ := ⟨repEntry (scaleRep u A) 0 0 ^ 2, pow_pos (Int.natAbs_pos.2 hBr.2.1.ne') 2⟩
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

-- Not `@[simp]`: `Polynomial.aevalAeval` is an `abbrev` unfolded by
-- `Polynomial.aevalAevalEquiv_apply_apply`, so `@[simp]` fails `simpNF`.
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

end TauCeti.ModularForm
