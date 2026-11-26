/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Bivariate
public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.NumberTheory.ModularForms.LevelOne.IsogenyQExpansion
import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
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
of `j((a τ + b) / d)` (`TauCeti.ModularForm.laurentQExpansion_j_toGLReal_smul`) is obtained from
the integral Laurent `q`-expansion of `j` (`TauCeti.ModularForm.laurentQExpansion_j_mem_map_rangeS`)
by rescaling by `ζ_n^{a b}` and substituting `X ↦ X^{a²}`. Its coefficients lie in the ring of
integers of the cyclotomic field `ℚ(ζ_n)`. Every automorphism `σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends
`ζ_n ↦ ζ_n^k` for a unit `k` modulo `n`, and `FixedDetMatrices.scaleRep k`
(`(a, b, d) ↦ (a, k b mod d, d)`) permutes `FixedDetMatrices.primitiveReps n`, so `σ` fixes all
Laurent `q`-coefficients of the symmetric functions of the `j((a τ + b) / d)`. Being both rational
and integral over `ℤ`, those coefficients are integers, and
`TauCeti.ModularForm.exists_aeval_j_eq` expresses each coefficient as a unique polynomial in `j`
over `ℤ`.

## Main definitions

* `TauCeti.ModularForm.modularPolynomial n`: the classical modular polynomial `Φ_n ∈ ℤ[X][Y]`,
  characterized by `(modularPolynomial n).map (aeval (j τ)) = cyclicIsogenyPolynomial n j τ`.

## Main results

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

open Complex Function Matrix Polynomial
open UpperHalfPlane hiding I
open scoped MatrixGroups Polynomial.Bivariate Real

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

open FixedDetMatrices

/-! ### Meromorphy at `i∞` and width-`n` expansion of `cyclicIsogenyPolynomial n j` -/

section CyclicExpansion

variable {n : ℕ} [NeZero n]

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

/-- Every coefficient of `cyclicIsogenyPolynomial n j` has a meromorphic width-one cusp function at
`q = 0`. -/
private theorem meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j (k : ℕ) :
    MeromorphicAt (cuspFunction 1 fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) 0 := by
  have hper : Periodic ((fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← UpperHalfPlane.modular_T_smul]
      exact congrArg (fun p : ℂ[X] ↦ p.coeff k) (cyclicIsogenyPolynomial_smul j_smul_SL2Z _ τ)
  refine TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_pnat_mul one_pos hper
    (mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k) ⟨n, NeZero.pos n⟩ ?_
  simp only [PNat.mk_coe, mul_one, cyclicIsogenyPolynomial_def]
  exact (meromorphicAt_and_laurentQExpansion_coeff_prod_X_sub_C _
    (fun _ hA ↦ (mem_primitiveReps.1 hA).1) k).1

end CyclicExpansion

/-! ### Cyclotomic Galois descent of the `q`-expansion coefficients -/

section GaloisDescent

variable {n : ℕ} [NeZero n]

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
  if A ∈ reps (n : ℤ) then
    LaurentSeries.expand (cyclotomicSubfield n) ((A.val 0 0).natAbs ^ 2).toPNat'
      (TauCeti.LaurentSeries.rescale
        (Units.mk0 (zetaCyclotomic n ^ ((A.val 0 0).natAbs * (A.val 0 1).natAbs))
          (pow_ne_zero _ (isPrimitiveRoot_zetaCyclotomic.ne_zero (NeZero.ne n))))
        (HahnSeries.mapRingHom (Int.castRingHom (cyclotomicSubfield n))
          (laurentQExpansion_j_mem_map_rangeS (Int.castRingHom ℂ)).choose))
  else 0

/-- Under `cyclotomicSubfield n → ℂ`, `repLaurentSeries A` maps to the width-`n` Laurent
`q`-expansion of `j (A • τ)`. -/
private theorem map_val_repLaurentSeries {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    HahnSeries.mapRingHom (cyclotomicSubfield n).val.toRingHom (repLaurentSeries A) =
      UpperHalfPlane.laurentQExpansion n (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  have hd : 0 < (A.val 1 1).natAbs := Int.natAbs_pos.2 (apply_one_one_ne_zero_of_mem_reps hA)
  have had : (A.val 0 0).natAbs * (A.val 1 1).natAbs = n :=
    (natAbs_apply_zero_zero_mul_natAbs_apply_one_one hA.1).trans (Int.natAbs_natCast n)
  have hq : 𝕢 1 ((A.val 0 1 / A.val 1 1 : ℝ) : ℂ) =
      cexp (2 * π * I / n) ^ ((A.val 0 0).natAbs * (A.val 0 1).natAbs) := by
    have hbZ : A.val 0 1 = ((A.val 0 1).natAbs : ℤ) := (Int.natAbs_of_nonneg hA.2.2.1).symm
    have hdZ : A.val 1 1 = ((A.val 1 1).natAbs : ℤ) :=
      (Int.natAbs_of_nonneg
        (pos_val_one_one_of_mem_reps (Int.natCast_pos.2 (NeZero.pos n)) hA).le).symm
    have hd0 : ((A.val 1 1).natAbs : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    have hadC : ((A.val 0 0).natAbs : ℂ) * (A.val 1 1).natAbs = n := by exact_mod_cast had
    rw [hbZ, hdZ]
    simp only [Function.Periodic.qParam, Int.cast_natCast, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_natCast, div_one, ← Complex.exp_natCast_mul]
    congr 1
    push_cast
    field_simp
    rw [← hadC, Int.natAbs_abs]
    ring
  simp only [repLaurentSeries, hA, ↓reduceIte]
  rw [laurentQExpansion_j_toGLReal_smul hA]
  conv_rhs => rw [← (laurentQExpansion_j_mem_map_rangeS (Int.castRingHom ℂ)).choose_spec]
  set d : ℕ+ := ((A.val 0 0).natAbs ^ 2).toPNat'
  ext g
  by_cases hdvd : (d : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [HahnSeries.coeff_mapRingHom, LaurentSeries.coeff_expand_mul, LaurentSeries.coeff_expand_mul,
      TauCeti.LaurentSeries.coeff_rescale, TauCeti.LaurentSeries.coeff_rescale,
      HahnSeries.coeff_mapRingHom, HahnSeries.coeff_mapRingHom]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul, map_zpow₀, hq]
    simp [zetaCyclotomic]
  · simp [LaurentSeries.coeff_expand_of_not_dvd d _ hdvd]

/-- Every coefficient of `repLaurentSeries A` is integral over `ℤ`. -/
private theorem repLaurentSeries_coeff_isIntegral {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps (n : ℤ)) (g : ℤ) :
    IsIntegral ℤ ((repLaurentSeries A).coeff g) := by
  simp only [repLaurentSeries, hA, ↓reduceIte]
  set d : ℕ+ := ((A.val 0 0).natAbs ^ 2).toPNat'
  by_cases hdvd : (d : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [LaurentSeries.coeff_expand_mul, TauCeti.LaurentSeries.coeff_rescale,
      HahnSeries.coeff_mapRingHom]
    have hζ : IsPrimitiveRoot (zetaCyclotomic n) n := isPrimitiveRoot_zetaCyclotomic
    have hζ_int : IsIntegral ℤ (zetaCyclotomic n) := hζ.isIntegral (NeZero.pos n)
    have hζ_inv : IsIntegral ℤ (zetaCyclotomic n)⁻¹ := by
      have h1 : zetaCyclotomic n * zetaCyclotomic n ^ (n - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos n), hζ.pow_eq_one]
      rw [inv_eq_of_mul_eq_one_right h1]
      exact hζ_int.pow _
    have hzpow : IsIntegral ℤ
        (((Units.mk0 (zetaCyclotomic n ^ ((A.val 0 0).natAbs * (A.val 0 1).natAbs))
          (pow_ne_zero _ (hζ.ne_zero (NeZero.ne n))) ^ r : (cyclotomicSubfield n)ˣ) :
          cyclotomicSubfield n)) := by
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
      cases r with
      | ofNat l => simpa using (hζ_int.pow _).pow l
      | negSucc l =>
        rw [zpow_negSucc, ← inv_pow, ← inv_pow]
        exact (hζ_inv.pow _).pow (l + 1)
    have hint : IsIntegral ℤ
        ((((laurentQExpansion_j_mem_map_rangeS (Int.castRingHom ℂ)).choose.coeff r : ℤ) :
          cyclotomicSubfield n)) :=
      intCast_mem (integralClosure ℤ (cyclotomicSubfield n)) _
    exact hzpow.mul hint
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
  have hBr : scaleRep u A ∈ reps (n : ℤ) := (scaleRep_mem_reps_iff u A).2 hA
  have had : (A.val 0 0).natAbs * (A.val 1 1).natAbs = n :=
    (natAbs_apply_zero_zero_mul_natAbs_apply_one_one hA.1).trans (Int.natAbs_natCast n)
  have hbB : ((scaleRep u A).val 0 1).natAbs =
      (u : ZMod n).val * (A.val 0 1).natAbs % (A.val 1 1).natAbs :=
    natAbs_scaleRep_apply_zero_one_of_mem_reps u hA
  have hpow : σ (zetaCyclotomic n ^ ((A.val 0 0).natAbs * (A.val 0 1).natAbs)) =
      zetaCyclotomic n ^ (((scaleRep u A).val 0 0).natAbs * ((scaleRep u A).val 0 1).natAbs) := by
    rw [scaleRep_apply_zero_zero, map_pow, ← hζ.autToPow_spec ℚ σ, ← pow_mul, hbB]
    set q := (u : ZMod n).val * (A.val 0 1).natAbs / (A.val 1 1).natAbs
    have hdiv := Nat.mod_add_div ((u : ZMod n).val * (A.val 0 1).natAbs) (A.val 1 1).natAbs
    have hexp : (u : ZMod n).val * ((A.val 0 0).natAbs * (A.val 0 1).natAbs) =
        (A.val 0 0).natAbs *
          ((u : ZMod n).val * (A.val 0 1).natAbs % (A.val 1 1).natAbs) + n * q := by
      calc (u : ZMod n).val * ((A.val 0 0).natAbs * (A.val 0 1).natAbs)
          = (A.val 0 0).natAbs * ((u : ZMod n).val * (A.val 0 1).natAbs) := by ring
        _ = (A.val 0 0).natAbs *
              (((u : ZMod n).val * (A.val 0 1).natAbs % (A.val 1 1).natAbs) +
                (A.val 1 1).natAbs * q) := by rw [hdiv]
        _ = _ := by rw [mul_add, ← mul_assoc, had]
    have hnq : zetaCyclotomic n ^ (n * q) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    rw [hexp, pow_add, hnq, mul_one]
  ext g
  simp only [repLaurentSeries, hA, hBr, ↓reduceIte, HahnSeries.coeff_mapRingHom]
  set dA : ℕ+ := ((A.val 0 0).natAbs ^ 2).toPNat'
  set dB : ℕ+ := (((scaleRep u A).val 0 0).natAbs ^ 2).toPNat'
  have hdAB : dA = dB := by simp [dA, dB]
  by_cases hdvd : (dA : ℤ) ∣ g
  · obtain ⟨r, rfl⟩ := hdvd
    rw [LaurentSeries.coeff_expand_mul, hdAB, LaurentSeries.coeff_expand_mul]
    simp [TauCeti.LaurentSeries.coeff_rescale, Units.val_zpow_eq_zpow_val, hpow]
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
    ← Finset.prod_image (f := fun A ↦ X - C (repLaurentSeries A))
      (scaleRep_injective (isPrimitiveRoot_zetaCyclotomic.autToPow ℚ σ)).injOn,
    image_scaleRep_primitiveReps]

/-- Every width-one Laurent `q`-coefficient of `(cyclicIsogenyPolynomial n j ·).coeff k` is an
integer. -/
private theorem laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_int (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion 1
      (fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m ∈
      (algebraMap ℤ ℂ).range := by
  let K := cyclotomicSubfield n
  have hζ : IsPrimitiveRoot (cexp (2 * π * I / n)) n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  have : IsCyclotomicExtension {n} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finite_of_singleton n ℚ K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  set PK : (LaurentSeries K)[X] := ∏ A ∈ primitiveReps (n : ℤ), (X - C (repLaurentSeries A))
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  set x : K := (PK.coeff k).coeff ((d : ℤ) * m)
  have hx_fixed : ∀ σ : K ≃ₐ[ℚ] K, σ x = x := fun σ ↦ by
    simpa [x, coeff_map] using
      congrArg (fun p : (LaurentSeries K)[X] ↦ (p.coeff k).coeff ((d : ℤ) * m))
        (map_gal_prod_repLaurentSeries (n := n) σ)
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) x).2 hx_fixed
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
    · obtain ⟨⟨h10, h00, -, h11⟩, -⟩ := mem_primitiveReps.1 hA
      exact (reps_one_id A h10 h00 h11).trans
        (by ext i j; fin_cases i <;> fin_cases j <;> simp [I₁])
    · subst h
      exact mem_primitiveReps.2 ⟨hI₁_reps,
        isPrimitive_def.2 ⟨(entryAddMonoidHom ℤ 0 0).toIntLinearMap, by simp [I₁]⟩⟩
  have hsmul : toGLReal (NeZero.ne ((1 : ℕ) : ℤ)) I₁ • τ = τ := by
    rw [toGLReal_smul_eq_vadd_smul one_pos hI₁_reps]
    apply UpperHalfPlane.ext
    rw [coe_vadd, coe_pos_real_smul, coe_repsScale]
    simp [I₁]
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
    (hA : TauCeti.IsPrimitive A.val) (τ : ℍ) :
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
        TauCeti.IsPrimitive A.val ∧ toGLReal (NeZero.ne (n : ℤ)) A • τ = τ' := by
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
