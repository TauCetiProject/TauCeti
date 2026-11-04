/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.LevelOne.Invariant
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.RingTheory.HahnSeries.Map

/-!
# Weakly holomorphic level-one modular functions are polynomials in `j`

A *weakly holomorphic modular function* of level one is a holomorphic function `f` on the upper
half-plane, invariant under `SL₂(ℤ)`, that is meromorphic at `i∞`: its cusp function, the function
of `q = e^{2πiτ}` attached to `f`, is meromorphic at `q = 0`, so `f` has a Laurent `q`-expansion
`∑ₙ aₙ qⁿ` with finitely many negative powers of `q`. This file proves that these functions are
exactly the polynomials in the modular invariant `j`, and that the polynomial has coefficients in
a subring as soon as the *principal part and constant term* `aₙ`, `n ≤ 0`, of `f` do.

More precisely, for a commutative ring `R` with `Algebra R ℂ`, a holomorphic `SL₂(ℤ)`-invariant
function `f` meromorphic at `i∞` whose coefficients `aₙ`, `n ≤ 0`, lie in the image of `R` is
`P(j)` for a polynomial `P` over `R`, of degree at most the order of the pole of `f` at `i∞`.
Conversely every `P(j)` is such a function, and all of its Laurent `q`-coefficients lie in the
image of `R`, because the Laurent `q`-expansion of `j = q⁻¹ + 744 + 196884 q + ⋯` has integer
coefficients. When `R → ℂ` is injective the polynomial is unique, since `j` takes infinitely many
values (`TauCeti.ModularForm.infinite_range_j`). In particular, the Laurent `q`-expansion of a
weakly holomorphic modular function is integral as soon as its principal part and constant term
are: this is the integral `q`-expansion principle in level one. It is the form in which symmetric
functions of the values of `j` along finite orbits, such as the coefficients of modular
polynomials, are recognised as integral polynomials in `j`.

The proof is by induction on the order `N` of the pole at `i∞`. If `N = 0` the cusp function is
analytic at `0`, so `f` has a limit at `i∞` and is constant
(`TauCeti.ModularForm.levelOne_eq_of_tendsto_atImInfty`). Otherwise, with `c = a_{-N}` the leading
coefficient of `f`, the function `f - c jᴺ` is again a weakly holomorphic modular function, with a
pole of order less than `N`, because `jᴺ` has Laurent expansion `q⁻ᴺ + ⋯`; its principal part and
constant term stay in the image of `R` because those of `jᴺ` are integers.

## Main results

* `TauCeti.ModularForm.laurentQExpansion_aeval_j`: the Laurent `q`-expansion of `P(j)` is `P`
  evaluated at the Laurent `q`-expansion of `j`.
* `TauCeti.ModularForm.laurentQExpansion_aeval_j_coeff_mem`: the Laurent `q`-coefficients of
  `P(j)` lie in the image of `R`.
* `TauCeti.ModularForm.exists_natDegree_le_and_aeval_j_eq`: a weakly holomorphic modular function
  with a pole of order at most `N` at `i∞` and principal part and constant term in the image of
  `R` is `P(j)` for some `P ∈ R[X]` of degree at most `N`.
* `TauCeti.ModularForm.exists_aeval_j_eq_iff`: a function on the upper half-plane is a polynomial
  in `j` over `R` exactly when it is a weakly holomorphic modular function whose principal part
  and constant term lie in the image of `R`.
* `TauCeti.ModularForm.laurentQExpansion_coeff_mem_of_coeff_mem`: the integral `q`-expansion
  principle.
* `TauCeti.ModularForm.aeval_j_injective`: the polynomial is unique when `R → ℂ` is injective.

## References

* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.3.3 (the modular invariant and the modular functions of weight zero).
* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.A (holomorphic modular
  functions as polynomials in `j`) and §11.C (the integral version, for the modular equation).
-/

public section

open Polynomial UpperHalfPlane Filter Topology
open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-! ### Polynomials in `j` -/

/-- A polynomial in `j` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_aeval_j (P : R[X]) : MDiff fun τ : ℍ ↦ aeval (j τ) P :=
  P.differentiable_aeval.mdifferentiable.comp j_mdifferentiable

private theorem aeval_j_add (p q : R[X]) :
    (fun τ : ℍ ↦ aeval (j τ) (p + q)) = (fun τ ↦ aeval (j τ) p) + fun τ ↦ aeval (j τ) q := by
  ext τ
  simp

private theorem aeval_j_monomial (n : ℕ) (a : R) :
    (fun τ : ℍ ↦ aeval (j τ) (monomial n a)) = (fun _ ↦ algebraMap R ℂ a) * j ^ n := by
  ext τ
  simp [aeval_monomial]

/-- The cusp function of a polynomial in `j` is meromorphic at `q = 0`. -/
theorem meromorphicAt_cuspFunction_aeval_j (P : R[X]) :
    MeromorphicAt (cuspFunction 1 fun τ : ℍ ↦ aeval (j τ) P) 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [aeval_j_add]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_add hp hq
  | monomial n a =>
    rw [aeval_j_monomial]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_mul
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_pow meromorphicAt_cuspFunction_j n)

/-- **The Laurent `q`-expansion of a polynomial in `j`** is the polynomial evaluated at the
Laurent `q`-expansion of `j`, its coefficients being mapped to constant Laurent series. -/
theorem laurentQExpansion_aeval_j (P : R[X]) :
    UpperHalfPlane.laurentQExpansion 1 (fun τ ↦ aeval (j τ) P) =
      eval₂ (HahnSeries.C.comp (algebraMap R ℂ)) (UpperHalfPlane.laurentQExpansion 1 j) P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [aeval_j_add, UpperHalfPlane.laurentQExpansion_add one_pos
      (meromorphicAt_cuspFunction_aeval_j p) (meromorphicAt_cuspFunction_aeval_j q), hp, hq,
      eval₂_add]
  | monomial n a =>
    rw [aeval_j_monomial, UpperHalfPlane.laurentQExpansion_mul one_pos
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_pow meromorphicAt_cuspFunction_j n),
      UpperHalfPlane.laurentQExpansion_pow one_pos meromorphicAt_cuspFunction_j,
      UpperHalfPlane.laurentQExpansion_const, eval₂_monomial, RingHom.comp_apply]

/-- The Laurent `q`-coefficients of the powers of `j` are integers. -/
private theorem exists_laurentQExpansion_j_pow_coeff_eq_intCast (k : ℕ) (n : ℤ) :
    ∃ m : ℤ, (UpperHalfPlane.laurentQExpansion 1 j ^ k).coeff n = m := by
  have hj : UpperHalfPlane.laurentQExpansion 1 j ∈
      (HahnSeries.mapRingHom (Int.castRingHom ℂ) : LaurentSeries ℤ →+* LaurentSeries ℂ).rangeS :=
    HahnSeries.mem_map_rangeS.mpr fun g ↦ by
      obtain ⟨m, hm⟩ := exists_laurentQExpansion_j_coeff_eq_intCast g
      exact ⟨m, hm.symm⟩
  obtain ⟨m, hm⟩ := HahnSeries.mem_map_rangeS.mp (pow_mem hj k) n
  exact ⟨m, hm.symm⟩

/-- **The Laurent `q`-coefficients of a polynomial in `j` over `R` lie in the image of `R`**, as
those of `j` are integers. -/
theorem laurentQExpansion_aeval_j_coeff_mem (P : R[X]) (n : ℤ) :
    (UpperHalfPlane.laurentQExpansion 1 (fun τ ↦ aeval (j τ) P)).coeff n ∈
      (algebraMap R ℂ).range := by
  rw [laurentQExpansion_aeval_j]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, HahnSeries.coeff_add]
    exact add_mem hp hq
  | monomial k a =>
    obtain ⟨m, hm⟩ := exists_laurentQExpansion_j_pow_coeff_eq_intCast k n
    rw [eval₂_monomial, RingHom.comp_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hm,
      smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ ⟨m, map_intCast _ m⟩

/-! ### The leading term of `jᴺ` -/

/-- The Laurent `q`-expansion of `jᴺ` is `q⁻ᴺ` times a power series with constant term `1`. -/
private theorem laurentQExpansion_j_pow_coeff (N : ℕ) (n : ℤ) :
    (UpperHalfPlane.laurentQExpansion 1 j ^ N).coeff n =
      if n + N < 0 then 0
      else ((qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ * j τ) ^ N).coeff (n + N).natAbs := by
  rw [laurentQExpansion_j, mul_pow, HahnSeries.single_pow, one_pow, ← map_pow,
    HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  simp [sub_eq_add_neg]

/-- The Laurent `q`-expansion of `jᴺ` vanishes below `q⁻ᴺ`. -/
private theorem laurentQExpansion_j_pow_coeff_of_lt (N : ℕ) {n : ℤ} (hn : n < -N) :
    (UpperHalfPlane.laurentQExpansion 1 j ^ N).coeff n = 0 := by
  simp [laurentQExpansion_j_pow_coeff, show n + N < 0 by omega]

/-- The leading Laurent `q`-coefficient of `jᴺ` is `1`, the coefficient of `q⁻ᴺ`. -/
private theorem laurentQExpansion_j_pow_coeff_neg (N : ℕ) :
    (UpperHalfPlane.laurentQExpansion 1 j ^ N).coeff (-N) = 1 := by
  rw [laurentQExpansion_j_pow_coeff, neg_add_cancel]
  simp only [lt_self_iff_false, ↓reduceIte, Int.natAbs_zero]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, qExpansion_qParam_mul_j_coeff_zero, one_pow]

/-! ### Weakly holomorphic modular functions -/

/-- A weakly holomorphic modular function without a pole at `i∞` is constant: its cusp function is
analytic at `0`, so it has a limit at `i∞`. -/
private theorem eq_laurentQExpansion_coeff_zero {f : ℍ → ℂ} (hf : MDiff f)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hmer : MeromorphicAt (cuspFunction 1 f) 0)
    (h0 : 0 ≤ meromorphicOrderAt (cuspFunction 1 f) 0) (τ : ℍ) :
    f τ = (UpperHalfPlane.laurentQExpansion 1 f).coeff 0 := by
  have han : AnalyticAt ℂ (cuspFunction 1 f) 0 := by
    simpa using UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul one_pos hmer (k := 0)
      (by simpa using h0)
  have hper : Function.Periodic (f ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← modular_T_smul]
      exact hinv _ τ
  rw [UpperHalfPlane.laurentQExpansion_coeff_zero_of_analyticAt one_pos han]
  exact levelOne_eq_of_tendsto_atImInfty hf hinv
    ((han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
      fun τ ↦ eq_cuspFunction τ one_ne_zero hper) τ

/-- **A weakly holomorphic modular function is a polynomial in `j`.** Let `f` be a holomorphic
`SL₂(ℤ)`-invariant function on the upper half-plane whose cusp function is meromorphic at `0`
with a pole of order at most `N`, and whose Laurent `q`-coefficients `aₙ`, `n ≤ 0`, lie in the
image of `R`. Then `f = P(j)` for a polynomial `P` over `R` of degree at most `N`. -/
theorem exists_natDegree_le_and_aeval_j_eq {f : ℍ → ℂ} (hf : MDiff f)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hmer : MeromorphicAt (cuspFunction 1 f) 0) {N : ℕ}
    (hN : ((-N : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction 1 f) 0)
    (hR : ∀ n ≤ 0, (UpperHalfPlane.laurentQExpansion 1 f).coeff n ∈ (algebraMap R ℂ).range) :
    ∃ P : R[X], P.natDegree ≤ N ∧ ∀ τ, aeval (j τ) P = f τ := by
  induction N generalizing f with
  | zero =>
    obtain ⟨c, hc⟩ := hR 0 le_rfl
    refine ⟨C c, by simp, fun τ ↦ ?_⟩
    rw [aeval_C, hc, eq_laurentQExpansion_coeff_zero hf hinv hmer (by simpa using hN)]
  | succ N ih =>
    -- subtract `c jᴺ⁺¹`, where `c` is the coefficient of `q⁻ᴺ⁻¹` in `f`
    obtain ⟨c, hc⟩ := hR (-(N + 1 : ℕ)) (by omega)
    set Q : R[X] := C c * X ^ (N + 1)
    set g : ℍ → ℂ := f - fun τ ↦ aeval (j τ) Q
    have hgmer : MeromorphicAt (cuspFunction 1 g) 0 :=
      UpperHalfPlane.meromorphicAt_cuspFunction_sub hmer (meromorphicAt_cuspFunction_aeval_j Q)
    have hcoeff (n : ℤ) : (UpperHalfPlane.laurentQExpansion 1 g).coeff n =
        (UpperHalfPlane.laurentQExpansion 1 f).coeff n -
          algebraMap R ℂ c * (UpperHalfPlane.laurentQExpansion 1 j ^ (N + 1)).coeff n := by
      rw [UpperHalfPlane.laurentQExpansion_sub one_pos hmer (meromorphicAt_cuspFunction_aeval_j Q),
        laurentQExpansion_aeval_j, HahnSeries.coeff_sub]
      simp only [Q, eval₂_mul, eval₂_C, eval₂_X_pow, RingHom.comp_apply, HahnSeries.C_mul_eq_smul,
        HahnSeries.coeff_smul, smul_eq_mul]
    have hfN := (HahnSeries.le_orderTop_iff_forall.mp
      ((UpperHalfPlane.orderTop_laurentQExpansion one_pos hmer).symm ▸ hN))
    have hgN : ((-N : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction 1 g) 0 := by
      rw [← UpperHalfPlane.orderTop_laurentQExpansion one_pos hgmer,
        HahnSeries.le_orderTop_iff_forall]
      intro n hn
      rw [hcoeff]
      have hn : n < -N := WithTop.coe_lt_coe.mp hn
      rcases lt_or_eq_of_le (show n ≤ -((N + 1 : ℕ) : ℤ) by omega) with hn | rfl
      · rw [hfN n (WithTop.coe_lt_coe.mpr hn), laurentQExpansion_j_pow_coeff_of_lt _ hn, mul_zero,
          sub_zero]
      · rw [laurentQExpansion_j_pow_coeff_neg, mul_one, hc, sub_self]
    obtain ⟨P, hPdeg, hP⟩ := ih (hf.sub (mdifferentiable_aeval_j Q))
      (fun γ τ ↦ by simp only [Pi.sub_apply, hinv, j_smul_SL2Z]) hgmer hgN fun n hn ↦ by
        obtain ⟨m, hm⟩ := exists_laurentQExpansion_j_pow_coeff_eq_intCast (N + 1) n
        rw [hcoeff, hm]
        exact sub_mem (hR n hn) (mul_mem ⟨c, rfl⟩ ⟨m, map_intCast _ m⟩)
    refine ⟨P + Q, natDegree_add_le_of_degree_le (hPdeg.trans (Nat.le_succ N))
      (natDegree_C_mul_X_pow_le c (N + 1)), fun τ ↦ ?_⟩
    rw [map_add, hP]
    simp

/-- **A weakly holomorphic modular function is a polynomial in `j`.** A holomorphic
`SL₂(ℤ)`-invariant function on the upper half-plane whose cusp function is meromorphic at `0`, and
whose Laurent `q`-coefficients `aₙ`, `n ≤ 0`, lie in the image of `R`, is `P(j)` for a polynomial
`P` over `R`. -/
theorem exists_aeval_j_eq {f : ℍ → ℂ} (hf : MDiff f)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hmer : MeromorphicAt (cuspFunction 1 f) 0)
    (hR : ∀ n ≤ 0, (UpperHalfPlane.laurentQExpansion 1 f).coeff n ∈ (algebraMap R ℂ).range) :
    ∃ P : R[X], ∀ τ, aeval (j τ) P = f τ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((-N : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction 1 f) 0 := by
    cases meromorphicOrderAt (cuspFunction 1 f) 0 using WithTop.recTopCoe with
    | top => exact ⟨0, le_top⟩
    | coe m => exact ⟨(-m).toNat, WithTop.coe_le_coe.mpr (by omega)⟩
  obtain ⟨P, -, hP⟩ := exists_natDegree_le_and_aeval_j_eq hf hinv hmer hN hR
  exact ⟨P, hP⟩

/-- **Polynomials in `j` are the weakly holomorphic modular functions.** A function on the upper
half-plane is a polynomial in `j` over `R` exactly when it is holomorphic, invariant under
`SL₂(ℤ)` and meromorphic at `i∞`, with principal part and constant term in the image of `R`. -/
theorem exists_aeval_j_eq_iff {f : ℍ → ℂ} :
    (∃ P : R[X], ∀ τ, aeval (j τ) P = f τ) ↔
      MDiff f ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) ∧
        MeromorphicAt (cuspFunction 1 f) 0 ∧
          ∀ n ≤ 0, (UpperHalfPlane.laurentQExpansion 1 f).coeff n ∈ (algebraMap R ℂ).range := by
  refine ⟨?_, fun ⟨hf, hinv, hmer, hR⟩ ↦ exists_aeval_j_eq hf hinv hmer hR⟩
  rintro ⟨P, hP⟩
  obtain rfl : (fun τ ↦ aeval (j τ) P) = f := funext hP
  exact ⟨mdifferentiable_aeval_j P, fun γ τ ↦ by simp only [j_smul_SL2Z],
    meromorphicAt_cuspFunction_aeval_j P, fun n _ ↦ laurentQExpansion_aeval_j_coeff_mem P n⟩

/-- **The integral `q`-expansion principle in level one.** If the principal part and the constant
term of the Laurent `q`-expansion of a weakly holomorphic modular function lie in the image of
`R`, then so does every Laurent `q`-coefficient. -/
theorem laurentQExpansion_coeff_mem_of_coeff_mem {f : ℍ → ℂ} (hf : MDiff f)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hmer : MeromorphicAt (cuspFunction 1 f) 0)
    (hR : ∀ n ≤ 0, (UpperHalfPlane.laurentQExpansion 1 f).coeff n ∈ (algebraMap R ℂ).range)
    (n : ℤ) : (UpperHalfPlane.laurentQExpansion 1 f).coeff n ∈ (algebraMap R ℂ).range := by
  obtain ⟨P, hP⟩ := exists_aeval_j_eq hf hinv hmer hR
  obtain rfl : (fun τ ↦ aeval (j τ) P) = f := funext hP
  exact laurentQExpansion_aeval_j_coeff_mem P n

/-! ### Uniqueness -/

/-- **Uniqueness of the polynomial in `j`.** When `R → ℂ` is injective, two polynomials over `R`
that agree after evaluation at `j` on the upper half-plane are equal. -/
theorem aeval_j_injective (hR : Function.Injective (algebraMap R ℂ)) :
    Function.Injective fun (P : R[X]) (τ : ℍ) ↦ aeval (j τ) P := by
  intro P Q hPQ
  refine map_injective _ hR (sub_eq_zero.mp (eq_zero_of_infinite_isRoot _
    (infinite_range_j.mono ?_)))
  rintro _ ⟨τ, rfl⟩
  simpa [IsRoot, eval_map_algebraMap, sub_eq_zero] using congrFun hPQ τ

end TauCeti.ModularForm
