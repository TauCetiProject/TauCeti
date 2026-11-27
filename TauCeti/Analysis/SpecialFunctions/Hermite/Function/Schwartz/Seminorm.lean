/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.MemLp
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Orthonormal

/-!
# Polynomial growth of the Schwartz seminorms of the Hermite functions

Every Schwartz seminorm of the Hermite function `ψₙ` (`TauCeti.hermiteSchwartzMap n`) grows at
most polynomially in `n`. This is the estimate that makes Hermite expansions of Schwartz
functions converge in the Schwartz topology: the Hermite coefficients of a Schwartz function
decay faster than every power of `n`.

The proof has two steps.

* A uniform bound `ψₙ(x)² ≤ 2(n + 1)`. Integrating `(ψₙ²)' = 2ψₙψₙ'` from `-∞` gives
  `ψₙ(x)² ≤ ∫ ψₙ² + ∫ ψₙ'²`; the first integral is `1` by orthonormality, and the derivative
  ladder relation `ψₙ' = √(n/2) ψₙ₋₁ - √((n+1)/2) ψₙ₊₁` bounds the second by `2n + 1`.
* The seminorm `sup |x|ᵏ |ψₙ⁽ᵐ⁾(x)|` is the sup norm of `Xᵏ Dᵐ ψₙ`, with `X` multiplication by
  `x` and `D` the derivative on `𝓢(ℝ, ℝ)`. Each of `X` and `D` sends `ψₙ` to a combination of
  `ψₙ₊₁` and `ψₙ₋₁` with coefficients at most `1 + n` (the ladder relations
  `TauCeti.mul_hermiteSchwartzMap` and `TauCeti.deriv_hermiteSchwartzMap`), so each factor raises
  the polynomial degree of the sup-norm bound by one.

## Main statements

* `TauCeti.hermiteFunction_sq_le`: `ψₙ(x)² ≤ 2(n + 1)`.
* `TauCeti.exists_seminorm_hermiteSchwartzMap_le`: for all `k m`, there are `C` and `N` with
  `SchwartzMap.seminorm ℝ k m ψₙ ≤ C (1 + n)ᴺ` for every `n`.
* `TauCeti.exists_hermiteSchwartzMap_le_of_continuous`: the same for every continuous seminorm
  on `𝓢(ℝ, ℝ)`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, §V.3 (the Hermite expansion of
  `𝓢(ℝ)`).
* The two-step argument (a uniform bound from integrating `(ψₙ²)'`, then the ladder relations)
  follows `hermiteFunction_sup_bound` and `hermiteFunction_seminorm_bound` in
  `SchwartzNuclear/HermiteFunctions.lean` of M. R. Douglas's GaussianField library
  (https://github.com/mrdouglasny/gaussian-field, Apache 2.0), which the Riemann-Masullo
  formalization (https://github.com/mccorvie/riemann-masullo) vendors and uses. No code is copied;
  here the induction runs over products of the position and derivative operators on `𝓢(ℝ, ℝ)`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set Topology
open scoped SchwartzMap

/-! ## A uniform bound -/

/-- The `L²` mass of `ψₙ'` is at most `2n + 1`, from the derivative ladder relation. -/
private theorem integral_deriv_hermiteFunction_sq_le (n : ℕ) :
    ∫ x, deriv (hermiteFunction n) x ^ 2 ≤ 2 * n + 1 := by
  set a := Real.sqrt ((n : ℝ) / 2)
  set b := Real.sqrt (((n : ℝ) + 1) / 2)
  have hint (m : ℕ) : Integrable (fun x => hermiteFunction m x * hermiteFunction m x) :=
    (memLp_two_hermiteFunction m).integrable_mul (memLp_two_hermiteFunction m)
  have hpt : ∀ x, deriv (hermiteFunction n) x ^ 2 ≤
      2 * a ^ 2 * (hermiteFunction (n - 1) x * hermiteFunction (n - 1) x) +
        2 * b ^ 2 * (hermiteFunction (n + 1) x * hermiteFunction (n + 1) x) := by
    intro x
    rw [deriv_hermiteFunction]
    nlinarith [sq_nonneg (a * hermiteFunction (n - 1) x + b * hermiteFunction (n + 1) x)]
  calc ∫ x, deriv (hermiteFunction n) x ^ 2
      ≤ ∫ x, (2 * a ^ 2 * (hermiteFunction (n - 1) x * hermiteFunction (n - 1) x) +
          2 * b ^ 2 * (hermiteFunction (n + 1) x * hermiteFunction (n + 1) x)) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          (((hint _).const_mul _).add ((hint _).const_mul _)) (ae_of_all _ hpt)
    _ = 2 * a ^ 2 + 2 * b ^ 2 := by
        rw [integral_add ((hint _).const_mul _) ((hint _).const_mul _), integral_const_mul,
          integral_const_mul, integral_hermiteFunction_mul_hermiteFunction,
          integral_hermiteFunction_mul_hermiteFunction]
        simp
    _ = 2 * n + 1 := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        ring

/-- **Uniform bound on the Hermite functions.** `ψₙ(x)² ≤ 2(n + 1)` for every `x`.

Integrating `(ψₙ²)' = 2ψₙψₙ'` over `(-∞, x]` and using `2uv ≤ u² + v²` gives
`ψₙ(x)² ≤ ‖ψₙ‖₂² + ‖ψₙ'‖₂² ≤ 1 + (2n + 1)`. -/
theorem hermiteFunction_sq_le (n : ℕ) (x : ℝ) : hermiteFunction n x ^ 2 ≤ 2 * (n + 1) := by
  set f := hermiteFunction n
  set f' := deriv f
  have hf'eq : f' = fun y => Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) y -
      Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) y :=
    funext (deriv_hermiteFunction n)
  have hd : ∀ y, HasDerivAt (fun y => f y ^ 2) (2 * f y * f' y) y := fun y => by
    refine ((hasDerivAt_pow 2 (f y)).comp y (hasDerivAt_hermiteFunction n y)).congr_deriv ?_
    simp [hf'eq]
  have hf2 : MemLp f 2 volume := memLp_two_hermiteFunction n
  have hf'2 : MemLp f' 2 volume := by
    rw [hf'eq]
    exact ((memLp_two_hermiteFunction _).const_mul _).sub
      ((memLp_two_hermiteFunction _).const_mul _)
  have hff : Integrable (fun y => f y ^ 2) := hf2.integrable_sq
  have hf'f' : Integrable (fun y => f' y ^ 2) := hf'2.integrable_sq
  have hff' : Integrable (fun y => 2 * f y * f' y) := by
    have h : Integrable (fun y => f y * f' y) := hf2.integrable_mul hf'2
    simpa only [mul_assoc] using h.const_mul 2
  have hsq : Integrable (fun y => f y ^ 2 + f' y ^ 2) := hff.add hf'f'
  have htend : Tendsto (fun y => f y ^ 2) atBot (𝓝 0) := by
    have h := ((hermiteSchwartzMap n).tendsto_cocompact.mono_left atBot_le_cocompact).pow 2
    simpa [f] using h
  have hftc :=
    integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (fun y _ => hd y) hff'.integrableOn htend
  have hf1 : ∫ y, f y ^ 2 = 1 := by
    simpa [sq] using integral_hermiteFunction_mul_hermiteFunction n n
  calc f x ^ 2 = ∫ y in Iic x, 2 * f y * f' y := by rw [hftc, sub_zero]
    _ ≤ ∫ y in Iic x, (f y ^ 2 + f' y ^ 2) :=
        setIntegral_mono hff'.integrableOn hsq.integrableOn fun y => by
          nlinarith [sq_nonneg (f y - f' y)]
    _ ≤ ∫ y, (f y ^ 2 + f' y ^ 2) :=
        setIntegral_le_integral hsq (ae_of_all _ fun y => by positivity)
    _ = (∫ y, f y ^ 2) + ∫ y, f' y ^ 2 :=
        integral_add hff hf'f'
    _ ≤ 1 + (2 * n + 1) := by
        rw [hf1]
        exact add_le_add_right (integral_deriv_hermiteFunction_sq_le n) 1
    _ = 2 * (n + 1) := by ring

/-- **Uniform bound on the Hermite functions.** `|ψₙ(x)| ≤ √(2(n + 1))` for every `x`. -/
theorem abs_hermiteFunction_le (n : ℕ) (x : ℝ) :
    |hermiteFunction n x| ≤ Real.sqrt (2 * (n + 1)) :=
  Real.abs_le_sqrt (hermiteFunction_sq_le n x)

/-! ## The ladder bootstrap -/

/-- `T` grows polynomially in sup norm along the Hermite functions. -/
private def PolyBoundedOnHermite (T : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ)) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), |T (hermiteSchwartzMap n) x| ≤ C * (1 + n) ^ N

/-- Multiplication by the coordinate, as a continuous linear map on `𝓢(ℝ, ℝ)`. -/
private noncomputable abbrev positionCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)

private theorem polyBoundedOnHermite_one : PolyBoundedOnHermite 1 := by
  refine ⟨2, 1, by norm_num, fun n x => ?_⟩
  simp only [one_apply_eq_self, hermiteSchwartzMap_apply, pow_one]
  refine (abs_hermiteFunction_le n x).trans (Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩)
  nlinarith

/-- A ladder-type map `L`, sending `ψₙ` to `aₙ ψₙ₊₁ + bₙ ψₙ₋₁` with `|aₙ|, |bₙ| ≤ 1 + n`, raises the
polynomial degree of a sup-norm bound along the Hermite functions by one. -/
private theorem PolyBoundedOnHermite.mul {T L : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ)} (a b : ℕ → ℝ)
    (ha : ∀ n : ℕ, |a n| ≤ 1 + n) (hb : ∀ n : ℕ, |b n| ≤ 1 + n)
    (hL : ∀ n, L (hermiteSchwartzMap n) =
      a n • hermiteSchwartzMap (n + 1) + b n • hermiteSchwartzMap (n - 1))
    (hT : PolyBoundedOnHermite T) : PolyBoundedOnHermite (T * L) := by
  obtain ⟨C, N, hC, h⟩ := hT
  refine ⟨C * (2 ^ N + 1), N + 1, by positivity, fun n x => ?_⟩
  have h1 : (1 + ((n + 1 : ℕ) : ℝ)) ^ N ≤ 2 ^ N * (1 + n) ^ N := by
    rw [← mul_pow]
    gcongr
    push_cast
    linarith
  have h2 : (1 + ((n - 1 : ℕ) : ℝ)) ^ N ≤ (1 + n) ^ N := by
    gcongr
    exact_mod_cast Nat.sub_le n 1
  simp only [mul_apply_eq_comp, hL, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  calc |a n * T (hermiteSchwartzMap (n + 1)) x + b n * T (hermiteSchwartzMap (n - 1)) x|
      ≤ |a n| * |T (hermiteSchwartzMap (n + 1)) x| +
          |b n| * |T (hermiteSchwartzMap (n - 1)) x| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ (1 + n) * (C * (1 + ((n + 1 : ℕ) : ℝ)) ^ N) +
          (1 + n) * (C * (1 + ((n - 1 : ℕ) : ℝ)) ^ N) := by
        gcongr
        exacts [ha n, h _ _, hb n, h _ _]
    _ ≤ (1 + n) * (C * (2 ^ N * (1 + n) ^ N)) + (1 + n) * (C * (1 + n) ^ N) := by
        gcongr
    _ = C * (2 ^ N + 1) * (1 + n) ^ (N + 1) := by ring

private theorem sqrt_le_one_add {y : ℝ} (n : ℕ) (hy : y ≤ ((n : ℝ) + 1) / 2) :
    |Real.sqrt y| ≤ 1 + n := by
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

private theorem PolyBoundedOnHermite.mul_position {T : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ)}
    (hT : PolyBoundedOnHermite T) : PolyBoundedOnHermite (T * positionCLM) :=
  hT.mul (fun n => Real.sqrt (((n : ℝ) + 1) / 2)) (fun n => Real.sqrt ((n : ℝ) / 2))
    (fun n => sqrt_le_one_add n le_rfl) (fun n => sqrt_le_one_add n (by linarith))
    mul_hermiteSchwartzMap

private theorem PolyBoundedOnHermite.mul_deriv {T : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ)}
    (hT : PolyBoundedOnHermite T) : PolyBoundedOnHermite (T * SchwartzMap.derivCLM ℝ ℝ) :=
  hT.mul (fun n => -Real.sqrt (((n : ℝ) + 1) / 2)) (fun n => Real.sqrt ((n : ℝ) / 2))
    (fun n => by rw [abs_neg]; exact sqrt_le_one_add n le_rfl)
    (fun n => sqrt_le_one_add n (by linarith))
    (fun n => by rw [deriv_hermiteSchwartzMap, neg_smul]; abel)

private theorem polyBoundedOnHermite_position_pow_mul_deriv_pow (k m : ℕ) :
    PolyBoundedOnHermite (positionCLM ^ k * SchwartzMap.derivCLM ℝ ℝ ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero, mul_one]
    induction k with
    | zero => simpa using polyBoundedOnHermite_one
    | succ k ih => simpa [pow_succ] using ih.mul_position
  | succ m ih => simpa [pow_succ, ← mul_assoc] using ih.mul_deriv

/-! ## Schwartz seminorms -/

/-- **Polynomial growth of the Schwartz seminorms of the Hermite functions.** For each Schwartz
seminorm `p_{k,m}(f) = sup_x |x|ᵏ |f⁽ᵐ⁾(x)|` there are `C` and `N` with
`p_{k,m}(ψₙ) ≤ C (1 + n)ᴺ` for every `n`. -/
theorem exists_seminorm_hermiteSchwartzMap_le (k m : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ n : ℕ, SchwartzMap.seminorm ℝ k m (hermiteSchwartzMap n) ≤ C * (1 + n) ^ N := by
  obtain ⟨C, N, hC, h⟩ := polyBoundedOnHermite_position_pow_mul_deriv_pow k m
  refine ⟨C, N, hC, fun n => SchwartzMap.seminorm_le_bound' ℝ k m _ (by positivity) fun x => ?_⟩
  have hx := h n x
  rw [mul_apply_eq_comp, positionCLM,
    SchwartzMap.smulLeftCLM_pow_apply Function.HasTemperateGrowth.id',
    SchwartzMap.coe_derivCLM_pow, smul_eq_mul, abs_mul, abs_pow] at hx
  simpa [Real.norm_eq_abs] using hx

/-- **Polynomial growth of every continuous seminorm along the Hermite functions.** For every
continuous seminorm `p` on `𝓢(ℝ, ℝ)` there are `C` and `N` with `p(ψₙ) ≤ C (1 + n)ᴺ` for every
`n`. A continuous seminorm is dominated by finitely many of the seminorms `p_{k,m}`
(`Seminorm.bound_of_continuous`), each of which grows polynomially by
`TauCeti.exists_seminorm_hermiteSchwartzMap_le`. -/
theorem exists_hermiteSchwartzMap_le_of_continuous (p : Seminorm ℝ 𝓢(ℝ, ℝ))
    (hp : Continuous p) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ n : ℕ, p (hermiteSchwartzMap n) ≤ C * (1 + n) ^ N := by
  obtain ⟨s, C₀, -, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℝ) p hp
  choose C N hC h using fun i : ℕ × ℕ => exists_seminorm_hermiteSchwartzMap_le i.1 i.2
  refine ⟨C₀ * ∑ i ∈ s, C i, s.sup N,
    mul_nonneg C₀.coe_nonneg (Finset.sum_nonneg fun i _ => hC i), fun n => ?_⟩
  have hn : (1 : ℝ) ≤ 1 + n := le_add_of_nonneg_right n.cast_nonneg
  have hsup : s.sup (schwartzSeminormFamily ℝ ℝ ℝ) (hermiteSchwartzMap n) ≤
      (∑ i ∈ s, C i) * (1 + n) ^ s.sup N := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun i _ => hC i) (by positivity)) fun i hi => ?_
    exact (h i n).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi)
      (pow_le_pow_right₀ hn (Finset.le_sup hi)) (by positivity)
      (Finset.sum_nonneg fun j _ => hC j))
  calc p (hermiteSchwartzMap n)
      ≤ (C₀ • s.sup (schwartzSeminormFamily ℝ ℝ ℝ)) (hermiteSchwartzMap n) := hle _
    _ = C₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℝ) (hermiteSchwartzMap n) := by
        rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    _ ≤ C₀ * ((∑ i ∈ s, C i) * (1 + n) ^ s.sup N) := by gcongr
    _ = (C₀ * ∑ i ∈ s, C i) * (1 + n) ^ s.sup N := by ring

end TauCeti
