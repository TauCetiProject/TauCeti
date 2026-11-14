/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Zsqrtd.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.InnerProductSpace.Gram.ChangeOfFamily
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# The Mertens sum over inert primes of a primitive quadratic character

For a nonprincipal primitive quadratic Dirichlet character `χ` mod `q ≥ 3` and a sufficiently large
exponent `C` divisible by `3`, the logarithmic reciprocal sum over primes `p ≤ q ^ C` with
`χ p = -1` carries at most three quarters of the Mertens mass `log (q ^ C)`, up to an additive
constant depending only on `C`.

Following Green (*On Landau–Siegel zeros*, 2026), let `d ≠ 1` be the squarefree radicand with
`|d| ≤ q` and `χ p = jacobiSym d p` for odd primes `p`, and set `X = q ^ C`, `R = X`, `S = X / C`,
and `N = q ^ (2 * (C / 3)) = X ^ (2 / 3)`. Consider the `R * S` basis polynomials
`z ^ r * z' ^ s ∈ (ℤ√d)[z', z]` (`r < R`, `s < S`) together with their jet evaluations
`∂_z ^ j P(x + y√d, x - y√d)` on the grid `{0, …, N - 1}³`. Embedding `ℤ√d` into `ℝ²` via the real
and imaginary coordinates of its two complex embeddings produces an integer Gram matrix `G` of size
`(R * S) × (R * S)`:

1. **Positivity (`1 ≤ G.det`).** Any real linear relation among the jet vectors gives a complex
   bivariate polynomial of bidegree `< (R, S)` vanishing to order `N` in `z` at `(x + y√d, x - y√d)`
   for all `x, y < N`. Since `N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3`, the
   bivariate multiplicity bound (`Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`)
   forces all coefficients to vanish, so `G` is positive definite and `1 ≤ G.det`.
2. **Archimedean upper bound.** Hadamard's inequality (`Matrix.log_det_gram_le`) bounds
   `log G.det` by `(1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * R ^ 2 * S * log X + O(R ^ 2 * S)`.
3. **`p`-adic lower bound.** At every odd prime `p` with `jacobiSym d p = -1`, Frobenius in
   `ℤ√d / (p)` flips `√d`, so `p` divides `(x + y√d) ^ p - (x - y√d)`. Replacing `z ^ r * z' ^ s`
   by `z ^ (r - p * h) * (z ^ p - z') ^ h * z' ^ s` with `h = min (r / p) (S - 1 - s)` is a
   unitriangular change of family (`Matrix.det_gram_sum_smul_of_det_eq_one`) whose `j`-th ordinary
   derivative at `(x + y√d, x - y√d)` is divisible by `p ^ h` for every `j`. Thus
   `p ^ (2 * ∑_{r, s} h)` divides `G.det`.

Comparing `∑_p 2 * (∑_{r, s} h) * log p ≤ log G.det` and dividing by `R ^ 2 * S` yields the
explicit bound for all `C ≥ 6` divisible by `3`, and specializes at `C ≥ 15` (`56 / 75 < 3 / 4`)
to `TauCeti.inert_prime_sum_le`.

## Main results

* `TauCeti.sum_primesLE_jacobiSym_eq_neg_one_le`: explicit upper bound on
  `∑_{2C < p ≤ q^C, (d / p) = -1} log p / p` for any squarefree `d ≠ 1` with `|d| ≤ q` (`q ≥ 3`)
  and any `C ≥ 6` divisible by `3`.
* `DirichletCharacter.IsPrimitive.sum_primesLE_filter_eq_neg_one_le`: explicit upper bound on
  `∑_{p ≤ q^C, χ p = -1} log p / p` for a primitive nonprincipal quadratic character `χ` mod `q ≥ 3`
  over any commutative ring with `2 ≠ 0`, for all `C ≥ 6` divisible by `3`.
* `TauCeti.inert_prime_sum_le`: for all sufficiently large `C` divisible by `3`, inert primes up to
  `q ^ C` carry at most `3 / 4 * log (q ^ C) + O_C(1)` of the Mertens mass.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon **2610.00311** (2026), Theorem 1.1 and §§2–6.
-/

public section

open Finset Polynomial
open scoped InnerProductSpace

namespace TauCeti

namespace InertPrimeSum

/-! ### Complex embeddings and Euclidean geometry of `ℤ√d` -/

/-- Choice of a complex square root of an integer `d`. -/
private noncomputable def csqrt (d : ℤ) : ℂ :=
  if 0 ≤ d then (Real.sqrt d : ℂ) else Complex.I * (Real.sqrt (-d : ℝ) : ℂ)

private theorem cast_natAbs_of_nonneg {d : ℤ} (hd : 0 ≤ d) : (d.natAbs : ℝ) = (d : ℝ) := by
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg hd]

private theorem cast_natAbs_of_nonpos {d : ℤ} (hd : d ≤ 0) : (d.natAbs : ℝ) = -(d : ℝ) := by
  rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hd, Int.cast_neg]

private theorem cast_natAbs_eq_abs (d : ℤ) : (d.natAbs : ℝ) = |(d : ℝ)| := by
  rcases le_or_gt 0 d with hd | hd
  · rw [cast_natAbs_of_nonneg hd, abs_of_nonneg (by exact_mod_cast hd)]
  · rw [cast_natAbs_of_nonpos hd.le, abs_of_neg (by exact_mod_cast hd)]

private theorem csqrt_mul_self (d : ℤ) : csqrt d * csqrt d = d := by
  dsimp [csqrt]
  split_ifs with hd
  · have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hdR, Complex.ofReal_intCast]
  · have hdR : (0 : ℝ) ≤ -d := by exact_mod_cast (by omega : (0 : ℤ) ≤ -d)
    calc (Complex.I * Real.sqrt (-d : ℝ)) * (Complex.I * Real.sqrt (-d : ℝ))
        = (Complex.I * Complex.I) * ((Real.sqrt (-d : ℝ) * Real.sqrt (-d : ℝ) : ℝ) : ℂ) := by
          push_cast; ring
      _ = -((-d : ℝ) : ℂ) := by rw [Complex.I_mul_I, Real.mul_self_sqrt hdR]; ring
      _ = d := by push_cast; ring

private theorem norm_csqrt (d : ℤ) : ‖csqrt d‖ = Real.sqrt d.natAbs := by
  dsimp [csqrt]
  split_ifs with hd
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), cast_natAbs_of_nonneg hd]
  · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), cast_natAbs_of_nonpos (not_le.mp hd).le]

private theorem csqrt_ne_zero {d : ℤ} (hd : d ≠ 0) : csqrt d ≠ 0 := by
  intro h0
  have hmul := csqrt_mul_self d
  rw [h0, zero_mul] at hmul
  exact hd (by exact_mod_cast hmul.symm)

/-- The two complex embeddings `a + b√d ↦ a ± b csqrt(d)` of `ℤ√d`. -/
private noncomputable def embPos (d : ℤ) : ℤ√d →+* ℂ :=
  Zsqrtd.lift ⟨csqrt d, csqrt_mul_self d⟩

private noncomputable def embNeg (d : ℤ) : ℤ√d →+* ℂ :=
  Zsqrtd.lift ⟨-csqrt d, by simp [csqrt_mul_self]⟩

private theorem embPos_apply (d : ℤ) (u : ℤ√d) :
    embPos d u = (u.re : ℂ) + (u.im : ℂ) * csqrt d :=
  rfl

private theorem embNeg_apply (d : ℤ) (u : ℤ√d) :
    embNeg d u = (u.re : ℂ) + (u.im : ℂ) * (-csqrt d) :=
  rfl

private theorem embPos_injective {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    Function.Injective (embPos d) := by
  refine Zsqrtd.lift_injective _ fun n hn ↦ ?_
  have hu : IsUnit n := hd n (hn ▸ dvd_rfl)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp_all

/-- Parallelogram identity relating the weighted coordinate norm on `ℤ√d` to the two complex
embeddings, uniformly in the sign of `d`. -/
private theorem two_mul_re_sq_add_im_sq_eq (d : ℤ) (u : ℤ√d) :
    2 * ((u.re : ℝ) ^ 2 + (d.natAbs : ℝ) * (u.im : ℝ) ^ 2) =
      ‖embPos d u‖ ^ 2 + ‖embNeg d u‖ ^ 2 := by
  rw [embPos_apply, embNeg_apply]
  dsimp [csqrt]
  split_ifs with hd
  · have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have hpos : ((u.re : ℂ) + (u.im : ℂ) * (Real.sqrt d : ℂ)) =
        (((u.re : ℝ) + (u.im : ℝ) * Real.sqrt d : ℝ) : ℂ) := by push_cast; ring
    have hneg : ((u.re : ℂ) + (u.im : ℂ) * -(Real.sqrt d : ℂ)) =
        (((u.re : ℝ) - (u.im : ℝ) * Real.sqrt d : ℝ) : ℂ) := by push_cast; ring
    rw [hpos, hneg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, cast_natAbs_of_nonneg hd]
    calc 2 * ((u.re : ℝ) ^ 2 + (d : ℝ) * (u.im : ℝ) ^ 2)
        = 2 * (u.re : ℝ) ^ 2 + 2 * (Real.sqrt d * Real.sqrt d) * (u.im : ℝ) ^ 2 := by
          rw [Real.mul_self_sqrt hdR]; ring
      _ = ((u.re : ℝ) + (u.im : ℝ) * Real.sqrt d) ^ 2 +
            ((u.re : ℝ) - (u.im : ℝ) * Real.sqrt d) ^ 2 := by ring
  · have hd_lt : d < 0 := not_le.mp hd
    have hdR : (0 : ℝ) ≤ -d := neg_nonneg.mpr (by exact_mod_cast hd_lt.le)
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    have hpos : (u.re : ℂ) + (u.im : ℂ) * (Complex.I * Real.sqrt (-d : ℝ)) =
        ((u.re : ℝ) : ℂ) + (((u.im : ℝ) * Real.sqrt (-d : ℝ) : ℝ) : ℂ) * Complex.I := by
      simp only [Complex.ofReal_intCast, Complex.ofReal_mul]; ring
    have hneg : (u.re : ℂ) + (u.im : ℂ) * -(Complex.I * Real.sqrt (-d : ℝ)) =
        ((u.re : ℝ) : ℂ) + ((-(u.im : ℝ) * Real.sqrt (-d : ℝ) : ℝ) : ℂ) * Complex.I := by
      simp only [Complex.ofReal_intCast, Complex.ofReal_mul, Complex.ofReal_neg]; ring
    rw [hpos, hneg, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I,
      cast_natAbs_of_nonpos hd_lt.le]
    calc 2 * ((u.re : ℝ) ^ 2 + -(d : ℝ) * (u.im : ℝ) ^ 2)
        = 2 * (u.re : ℝ) ^ 2 + 2 * (Real.sqrt (-d : ℝ) * Real.sqrt (-d : ℝ)) * (u.im : ℝ) ^ 2 := by
          rw [Real.mul_self_sqrt hdR]; ring
      _ = (u.re : ℝ) ^ 2 + ((u.im : ℝ) * Real.sqrt (-d : ℝ)) ^ 2 +
            ((u.re : ℝ) ^ 2 + (-(u.im : ℝ) * Real.sqrt (-d : ℝ)) ^ 2) := by ring

/-- Euclidean realization of a finite tuple in `(ℤ√d) ^ κ` whose real inner products match the
trace pairing `∑_k 2 (re_1 re_2 + |d| im_1 im_2)`. -/
private noncomputable def zsqrtdFamToLp (d : ℤ) {κ : Type*} (v : κ → ℤ√d) :
    EuclideanSpace ℝ (κ × Fin 2) :=
  WithLp.toLp 2 fun p ↦
    if p.2 = 0 then Real.sqrt 2 * (v p.1).re else Real.sqrt (2 * d.natAbs) * (v p.1).im

private theorem zsqrtdFamToLp_sum (d : ℤ) {κ ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (v : ι → κ → ℤ√d) :
    zsqrtdFamToLp d (fun k ↦ ∑ i ∈ s, c i • v i k) =
      ∑ i ∈ s, (c i : ℝ) • zsqrtdFamToLp d (v i) := by
  ext p
  simp only [zsqrtdFamToLp, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    WithLp.ofLp_toLp, smul_eq_mul]
  rcases Fin.eq_zero_or_eq_succ p.2 with hp | ⟨j, hj⟩
  · rw [hp]
    have hre : ((∑ i ∈ s, c i • v i p.1).re : ℝ) = ∑ i ∈ s, (c i : ℝ) * ((v i p.1).re : ℝ) := by
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a t ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, Zsqrtd.re_add, Int.cast_add, ih, zsmul_eq_mul,
          Zsqrtd.re_smul, Int.cast_mul]
    simp only [↓reduceIte, hre, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  · rw [hj]
    have him : ((∑ i ∈ s, c i • v i p.1).im : ℝ) = ∑ i ∈ s, (c i : ℝ) * ((v i p.1).im : ℝ) := by
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a t ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, Zsqrtd.im_add, Int.cast_add, ih, zsmul_eq_mul,
          Zsqrtd.im_smul, Int.cast_mul]
    simp only [Fin.succ_ne_zero, ↓reduceIte, him, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

private theorem inner_zsqrtdFamToLp (d : ℤ) {κ : Type*} [Fintype κ] (v w : κ → ℤ√d) :
    ⟪zsqrtdFamToLp d v, zsqrtdFamToLp d w⟫_ℝ =
      ((∑ k : κ, 2 * ((v k).re * (w k).re + (d.natAbs : ℤ) * (v k).im * (w k).im) : ℤ) : ℝ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Fin.sum_univ_two]
  simp only [zsqrtdFamToLp, WithLp.ofLp_toLp, ↓reduceIte, Fin.isValue, one_ne_zero,
    RCLike.inner_apply, conj_trivial]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by positivity)
  have hd : Real.sqrt (2 * (d.natAbs : ℝ)) * Real.sqrt (2 * (d.natAbs : ℝ)) =
      2 * |(d : ℝ)| := by
    rw [Real.mul_self_sqrt (by positivity), cast_natAbs_eq_abs]
  calc Real.sqrt 2 * (w k).re * (Real.sqrt 2 * (v k).re) +
        Real.sqrt (2 * d.natAbs) * (w k).im * (Real.sqrt (2 * d.natAbs) * (v k).im)
      = (Real.sqrt 2 * Real.sqrt 2) * ((v k).re * (w k).re) +
          (Real.sqrt (2 * d.natAbs) * Real.sqrt (2 * d.natAbs)) * ((v k).im * (w k).im) := by ring
    _ = 2 * ((v k).re * (w k).re + |(d : ℝ)| * (v k).im * (v k).im +
          |(d : ℝ)| * (v k).im * ((w k).im - (v k).im)) := by rw [h2, hd]; ring
    _ = 2 * ((v k).re * (w k).re + |(d : ℝ)| * (v k).im * (w k).im) := by ring

private theorem norm_sq_zsqrtdFamToLp (d : ℤ) {κ : Type*} [Fintype κ] (v : κ → ℤ√d) :
    ‖zsqrtdFamToLp d v‖ ^ 2 = ∑ k : κ, (‖embPos d (v k)‖ ^ 2 + ‖embNeg d (v k)‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_zsqrtdFamToLp]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := two_mul_re_sq_add_im_sq_eq d (v k)
  rw [cast_natAbs_eq_abs] at h
  linarith [h]

/-- Integer Gram matrix of a family of `(ℤ√d)^κ`-tuples. -/
private noncomputable def intGram (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → ℤ√d) :
    Matrix ι ι ℤ :=
  Matrix.of fun i j ↦
    ∑ k : κ, 2 * ((v i k).re * (v j k).re + (d.natAbs : ℤ) * (v i k).im * (v j k).im)

private theorem map_intGram_eq_gram (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → ℤ√d) :
    (intGram d v).map (Int.castRingHom ℝ) = Matrix.gram ℝ (fun i ↦ zsqrtdFamToLp d (v i)) := by
  ext i j
  simp [intGram, Matrix.gram_apply, inner_zsqrtdFamToLp]

private theorem cast_det_intGram (d : ℤ) {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (v : ι → κ → ℤ√d) :
    ((intGram d v).det : ℝ) = (Matrix.gram ℝ (fun i ↦ zsqrtdFamToLp d (v i))).det := by
  rw [← map_intGram_eq_gram, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]

/-! ### Jet evaluations on `{0, …, N - 1}³` and positivity of `G.det` -/

/-- Evaluation of `∂_z^j P(z, z')` at `(x + y√d, x - y√d)` for `(x, y, j) ∈ Fin N × Fin N × Fin N`.
Here `C X` is the inner variable `z'` and `X` is the outer variable `z`. -/
private noncomputable def jetEval (d : ℤ) (N : ℕ) (P : (ℤ√d)[X][X])
    (k : Fin N × Fin N × Fin N) : ℤ√d :=
  (Polynomial.derivative^[k.2.2.1]
    (P.map (Polynomial.evalRingHom ⟨k.1.1, -(k.2.1.1 : ℤ)⟩))).eval ⟨k.1.1, (k.2.1.1 : ℤ)⟩

private theorem jetEval_sum (d : ℤ) (N : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (P : ι → (ℤ√d)[X][X]) (k : Fin N × Fin N × Fin N) :
    jetEval d N (∑ i ∈ s, c i • P i) k = ∑ i ∈ s, c i • jetEval d N (P i) k := by
  simp only [jetEval, zsmul_eq_mul, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_intCast,
    iterate_derivative_sum, iterate_derivative_intCast_mul, eval_finsetSum, eval_mul, eval_intCast]

/-- The monomial `z ^ r * z' ^ s` in `(ℤ√d)[z', z]`. -/
private noncomputable def basePoly (d : ℤ) {R S : ℕ} (i : Fin R × Fin S) : (ℤ√d)[X][X] :=
  Polynomial.C (Polynomial.X ^ i.2.1) * Polynomial.X ^ i.1.1

private noncomputable def baseFam (d : ℤ) (N R S : ℕ) (i : Fin R × Fin S) :
    Fin N × Fin N × Fin N → ℤ√d :=
  jetEval d N (basePoly d i)

private noncomputable def baseVec (d : ℤ) (N R S : ℕ) (i : Fin R × Fin S) :
    EuclideanSpace ℝ ((Fin N × Fin N × Fin N) × Fin 2) :=
  zsqrtdFamToLp d (baseFam d N R S i)

private theorem jetEval_basePoly_eq (d : ℤ) (N : ℕ) {R S : ℕ} (i : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    baseFam d N R S i k =
      (⟨k.1.1, -(k.2.1.1 : ℤ)⟩ : ℤ√d) ^ i.2.1 *
        (i.1.1.descFactorial k.2.2.1 : ℤ√d) *
        (⟨k.1.1, (k.2.1.1 : ℤ)⟩ : ℤ√d) ^ (i.1.1 - k.2.2.1) := by
  simp only [baseFam, jetEval, basePoly, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, coe_evalRingHom, eval_pow, eval_X, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, C_eq_natCast, eval_natCast]
  ring

/-- Injectivity of the linear coordinate change `(z', z) ↦ (X₀ - δ X₁, X₀ + δ X₁)` when `δ ≠ 0`. -/
private theorem aevalAeval_conj_injective {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective
      (aevalAeval (MvPolynomial.X 0 - MvPolynomial.C δ * MvPolynomial.X 1)
        (MvPolynomial.X 0 + MvPolynomial.C δ * MvPolynomial.X 1) :
        ℂ[X][X] →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
  let L₁ : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 + MvPolynomial.C δ * MvPolynomial.X 1
  let L₂ : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 - MvPolynomial.C δ * MvPolynomial.X 1
  let U₀ : ℂ[X][X] := (2⁻¹ : ℂ) • (C X + X)
  let U₁ : ℂ[X][X] := (2 * δ)⁻¹ • (X - C X)
  let invHom : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ[X][X] := MvPolynomial.aeval ![U₀, U₁]
  have h1 : (2⁻¹ : ℂ) + δ * (2 * δ)⁻¹ = 1 := by field_simp [hδ]; norm_num
  have h2 : (2⁻¹ : ℂ) - δ * (2 * δ)⁻¹ = 0 := by field_simp [hδ]; ring
  have hcomp : invHom.comp (aevalAeval L₂ L₁) = AlgHom.id ℂ ℂ[X][X] := by
    refine (aevalAevalEquiv ℂ ℂ[X][X]).symm.injective (Prod.ext ?_ ?_)
    · simp only [aevalAevalEquiv_symm_apply, AlgHom.comp_apply, AlgHom.id_apply, aevalAeval_X,
        invHom, L₂, U₀, U₁, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul]
      calc (2⁻¹ : ℂ) • (C X + X : ℂ[X][X]) - δ • ((2 * δ)⁻¹ • (X - C X))
          = ((2⁻¹ + δ * (2 * δ)⁻¹ : ℂ)) • (C X : ℂ[X][X]) +
              ((2⁻¹ - δ * (2 * δ)⁻¹ : ℂ)) • (X : ℂ[X][X]) := by
            rw [smul_add, smul_smul, smul_sub, add_smul, sub_smul]
            abel
        _ = C X := by rw [h1, h2, one_smul, zero_smul, add_zero]
    · simp only [aevalAevalEquiv_symm_apply, AlgHom.comp_apply, AlgHom.id_apply, aevalAeval_Y,
        invHom, L₁, U₀, U₁, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul]
      calc (2⁻¹ : ℂ) • (C X + X : ℂ[X][X]) + δ • ((2 * δ)⁻¹ • (X - C X))
          = ((2⁻¹ - δ * (2 * δ)⁻¹ : ℂ)) • (C X : ℂ[X][X]) +
              ((2⁻¹ + δ * (2 * δ)⁻¹ : ℂ)) • (X : ℂ[X][X]) := by
            rw [smul_add, smul_smul, smul_sub, sub_smul, add_smul]
            abel
        _ = X := by rw [h2, h1, zero_smul, one_smul, zero_add]
  exact Function.LeftInverse.injective (g := invHom) fun P ↦ DFunLike.congr_fun hcomp P

/-- Extracting the complex jet relation from a real linear dependence among `baseVec`. -/
private theorem sum_embPos_baseFam_eq_zero_of_sum_smul_eq_zero {d : ℤ} (hd0 : d ≠ 0)
    {N R S : ℕ} {c : Fin R × Fin S → ℝ}
    (hc : ∑ i : Fin R × Fin S, c i • baseVec d N R S i = 0)
    (k : Fin N × Fin N × Fin N) :
    ∑ i : Fin R × Fin S, (c i : ℂ) * embPos d (baseFam d N R S i k) = 0 := by
  have h0 := congrArg (fun w : EuclideanSpace ℝ _ ↦ w.ofLp (k, 0)) hc
  have h1 := congrArg (fun w : EuclideanSpace ℝ _ ↦ w.ofLp (k, 1)) hc
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply, Pi.smul_apply,
    Pi.zero_apply, baseVec, zsqrtdFamToLp, ↓reduceIte, Fin.isValue, one_ne_zero,
    smul_eq_mul] at h0 h1
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hsd : Real.sqrt (2 * (d.natAbs : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by positivity [Int.natAbs_pos.mpr hd0])
  have hre : ∑ i : Fin R × Fin S, c i * ((baseFam d N R S i k).re : ℝ) = 0 := by
    refine mul_left_cancel₀ hs2 ?_
    rw [Finset.mul_sum, mul_zero, ← h0]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have him : ∑ i : Fin R × Fin S, c i * ((baseFam d N R S i k).im : ℝ) = 0 := by
    refine mul_left_cancel₀ hsd ?_
    rw [Finset.mul_sum, mul_zero, ← h1]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hreC : ∑ i : Fin R × Fin S, (c i : ℂ) * ((baseFam d N R S i k).re : ℂ) = 0 := by
    exact_mod_cast hre
  have himC : ∑ i : Fin R × Fin S, (c i : ℂ) * ((baseFam d N R S i k).im : ℂ) = 0 := by
    exact_mod_cast him
  calc ∑ i : Fin R × Fin S, (c i : ℂ) * embPos d (baseFam d N R S i k)
      = (∑ i, (c i : ℂ) * ((baseFam d N R S i k).re : ℂ)) +
          csqrt d * ∑ i, (c i : ℂ) * ((baseFam d N R S i k).im : ℂ) := by
        simp only [embPos_apply, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = 0 := by simp [hreC, himC]

private noncomputable def relationPoly {R S : ℕ} (c : Fin R × Fin S → ℝ) : ℂ[X][X] :=
  ∑ r : Fin R, Polynomial.monomial r.1 (∑ s : Fin S, Polynomial.monomial s.1 (c (r, s) : ℂ))

private theorem dvd_map_evalRingHom_relationPoly {d : ℤ} (hd0 : d ≠ 0) {N R S : ℕ}
    {c : Fin R × Fin S → ℝ} (hc : ∑ i : Fin R × Fin S, c i • baseVec d N R S i = 0)
    {nx ny : ℕ} (hnx : nx < N) (hny : ny < N) :
    (X - C ((nx : ℂ) + (ny : ℂ) * csqrt d)) ^ N ∣
      (relationPoly c).map (evalRingHom ((nx : ℂ) - (ny : ℂ) * csqrt d)) := by
  rw [X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero]
  intro j hj
  have hjet := sum_embPos_baseFam_eq_zero_of_sum_smul_eq_zero hd0 hc (⟨nx, hnx⟩, ⟨ny, hny⟩, ⟨j, hj⟩)
  have hderiv : (derivative^[j]
      ((relationPoly c).map (evalRingHom ((nx : ℂ) - (ny : ℂ) * csqrt d)))).eval
        ((nx : ℂ) + (ny : ℂ) * csqrt d) =
      ∑ i : Fin R × Fin S,
        (c i : ℂ) * embPos d (baseFam d N R S i (⟨nx, hnx⟩, ⟨ny, hny⟩, ⟨j, hj⟩)) := by
    rw [Fintype.sum_prod_type]
    simp only [relationPoly, Polynomial.map_sum, iterate_derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, coe_evalRingHom, iterate_derivative_C_mul,
      iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, eval_mul, eval_C, eval_pow, eval_X,
      eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [eval_monomial]
    simp only [jetEval_basePoly_eq, map_mul, map_pow, map_natCast, embPos_apply,
      Int.cast_natCast, Int.cast_neg]
    ring
  rw [hjet, ← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul, nsmul_eq_mul] at hderiv
  exact (mul_eq_zero.mp hderiv).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))

/-- **Fact 1: Linear independence of the jet vectors**, hence `1 ≤ G.det`. -/
private theorem linearIndependent_baseVec {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {N R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    LinearIndependent ℝ (baseVec d N R S) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set F := relationPoly c
  have hF_deg : F.natDegree ≤ R - 1 :=
    (natDegree_sum_le _ _).trans (Finset.sup_le fun r _ ↦
      natDegree_monomial_le _ |>.trans (by omega))
  have hF_swap : (Bivariate.swap F).natDegree ≤ S - 1 := by
    refine Bivariate.natDegree_swap_le_iff.mpr fun n ↦ ?_
    rw [show F = relationPoly c from rfl, relationPoly, finsetSum_coeff]
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun r _ ↦ ?_)
    simp only [Function.comp_apply, coeff_monomial_apply]
    split_ifs
    · exact (natDegree_sum_le _ _).trans (Finset.sup_le fun s _ ↦
        natDegree_monomial_le _ |>.trans (by omega))
    · simp
  let grid : Finset ℂ := (Finset.range N).image Nat.cast
  have hgrid_card : grid.card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  let L₁ : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 + MvPolynomial.C (csqrt d) * MvPolynomial.X 1
  let L₂ : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 - MvPolynomial.C (csqrt d) * MvPolynomial.X 1
  have hL₁ : L₁.totalDegree ≤ 1 := (MvPolynomial.totalDegree_add _ _).trans
    (max_le (by simp) ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
  have hL₂ : L₂.totalDegree ≤ 1 := (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (by simp) ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
  have hinj_β (x₁ : ℂ) (hx₁ : x₁ ∈ grid) (y₁ : ℂ) (hy₁ : y₁ ∈ grid)
      (x₂ : ℂ) (hx₂ : x₂ ∈ grid) (y₂ : ℂ) (hy₂ : y₂ ∈ grid)
      (heq : MvPolynomial.eval ![x₁, y₁] L₂ = MvPolynomial.eval ![x₂, y₂] L₂) :
      x₁ = x₂ ∧ y₁ = y₂ := by
    rcases Finset.mem_image.mp hx₁ with ⟨nx₁, -, rfl⟩
    rcases Finset.mem_image.mp hy₁ with ⟨ny₁, -, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨nx₂, -, rfl⟩
    rcases Finset.mem_image.mp hy₂ with ⟨ny₂, -, rfl⟩
    have hemb : embPos d ⟨nx₁, -(ny₁ : ℤ)⟩ = embPos d ⟨nx₂, -(ny₂ : ℤ)⟩ := by
      simpa [L₂, embPos_apply, sub_eq_add_neg, mul_comm (csqrt d)] using heq
    obtain ⟨hre, him⟩ := Zsqrtd.ext_iff.mp (embPos_injective hd hd1 hemb)
    dsimp at hre him
    have hnx : nx₁ = nx₂ := by omega
    have hny : ny₁ = ny₂ := by omega
    exact ⟨by simp [hnx], by simp [hny]⟩
  have hmult (x : ℂ) (hx : x ∈ grid) (y : ℂ) (hy : y ∈ grid) :
      (X - C (MvPolynomial.eval ![x, y] L₁)) ^ grid.card ∣
        F.map (evalRingHom (MvPolynomial.eval ![x, y] L₂)) := by
    rcases Finset.mem_image.mp hx with ⟨nx, hnx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ny, hny, rfl⟩
    simpa [hgrid_card, L₁, L₂, mul_comm (csqrt d)] using
      dvd_map_evalRingHom_relationPoly hd.ne_zero hc (Finset.mem_range.mp hnx)
        (Finset.mem_range.mp hny)
  have hdeg_lt : grid.card * (F.natDegree + (Bivariate.swap F).natDegree) +
      2 * F.natDegree * (Bivariate.swap F).natDegree < grid.card ^ 3 := by
    rw [hgrid_card]
    refine lt_of_le_of_lt (add_le_add (Nat.mul_le_mul_left N (add_le_add hF_deg hF_swap))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hF_deg) hF_swap)) hdeg
  have hF0 : F = 0 := eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube grid hL₁ hL₂
    (aevalAeval_conj_injective (csqrt_ne_zero hd.ne_zero)) hinj_β hmult hdeg_lt
  intro i
  have hcoeff : (F.coeff i.1.1).coeff i.2.1 = 0 := by simp [hF0]
  have hval : (F.coeff i.1.1).coeff i.2.1 = (c i : ℂ) := by
    rw [show F = relationPoly c from rfl, relationPoly, finsetSum_coeff,
      Finset.sum_eq_single i.1
        (fun r _ hr ↦ coeff_monomial_of_ne _ (Fin.ext_iff.not.mp hr.symm))
        (fun h ↦ absurd (Finset.mem_univ _) h),
      coeff_monomial_same, finsetSum_coeff,
      Finset.sum_eq_single i.2
        (fun s _ hs ↦ coeff_monomial_of_ne _ (Fin.ext_iff.not.mp hs.symm))
        (fun h ↦ absurd (Finset.mem_univ _) h),
      coeff_monomial_same]
  exact Complex.ofReal_eq_zero.mp (hval.symm.trans hcoeff)

private theorem one_le_det_intGram {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {N R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    1 ≤ (intGram d (baseFam d N R S)).det := by
  have hpos : (0 : ℝ) < ((intGram d (baseFam d N R S)).det : ℝ) := by
    rw [cast_det_intGram]
    exact Matrix.det_gram_pos_iff.mpr (linearIndependent_baseVec hd hd1 hR hS hdeg)
  have hposZ : 0 < (intGram d (baseFam d N R S)).det := by exact_mod_cast hpos
  omega

/-! ### Archimedean upper bound on `log G.det` -/

private theorem norm_emb_baseFam_le {d : ℤ} {q N R S : ℕ} (hdq : d.natAbs ≤ q) (hq3 : 3 ≤ q)
    (hN : 0 < N) (hR : 0 < R) (i : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
    ‖embPos d (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1) ∧
      ‖embNeg d (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1) := by
  have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ q))
  have h2Nq_ge : (1 : ℝ) ≤ 2 * N * Real.sqrt q := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hδ_le : ‖csqrt d‖ ≤ Real.sqrt q := by
    rw [norm_csqrt]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hdq)
  have hpt (sgn : ℤ) (hsgn : |sgn| ≤ 1) (ε : ℂ) (hε : ‖ε‖ = ‖csqrt d‖) :
      ‖((k.1.1 : ℂ) + ((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ) * ε)‖ ≤ 2 * N * Real.sqrt q := by
    have hx : (k.1.1 : ℝ) ≤ N := by exact_mod_cast k.1.2.le
    have hy : ‖((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ)‖ ≤ N := by
      rw [Complex.norm_intCast, ← Int.cast_abs, abs_mul, Int.abs_natCast]
      have : |sgn| * (k.2.1.1 : ℤ) ≤ N := by
        simpa using mul_le_mul hsgn (by exact_mod_cast k.2.1.2.le) (by positivity) (by omega)
      exact_mod_cast this
    calc ‖(k.1.1 : ℂ) + ((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ) * ε‖
        ≤ ‖(k.1.1 : ℂ)‖ + ‖((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ)‖ * ‖ε‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ N + N * Real.sqrt q := by
          rw [Complex.norm_natCast, hε]
          exact add_le_add hx (mul_le_mul hy hδ_le (norm_nonneg _) (by positivity))
      _ ≤ 2 * N * Real.sqrt q := by nlinarith
  have hdesc : (i.1.1.descFactorial k.2.2.1 : ℝ) ≤ (R : ℝ) ^ N := by
    have h1 : i.1.1.descFactorial k.2.2.1 ≤ R ^ N :=
      (Nat.descFactorial_le_pow _ _).trans
        ((Nat.pow_le_pow_left i.1.2.le _).trans (Nat.pow_le_pow_right hR k.2.2.2.le))
    exact_mod_cast h1
  have hbound (φ : ℤ√d →+* ℂ) (ε : ℂ) (hε : ‖ε‖ = ‖csqrt d‖)
      (hφ : ∀ a b : ℤ, φ ⟨a, b⟩ = (a : ℂ) + (b : ℂ) * ε) :
      ‖φ (baseFam d N R S i k)‖ ≤ (R : ℝ) ^ N * (2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1) := by
    rw [jetEval_basePoly_eq, map_mul, map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_mul,
      norm_pow, norm_pow, Complex.norm_natCast]
    have hp1 : ‖φ ⟨k.1.1, -(k.2.1.1 : ℤ)⟩‖ ≤ 2 * N * Real.sqrt q := by
      simpa [hφ] using hpt (-1) (by norm_num) ε hε
    have hp2 : ‖φ ⟨k.1.1, (k.2.1.1 : ℤ)⟩‖ ≤ 2 * N * Real.sqrt q := by
      simpa [hφ] using hpt 1 (by norm_num) ε hε
    calc ‖φ ⟨k.1.1, -k.2.1.1⟩‖ ^ i.2.1 * i.1.1.descFactorial k.2.2.1 *
            ‖φ ⟨k.1.1, k.2.1.1⟩‖ ^ (i.1.1 - k.2.2.1)
        ≤ (2 * N * Real.sqrt q) ^ i.2.1 * (R : ℝ) ^ N *
            (2 * N * Real.sqrt q) ^ (i.1.1 - k.2.2.1) := by
          gcongr
      _ = (R : ℝ) ^ N * (2 * N * Real.sqrt q) ^ (i.1.1 - k.2.2.1 + i.2.1) := by
          rw [pow_add]; ring
      _ ≤ (R : ℝ) ^ N * (2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h2Nq_ge (by omega)) (by positivity)
  exact ⟨hbound (embPos d) (csqrt d) rfl (fun _ _ ↦ rfl),
    hbound (embNeg d) (-csqrt d) (norm_neg _) (fun _ _ ↦ rfl)⟩

private theorem two_mul_log_norm_baseVec_le {d : ℤ} {q N R S : ℕ} (hdq : d.natAbs ≤ q)
    (hq3 : 3 ≤ q) (hN : 0 < N) (hR : 0 < R) {i : Fin R × Fin S}
    (hi : baseVec d N R S i ≠ 0) :
    2 * Real.log ‖baseVec d N R S i‖ ≤
      Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R +
        2 * ((i.1.1 : ℝ) + i.2.1) * Real.log (2 * N * Real.sqrt q) := by
  have hv0 : 0 < ‖baseVec d N R S i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi)
  have hsq : ‖baseVec d N R S i‖ ^ 2 ≤
      2 * (N : ℝ) ^ 3 * ((R : ℝ) ^ N) ^ 2 *
        ((2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1)) ^ 2 := by
    rw [baseVec, norm_sq_zsqrtdFamToLp]
    calc ∑ k : Fin N × Fin N × Fin N,
            (‖embPos d (baseFam d N R S i k)‖ ^ 2 + ‖embNeg d (baseFam d N R S i k)‖ ^ 2)
        ≤ ∑ _k : Fin N × Fin N × Fin N,
            2 * ((R : ℝ) ^ N * (2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1)) ^ 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          obtain ⟨h1, h2⟩ := norm_emb_baseFam_le hdq hq3 hN hR i k
          have hp1 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h1
          have hp2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h2
          linarith
      _ = 2 * (N : ℝ) ^ 3 * ((R : ℝ) ^ N) ^ 2 *
            ((2 * N * Real.sqrt q) ^ (i.1.1 + i.2.1)) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  have hlog := Real.log_le_log hv0 hsq
  rw [Real.log_pow, Nat.cast_ofNat, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **Fact 2: Hadamard upper bound on `log G.det`.** -/
private theorem log_det_intGram_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {q N R S : ℕ} (hdq : d.natAbs ≤ q) (hq3 : 3 ≤ q)
    (hN : 0 < N) (hR : 0 < R) (hS : 0 < S)
    (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    Real.log ((intGram d (baseFam d N R S)).det : ℝ) ≤
      (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
        (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt q) := by
  rw [cast_det_intGram]
  have hlin := linearIndependent_baseVec hd hd1 hR hS hdeg
  have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ q))
  have hfin_sq (n : ℕ) : ∑ r : Fin n, (2 * (r.1 : ℝ)) ≤ (n : ℝ) ^ 2 := by
    have : (∑ r : Fin n, 2 * (r.1 : ℝ)) = 2 * ((∑ r ∈ Finset.range n, r : ℕ) : ℝ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ ↦ r) n]
      push_cast; rw [Finset.mul_sum]
    rw [this, Finset.sum_range_id, sq]
    exact_mod_cast (Nat.mul_div_le (n * (n - 1)) 2).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  have hsum_idx : ∑ i : Fin R × Fin S, 2 * ((i.1.1 : ℝ) + i.2.1) ≤ (R : ℝ) * S * (R + S) := by
    rw [Fintype.sum_prod_type]
    have hsplit : (∑ r : Fin R, ∑ s : Fin S, 2 * ((r.1 : ℝ) + s.1)) =
        (S : ℝ) * (∑ r : Fin R, 2 * (r.1 : ℝ)) + (R : ℝ) * (∑ s : Fin S, 2 * (s.1 : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    rw [hsplit]
    nlinarith [hfin_sq R, hfin_sq S]
  calc Real.log (Matrix.gram ℝ (baseVec d N R S)).det
      ≤ ∑ i : Fin R × Fin S, 2 * Real.log ‖baseVec d N R S i‖ := Matrix.log_det_gram_le hlin
    _ ≤ ∑ i : Fin R × Fin S,
          (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R +
            2 * ((i.1.1 : ℝ) + i.2.1) * Real.log (2 * N * Real.sqrt q)) :=
        Finset.sum_le_sum fun i _ ↦ two_mul_log_norm_baseVec_le hdq hq3 hN hR (hlin.ne_zero i)
    _ = (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (∑ i : Fin R × Fin S, 2 * ((i.1.1 : ℝ) + i.2.1)) *
            Real.log (2 * N * Real.sqrt q) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
        push_cast; ring
    _ ≤ (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt q) := by
        have hlog_nn : 0 ≤ Real.log (2 * N * Real.sqrt q) :=
          Real.log_nonneg (by nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN])
        nlinarith

/-! ### `p`-adic divisibility of `G.det` at inert primes -/

/-- Elementary factorial divisibility: `p ^ m` divides `j!` whenever `p * m ≤ j` and `0 < p`. -/
private theorem pow_dvd_factorial_of_mul_le {p m j : ℕ} (hp : 0 < p) (h : p * m ≤ j) :
    p ^ m ∣ j.factorial := by
  suffices hpm : p ^ m ∣ (p * m).factorial from hpm.trans (Nat.factorial_dvd_factorial h)
  clear h
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : p * (m + 1) = (p * m + (p - 1)) + 1 := by
      rw [Nat.mul_succ]; omega
    rw [pow_succ', hstep, Nat.factorial_succ, ← hstep]
    exact mul_dvd_mul (dvd_mul_right p (m + 1))
      (ih.trans (Nat.factorial_dvd_factorial (Nat.le_add_right _ _)))

/-- Split `(a + b) ^ p` in a commutative ring at `i = 0`, `1 ≤ i ≤ p - 1`, and `i = p`. -/
private theorem add_pow_prime_split {R : Type*} [CommRing R] (a b : R) {p : ℕ} (hp : 0 < p) :
    (a + b) ^ p = b ^ p + (∑ i ∈ Finset.range (p - 1),
      a ^ (i + 1) * b ^ (p - (i + 1)) * (p.choose (i + 1) : R)) + a ^ p := by
  rw [(Commute.all a b).add_pow p, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    Nat.choose_self, Nat.cast_one, mul_one]
  congr 1
  conv_lhs => rw [(Nat.sub_add_cancel hp).symm]
  rw [Finset.sum_range_succ']
  simp [Nat.sub_add_cancel hp, add_comm]

/-- Frobenius at an odd prime `p` with `jacobiSym d p = -1` sends `x + y√d` to `x - y√d` mod `p`. -/
private theorem inert_frobenius_sub_conj {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : _root_.Odd p)
    (hjac : jacobiSym d p = -1) (x y : ℤ) :
    (p : ℤ√d) ∣ (⟨x, y⟩ : ℤ√d) ^ p - ⟨x, -y⟩ := by
  have : Fact p.Prime := ⟨hp⟩
  have hdec : (⟨x, y⟩ : ℤ√d) = (x : ℤ√d) + (y : ℤ√d) * Zsqrtd.sqrtd := by ext <;> simp
  rw [hdec, add_pow_prime_split _ _ hp.pos]
  have hmid : (p : ℤ√d) ∣ ∑ i ∈ Finset.range (p - 1),
      (x : ℤ√d) ^ (i + 1) * ((y : ℤ√d) * Zsqrtd.sqrtd) ^ (p - (i + 1)) *
        (p.choose (i + 1) : ℤ√d) := by
    refine Finset.dvd_sum fun i hi ↦ dvd_mul_of_dvd_right ?_ _
    obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero i)
      (by have := Finset.mem_range.mp hi; omega)
    exact ⟨c, by exact_mod_cast hc⟩
  have hsqrtd_pow : (Zsqrtd.sqrtd : ℤ√d) ^ p = ((d ^ (p / 2) : ℤ) : ℤ√d) * Zsqrtd.sqrtd := by
    obtain ⟨k, hk⟩ := hodd
    have hpk : p / 2 = k := by omega
    rw [hpk, hk, pow_add, pow_one, pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow]
  have hx_dvd : (p : ℤ) ∣ x ^ p - x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [ZMod.pow_card]
  have hy_dvd : (p : ℤ) ∣ y ^ p * d ^ (p / 2) + y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, ← legendreSym.eq_pow, jacobiSym.legendreSym.to_jacobiSym, hjac]
    ring
  have hrem_eq : ((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + (x : ℤ√d) ^ p - ⟨x, -y⟩ =
      ⟨x ^ p - x, y ^ p * d ^ (p / 2) + y⟩ := by
    rw [mul_pow, hsqrtd_pow, ← mul_assoc, ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_pow]
    ext <;> simp [-Int.cast_pow, -Int.cast_mul]
  have hrem : (p : ℤ√d) ∣
      ((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + (x : ℤ√d) ^ p - ⟨x, -y⟩ := by
    rw [hrem_eq, ← Int.cast_natCast, Zsqrtd.intCast_dvd]
    exact ⟨hx_dvd, hy_dvd⟩
  have hsplit : (((y : ℤ√d) * Zsqrtd.sqrtd) ^ p +
        (∑ i ∈ Finset.range (p - 1),
          (x : ℤ√d) ^ (i + 1) * ((y : ℤ√d) * Zsqrtd.sqrtd) ^ (p - (i + 1)) *
            (p.choose (i + 1) : ℤ√d)) + (x : ℤ√d) ^ p - ⟨x, -y⟩) =
      (∑ i ∈ Finset.range (p - 1),
        (x : ℤ√d) ^ (i + 1) * ((y : ℤ√d) * Zsqrtd.sqrtd) ^ (p - (i + 1)) *
          (p.choose (i + 1) : ℤ√d)) +
        (((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + (x : ℤ√d) ^ p - ⟨x, -y⟩) := by ring
  rw [hsplit]
  exact dvd_add hmid hrem

/-- Exponent `h = min (r / p) (S - 1 - s)` and the modified polynomial
`z ^ (r - p * h) * (z ^ p - z') ^ h * z' ^ s`. -/
private def shiftExp (p S : ℕ) (i : Fin R × Fin S) : ℕ :=
  min (i.1.1 / p) (S - 1 - i.2.1)

private noncomputable def shiftPoly (d : ℤ) (p : ℕ) {R S : ℕ} (i : Fin R × Fin S) :
    (ℤ√d)[X][X] :=
  let h := shiftExp p S i
  Polynomial.C (Polynomial.X ^ i.2.1) *
    (Polynomial.X ^ (i.1.1 - p * h) * (Polynomial.X ^ p - Polynomial.C Polynomial.X) ^ h)

private noncomputable def shiftFam (d : ℤ) (p N R S : ℕ) (i : Fin R × Fin S) :
    Fin N × Fin N × Fin N → ℤ√d :=
  jetEval d N (shiftPoly d p i)

private def shiftMatrix (p : ℕ) {R S : ℕ} : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  Matrix.of fun i j ↦
    (if i = j then 1 else 0) +
      ∑ m ∈ Finset.range (shiftExp p S i),
        if j.1.1 = i.1.1 - p * shiftExp p S i + p * m ∧
            j.2.1 = i.2.1 + (shiftExp p S i - m) then
          (-1 : ℤ) ^ (shiftExp p S i - m) * (shiftExp p S i).choose m
        else 0

private theorem shiftPoly_eq_sum_basePoly (d : ℤ) {p R S : ℕ} (hp : 0 < p) (i : Fin R × Fin S) :
    shiftPoly d p i = ∑ j : Fin R × Fin S, shiftMatrix p i j • basePoly d j := by
  have h_le : p * shiftExp p S i ≤ i.1.1 :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le i.1.1 p)
  have htop : Polynomial.C (Polynomial.X ^ i.2.1 : (ℤ√d)[X]) *
      (Polynomial.X ^ (i.1.1 - p * shiftExp p S i) *
        (Polynomial.X ^ p) ^ shiftExp p S i) = basePoly d i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel h_le, basePoly]
  simp only [shiftMatrix, Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_smul]
  rw [Finset.sum_comm]
  have hsub_pow : (X ^ p - C X : (ℤ√d)[X][X]) ^ shiftExp p S i =
      (∑ m ∈ Finset.range (shiftExp p S i),
        (X ^ p) ^ m * (-(C (X : (ℤ√d)[X])) : (ℤ√d)[X][X]) ^ (shiftExp p S i - m) *
          ((shiftExp p S i).choose m : (ℤ√d)[X][X])) +
        (X ^ p) ^ shiftExp p S i := by
    rw [sub_eq_add_neg,
      (Commute.all (X ^ p : (ℤ√d)[X][X]) (-(C (X : (ℤ√d)[X])) : (ℤ√d)[X][X])).add_pow,
      Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      mul_one]
  rw [shiftPoly, hsub_pow, mul_add, mul_add, htop, add_comm _ (basePoly d i)]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm_lt : m < shiftExp p S i := Finset.mem_range.mp hm
  have hr' : i.1.1 - p * shiftExp p S i + p * m < R := by
    have := Nat.mul_lt_mul_of_pos_left hm_lt hp
    have := i.1.2
    omega
  have hs' : i.2.1 + (shiftExp p S i - m) < S := by
    have : shiftExp p S i ≤ S - 1 - i.2.1 := min_le_right _ _
    have := i.2.2
    omega
  let j₀ : Fin R × Fin S := (⟨_, hr'⟩, ⟨_, hs'⟩)
  rw [Finset.sum_eq_single j₀
    (fun j _ hj ↦ by
      have hcond : ¬ (j.1.1 = j₀.1.1 ∧ j.2.1 = j₀.2.1) := fun ⟨h1, h2⟩ ↦
        hj (Prod.ext (Fin.ext h1) (Fin.ext h2))
      simp [j₀, hcond])
    (fun h ↦ absurd (Finset.mem_univ j₀) h)]
  have hneg_pow : (-(C (X : (ℤ√d)[X])) : (ℤ√d)[X][X]) ^ (shiftExp p S i - m) =
      (-1 : (ℤ√d)[X][X]) ^ (shiftExp p S i - m) * (C (X : (ℤ√d)[X])) ^ (shiftExp p S i - m) := by
    have hneg : (-(C (X : (ℤ√d)[X])) : (ℤ√d)[X][X]) =
        (-1 : (ℤ√d)[X][X]) * C (X : (ℤ√d)[X]) := by ring
    rw [hneg, mul_pow]
  have hbase : basePoly d j₀ =
      C (X ^ i.2.1) * C (X ^ (shiftExp p S i - m)) *
        (X ^ (i.1.1 - p * shiftExp p S i) * (X ^ p) ^ m) := by
    dsimp [basePoly, j₀]
    rw [pow_add, C_mul, pow_add, pow_mul]
  rw [ite_eq_left ⟨rfl, rfl⟩, hbase, hneg_pow, ← C_pow, zsmul_eq_mul]
  push_cast
  ring

/-- Unitriangularity of the change of basis `basePoly ↦ shiftPoly` in reverse lexicographic
order preserves the integer Gram determinant. -/
private theorem det_intGram_shiftFam_eq (d : ℤ) {p N R S : ℕ} (hp : 0 < p) :
    (intGram d (shiftFam d p N R S)).det = (intGram d (baseFam d N R S)).det := by
  let U : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ := shiftMatrix p
  have hvec (i : Fin R × Fin S) :
      zsqrtdFamToLp d (shiftFam d p N R S i) =
        ∑ j : Fin R × Fin S, (U i j : ℝ) • baseVec d N R S j := by
    have hfam : shiftFam d p N R S i = fun k ↦ ∑ j, U i j • baseFam d N R S j k := by
      funext k
      simp only [shiftFam, shiftPoly_eq_sum_basePoly d hp i, U, baseFam, jetEval_sum]
    rw [hfam, zsqrtdFamToLp_sum]
    rfl
  have hno_match {i j : Fin R × Fin S} (hij : i.1.1 ≤ j.1.1) (m : ℕ)
      (hm : m ∈ Finset.range (shiftExp p S i)) :
      ¬ (j.1.1 = i.1.1 - p * shiftExp p S i + p * m ∧
        j.2.1 = i.2.1 + (shiftExp p S i - m)) := by
    intro ⟨h1, _⟩
    have hm_lt : m < shiftExp p S i := Finset.mem_range.mp hm
    have hpm : p * m < p * shiftExp p S i := Nat.mul_lt_mul_of_pos_left hm_lt hp
    have h_le : p * shiftExp p S i ≤ i.1.1 :=
      (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le i.1.1 p)
    omega
  let rank : Fin R × Fin S → OrderDual (Fin R ×ₗ Fin S) := OrderDual.toDual ∘ toLex
  have htri : (U.map (Int.castRingHom ℝ)).BlockTriangular rank := by
    intro i j hij
    have hlex : toLex i < toLex j := hij
    have hij_ne : i ≠ j := fun h ↦ lt_irrefl _ (h ▸ hlex)
    have hi_le_j : i.1.1 ≤ j.1.1 := by
      rcases Prod.Lex.lt_iff.mp hlex with h1 | ⟨h1, _⟩
      · exact Nat.le_of_lt h1
      · exact le_of_eq (congrArg Fin.val h1)
    simp only [Matrix.map_apply, U, shiftMatrix, Matrix.of_apply, hij_ne, ↓reduceIte, zero_add]
    rw [Finset.sum_eq_zero fun m hm ↦
      ite_eq_right_iff.mpr fun h ↦ absurd h (hno_match hi_le_j m hm), map_zero]
  have hdiag (i : Fin R × Fin S) : (U.map (Int.castRingHom ℝ)) i i = 1 := by
    simp only [Matrix.map_apply, U, shiftMatrix, Matrix.of_apply, ↓reduceIte]
    rw [Finset.sum_eq_zero fun m hm ↦ ite_eq_right_iff.mpr fun h ↦ absurd h (hno_match le_rfl m hm),
      add_zero, map_one]
  have hdetU : (U.map (Int.castRingHom ℝ)).det = 1 := by
    rw [htri.det_eq_prod_diag (OrderDual.toDual.injective.comp toLex.injective)]
    exact Finset.prod_eq_one fun i _ ↦ hdiag i
  have hR_eq : ((intGram d (shiftFam d p N R S)).det : ℝ) =
      ((intGram d (baseFam d N R S)).det : ℝ) := by
    rw [cast_det_intGram, cast_det_intGram, funext hvec]
    exact Matrix.det_gram_sum_smul_of_det_eq_one hdetU (baseVec d N R S)
  exact_mod_cast hR_eq

private theorem exists_taylor_X_pow_sub_C_conj {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hodd : _root_.Odd p) (hjac : jacobiSym d p = -1) (x y : ℤ) :
    ∃ A : (ℤ√d)[X],
      taylor ⟨x, y⟩ (X ^ p - C (⟨x, -y⟩ : ℤ√d)) = C (p : ℤ√d) * A + X ^ p := by
  set α : ℤ√d := ⟨x, y⟩
  set α_bar : ℤ√d := ⟨x, -y⟩
  obtain ⟨γ, hγ⟩ := inert_frobenius_sub_conj hp hodd hjac x y
  have hexp : taylor α (X ^ p - C α_bar) = (X + C α) ^ p - C α_bar := by simp [taylor_apply]
  rw [hexp, add_pow_prime_split _ _ hp.pos]
  let c : ℕ → ℤ√d := fun m ↦ ((p.choose (m + 1) / p : ℕ) : ℤ√d)
  refine ⟨C γ + ∑ m ∈ Finset.range (p - 1),
      C (c m) * X ^ (m + 1) * (C α) ^ (p - (m + 1)), ?_⟩
  have hconst : (C α : (ℤ√d)[X]) ^ p - C α_bar = C (p : ℤ√d) * C γ := by
    rw [← C_pow, ← C_sub, hγ, C_mul]
  have hsum_eq : (∑ m ∈ Finset.range (p - 1),
        X ^ (m + 1) * (C α : (ℤ√d)[X]) ^ (p - (m + 1)) * (p.choose (m + 1) : (ℤ√d)[X])) =
      C (p : ℤ√d) * ∑ m ∈ Finset.range (p - 1),
        C (c m) * X ^ (m + 1) * (C α) ^ (p - (m + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hdvd : p ∣ p.choose (m + 1) :=
      Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero m) (by have := Finset.mem_range.mp hm; omega)
    have hc : (p.choose (m + 1) : (ℤ√d)[X]) = C (p : ℤ√d) * C (c m) := by
      dsimp [c]
      rw [← C_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd, C_eq_natCast]
    rw [hc]
    ring
  calc (C α : (ℤ√d)[X]) ^ p +
          (∑ m ∈ Finset.range (p - 1),
            X ^ (m + 1) * (C α : (ℤ√d)[X]) ^ (p - (m + 1)) * (p.choose (m + 1) : (ℤ√d)[X])) +
          X ^ p - C α_bar
      = ((C α) ^ p - C α_bar) +
          (∑ m ∈ Finset.range (p - 1),
            X ^ (m + 1) * (C α) ^ (p - (m + 1)) * (p.choose (m + 1) : (ℤ√d)[X])) +
          X ^ p := by ring
    _ = C (p : ℤ√d) * (C γ + ∑ m ∈ Finset.range (p - 1),
          C (c m) * X ^ (m + 1) * (C α) ^ (p - (m + 1))) + X ^ p := by
        rw [hconst, hsum_eq]; ring

/-- Every jet evaluation of `shiftPoly d p i` at an inert odd prime `p` is divisible by `p ^ h`. -/
private theorem pow_dvd_shiftFam {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : _root_.Odd p)
    (hjac : jacobiSym d p = -1) (N R S : ℕ) (i : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    (p : ℤ√d) ^ shiftExp p S i ∣ shiftFam d p N R S i k := by
  set h := shiftExp p S i
  set α : ℤ√d := ⟨k.1.1, (k.2.1.1 : ℤ)⟩
  set α_bar : ℤ√d := ⟨k.1.1, -(k.2.1.1 : ℤ)⟩
  set j := k.2.2.1
  set f : (ℤ√d)[X] := (shiftPoly d p i).map (evalRingHom α_bar)
  change (p : ℤ√d) ^ h ∣ (derivative^[j] f).eval α
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul, ← taylor_coeff, nsmul_eq_mul]
  have hf : f = C (α_bar ^ i.2.1) * X ^ (i.1.1 - p * h) * (X ^ p - C α_bar) ^ h := by
    simp [f, shiftPoly, h, mul_assoc]
  obtain ⟨A, hA⟩ := exists_taylor_X_pow_sub_C_conj hp hodd hjac k.1.1 k.2.1.1
  have htf : taylor α f =
      C (α_bar ^ i.2.1) * (X + C α) ^ (i.1.1 - p * h) * (X ^ p + C (p : ℤ√d) * A) ^ h := by
    simp only [hf, taylor_apply, mul_comp, pow_comp, X_comp, C_comp]
    rw [← taylor_apply α (X ^ p - C α_bar), hA, add_comm (C (p : ℤ√d) * A) (X ^ p)]
  rw [htf, (Commute.all (X ^ p : (ℤ√d)[X]) (C (p : ℤ√d) * A)).add_pow h, Finset.mul_sum,
    finsetSum_coeff, Finset.mul_sum]
  refine Finset.dvd_sum fun m hm ↦ ?_
  have hm_le : m ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hterm : C (α_bar ^ i.2.1) * (X + C α) ^ (i.1.1 - p * h) *
        ((X ^ p) ^ m * (C (p : ℤ√d) * A) ^ (h - m) * (h.choose m : (ℤ√d)[X])) =
      C ((p : ℤ√d) ^ (h - m)) *
        (C (α_bar ^ i.2.1) * (X + C α) ^ (i.1.1 - p * h) * A ^ (h - m) *
          (h.choose m : (ℤ√d)[X])) * X ^ (p * m) := by
    rw [mul_pow, ← C_pow, ← pow_mul]
    ring
  rw [hterm, mul_assoc, coeff_C_mul]
  set B := C (α_bar ^ i.2.1) * (X + C α) ^ (i.1.1 - p * h) * A ^ (h - m) *
    (h.choose m : (ℤ√d)[X])
  rcases lt_or_ge j (p * m) with hlt | hge
  · simp only [coeff_mul_X_pow', not_le.mpr hlt, ↓reduceIte, mul_zero, dvd_zero]
  · obtain ⟨q_fac, hq_fac⟩ := pow_dvd_factorial_of_mul_le hp.pos hge
    have hcast : (j.factorial : ℤ√d) = (p : ℤ√d) ^ m * (q_fac : ℤ√d) := by exact_mod_cast hq_fac
    rw [hcast]
    refine ⟨(q_fac : ℤ√d) * (B * X ^ (p * m)).coeff j, ?_⟩
    calc (p : ℤ√d) ^ m * (q_fac : ℤ√d) * ((p : ℤ√d) ^ (h - m) * (B * X ^ (p * m)).coeff j)
        = (p : ℤ√d) ^ (m + (h - m)) * ((q_fac : ℤ√d) * (B * X ^ (p * m)).coeff j) := by
          rw [pow_add]; ring
      _ = (p : ℤ√d) ^ h * ((q_fac : ℤ√d) * (B * X ^ (p * m)).coeff j) := by
          rw [Nat.add_sub_of_le hm_le]

/-- **Fact 3: `p`-adic divisibility of `G.det`** at odd inert primes. -/
private theorem pow_dvd_det_intGram {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : _root_.Odd p)
    (hjac : jacobiSym d p = -1) (N R S : ℕ) :
    ((p : ℤ) ^ (2 * ∑ i : Fin R × Fin S, shiftExp p S i)) ∣
      (intGram d (baseFam d N R S)).det := by
  have hdvd_entry (i j : Fin R × Fin S) :
      ((p : ℤ) ^ shiftExp p S i * (p : ℤ) ^ shiftExp p S j) ∣
        intGram d (shiftFam d p N R S) i j := by
    refine Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right ?_ 2
    obtain ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ := (Zsqrtd.intCast_dvd ((p : ℤ) ^ shiftExp p S i) _).mp
      (by simpa using pow_dvd_shiftFam hp hodd hjac N R S i k)
    obtain ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ := (Zsqrtd.intCast_dvd ((p : ℤ) ^ shiftExp p S j) _).mp
      (by simpa using pow_dvd_shiftFam hp hodd hjac N R S j k)
    refine ⟨a₁ * a₂ + (d.natAbs : ℤ) * b₁ * b₂, ?_⟩
    rw [ha₁, hb₁, ha₂, hb₂]
    ring
  choose M₀ hM₀ using hdvd_entry
  have hmat : intGram d (shiftFam d p N R S) =
      Matrix.diagonal (fun i ↦ (p : ℤ) ^ shiftExp p S i) * Matrix.of M₀ *
        Matrix.diagonal (fun i ↦ (p : ℤ) ^ shiftExp p S i) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hM₀ i j]
    ring
  rw [← det_intGram_shiftFam_eq d hp.pos, hmat, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  refine ⟨(Matrix.of M₀).det, ?_⟩
  rw [two_mul, pow_add]
  ring

/-! ### Summing the `p`-adic exponents and assembling the Mertens bound -/

private theorem sum_range_cast_eq (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * (n - 1) / 2 := by
  have : ∑ i ∈ Finset.range n, (i : ℝ) = ((∑ i ∈ Finset.range n, i : ℕ) : ℝ) := by push_cast; rfl
  rw [this, Finset.sum_range_id]
  rcases n with _ | n
  · simp
  · have heven : 2 ∣ (n + 1) * n := by
      rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨(2 * m + 1) * m, by ring⟩
      · exact ⟨(m + 1) * (2 * m + 1), by ring⟩
    simp only [Nat.add_sub_cancel, Nat.cast_div heven (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast; ring

private theorem sum_range_min_ge (S k : ℕ) :
    2 * (S : ℝ) * k - (k : ℝ) ^ 2 - k ≤ 2 * ∑ s ∈ Finset.range S, (min k s : ℝ) := by
  rcases le_or_gt k S with hkS | hSk
  · conv_rhs => rw [(Nat.add_sub_of_le hkS).symm, Finset.sum_range_add]
    have h1 : ∑ s ∈ Finset.range k, (min k s : ℝ) = (k : ℝ) * (k - 1) / 2 := by
      rw [Finset.sum_congr rfl fun s hs ↦
        min_eq_right (by exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hs))]
      exact sum_range_cast_eq k
    have h2 : ∑ x ∈ Finset.range (S - k), min (k : ℝ) ((k + x : ℕ) : ℝ) =
        ((S - k : ℕ) : ℝ) * k := by
      rw [Finset.sum_congr rfl fun x _ ↦
          min_eq_left (by exact_mod_cast Nat.le_add_right k x),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1, h2, Nat.cast_sub hkS]
    exact le_of_eq (by ring)
  · have h1 : ∑ s ∈ Finset.range S, (min k s : ℝ) = (S : ℝ) * (S - 1) / 2 := by
      rw [Finset.sum_congr rfl fun s hs ↦ by
        have := Finset.mem_range.mp hs
        exact min_eq_right (by exact_mod_cast (by omega : s ≤ k))]
      exact sum_range_cast_eq S
    rw [h1]
    have hle : (S : ℝ) ≤ k := by exact_mod_cast hSk.le
    nlinarith [sq_nonneg ((k : ℝ) - S)]

private theorem two_mul_sum_shiftExp_ge {p R S : ℕ} (hp : 0 < p) (hSR : S ≤ R) :
    (R : ℝ) ^ 2 * S / p - 2 * (R : ℝ) ^ 2 / p - 2 * R * S - (R : ℝ) ^ 3 / p ^ 2 ≤
      2 * (∑ i : Fin R × Fin S, shiftExp p S i : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hrev (r : Fin R) :
      (∑ s : Fin S, (shiftExp p S (r, s) : ℝ)) =
        ∑ s ∈ Finset.range S, min ((r.1 / p : ℕ) : ℝ) (s : ℝ) := by
    rw [← Equiv.sum_comp Fin.revPerm (fun s : Fin S ↦ (shiftExp p S (r, s) : ℝ)),
      ← Fin.sum_univ_eq_sum_range (fun s : ℕ ↦ min ((r.1 / p : ℕ) : ℝ) (s : ℝ)) S]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hval : S - 1 - (Fin.revPerm s).1 = s.1 := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have := s.2
      omega
    rw [shiftExp, hval, Nat.cast_min]
  have hr_term (r : Fin R) :
      2 * (S : ℝ) * r.1 / p - 2 * S - (R : ℝ) ^ 2 / p ^ 2 - (R : ℝ) / p ≤
        2 * ∑ s : Fin S, (shiftExp p S (r, s) : ℝ) := by
    rw [hrev r]
    set k := r.1 / p
    have hk_le : (k : ℝ) ≤ (r.1 : ℝ) / p :=
      (le_div_iff₀ hpR).mpr (by exact_mod_cast Nat.div_mul_le_self r.1 p)
    have hk_ge : (r.1 : ℝ) / p - 1 ≤ k := by
      rw [sub_le_iff_le_add, div_le_iff₀ hpR]
      have hdiv : p * k + r.1 % p = r.1 := Nat.div_add_mod r.1 p
      have hmod : r.1 % p < p := Nat.mod_lt r.1 hp
      have hk1 : (k + 1) * p = p * k + p := by ring
      exact_mod_cast (by omega : r.1 ≤ (k + 1) * p)
    have hrR : (r.1 : ℝ) / p ≤ (R : ℝ) / p := by gcongr; exact_mod_cast r.2.le
    have hksq : (k : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 / p ^ 2 := by
      calc (k : ℝ) ^ 2 ≤ ((R : ℝ) / p) ^ 2 :=
            sq_le_sq₀ (by positivity) (by positivity) |>.mpr (hk_le.trans hrR)
        _ = (R : ℝ) ^ 2 / p ^ 2 := div_pow _ _ 2
    have h2Sk : 2 * (S : ℝ) * r.1 / p - 2 * S ≤ 2 * (S : ℝ) * k := by
      calc 2 * (S : ℝ) * r.1 / p - 2 * S
          = (2 * (S : ℝ)) * ((r.1 : ℝ) / p - 1) := by ring
        _ ≤ (2 * (S : ℝ)) * k := mul_le_mul_of_nonneg_left hk_ge (by positivity)
    linarith [sum_range_min_ge S k, h2Sk, hksq, hk_le.trans hrR]
  have hsum_r : (∑ r : Fin R, (2 * (S : ℝ) * r.1 / p)) =
      (S : ℝ) * ((R : ℝ) * (R - 1)) / p := by
    calc (∑ r : Fin R, (2 * (S : ℝ) * r.1 / p))
        = (2 * (S : ℝ) / p) * ∑ r ∈ Finset.range R, (r : ℝ) := by
          rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ ↦ (r : ℝ)) R, Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ ↦ by ring
      _ = (S : ℝ) * ((R : ℝ) * (R - 1)) / p := by rw [sum_range_cast_eq]; ring
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  calc (R : ℝ) ^ 2 * S / p - 2 * (R : ℝ) ^ 2 / p - 2 * R * S - (R : ℝ) ^ 3 / p ^ 2
      ≤ (S : ℝ) * ((R : ℝ) * (R - 1)) / p - (R : ℝ) * (2 * S) -
          (R : ℝ) * ((R : ℝ) ^ 2 / p ^ 2) - (R : ℝ) * ((R : ℝ) / p) := by
        have hSR_R : (S : ℝ) ≤ R := by exact_mod_cast hSR
        have hnn : 0 ≤ (R : ℝ) * (R - S) / p :=
          div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hSR_R)) hpR.le
        linarith [show ((S : ℝ) * ((R : ℝ) * (R - 1)) / p - (R : ℝ) * ((R : ℝ) / p)) -
            ((R : ℝ) ^ 2 * S / p - 2 * (R : ℝ) ^ 2 / p) = (R : ℝ) * (R - S) / p by ring,
          show (R : ℝ) * ((R : ℝ) ^ 2 / p ^ 2) = (R : ℝ) ^ 3 / p ^ 2 by ring]
    _ = ∑ r : Fin R,
          (2 * (S : ℝ) * r.1 / p - 2 * S - (R : ℝ) ^ 2 / p ^ 2 - (R : ℝ) / p) := by
        simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum_r]
    _ ≤ ∑ r : Fin R, 2 * ∑ s : Fin S, (shiftExp p S (r, s) : ℝ) :=
        Finset.sum_le_sum fun r _ ↦ hr_term r

/-- Parameter arithmetic for `X = q ^ C`, `S = X / C`, `N = q ^ (2 * (C / 3))` when `6 ≤ C` and
`3 ∣ C`. -/
private theorem grid_deg_lt_cube {q C : ℕ} (hq3 : 3 ≤ q) (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    let X := q ^ C
    let S := X / C
    let N := q ^ (2 * (C / 3))
    0 < X ∧ 0 < S ∧ 0 < N ∧
      N * ((X - 1) + (S - 1)) + 2 * (X - 1) * (S - 1) < N ^ 3 := by
  intro X S N
  obtain ⟨m, rfl⟩ := hC3
  have hm : 2 ≤ m := by omega
  have hm_div : 3 * m / 3 = m := by omega
  set u := q ^ m
  have hu9 : 9 ≤ u :=
    (by norm_num : 9 ≤ 3 ^ 2).trans ((Nat.pow_le_pow_right (by omega) hm).trans
      (Nat.pow_le_pow_left hq3 m))
  have hX_eq : X = u ^ 3 := by dsimp [X, u]; rw [mul_comm 3 m, pow_mul]
  have hN_eq : N = u ^ 2 := by dsimp [N, u]; rw [hm_div, mul_comm 2 m, pow_mul]
  have hN3_eq : N ^ 3 = X ^ 2 := by rw [hN_eq, hX_eq]; ring
  have h9N : 9 * N ≤ X := by rw [hN_eq, hX_eq]; nlinarith
  have hX_gt_C : 3 * m < X :=
    (Nat.lt_two_pow_self (n := 3 * m)).trans_le (Nat.pow_le_pow_left (by omega) (3 * m))
  have hS_pos : 0 < S := Nat.div_pos hX_gt_C.le (by omega)
  have h6S : 6 * S ≤ X := by
    have : S ≤ X / 6 := Nat.div_le_div_left hC6 (by omega)
    omega
  refine ⟨by positivity, hS_pos, by positivity, ?_⟩
  have hX_pos : 1 ≤ X := by omega
  have hN_pos : 1 ≤ N := by rw [hN_eq]; nlinarith
  rw [hN3_eq]
  have hlt1 : N * ((X - 1) + (S - 1)) < 2 * N * X := by
    have hXS : (X - 1) + (S - 1) < 2 * X := by omega
    nlinarith
  have hle2 : 2 * (X - 1) * (S - 1) ≤ 2 * X * S :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.sub_le X 1)) (Nat.sub_le S 1)
  nlinarith

private theorem sum_shiftExp_mul_log_le_log_det {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {C N X S : ℕ} (hC_pos : 0 < C) (hX_pos : 0 < X) (hS_pos : 0 < S)
    (hdeg : N * ((X - 1) + (S - 1)) + 2 * (X - 1) * (S - 1) < N ^ 3) :
    let P := (Nat.primesLE X).filter fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1
    ∑ p ∈ P, (2 * (∑ i : Fin X × Fin S, shiftExp p S i : ℝ)) * Real.log p ≤
      Real.log ((intGram d (baseFam d N X S)).det : ℝ) := by
  intro P
  have h1 : 1 ≤ (intGram d (baseFam d N X S)).det :=
    one_le_det_intGram hd hd1 hX_pos hS_pos hdeg
  have hprod_dvd :
      (∏ p ∈ P, (p : ℤ) ^ (2 * ∑ i : Fin X × Fin S, shiftExp p S i)) ∣
        (intGram d (baseFam d N X S)).det := by
    refine Finset.prod_dvd_of_coprime (fun p hp p' hp' hne ↦ ?_) (fun p hp ↦ ?_)
    · have hp_pr := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      have hp'_pr := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp').1).2
      have hcop := ((hp_pr.coprime_iff_not_dvd.mpr fun h ↦
        hne ((Nat.prime_dvd_prime_iff_eq hp_pr hp'_pr).mp h)).pow
          (2 * ∑ i : Fin X × Fin S, shiftExp p S i)
          (2 * ∑ i : Fin X × Fin S, shiftExp p' S i)).isCoprime
      simpa only [Nat.cast_pow] using hcop
    · obtain ⟨hpX, h2C, hjac⟩ := Finset.mem_filter.mp hp
      have hp_pr := (Nat.mem_primesLE.mp hpX).2
      exact pow_dvd_det_intGram hp_pr (hp_pr.odd_of_ne_two (by omega)) hjac N X S
  have hprod_pos_Z : 0 < (∏ p ∈ P, (p : ℤ) ^ (2 * ∑ i : Fin X × Fin S, shiftExp p S i)) :=
    Finset.prod_pos fun p hp ↦
      pow_pos (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.pos) _
  have hle_Z : (∏ p ∈ P, (p : ℤ) ^ (2 * ∑ i : Fin X × Fin S, shiftExp p S i)) ≤
      (intGram d (baseFam d N X S)).det := by
    obtain ⟨k, hk⟩ := hprod_dvd
    have hk1 : 1 ≤ k := by nlinarith
    nlinarith
  have hprod_pos : 0 < (∏ p ∈ P, (p : ℝ) ^ (2 * ∑ i : Fin X × Fin S, shiftExp p S i)) := by
    exact_mod_cast hprod_pos_Z
  have hle_R : (∏ p ∈ P, (p : ℝ) ^ (2 * ∑ i : Fin X × Fin S, shiftExp p S i)) ≤
      ((intGram d (baseFam d N X S)).det : ℝ) := by
    exact_mod_cast hle_Z
  have hlog := Real.log_le_log hprod_pos hle_R
  rw [Real.log_prod (fun p hp ↦ pow_ne_zero _
    (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.ne_zero))] at hlog
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_)) hlog
  rw [Real.log_pow]
  push_cast; ring

private theorem log_det_intGram_le_explicit {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {q C : ℕ} (hq3 : 3 ≤ q) (hdq : d.natAbs ≤ q) (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    let X := q ^ C
    let S := X / C
    let N := q ^ (2 * (C / 3))
    Real.log ((intGram d (baseFam d N X S)).det : ℝ) ≤
      (X : ℝ) ^ 2 * S * ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) *
        Real.log ((q : ℝ) ^ C) + 15) := by
  intro X S N
  obtain ⟨hX_pos, hS_pos, hN_pos, hdeg⟩ := grid_deg_lt_cube hq3 hC6 hC3
  have hhad := log_det_intGram_le hd hd1 hdq hq3 hN_pos hX_pos hS_pos hdeg
  obtain ⟨m, hm⟩ := hC3
  have hm_div : C / 3 = m := by omega
  set u := q ^ m
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast Nat.one_le_pow m q (by omega)
  have hX_u : (X : ℝ) = (u : ℝ) ^ 3 := by
    exact_mod_cast (show X = u ^ 3 by dsimp [X, u]; rw [hm, mul_comm 3 m, pow_mul])
  have hN_u : (N : ℝ) = (u : ℝ) ^ 2 := by
    exact_mod_cast (show N = u ^ 2 by dsimp [N, u]; rw [hm_div, mul_comm 2 m, pow_mul])
  have hlogu : Real.log u ≤ u :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by norm_num)
  have herr1 : Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log X ≤ 13 * X := by
    rw [hN_u, hX_u, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    have hu2_log : (u : ℝ) ^ 2 * Real.log u ≤ (u : ℝ) ^ 3 := by
      calc (u : ℝ) ^ 2 * Real.log u
          ≤ (u : ℝ) ^ 2 * u := mul_le_mul_of_nonneg_left hlogu (by positivity)
        _ = (u : ℝ) ^ 3 := by ring
    nlinarith [show (u : ℝ) ≤ (u : ℝ) ^ 3 by nlinarith, show (1 : ℝ) ≤ (u : ℝ) ^ 3 by nlinarith]
  have h2Nq_log : Real.log (2 * N * Real.sqrt q) =
      Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) := by
    have hq_pos : (0 : ℝ) < q := by positivity
    have hC_ne : (C : ℝ) ≠ 0 := by positivity
    have hlogN : Real.log N = 2 / 3 * Real.log ((q : ℝ) ^ C) := by
      rw [show (N : ℝ) = (q : ℝ) ^ (2 * m) by exact_mod_cast (by simp [N, hm_div]),
        Real.log_pow, Real.log_pow, hm]
      push_cast; ring
    have hlogsq : Real.log (Real.sqrt q) = 1 / (2 * (C : ℝ)) * Real.log ((q : ℝ) ^ C) := by
      rw [Real.log_sqrt hq_pos.le, Real.log_pow]
      field_simp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), hlogN, hlogsq]
    ring
  have hSC : (S : ℝ) ≤ (X : ℝ) / C :=
    (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast Nat.div_mul_le_self X C)
  have hXS_sum : (X : ℝ) + S ≤ (1 + 1 / (C : ℝ)) * X := by
    linarith [show (X : ℝ) / C = 1 / (C : ℝ) * X by ring]
  have hlog2Nq_nn : 0 ≤ Real.log (2 * N * Real.sqrt q) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ q))
    exact Real.log_nonneg (by nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN_pos])
  calc Real.log ((intGram d (baseFam d N X S)).det : ℝ)
      ≤ (X : ℝ) * S * (13 * X) +
          (X : ℝ) * S * ((1 + 1 / (C : ℝ)) * X) * Real.log (2 * N * Real.sqrt q) := by
        refine hhad.trans (add_le_add (mul_le_mul_of_nonneg_left herr1 (by positivity)) ?_)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXS_sum (by positivity)) hlog2Nq_nn
    _ = (X : ℝ) ^ 2 * S * (13 + (1 + 1 / (C : ℝ)) * Real.log 2 +
          (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C)) := by
        rw [h2Nq_log]; ring
    _ ≤ (X : ℝ) ^ 2 * S * ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) *
          Real.log ((q : ℝ) ^ C) + 15) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1C : 1 / (C : ℝ) ≤ 1 :=
          div_le_one_of_le₀ (by exact_mod_cast (by omega : 1 ≤ C)) (by positivity)
        nlinarith [show 0 ≤ 1 + 1 / (C : ℝ) by positivity]

private theorem prime_error_sums_le {P : Finset ℕ} {X S C : ℕ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesLE X ∧ 2 * C < p) (hS_pos : 0 < S) (hC_pos : 0 < C)
    (hS_eq : S = X / C) :
    2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p) +
        2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p) +
        (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2) ≤
      (X : ℝ) ^ 2 * S * (4 * (C : ℝ) * Real.log 4 + 4 * Real.log 4) := by
  have htheta_P : ∑ p ∈ P, Real.log p ≤ Real.log 4 * X := by
    calc ∑ p ∈ P, Real.log p
        ≤ ∑ p ∈ Nat.primesLE X, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ (hP p hp).1) fun p hp _ ↦
            Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
      _ = Chebyshev.theta X := (Chebyshev.theta_eq_sum_primesLE_log X).symm
      _ ≤ Real.log 4 * X := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hsum_p_le : ∑ p ∈ P, Real.log p / p ≤ Real.log 4 * X := by
    refine le_trans (Finset.sum_le_sum fun p hp ↦ ?_) htheta_P
    have hp_pr := (Nat.mem_primesLE.mp (hP p hp).1).2
    exact div_le_self (Real.log_nonneg (by exact_mod_cast hp_pr.one_le))
      (by exact_mod_cast hp_pr.one_le)
  have htail_sq : ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2 ≤ Real.log 4 / C := by
    calc ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (Nat.primesLE ⌊(X : ℝ)⌋₊).filter (fun p : ℕ ↦ (2 * (C : ℝ)) < p),
            Real.log p / (p : ℝ) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) (fun _ _ _ ↦ by positivity)
          rw [Nat.floor_natCast, Finset.mem_filter]
          exact ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2⟩
      _ ≤ 2 * Real.log 4 / (2 * (C : ℝ)) := sum_primesLE_log_div_sq_le (by positivity)
      _ = Real.log 4 / C := by field_simp
  have hX_le_2SC : (X : ℝ) ≤ 2 * S * C := by
    have hdiv : X < (S + 1) * C := by
      have hmod := Nat.div_add_mod X C
      have hlt := Nat.mod_lt X hC_pos
      nlinarith
    exact_mod_cast (by nlinarith : X ≤ 2 * S * C)
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he1 : 2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p) ≤
      (X : ℝ) ^ 2 * S * (4 * (C : ℝ) * Real.log 4) :=
    calc 2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p)
        ≤ 2 * (X : ℝ) ^ 2 * (Real.log 4 * X) :=
          mul_le_mul_of_nonneg_left hsum_p_le (by positivity)
      _ ≤ 2 * (X : ℝ) ^ 2 * (Real.log 4 * (2 * S * C)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX_le_2SC hlog4_nn) (by positivity)
      _ = (X : ℝ) ^ 2 * S * (4 * (C : ℝ) * Real.log 4) := by ring
  have he2 : 2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p) ≤ (X : ℝ) ^ 2 * S * (2 * Real.log 4) :=
    calc 2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p)
        ≤ 2 * (X : ℝ) * S * (Real.log 4 * X) :=
          mul_le_mul_of_nonneg_left htheta_P (by positivity)
      _ = (X : ℝ) ^ 2 * S * (2 * Real.log 4) := by ring
  have he3 : (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2) ≤
      (X : ℝ) ^ 2 * S * (2 * Real.log 4) :=
    calc (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2)
        ≤ (X : ℝ) ^ 3 * (Real.log 4 / C) := mul_le_mul_of_nonneg_left htail_sq (by positivity)
      _ = (X : ℝ) ^ 2 * X * (Real.log 4 / C) := by ring
      _ ≤ (X : ℝ) ^ 2 * (2 * S * C) * (Real.log 4 / C) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX_le_2SC (by positivity)) (by positivity)
      _ = (X : ℝ) ^ 2 * S * (2 * Real.log 4) := by
          have : (C : ℝ) ≠ 0 := by positivity
          field_simp
  linarith

end InertPrimeSum

/-- **Explicit Mertens bound for primes inert in `ℚ(√d)`.** For any squarefree integer `d ≠ 1`,
any integer `q ≥ 3` with `|d| ≤ q`, and any exponent `C ≥ 6` divisible by `3`, the sum of
`log p / p` over primes `2 * C < p ≤ q ^ C` with `jacobiSym d p = -1` is bounded by
`(1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * log (q ^ C) + (4 * C * log 4 + 4 * log 4 + 15)`. -/
theorem sum_primesLE_jacobiSym_eq_neg_one_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {q C : ℕ} (hq3 : 3 ≤ q) (hdq : d.natAbs ≤ q) (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1),
        Real.log p / (p : ℝ) ≤
      (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) +
        (4 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15) := by
  open InertPrimeSum in
  set X := q ^ C
  set S := X / C
  set N := q ^ (2 * (C / 3))
  obtain ⟨hX_pos, hS_pos, -, hdeg⟩ := grid_deg_lt_cube hq3 hC6 hC3
  set P := (Nat.primesLE X).filter fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1
  have hsum_log_le :
      ∑ p ∈ P, (2 * (∑ i : Fin X × Fin S, shiftExp p S i : ℝ)) * Real.log p ≤
        Real.log ((intGram d (baseFam d N X S)).det : ℝ) :=
    sum_shiftExp_mul_log_le_log_det hd hd1 (by omega) hX_pos hS_pos hdeg
  have hSX : S ≤ X := Nat.div_le_self X C
  have hlhs_ge :
      (X : ℝ) ^ 2 * S * (∑ p ∈ P, Real.log p / p) -
          2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p) -
          2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p) -
          (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2) ≤
        ∑ p ∈ P, (2 * (∑ i : Fin X × Fin S, shiftExp p S i : ℝ)) * Real.log p := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hp_pr := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_pr.one_le)
    have hexp := mul_le_mul_of_nonneg_right (two_mul_sum_shiftExp_ge hp_pr.pos hSX) hlog_nn
    linarith [show ((X : ℝ) ^ 2 * S / p - 2 * (X : ℝ) ^ 2 / p - 2 * X * S - (X : ℝ) ^ 3 / p ^ 2) *
        Real.log p =
      (X : ℝ) ^ 2 * S * (Real.log p / p) - 2 * (X : ℝ) ^ 2 * (Real.log p / p) -
        2 * (X : ℝ) * S * Real.log p - (X : ℝ) ^ 3 * (Real.log p / (p : ℝ) ^ 2) by ring]
  have hrhs_le := log_det_intGram_le_explicit hd hd1 hq3 hdq hC6 hC3
  have herr_sum := prime_error_sums_le
    (P := P) (fun _ hp ↦ ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩)
    hS_pos (by omega : 0 < C) rfl
  have hcomb : (X : ℝ) ^ 2 * S * (∑ p ∈ P, Real.log p / p) ≤
      (X : ℝ) ^ 2 * S *
        ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) +
          (4 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15)) := by
    linarith [hlhs_ge.trans (hsum_log_le.trans hrhs_le), herr_sum]
  exact le_of_mul_le_mul_left hcomb (by positivity : (0 : ℝ) < (X : ℝ) ^ 2 * S)

end TauCeti

/-- **Explicit Mertens bound for inert primes of a primitive quadratic character.** Over any
commutative ring `R` with `2 ≠ 0`, for any primitive nonprincipal quadratic Dirichlet character
`χ` mod `q ≥ 3` and any exponent `C ≥ 6` divisible by `3`, the sum of `log p / p` over primes
`p ≤ q ^ C` with `χ p = -1` is bounded by
`(1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * log (q ^ C) + (6 * C * log 4 + 4 * log 4 + 15)`. -/
theorem DirichletCharacter.IsPrimitive.sum_primesLE_filter_eq_neg_one_le {R : Type*}
    [CommRing R] [DecidableEq R] [NeZero (2 : R)] {q : ℕ} {χ : DirichletCharacter R q}
    (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (h1 : χ ≠ 1) (hq3 : 3 ≤ q)
    {C : ℕ} (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1),
        Real.log p / (p : ℝ) ≤
      (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) +
        (6 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15) := by
  have : NeZero q := ⟨by omega⟩
  have : Nontrivial R := ⟨⟨2, 0, NeZero.ne (2 : R)⟩⟩
  obtain ⟨d, hd, hd1, hdq_abs, hval⟩ := hprim.exists_squarefree_apply_eq_jacobiSym hquad h1
  have hdq : d.natAbs ≤ q := Int.ofNat_le.mp (Int.abs_eq_natAbs d ▸ hdq_abs)
  set S_all := (Nat.primesLE (q ^ C)).filter fun p : ℕ ↦ χ (p : ZMod q) = -1
  have hsplit := (Finset.sum_filter_add_sum_filter_not S_all (fun p : ℕ ↦ p ≤ 2 * C)
    (fun p : ℕ ↦ Real.log p / (p : ℝ))).symm
  have hsmall : ∑ p ∈ S_all.filter (· ≤ 2 * C), Real.log p / (p : ℝ) ≤ 2 * (C : ℝ) * Real.log 4 :=
    calc ∑ p ∈ S_all.filter (· ≤ 2 * C), Real.log p / (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE (2 * C), Real.log p := by
          refine (Finset.sum_le_sum fun p hp ↦ ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦
              Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
          · have hp_pr :=
              (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
            exact div_le_self (Real.log_nonneg (by exact_mod_cast hp_pr.one_le))
              (by exact_mod_cast hp_pr.one_le)
          · obtain ⟨hpS, hp2C⟩ := Finset.mem_filter.mp hp
            exact Nat.mem_primesLE.mpr ⟨hp2C, (Nat.mem_primesLE.mp (Finset.mem_filter.mp hpS).1).2⟩
      _ = Chebyshev.theta (2 * C : ℕ) := (Chebyshev.theta_eq_sum_primesLE_log (2 * C)).symm
      _ ≤ Real.log 4 * (2 * C : ℕ) := Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = 2 * (C : ℝ) * Real.log 4 := by push_cast; ring
  have hlarge_sub : S_all.filter (¬ · ≤ 2 * C) ⊆
      (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1) := by
    intro p hp
    obtain ⟨hpS, hp2C⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX, hχp⟩ := Finset.mem_filter.mp hpS
    have hp_pr := (Nat.mem_primesLE.mp hpX).2
    have hgt : 2 * C < p := Nat.lt_of_not_ge hp2C
    have hjac_cast : (jacobiSym d p : R) = -1 :=
      (hval p (hp_pr.odd_of_ne_two (by omega))).symm.trans hχp
    rcases jacobiSym.trichotomy d p with h0 | h1' | hm1
    · rw [h0, Int.cast_zero, eq_comm, neg_eq_zero] at hjac_cast
      exact absurd hjac_cast one_ne_zero
    · rw [h1', Int.cast_one] at hjac_cast
      exact absurd (calc (2 : R) = 1 - (-1) := by ring
        _ = 0 := by rw [← hjac_cast, sub_self]) (NeZero.ne (2 : R))
    · exact Finset.mem_filter.mpr ⟨hpX, hgt, hm1⟩
  have hlarge := (Finset.sum_le_sum_of_subset_of_nonneg hlarge_sub fun _ _ _ ↦ by positivity).trans
    (TauCeti.sum_primesLE_jacobiSym_eq_neg_one_le hd hd1 hq3 hdq hC6 hC3)
  linarith

namespace TauCeti

open scoped Classical in
/-- **Inert primes carry at most three quarters of the Mertens mass** (Green, Theorem 1.1).
For every sufficiently large exponent `C` divisible by `3`, there is a constant `K` such that for
every modulus `q ≥ 3` and every primitive nonprincipal quadratic Dirichlet character `χ` mod `q`,
`∑_{p ≤ q ^ C, χ p = -1} log p / p ≤ 3 / 4 * log (q ^ C) + K`. -/
theorem inert_prime_sum_le :
    ∃ C₀ : ℕ, ∀ C : ℕ, C₀ ≤ C → 3 ∣ C → ∃ K : ℝ,
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        3 ≤ q → χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
        ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1),
            Real.log p / (p : ℝ) ≤
          3 / 4 * Real.log ((q : ℝ) ^ C) + K := by
  refine ⟨15, fun C hC15 hC3 ↦ ⟨6 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15,
    fun q χ hq3 hprim hquad h1 ↦ ?_⟩⟩
  have hbound := hprim.sum_primesLE_filter_eq_neg_one_le hquad h1 hq3 (by omega) hC3
  have hinv : 1 / (C : ℝ) ≤ 1 / 15 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hC15)
  have hinv2 : 1 / (2 * (C : ℝ)) ≤ 1 / 30 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 30 ≤ 2 * C))
  have hcoeff : (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) ≤ 3 / 4 := by
    calc (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ)))
        ≤ (1 + (1 : ℝ) / 15) * (2 / 3 + 1 / 30) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ ≤ 3 / 4 := by norm_num
  have hlog_nn : 0 ≤ Real.log ((q : ℝ) ^ C) :=
    Real.log_nonneg (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q)))
  nlinarith

end TauCeti
