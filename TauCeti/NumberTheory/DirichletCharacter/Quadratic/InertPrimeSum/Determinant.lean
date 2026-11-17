/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Zsqrtd.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.InnerProductSpace.Gram.ChangeOfFamily
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Green's Gram determinant for jet evaluations in `ℤ√d`

For a squarefree integer `d ≠ 1` and parameters `N, R, S : ℕ` satisfying the planar-grid degree
condition `N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3`, consider the `R * S` basis
polynomials `z ^ r * z' ^ s ∈ (ℤ√d)[z', z]` (`r < R`, `s < S`) together with their jet evaluations
`∂_z ^ j P(x + y√d, x - y√d)` on the grid `{0, …, N - 1}³`. Embedding `ℤ√d` into `ℝ²` via the
trace pairing `2 * (a₁ a₂ + |d| b₁ b₂)` gives an `(R * S) × (R * S)` integer Gram matrix `G`:

1. **Positivity (`1 ≤ G.det`).** Any real linear relation among the jet vectors gives a complex
   bivariate polynomial of bidegree `< (R, S)` vanishing to order `N` in `z` at `(x + y√d, x - y√d)`
   for all `x, y < N`, which is forced to vanish by
   `Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`.
2. **Archimedean upper bound.** Hadamard's inequality (`Matrix.log_det_gram_le`) bounds `log G.det`
   in terms of `N, R, S` and `|d|`.
3. **`p`-adic divisibility.** At every odd prime `p` with `jacobiSym d p = -1`, Frobenius in
   `ℤ√d / (p)` flips `√d`, so the unitriangular change of family
   `z ^ r * z' ^ s ↦ z ^ (r - p * h) * (z ^ p - z') ^ h * z' ^ s` with
   `h = min (r / p) (S - 1 - s)` preserves `G.det` (`Matrix.det_gram_sum_smul_of_det_eq_one`)
   and makes every `j`-th derivative divisible by `p ^ h`.

## Main results

* `TauCeti.exists_pos_nat_log_le_and_pow_dvd_of_jacobiSym_eq_neg_one`: existence of a positive
  natural number `D` (namely `G.det`) satisfying both the Hadamard upper bound and the simultaneous
  `p`-adic divisibilities at all odd primes `p` with `jacobiSym d p = -1`.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon **2610.00311** (2026), §§2–5.
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

private theorem csqrt_mul_self (d : ℤ) : csqrt d * csqrt d = d := by
  dsimp [csqrt]
  split_ifs with hd
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hd), Complex.ofReal_intCast]
  · have hdR : (0 : ℝ) ≤ -d := by exact_mod_cast (by omega : (0 : ℤ) ≤ -d)
    calc (Complex.I * Real.sqrt (-d : ℝ)) * (Complex.I * Real.sqrt (-d : ℝ))
        = (Complex.I * Complex.I) * ((Real.sqrt (-d : ℝ) * Real.sqrt (-d : ℝ) : ℝ) : ℂ) := by
          push_cast; ring
      _ = d := by rw [Complex.I_mul_I, Real.mul_self_sqrt hdR]; push_cast; ring

private theorem norm_csqrt (d : ℤ) : ‖csqrt d‖ = Real.sqrt d.natAbs := by
  dsimp [csqrt]
  split_ifs with hd
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Nat.cast_natAbs, Int.cast_abs,
      abs_of_nonneg (by exact_mod_cast hd)]
  · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Nat.cast_natAbs, Int.cast_abs,
      abs_of_neg (by exact_mod_cast not_le.mp hd)]

private theorem csqrt_ne_zero {d : ℤ} (hd : d ≠ 0) : csqrt d ≠ 0 := fun h0 ↦
  hd (by simpa [h0] using (csqrt_mul_self d).symm)

/-- The two complex embeddings `a + b√d ↦ a ± b csqrt(d)` of `ℤ√d`. -/
private noncomputable def embPos (d : ℤ) : ℤ√d →+* ℂ :=
  Zsqrtd.lift ⟨csqrt d, csqrt_mul_self d⟩

private noncomputable def embNeg (d : ℤ) : ℤ√d →+* ℂ :=
  Zsqrtd.lift ⟨-csqrt d, by simp [csqrt_mul_self]⟩

private theorem embPos_apply (d : ℤ) (u : ℤ√d) :
    embPos d u = (u.re : ℂ) + (u.im : ℂ) * csqrt d := rfl

private theorem embNeg_apply (d : ℤ) (u : ℤ√d) :
    embNeg d u = (u.re : ℂ) + (u.im : ℂ) * (-csqrt d) := rfl

private theorem embPos_injective {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    Function.Injective (embPos d) := by
  refine Zsqrtd.lift_injective _ fun n hn ↦ ?_
  rcases Int.isUnit_iff.mp (hd n (hn ▸ dvd_rfl)) with rfl | rfl <;> simp_all

/-- Parallelogram identity relating the weighted coordinate norm on `ℤ√d` to the two complex
embeddings, uniformly in the sign of `d`. -/
private theorem two_mul_re_sq_add_im_sq_eq (d : ℤ) (u : ℤ√d) :
    2 * ((u.re : ℝ) ^ 2 + (d.natAbs : ℝ) * (u.im : ℝ) ^ 2) =
      ‖embPos d u‖ ^ 2 + ‖embNeg d u‖ ^ 2 := by
  have hpar (z w : ℂ) : ‖z + w‖ ^ 2 + ‖z - w‖ ^ 2 = 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  rw [embPos_apply, embNeg_apply, mul_neg, ← sub_eq_add_neg, hpar, Complex.norm_intCast,
    norm_mul, Complex.norm_intCast, norm_csqrt, mul_pow, sq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

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
  induction s using Finset.cons_induction with
  | empty => ext p; simp [zsqrtdFamToLp]
  | cons a t ha ih =>
    simp_rw [Finset.sum_cons]
    rw [← ih]
    ext p
    rcases Fin.eq_zero_or_eq_succ p.2 with hp | ⟨j, hj⟩
    · simp [zsqrtdFamToLp, hp, zsmul_eq_mul]; ring
    · simp [zsqrtdFamToLp, hj, zsmul_eq_mul]; ring

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
  have hd : Real.sqrt (2 * (d.natAbs : ℝ)) * Real.sqrt (2 * (d.natAbs : ℝ)) = 2 * |(d : ℝ)| := by
    rw [Real.mul_self_sqrt (by positivity), Nat.cast_natAbs, Int.cast_abs]
  linear_combination (v k).re * (w k).re * h2 + (v k).im * (w k).im * hd

private theorem norm_sq_zsqrtdFamToLp (d : ℤ) {κ : Type*} [Fintype κ] (v : κ → ℤ√d) :
    ‖zsqrtdFamToLp d v‖ ^ 2 = ∑ k : κ, (‖embPos d (v k)‖ ^ 2 + ‖embNeg d (v k)‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_zsqrtdFamToLp]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := two_mul_re_sq_add_im_sq_eq d (v k)
  rw [Nat.cast_natAbs, Int.cast_abs] at h
  linear_combination h

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
            rw [smul_add, smul_smul, smul_sub, add_smul, sub_smul]
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

private theorem norm_emb_baseFam_le {d : ℤ} (hd0 : d ≠ 0) {N R S : ℕ}
    (hN : 0 < N) (hR : 0 < R) (i : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
    ‖embPos d (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1) ∧
      ‖embNeg d (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1) := by
  have hsq1 : (1 : ℝ) ≤ Real.sqrt d.natAbs := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Int.natAbs_pos.mpr hd0)
  have h2Nd_ge : (1 : ℝ) ≤ 2 * N * Real.sqrt d.natAbs := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hpt (sgn : ℤ) (hsgn : |sgn| ≤ 1) (ε : ℂ) (hε : ‖ε‖ = ‖csqrt d‖) :
      ‖((k.1.1 : ℂ) + ((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ) * ε)‖ ≤ 2 * N * Real.sqrt d.natAbs := by
    have hx : (k.1.1 : ℝ) ≤ N := by exact_mod_cast k.1.2.le
    have hy : ‖((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ)‖ ≤ N := by
      rw [Complex.norm_intCast, ← Int.cast_abs, abs_mul, Int.abs_natCast]
      have : |sgn| * (k.2.1.1 : ℤ) ≤ N := by
        simpa using mul_le_mul hsgn (by exact_mod_cast k.2.1.2.le) (by positivity) (by omega)
      exact_mod_cast this
    calc ‖(k.1.1 : ℂ) + ((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ) * ε‖
        ≤ ‖(k.1.1 : ℂ)‖ + ‖((sgn * (k.2.1.1 : ℤ) : ℤ) : ℂ)‖ * ‖ε‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ N + N * Real.sqrt d.natAbs := by
          rw [Complex.norm_natCast, hε, norm_csqrt]
          exact add_le_add hx (mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg _))
      _ ≤ 2 * N * Real.sqrt d.natAbs := by nlinarith
  have hdesc : (i.1.1.descFactorial k.2.2.1 : ℝ) ≤ (R : ℝ) ^ N := by
    have h1 : i.1.1.descFactorial k.2.2.1 ≤ R ^ N :=
      (Nat.descFactorial_le_pow _ _).trans
        ((Nat.pow_le_pow_left i.1.2.le _).trans (Nat.pow_le_pow_right hR k.2.2.2.le))
    exact_mod_cast h1
  have hbound (φ : ℤ√d →+* ℂ) (ε : ℂ) (hε : ‖ε‖ = ‖csqrt d‖)
      (hφ : ∀ a b : ℤ, φ ⟨a, b⟩ = (a : ℂ) + (b : ℂ) * ε) :
      ‖φ (baseFam d N R S i k)‖ ≤ (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1) := by
    rw [jetEval_basePoly_eq, map_mul, map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_mul,
      norm_pow, norm_pow, Complex.norm_natCast]
    have hp1 : ‖φ ⟨k.1.1, -(k.2.1.1 : ℤ)⟩‖ ≤ 2 * N * Real.sqrt d.natAbs := by
      simpa [hφ] using hpt (-1) (by norm_num) ε hε
    have hp2 : ‖φ ⟨k.1.1, (k.2.1.1 : ℤ)⟩‖ ≤ 2 * N * Real.sqrt d.natAbs := by
      simpa [hφ] using hpt 1 (by norm_num) ε hε
    calc ‖φ ⟨k.1.1, -k.2.1.1⟩‖ ^ i.2.1 * i.1.1.descFactorial k.2.2.1 *
            ‖φ ⟨k.1.1, k.2.1.1⟩‖ ^ (i.1.1 - k.2.2.1)
        ≤ (2 * N * Real.sqrt d.natAbs) ^ i.2.1 * (R : ℝ) ^ N *
            (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 - k.2.2.1) := by
          gcongr
      _ = (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 - k.2.2.1 + i.2.1) := by
          rw [pow_add]; ring
      _ ≤ (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h2Nd_ge (by omega)) (by positivity)
  exact ⟨hbound (embPos d) (csqrt d) rfl (fun _ _ ↦ rfl),
    hbound (embNeg d) (-csqrt d) (norm_neg _) (fun _ _ ↦ rfl)⟩

private theorem two_mul_log_norm_baseVec_le {d : ℤ} (hd0 : d ≠ 0) {N R S : ℕ}
    (hN : 0 < N) (hR : 0 < R) {i : Fin R × Fin S} (hi : baseVec d N R S i ≠ 0) :
    2 * Real.log ‖baseVec d N R S i‖ ≤
      Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R +
        2 * ((i.1.1 : ℝ) + i.2.1) * Real.log (2 * N * Real.sqrt d.natAbs) := by
  have hv0 : 0 < ‖baseVec d N R S i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi)
  have hsq : ‖baseVec d N R S i‖ ^ 2 ≤
      2 * (N : ℝ) ^ 3 * ((R : ℝ) ^ N) ^ 2 *
        ((2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1)) ^ 2 := by
    rw [baseVec, norm_sq_zsqrtdFamToLp]
    calc ∑ k : Fin N × Fin N × Fin N,
            (‖embPos d (baseFam d N R S i k)‖ ^ 2 + ‖embNeg d (baseFam d N R S i k)‖ ^ 2)
        ≤ ∑ _k : Fin N × Fin N × Fin N,
            2 * ((R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1)) ^ 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          obtain ⟨h1, h2⟩ := norm_emb_baseFam_le hd0 hN hR i k
          have hp1 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h1
          have hp2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h2
          linarith
      _ = 2 * (N : ℝ) ^ 3 * ((R : ℝ) ^ N) ^ 2 *
            ((2 * N * Real.sqrt d.natAbs) ^ (i.1.1 + i.2.1)) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  have : (0 : ℝ) < Real.sqrt d.natAbs :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr hd0)
  have hlog := Real.log_le_log hv0 hsq
  rw [Real.log_pow, Nat.cast_ofNat, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **Fact 2: Hadamard upper bound on `log G.det`.** -/
private theorem log_det_intGram_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {N R S : ℕ} (hN : 0 < N) (hR : 0 < R) (hS : 0 < S)
    (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    Real.log ((intGram d (baseFam d N R S)).det : ℝ) ≤
      (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
        (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt d.natAbs) := by
  rw [cast_det_intGram]
  have hlin := linearIndependent_baseVec hd hd1 hR hS hdeg
  have hsq1 : (1 : ℝ) ≤ Real.sqrt d.natAbs := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Int.natAbs_pos.mpr hd.ne_zero)
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
            2 * ((i.1.1 : ℝ) + i.2.1) * Real.log (2 * N * Real.sqrt d.natAbs)) :=
        Finset.sum_le_sum fun i _ ↦
          two_mul_log_norm_baseVec_le hd.ne_zero hN hR (hlin.ne_zero i)
    _ = (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (∑ i : Fin R × Fin S, 2 * ((i.1.1 : ℝ) + i.2.1)) *
            Real.log (2 * N * Real.sqrt d.natAbs) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
        push_cast; ring
    _ ≤ (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt d.natAbs) := by
        have hlog_nn : 0 ≤ Real.log (2 * N * Real.sqrt d.natAbs) :=
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
private theorem inert_frobenius_sub_conj {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hjac : jacobiSym d p = -1) (x y : ℤ) :
    (p : ℤ√d) ∣ (⟨x, y⟩ : ℤ√d) ^ p - ⟨x, -y⟩ := by
  have : Fact p.Prime := ⟨hp⟩
  have hdec : (⟨x, y⟩ : ℤ√d) = (x : ℤ√d) + (y : ℤ√d) * Zsqrtd.sqrtd := by ext <;> simp
  rw [hdec, add_pow_prime_split _ _ hp.pos]
  set S := ∑ i ∈ Finset.range (p - 1),
      (x : ℤ√d) ^ (i + 1) * ((y : ℤ√d) * Zsqrtd.sqrtd) ^ (p - (i + 1)) * (p.choose (i + 1) : ℤ√d)
  have hmid : (p : ℤ√d) ∣ S := by
    refine Finset.dvd_sum fun i hi ↦ dvd_mul_of_dvd_right ?_ _
    obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero i)
      (by have := Finset.mem_range.mp hi; omega)
    exact ⟨c, by exact_mod_cast hc⟩
  have hsqrtd_pow : (Zsqrtd.sqrtd : ℤ√d) ^ p = ((d ^ (p / 2) : ℤ) : ℤ√d) * Zsqrtd.sqrtd := by
    obtain ⟨k, hk⟩ := hodd
    rw [show p / 2 = k by omega, hk, pow_add, pow_one, pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow]
  have hx_dvd : (p : ℤ) ∣ x ^ p - x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp [ZMod.pow_card]
  have hy_dvd : (p : ℤ) ∣ y ^ p * d ^ (p / 2) + y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, ← legendreSym.eq_pow, jacobiSym.legendreSym.to_jacobiSym, hjac]
    ring
  have hrem : (p : ℤ√d) ∣ ((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + (x : ℤ√d) ^ p - ⟨x, -y⟩ := by
    have hrem_eq : ((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + (x : ℤ√d) ^ p - ⟨x, -y⟩ =
        ⟨x ^ p - x, y ^ p * d ^ (p / 2) + y⟩ := by
      rw [mul_pow, hsqrtd_pow, ← mul_assoc, ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_pow]
      ext <;> simp [-Int.cast_pow, -Int.cast_mul]
    rw [hrem_eq, ← Int.cast_natCast, Zsqrtd.intCast_dvd]
    exact ⟨hx_dvd, hy_dvd⟩
  rw [show ((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + S + (x : ℤ√d) ^ p - ⟨x, -y⟩ =
    S + (((y : ℤ√d) * Zsqrtd.sqrtd) ^ p + (x : ℤ√d) ^ p - ⟨x, -y⟩) by ring]
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
    (hodd : Odd p) (hjac : jacobiSym d p = -1) (x y : ℤ) :
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
      dsimp [c]; rw [← C_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd, C_eq_natCast]
    rw [hc]; ring
  linear_combination hconst + hsum_eq

/-- Every jet evaluation of `shiftPoly d p i` at an inert odd prime `p` is divisible by `p ^ h`. -/
private theorem pow_dvd_shiftFam {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : Odd p)
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
private theorem pow_dvd_det_intGram {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : Odd p)
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

end InertPrimeSum

/-- **Green's Gram determinant for jet evaluations in `ℤ√d`.** For a squarefree integer `d ≠ 1`
and parameters `N, R, S : ℕ` satisfying `N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3`,
there exists a positive natural number `D` satisfying both the Hadamard upper bound
`log D ≤ R * S * (log (2 * N ^ 3) + 2 * N * log R) + R * S * (R + S) * log (2 * N * √|d|)`
and, at every odd prime `p` with `jacobiSym d p = -1`, the `p`-adic divisibility
`p ^ (2 * ∑ i : Fin R × Fin S, min (i.1 / p) (S - 1 - i.2)) ∣ D`. -/
theorem exists_pos_nat_log_le_and_pow_dvd_of_jacobiSym_eq_neg_one {d : ℤ} (hd : Squarefree d)
    (hd1 : d ≠ 1) {N R S : ℕ}
    (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    ∃ D : ℕ, 0 < D ∧
      Real.log (D : ℝ) ≤
        (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt d.natAbs) ∧
      ∀ p : ℕ, p.Prime → Odd p → jacobiSym d p = -1 →
        p ^ (2 * ∑ i : Fin R × Fin S, min (i.1.1 / p) (S - 1 - i.2.1)) ∣ D := by
  open InertPrimeSum in
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact ⟨1, Nat.one_pos, by simp, fun _ _ _ _ ↦ by simp⟩
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · exact ⟨1, Nat.one_pos, by simp, fun _ _ _ _ ↦ by simp⟩
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp at hdeg
    · exact hN
  have h1 : 1 ≤ (intGram d (baseFam d N R S)).det :=
    one_le_det_intGram hd hd1 hR hS hdeg
  set D := (intGram d (baseFam d N R S)).det.toNat
  have hD_cast : (D : ℤ) = (intGram d (baseFam d N R S)).det := Int.toNat_of_nonneg (by omega)
  refine ⟨D, by omega, ?_, fun p hp hodd hjac ↦ ?_⟩
  · have hD_real : (D : ℝ) = ((intGram d (baseFam d N R S)).det : ℝ) := by exact_mod_cast hD_cast
    rw [hD_real]
    exact log_det_intGram_le hd hd1 hN hR hS hdeg
  · rw [← Int.ofNat_dvd, Nat.cast_pow, hD_cast]
    exact pow_dvd_det_intGram hp hodd hjac N R S

end TauCeti
