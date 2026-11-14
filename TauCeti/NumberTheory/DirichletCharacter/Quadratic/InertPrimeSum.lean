/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Order.Prod.Lex.Basic
import TauCeti.Algebra.MvPolynomial.Fin.Two
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.QuadraticOrder.Frobenius
import TauCeti.RingTheory.MvPolynomial.BivariateMultiplicity
import TauCeti.RingTheory.MvPolynomial.DerivativeIdealPow

/-!
# Upper bound on the reciprocal-prime sum over inert primes of a quadratic character

Let `χ` be a nontrivial primitive quadratic Dirichlet character modulo `q`. By Kronecker's
realization (`DirichletCharacter.IsPrimitive.exists_squarefree_apply_eq_jacobiSym`), there is a
squarefree integer `d ≠ 1` with `|d| ≤ q` such that `χ n = (d / n)` for every odd `n`. At every
odd prime `p` with `χ p = -1`, `d` is a quadratic nonresidue modulo `p`, so the integral Frobenius
congruence `z ^ p ≡ star z (mod p)` holds throughout the quadratic order `ℤ[√d]`
(`QuadraticAlgebra.frobenius_congruence`).

Following Green, we compare three estimates on the determinant of an integral Gram matrix `G`
indexed by `Fin R ×ₗ Fin S` (`R = X`, `S = X / C + 1`, `X = q ^ C`, `N = q ^ (2 * c)` for
`C = 3 * c ≥ 18`), built from the `X₀`-jets of order `< N` of the monomials `X₀ ^ r * X₁ ^ s` at
the `N × N` grid of conjugate pairs `(x + y√d, x - y√d)` (`0 ≤ x, y < N`):

1. **Positivity (`det G ≥ 1`).** If the rows of the embedded evaluation matrix were `ℂ`-linearly
   dependent, a nonzero bivariate polynomial of bidegree `< (R, S)` would vanish to `X₀`-order at
   least `N` at all `N²` conjugate grid points, contradicting
   `MvPolynomial.eq_zero_of_forall_eval_iterate_pderiv_eq_zero_conjugate_grid` since
   `2 * R * S + N * (R + S) < N ^ 3`.
2. **Archimedean upper bound (Hadamard's inequality).** Applying `Matrix.log_re_det_gram_le` to the
   row vectors in `EuclideanSpace ℂ ((Fin N × Fin N × Fin N) × Bool)` bounds `log (det G)` from
   above by `(1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * S * X ^ 2 * log X + O_C(S * X ^ 2)`. For
   `C ≥ 18`, the leading coefficient `(19 / 18) * (25 / 36) = 475 / 648` is strictly below `3 / 4`.
3. **`p`-adic lower bound (Frobenius divisibility).** At each prime `p ≥ C` with `χ p = -1`, a
   unitriangular basis change replaces `X₀ ^ r * X₁ ^ s` by
   `X₀ ^ (r - p * h) * X₁ ^ s * (X₀ ^ p - X₁) ^ h` (`h = min (r / p) (S - 1 - s)`). By the
   integral Frobenius congruence and the Leibniz ideal-power rule
   (`MvPolynomial.pderiv_prod_mem_ideal_pow`), row `a` of the transformed evaluation matrix is
   divisible by `p ^ h`, so `p ^ (2 * ∑ h)` divides `det G`. Summing over `p` and applying
   Chebyshev's bound `θ(X) = O(X)` produces `S * X ^ 2 * ∑_{p ≤ X, χ(p) = -1} log p / p` up to
   `O_C(S * X ^ 2)`.

## Main results

* `DirichletCharacter.IsPrimitive.sum_primesLE_log_div_le`: for `C ≥ 18` with `3 ∣ C`, the sum
  `∑_{p ≤ q ^ C, χ p = -1} log p / p` for any nontrivial primitive quadratic character `χ` modulo
  `q` (taking values in a commutative ring `R` with `DecidableEq R` and `2 ≠ 0`) is at most
  `3 / 4 * log (q ^ C) + K(C)` for an explicit constant `K(C)`.
* `TauCeti.inert_prime_sum_le`: specialization to complex-valued Dirichlet characters.

## References

* [B. Green, *On Landau–Siegel zeros*][green2026], Theorem 1.1 and §§2–6.
* [OpenAI, *Uniform exclusion of Landau–Siegel zeros*][openai2026], Theorem 1, §2, §6.
* [T. Tao, *A sketch of the proof of non-existence of Siegel zeroes*][tao2026].
-/

public section

open scoped Finset Matrix

namespace TauCeti

namespace InertPrimeSum

/-! ### Complex embeddings and integral pairing on `ℤ[√d]` -/

/-- Chosen complex square root of `d`: `√d` for `d ≥ 0` and `i √(-d)` for `d < 0`. -/
private noncomputable def quadTheta (d : ℤ) : ℂ :=
  if 0 ≤ d then ((Real.sqrt (d : ℝ) : ℝ) : ℂ) else Complex.I * ((Real.sqrt (-d : ℝ) : ℝ) : ℂ)

private theorem quadTheta_sq (d : ℤ) : (quadTheta d) ^ 2 = (d : ℂ) := by
  dsimp [quadTheta]
  split_ifs with hd
  · have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [← Complex.ofReal_pow, Real.sq_sqrt hdR, Complex.ofReal_intCast]
  · have hdR : (0 : ℝ) ≤ (-d : ℝ) := by push Not at hd; exact_mod_cast (by omega : 0 ≤ -d)
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hdR]
    push_cast
    ring

private theorem norm_quadTheta (d : ℤ) : ‖quadTheta d‖ = Real.sqrt (d.natAbs : ℝ) := by
  dsimp [quadTheta]
  split_ifs with hd
  · have hnat : (d.natAbs : ℝ) = (d : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hd]
    rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _), hnat]
  · push Not at hd
    have hnat : (d.natAbs : ℝ) = -(d : ℝ) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hd.le, Int.cast_neg]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), hnat]

/-- If `d` is squarefree and `d ≠ 1`, then `1` and `quadTheta d` are linearly independent over `ℤ`.
-/
private theorem quadTheta_linearIndependent {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    ∀ a b : ℤ, (a : ℂ) + (b : ℂ) * quadTheta d = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have ha_eq : (a : ℂ) = -(b : ℂ) * quadTheta d := by linear_combination hab
  have hsqC : ((a ^ 2 : ℤ) : ℂ) = ((b ^ 2 * d : ℤ) : ℂ) := by
    push_cast
    calc
      (a : ℂ) ^ 2 = (-(b : ℂ) * quadTheta d) ^ 2 := by rw [ha_eq]
      _ = (b : ℂ) ^ 2 * (quadTheta d) ^ 2 := by ring
      _ = (b : ℂ) ^ 2 * (d : ℂ) := by rw [quadTheta_sq]
  have hsq : a ^ 2 = b ^ 2 * d := Int.cast_injective hsqC
  by_cases hb : b = 0
  · subst hb
    have ha0 : a ^ 2 = 0 := by simpa using hsq
    exact ⟨sq_eq_zero_iff.mp ha0, rfl⟩
  exfalso
  obtain ⟨g, a', b', hg, rfl, rfl, hcop⟩ :
      ∃ g a' b' : ℤ, g ≠ 0 ∧ a = g * a' ∧ b = g * b' ∧ IsCoprime a' b' := by
    refine ⟨(a.gcd b : ℤ), a / a.gcd b, b / a.gcd b, ?_,
      (Int.mul_ediv_cancel' (Int.gcd_dvd_left a b)).symm,
      (Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)).symm, ?_⟩
    · exact Nat.cast_ne_zero.mpr (Int.gcd_ne_zero_right hb)
    · exact Int.isCoprime_iff_gcd_eq_one.mpr
        (Int.gcd_ediv_gcd_ediv_gcd (Nat.pos_of_ne_zero (Int.gcd_ne_zero_right hb)))
  have hsq' : a' ^ 2 = b' ^ 2 * d :=
    mul_left_cancel₀ (pow_ne_zero 2 hg) (by linear_combination hsq)
  obtain ⟨u, v, huv⟩ : IsCoprime (a' ^ 2) b' := hcop.pow_left
  have hb'_unit : IsUnit b' :=
    isUnit_iff_exists_inv.mpr ⟨u * b' * d + v, by linear_combination huv - u * hsq'⟩
  have hb'2 : b' ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hb'_unit with rfl | rfl <;> norm_num
  have hd_eq : d = a' * a' := by rw [hb'2, one_mul] at hsq'; linear_combination -hsq'
  have ha'_unit : IsUnit a' := hd a' ⟨1, by linear_combination hd_eq⟩
  have ha'2 : a' * a' = 1 := by
    rcases Int.isUnit_iff.mp ha'_unit with rfl | rfl <;> norm_num
  exact hd1 (hd_eq.trans ha'2)

/-- Ring homomorphism `ℤ[√d] →+* ℂ` sending `ω` to `+quadTheta d` (`sgn = true`) or
`-quadTheta d` (`sgn = false`). -/
private noncomputable def embedSign (d : ℤ) (sgn : Bool) : QuadraticAlgebra ℤ d 0 →+* ℂ :=
  (QuadraticAlgebra.lift
    ⟨if sgn then quadTheta d else -quadTheta d, by
      cases sgn <;> simp [← sq, quadTheta_sq, zsmul_eq_mul]⟩ :
    QuadraticAlgebra ℤ d 0 →ₐ[ℤ] ℂ).toRingHom

@[simp]
private theorem embedSign_apply (d : ℤ) (sgn : Bool) (z : QuadraticAlgebra ℤ d 0) :
    embedSign d sgn z =
      (z.re : ℂ) + (z.im : ℂ) * (if sgn then quadTheta d else -quadTheta d) := by
  simp [embedSign, zsmul_eq_mul]

/-- Positive-definite symmetric `ℤ`-bilinear pairing `2 * (z.re * w.re + |d| * z.im * w.im)` on
`ℤ[√d]`. -/
private def intPair (d : ℤ) (z w : QuadraticAlgebra ℤ d 0) : ℤ :=
  2 * (z.re * w.re + (d.natAbs : ℤ) * z.im * w.im)

private theorem star_embedSign_add_eq_intPair (d : ℤ) (z w : QuadraticAlgebra ℤ d 0) :
    star (embedSign d true z) * embedSign d true w +
        star (embedSign d false z) * embedSign d false w =
      (intPair d z w : ℂ) := by
  simp only [embedSign_apply, ↓reduceIte, Bool.false_eq_true, map_add, map_mul,
    Complex.star_def, map_intCast, map_neg, intPair]
  by_cases hd : 0 ≤ d
  · have hconj : (starRingEnd ℂ) (quadTheta d) = quadTheta d := by
      simp [quadTheta, hd, Complex.conj_ofReal]
    have hd_abs : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd
    rw [hconj, hd_abs]
    push_cast
    linear_combination 2 * (z.im : ℂ) * (w.im : ℂ) * quadTheta_sq d
  · push Not at hd
    have hconj : (starRingEnd ℂ) (quadTheta d) = -quadTheta d := by
      simp [quadTheta, not_le.mpr hd, Complex.conj_ofReal]
    have hd_abs : (d.natAbs : ℤ) = -d := by omega
    rw [hconj, hd_abs]
    push_cast
    linear_combination -2 * (z.im : ℂ) * (w.im : ℂ) * quadTheta_sq d

/-! ### Jet evaluation matrix and Gram determinant (Facts 1 and 2) -/

private abbrev Idx (R S : ℕ) := Fin R ×ₗ Fin S

private abbrev Pt (N : ℕ) := Fin N × Fin N × Fin N

private theorem iterate_pderiv_X_zero_pow_mul_X_one_pow {A : Type*} [CommSemiring A]
    (r s j : ℕ) :
    (MvPolynomial.pderiv 0)^[j] (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ s :
        MvPolynomial (Fin 2) A) =
      (r.descFactorial j : MvPolynomial (Fin 2) A) *
        MvPolynomial.X 0 ^ (r - j) * MvPolynomial.X 1 ^ s := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, ← MvPolynomial.C_eq_natCast, mul_assoc,
      MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X_of_ne (by decide), MvPolynomial.C_eq_natCast]
    simp only [mul_one, mul_zero, add_zero, Nat.descFactorial_succ, Nat.cast_mul, Nat.sub_sub]
    by_cases hlt : r ≤ j
    · simp [Nat.sub_eq_zero_of_le hlt]
    · ring

/-- Jet value in `ℤ[√d]` of `X₀ ^ r * X₁ ^ s` at grid index `t = (x, y, j)`. -/
private noncomputable def jetEntry (d : ℤ) {R S N : ℕ} (a : Idx R S) (t : Pt N) :
    QuadraticAlgebra ℤ d 0 :=
  MvPolynomial.eval
    ![(⟨(t.1 : ℤ), (t.2.1 : ℤ)⟩ : QuadraticAlgebra ℤ d 0),
      (⟨(t.1 : ℤ), -(t.2.1 : ℤ)⟩ : QuadraticAlgebra ℤ d 0)]
    ((MvPolynomial.pderiv 0)^[t.2.2.val]
      (MvPolynomial.X 0 ^ (ofLex a).1.val * MvPolynomial.X 1 ^ (ofLex a).2.val))

private theorem embedSign_jetEntry (d : ℤ) (sgn : Bool) {R S N : ℕ} (a : Idx R S) (t : Pt N) :
    embedSign d sgn (jetEntry d a t) =
      let θs := if sgn then quadTheta d else -quadTheta d
      MvPolynomial.eval ![(t.1 : ℂ) + (t.2.1 : ℂ) * θs, (t.1 : ℂ) - (t.2.1 : ℂ) * θs]
        ((MvPolynomial.pderiv 0)^[t.2.2.val]
          (MvPolynomial.X 0 ^ (ofLex a).1.val * MvPolynomial.X 1 ^ (ofLex a).2.val)) := by
  dsimp only [jetEntry]
  rw [iterate_pderiv_X_zero_pow_mul_X_one_pow, iterate_pderiv_X_zero_pow_mul_X_one_pow]
  simp only [map_mul, map_pow, map_natCast, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, embedSign_apply, Int.cast_natCast, Int.cast_neg, neg_mul]
  rfl

/-- Integral Gram matrix of the jet rows under `intPair d`. -/
private noncomputable def intGram (d : ℤ) (R S N : ℕ) : Matrix (Idx R S) (Idx R S) ℤ :=
  Matrix.of fun a b ↦ ∑ t : Pt N, intPair d (jetEntry d a t) (jetEntry d b t)

/-- Embedded row vector in `EuclideanSpace ℂ (Pt N × Bool)`. -/
private noncomputable def rowVec (d : ℤ) (R S N : ℕ) (a : Idx R S) :
    EuclideanSpace ℂ (Pt N × Bool) :=
  WithLp.toLp 2 fun q : Pt N × Bool ↦ embedSign d q.2 (jetEntry d a q.1)

private theorem gram_rowVec_eq_map_intGram (d : ℤ) (R S N : ℕ) :
    Matrix.gram ℂ (rowVec d R S N) = (intGram d R S N).map (fun x : ℤ ↦ (x : ℂ)) := by
  ext a b
  rw [Matrix.gram_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [rowVec, RCLike.inner_apply, Fintype.sum_bool, intGram, Matrix.map_apply,
    Matrix.of_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [← Complex.star_def]
  linear_combination star_embedSign_add_eq_intPair d (jetEntry d a t) (jetEntry d b t)

private theorem degreeOf_sum_C_mul_monomial_le {R S : ℕ} (c : Idx R S → ℂ) :
    (∑ a : Idx R S, MvPolynomial.C (c a) *
      (MvPolynomial.X (0 : Fin 2) ^ (ofLex a).1.val *
        MvPolynomial.X (1 : Fin 2) ^ (ofLex a).2.val)).degreeOf 0 ≤ R ∧
    (∑ a : Idx R S, MvPolynomial.C (c a) *
      (MvPolynomial.X (0 : Fin 2) ^ (ofLex a).1.val *
        MvPolynomial.X (1 : Fin 2) ^ (ofLex a).2.val)).degreeOf 1 ≤ S := by
  classical
  constructor
  · refine (MvPolynomial.degreeOf_sum_le 0 _ _).trans (Finset.sup_le fun a _ ↦ ?_)
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add]
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have h0 : (MvPolynomial.X 0 ^ (ofLex a).1.val : MvPolynomial (Fin 2) ℂ).degreeOf 0 ≤ R := by
      refine MvPolynomial.degreeOf_le_iff.mpr fun m hm ↦ ?_
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.mem_support_iff,
        MvPolynomial.coeff_monomial] at hm
      split_ifs at hm with h
      · subst h; simp [(ofLex a).1.isLt.le]
      · exact absurd rfl hm
    have h1 : (MvPolynomial.X 1 ^ (ofLex a).2.val : MvPolynomial (Fin 2) ℂ).degreeOf 0 = 0 := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.degreeOf_monomial_eq _ 0 one_ne_zero]
      simp
    simpa using add_le_add h0 h1.le
  · refine (MvPolynomial.degreeOf_sum_le 1 _ _).trans (Finset.sup_le fun a _ ↦ ?_)
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add]
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have h0 : (MvPolynomial.X 0 ^ (ofLex a).1.val : MvPolynomial (Fin 2) ℂ).degreeOf 1 = 0 := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.degreeOf_monomial_eq _ 1 one_ne_zero]
      simp
    have h1 : (MvPolynomial.X 1 ^ (ofLex a).2.val : MvPolynomial (Fin 2) ℂ).degreeOf 1 ≤ S := by
      refine MvPolynomial.degreeOf_le_iff.mpr fun m hm ↦ ?_
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.mem_support_iff,
        MvPolynomial.coeff_monomial] at hm
      split_ifs at hm with h
      · subst h; simp [(ofLex a).2.isLt.le]
      · exact absurd rfl hm
    simpa using add_le_add h0.le h1

private theorem iterate_pderiv_sum_C_mul {R S : ℕ} (c : Idx R S → ℂ)
    (f : Idx R S → MvPolynomial (Fin 2) ℂ) (j : ℕ) :
    (MvPolynomial.pderiv 0)^[j] (∑ a : Idx R S, MvPolynomial.C (c a) * f a) =
      ∑ a : Idx R S, MvPolynomial.C (c a) * (MvPolynomial.pderiv 0)^[j] (f a) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [MvPolynomial.pderiv_C_mul, Function.iterate_succ_apply']

/-- **Fact 1 (Linear independence and positive Gram determinant).** When `2 * R * S + N * (R + S) <
N ^ 3`, the embedded jet row vectors are `ℂ`-linearly independent. -/
private theorem linearIndependent_rowVec {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N : ℕ} (hdeg : 2 * R * S + N * (R + S) < N ^ 3) :
    LinearIndependent ℂ (rowVec d R S N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set F : MvPolynomial (Fin 2) ℂ :=
    ∑ a : Idx R S, MvPolynomial.C (c a) *
      (MvPolynomial.X 0 ^ (ofLex a).1.val * MvPolynomial.X 1 ^ (ofLex a).2.val)
  have hF_deg0 : F.degreeOf 0 ≤ R := (degreeOf_sum_C_mul_monomial_le c).1
  have hF_deg1 : F.degreeOf 1 ≤ S := (degreeOf_sum_C_mul_monomial_le c).2
  set S_grid : Finset ℤ := (Finset.range N).image Nat.cast
  have hS_card : #S_grid = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hF_bound :
      2 * F.degreeOf 0 * F.degreeOf 1 + #S_grid * (F.degreeOf 0 + F.degreeOf 1) < #S_grid ^ 3 := by
    rw [hS_card]; nlinarith
  have hvan : ∀ x ∈ S_grid, ∀ y ∈ S_grid, ∀ j < #S_grid,
      MvPolynomial.eval ![(x : ℂ) + (y : ℂ) * quadTheta d, (x : ℂ) - (y : ℂ) * quadTheta d]
        ((MvPolynomial.pderiv 0)^[j] F) = 0 := by
    intro x hx y hy j hj
    rw [hS_card] at hj
    rcases Finset.mem_image.mp hx with ⟨nx, hnx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ny, hny, rfl⟩
    let t : Pt N := (⟨nx, Finset.mem_range.mp hnx⟩, ⟨ny, Finset.mem_range.mp hny⟩, ⟨j, hj⟩)
    have hcoord := congr_fun (congr_arg WithLp.ofLp hc) (t, true)
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      WithLp.ofLp_zero, Pi.zero_apply, rowVec, embedSign_jetEntry, ↓reduceIte] at hcoord
    rw [iterate_pderiv_sum_C_mul, map_sum]
    simpa [t] using hcoord
  have hF0 : F = 0 :=
    MvPolynomial.eq_zero_of_forall_eval_iterate_pderiv_eq_zero_conjugate_grid
      (quadTheta_linearIndependent hd hd1) S_grid hF_bound hvan
  intro a
  have hcoeff := congr_arg (fun P ↦ P.coeff
    (Finsupp.single 0 (ofLex a).1.val + Finsupp.single 1 (ofLex a).2.val)) hF0
  simp only [F, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X_zero_pow_mul_X_one_pow] at hcoeff
  rw [Finset.sum_eq_single a] at hcoeff
  · simpa using hcoeff
  · intro b _ hba
    rw [ite_eq_right]
    · simp
    · rintro ⟨h1, h2⟩
      exact hba (ofLex.injective (Prod.ext (Fin.ext h1) (Fin.ext h2)))
  · simp

private theorem intGram_det_pos {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N : ℕ} (hdeg : 2 * R * S + N * (R + S) < N ^ 3) :
    0 < (intGram d R S N).det := by
  have hv := linearIndependent_rowVec hd hd1 hdeg
  have hpos : 0 < RCLike.re (Matrix.gram ℂ (rowVec d R S N)).det :=
    Matrix.re_det_gram_pos_iff.mpr hv
  rw [gram_rowVec_eq_map_intGram, ← Int.cast_det, RCLike.intCast_re] at hpos
  exact_mod_cast hpos

private theorem norm_embedSign_jetEntry_le {d : ℤ} {R S N q : ℕ}
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hq : 3 ≤ q) (hdq : d.natAbs ≤ q)
    (a : Idx R S) (p : Pt N × Bool) :
    ‖embedSign d p.2 (jetEntry d a p.1)‖ ≤
      (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt q) ^ ((ofLex a).1.val + (ofLex a).2.val) := by
  rcases p with ⟨t, sgn⟩
  set r := (ofLex a).1.val
  set s := (ofLex a).2.val
  rw [embedSign_jetEntry, iterate_pderiv_X_zero_pow_mul_X_one_pow]
  simp only [map_mul, map_pow, map_natCast, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, norm_mul, norm_pow, Complex.norm_natCast]
  have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt q := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ q))
  have hbase_ge : (1 : ℝ) ≤ 2 * (N : ℝ) * Real.sqrt q := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hdf : (r.descFactorial t.2.2.val : ℝ) ≤ (R : ℝ) ^ N := by
    exact_mod_cast (Nat.descFactorial_le_pow r t.2.2.val).trans
      ((Nat.pow_le_pow_left (ofLex a).1.isLt.le _).trans (Nat.pow_le_pow_right hR t.2.2.isLt.le))
  have hθ : ‖if sgn then quadTheta d else -quadTheta d‖ ≤ Real.sqrt q := by
    have hEq : ‖if sgn then quadTheta d else -quadTheta d‖ = Real.sqrt d.natAbs := by
      cases sgn <;> simp [norm_quadTheta]
    rw [hEq]; exact Real.sqrt_le_sqrt (by exact_mod_cast hdq)
  have hx : (t.1.val : ℝ) ≤ N := by exact_mod_cast t.1.isLt.le
  have hy : (t.2.1.val : ℝ) ≤ N := by exact_mod_cast t.2.1.isLt.le
  set θs : ℂ := if sgn then quadTheta d else -quadTheta d
  have hz1 : ‖(t.1.val : ℂ) + (t.2.1.val : ℂ) * θs‖ ≤ 2 * (N : ℝ) * Real.sqrt q := by
    have h1 := norm_add_le (t.1.val : ℂ) ((t.2.1.val : ℂ) * θs)
    simp only [Complex.norm_natCast, norm_mul] at h1
    nlinarith [show ‖θs‖ ≤ Real.sqrt q from hθ]
  have hz2 : ‖(t.1.val : ℂ) - (t.2.1.val : ℂ) * θs‖ ≤ 2 * (N : ℝ) * Real.sqrt q := by
    have h1 := norm_sub_le (t.1.val : ℂ) ((t.2.1.val : ℂ) * θs)
    simp only [Complex.norm_natCast, norm_mul] at h1
    nlinarith [show ‖θs‖ ≤ Real.sqrt q from hθ]
  calc
    (r.descFactorial t.2.2.val : ℝ) *
        ‖(t.1.val : ℂ) + (t.2.1.val : ℂ) * θs‖ ^ (r - t.2.2.val) *
        ‖(t.1.val : ℂ) - (t.2.1.val : ℂ) * θs‖ ^ s
      ≤ (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt q) ^ (r - t.2.2.val) *
          (2 * (N : ℝ) * Real.sqrt q) ^ s := by gcongr
    _ ≤ (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt q) ^ r *
          (2 * (N : ℝ) * Real.sqrt q) ^ s := by
        have hpow := pow_le_pow_right₀ hbase_ge (Nat.sub_le r t.2.2.val)
        gcongr
    _ = (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt q) ^ (r + s) := by rw [mul_assoc, ← pow_add]

private theorem two_mul_log_norm_rowVec_le {d : ℤ} {R S N q : ℕ}
    (hv : LinearIndependent ℂ (rowVec d R S N))
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hq : 3 ≤ q) (hdq : d.natAbs ≤ q) (a : Idx R S) :
    2 * Real.log ‖rowVec d R S N a‖ ≤
      Real.log (2 * (N : ℝ) ^ 3) + 2 * (N : ℝ) * Real.log R +
        2 * (((ofLex a).1.val : ℝ) + ((ofLex a).2.val : ℝ)) *
          Real.log (2 * (N : ℝ) * Real.sqrt q) := by
  set r := (ofLex a).1.val
  set s := (ofLex a).2.val
  set B : ℝ := (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt q) ^ (r + s)
  have hnorm_sq : ‖rowVec d R S N a‖ ^ 2 ≤ (2 * (N : ℝ) ^ 3) * B ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ p : Pt N × Bool, ‖rowVec d R S N a p‖ ^ 2
        ≤ ∑ _p : Pt N × Bool, B ^ 2 :=
          Finset.sum_le_sum fun p _ ↦
            pow_le_pow_left₀ (norm_nonneg _) (norm_embedSign_jetEntry_le hR hN hq hdq a p) 2
      _ = (2 * (N : ℝ) ^ 3) * B ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul]
          push_cast; ring
  have hv_ne : ‖rowVec d R S N a‖ ≠ 0 := norm_ne_zero_iff.mpr (hv.ne_zero a)
  have hlogB : Real.log B = (N : ℝ) * Real.log R +
      ((r : ℝ) + (s : ℝ)) * Real.log (2 * (N : ℝ) * Real.sqrt q) := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  calc
    2 * Real.log ‖rowVec d R S N a‖
      = Real.log (‖rowVec d R S N a‖ ^ 2) := by rw [Real.log_pow]; ring
    _ ≤ Real.log ((2 * (N : ℝ) ^ 3) * B ^ 2) := Real.log_le_log (by positivity) hnorm_sq
    _ = Real.log (2 * (N : ℝ) ^ 3) + Real.log (B ^ 2) :=
        Real.log_mul (by positivity) (by positivity)
    _ = Real.log (2 * (N : ℝ) ^ 3) + 2 * Real.log B := by rw [Real.log_pow]; ring
    _ = Real.log (2 * (N : ℝ) ^ 3) + 2 * (N : ℝ) * Real.log R +
          2 * ((r : ℝ) + (s : ℝ)) * Real.log (2 * (N : ℝ) * Real.sqrt q) := by
        rw [hlogB]; ring

private theorem sum_two_mul_add_idx_le (R S : ℕ) :
    ∑ a : Idx R S, 2 * ((ofLex a).1.val + (ofLex a).2.val) ≤ R * S * (R + S) := by
  rw [← Equiv.sum_comp (ofLex : Idx R S ≃ Fin R × Fin S).symm]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  have hfin_sum : ∀ m : ℕ, ∑ i : Fin m, 2 * (i : ℕ) ≤ m * m := fun m ↦ by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ 2 * k), ← Finset.mul_sum,
      mul_comm 2, Finset.sum_range_id_mul_two]
    exact Nat.mul_le_mul_left m (Nat.sub_le m 1)
  calc
    ∑ x : Fin R, ∑ y : Fin S, 2 * ((x : ℕ) + (y : ℕ))
      = ∑ x : Fin R, (S * (2 * (x : ℕ)) + ∑ y : Fin S, 2 * (y : ℕ)) :=
        Finset.sum_congr rfl fun x _ ↦ by simp [mul_add, Finset.sum_add_distrib]
    _ = S * (∑ x : Fin R, 2 * (x : ℕ)) + R * (∑ y : Fin S, 2 * (y : ℕ)) := by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ S * (R * R) + R * (S * S) :=
        Nat.add_le_add (Nat.mul_le_mul_left S (hfin_sum R)) (Nat.mul_le_mul_left R (hfin_sum S))
    _ = R * S * (R + S) := by ring

/-- **Fact 2 (Archimedean upper bound via Hadamard's inequality).** -/
private theorem log_intGram_det_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N q : ℕ} (hR : 1 ≤ R) (hN : 1 ≤ N) (hq : 3 ≤ q) (hdq : d.natAbs ≤ q)
    (hdeg : 2 * R * S + N * (R + S) < N ^ 3) :
    Real.log ((intGram d R S N).det : ℝ) ≤
      (R * S : ℝ) * Real.log (2 * (N : ℝ) ^ 3) +
        2 * (R * S * N : ℝ) * Real.log R +
        (R * S * (R + S) : ℝ) * Real.log (2 * (N : ℝ) * Real.sqrt q) := by
  have hv := linearIndependent_rowVec hd hd1 hdeg
  have hhad := Matrix.log_re_det_gram_le hv
  rw [gram_rowVec_eq_map_intGram, ← Int.cast_det, RCLike.intCast_re] at hhad
  have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt q := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ q))
  have hbase_ge : (1 : ℝ) ≤ 2 * (N : ℝ) * Real.sqrt q := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hcard : Fintype.card (Idx R S) = R * S := by simp
  calc
    Real.log ((intGram d R S N).det : ℝ)
      ≤ ∑ a : Idx R S, 2 * Real.log ‖rowVec d R S N a‖ := hhad
    _ ≤ ∑ a : Idx R S, (Real.log (2 * (N : ℝ) ^ 3) + 2 * (N : ℝ) * Real.log R +
          2 * (((ofLex a).1.val : ℝ) + ((ofLex a).2.val : ℝ)) *
            Real.log (2 * (N : ℝ) * Real.sqrt q)) :=
        Finset.sum_le_sum fun a _ ↦ two_mul_log_norm_rowVec_le hv hR hN hq hdq a
    _ = (R * S : ℝ) * Real.log (2 * (N : ℝ) ^ 3) + 2 * (R * S * N : ℝ) * Real.log R +
          (∑ a : Idx R S, 2 * (((ofLex a).1.val : ℝ) + ((ofLex a).2.val : ℝ))) *
            Real.log (2 * (N : ℝ) * Real.sqrt q) := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          hcard, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (R * S : ℝ) * Real.log (2 * (N : ℝ) ^ 3) + 2 * (R * S * N : ℝ) * Real.log R +
          (R * S * (R + S) : ℝ) * Real.log (2 * (N : ℝ) * Real.sqrt q) := by
        gcongr
        · exact Real.log_nonneg hbase_ge
        · exact_mod_cast sum_two_mul_add_idx_le R S

/-! ### Fact 3: `p`-adic divisibility of `det (intGram d R S N)` at inert primes -/

private theorem pow_two_mul_sum_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (e : ι → ℕ) (p : ℤ)
    (hM : ∀ a b, p ^ (e a + e b) ∣ M a b) :
    p ^ (2 * ∑ a, e a) ∣ M.det := by
  rw [Matrix.det_apply']
  refine Finset.dvd_sum fun σ _ ↦ ?_
  have hprod : ∏ a : ι, p ^ (e (σ a) + e a) ∣ ∏ a : ι, M (σ a) a :=
    Finset.prod_dvd_prod_of_dvd _ _ fun a _ ↦ hM (σ a) a
  have hexp : ∏ a : ι, p ^ (e (σ a) + e a) = p ^ (2 * ∑ a : ι, e a) := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Equiv.sum_comp σ e, ← two_mul]
  rw [← hexp]
  rcases Int.units_eq_one_or σ.sign with hs | hs
  · simpa [hs] using hprod
  · simpa [hs] using hprod

private def rowOrder (p S : ℕ) {R : ℕ} (a : Idx R S) : ℕ :=
  min ((ofLex a).1.val / p) (S - 1 - (ofLex a).2.val)

private def frobeniusBasisChange (p R S : ℕ) : Matrix (Idx R S) (Idx R S) ℤ :=
  Matrix.of fun a b ↦
    let r := (ofLex a).1.val
    let s := (ofLex a).2.val
    let r' := (ofLex b).1.val
    let s' := (ofLex b).2.val
    let h := rowOrder p S a
    if s ≤ s' ∧ s' - s ≤ h ∧ r' + p * (s' - s) = r then
      (-1 : ℤ) ^ (s' - s) * (h.choose (s' - s) : ℤ)
    else 0

private theorem det_frobeniusBasisChange {p : ℕ} (hp : 0 < p) (R S : ℕ) :
    (frobeniusBasisChange p R S).det = 1 := by
  rw [← Matrix.det_transpose]
  refine Matrix.IsUpperUnitriangular.det_eq_one ((Matrix.isUpperUnitriangular_def _).mpr ⟨?_, ?_⟩)
  · intro a b hba
    simp only [Matrix.transpose_apply, frobeniusBasisChange, Matrix.of_apply]
    rw [ite_eq_right]
    rintro ⟨_, _, hrr'⟩
    rcases Prod.Lex.lt_iff.mp hba with hlt | ⟨heq, hlt⟩
    · have : (ofLex b).1.val < (ofLex a).1.val := hlt
      omega
    · have hr : (ofLex b).1.val = (ofLex a).1.val := congr_arg Fin.val heq
      have hs : (ofLex b).2.val < (ofLex a).2.val := hlt
      have hp0 : p * ((ofLex a).2.val - (ofLex b).2.val) = 0 := by omega
      rcases Nat.mul_eq_zero.mp hp0 with hp0 | hd0 <;> omega
  · intro a
    simp [frobeniusBasisChange]

private theorem frobeniusBasisChange_apply_of_cond (p R S : ℕ) (a b : Idx R S)
    (h1 : (ofLex a).2.val ≤ (ofLex b).2.val)
    (h2 : (ofLex b).2.val - (ofLex a).2.val ≤ rowOrder p S a)
    (h3 : (ofLex b).1.val + p * ((ofLex b).2.val - (ofLex a).2.val) = (ofLex a).1.val) :
    frobeniusBasisChange p R S a b =
      (-1 : ℤ) ^ ((ofLex b).2.val - (ofLex a).2.val) *
        ((rowOrder p S a).choose ((ofLex b).2.val - (ofLex a).2.val) : ℤ) := by
  dsimp only [frobeniusBasisChange, Matrix.of_apply]
  exact ite_eq_left ⟨h1, h2, h3⟩

private theorem sum_frobeniusBasisChange_eq_range {A : Type*} [CommRing A]
    (p R S : ℕ) (a : Idx R S) :
    ∑ b : Idx R S,
        (frobeniusBasisChange p R S a b : MvPolynomial (Fin 2) A) *
          (MvPolynomial.X 0 ^ (ofLex b).1.val * MvPolynomial.X 1 ^ (ofLex b).2.val) =
      ∑ k ∈ Finset.range (rowOrder p S a + 1),
        ((-1 : MvPolynomial (Fin 2) A) ^ k *
            ((rowOrder p S a).choose k : MvPolynomial (Fin 2) A)) *
          (MvPolynomial.X 0 ^ ((ofLex a).1.val - p * k) *
            MvPolynomial.X 1 ^ ((ofLex a).2.val + k)) := by
  classical
  let r := (ofLex a).1.val
  let s := (ofLex a).2.val
  let h := rowOrder p S a
  have hph : p * h ≤ r :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le r p)
  have hsh : s + h < S := by
    have := (ofLex a).2.isLt; have : h ≤ S - 1 - s := min_le_right _ _; omega
  let idxAt : ℕ → Idx R S := fun k ↦
    if hk : k ≤ h then
      toLex (⟨r - p * k, by have := (ofLex a).1.isLt; omega⟩, ⟨s + k, by omega⟩)
    else a
  have hidx_eq : ∀ (k : ℕ) (hk : k ≤ h),
      idxAt k = toLex (⟨r - p * k, by have := (ofLex a).1.isLt; omega⟩, ⟨s + k, by omega⟩) :=
    fun _ hk ↦ dite_eq_left hk
  have hidx_inj : Set.InjOn idxAt (Finset.range (h + 1) : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁_le : k₁ ≤ h := Nat.lt_succ_iff.mp (Finset.mem_coe.mp hk₁ |> Finset.mem_range.mp)
    have hk₂_le : k₂ ≤ h := Nat.lt_succ_iff.mp (Finset.mem_coe.mp hk₂ |> Finset.mem_range.mp)
    have hs_eq := congr_arg (fun x ↦ (ofLex x).2.val) heq
    rw [hidx_eq k₁ hk₁_le, hidx_eq k₂ hk₂_le] at hs_eq
    dsimp only [ofLex_toLex] at hs_eq
    omega
  rw [← Finset.sum_subset (s₁ := (Finset.range (h + 1)).image idxAt) (Finset.subset_univ _),
    Finset.sum_image hidx_inj]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk_le : k ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpk : p * k ≤ r := (Nat.mul_le_mul_left p hk_le).trans hph
    rw [hidx_eq k hk_le]
    have hentry : frobeniusBasisChange p R S a
        (toLex (⟨r - p * k, by have := (ofLex a).1.isLt; omega⟩, ⟨s + k, by omega⟩)) =
        (-1 : ℤ) ^ k * (h.choose k : ℤ) := by
      rw [frobeniusBasisChange_apply_of_cond]
      · dsimp only [ofLex_toLex, s, h]; rw [Nat.add_sub_cancel_left]
      · dsimp only [ofLex_toLex, s]; exact Nat.le_add_right _ _
      · dsimp only [ofLex_toLex, s, h]; omega
      · dsimp only [ofLex_toLex, r, s]; rw [Nat.add_sub_cancel_left]; omega
    rw [hentry]
    dsimp only [ofLex_toLex]
    push_cast; rfl
  · intro b _ hbnot
    simp only [frobeniusBasisChange, Matrix.of_apply]
    rw [ite_eq_right]
    · simp
    · rintro ⟨hss', hk_le, hrr'⟩
      refine hbnot (Finset.mem_image.mpr ⟨(ofLex b).2.val - s,
        Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), ?_⟩)
      rw [hidx_eq _ hk_le]
      apply ofLex.injective
      ext <;> dsimp [r, s] at * <;> omega

private theorem sum_frobeniusBasisChange_monomial {A : Type*} [CommRing A]
    (p R S : ℕ) (a : Idx R S) :
    ∑ b : Idx R S,
        (frobeniusBasisChange p R S a b : MvPolynomial (Fin 2) A) *
          (MvPolynomial.X 0 ^ (ofLex b).1.val * MvPolynomial.X 1 ^ (ofLex b).2.val) =
      (MvPolynomial.X 0 ^ ((ofLex a).1.val - p * rowOrder p S a) *
          MvPolynomial.X 1 ^ (ofLex a).2.val) *
        ∏ _i : Fin (rowOrder p S a), (MvPolynomial.X 0 ^ p - MvPolynomial.X 1) := by
  set r := (ofLex a).1.val
  set s := (ofLex a).2.val
  set h := rowOrder p S a
  have hph : p * h ≤ r :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le r p)
  rw [sum_frobeniusBasisChange_eq_range]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : (MvPolynomial.X 0 ^ p - MvPolynomial.X 1 : MvPolynomial (Fin 2) A) =
      -MvPolynomial.X 1 + MvPolynomial.X 0 ^ p := by ring
  rw [hsub, Commute.add_pow (Commute.all _ _) h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk_le : k ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hexp : r - p * h + p * (h - k) = r - p * k := by
    have : p * (h - k) = p * h - p * k := Nat.mul_sub p h k
    have : p * k ≤ p * h := Nat.mul_le_mul_left p hk_le
    omega
  have hneg : (-MvPolynomial.X 1 : MvPolynomial (Fin 2) A) ^ k =
      (-1 : MvPolynomial (Fin 2) A) ^ k * MvPolynomial.X 1 ^ k := neg_pow _ k
  rw [hneg, ← pow_mul]
  calc
    ((-1 : MvPolynomial (Fin 2) A) ^ k * (h.choose k : MvPolynomial (Fin 2) A)) *
        (MvPolynomial.X 0 ^ (r - p * k) * MvPolynomial.X 1 ^ (s + k))
      = ((-1 : MvPolynomial (Fin 2) A) ^ k * (h.choose k : MvPolynomial (Fin 2) A)) *
          ((MvPolynomial.X 0 ^ (r - p * h) * MvPolynomial.X 0 ^ (p * (h - k))) *
            (MvPolynomial.X 1 ^ s * MvPolynomial.X 1 ^ k)) := by
        rw [← pow_add, ← pow_add, hexp]
    _ = (MvPolynomial.X 0 ^ (r - p * h) * MvPolynomial.X 1 ^ s) *
          (((-1 : MvPolynomial (Fin 2) A) ^ k * MvPolynomial.X 1 ^ k) *
            MvPolynomial.X 0 ^ (p * (h - k)) * (h.choose k : MvPolynomial (Fin 2) A)) := by
        ring

private theorem iterate_pderiv_intCast_mul {A : Type*} [CommRing A]
    (c : ℤ) (P : MvPolynomial (Fin 2) A) (j : ℕ) :
    (MvPolynomial.pderiv 0)^[j] ((c : MvPolynomial (Fin 2) A) * P) =
      (c : MvPolynomial (Fin 2) A) * (MvPolynomial.pderiv 0)^[j] P := by
  have hc : (c : MvPolynomial (Fin 2) A) = MvPolynomial.C (c : A) := by simp
  rw [hc]
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_C_mul, Function.iterate_succ_apply']

private theorem eval_iterate_pderiv_frobeniusPoly_mem {d : ℤ} {p : ℕ} [Fact p.Prime]
    (hr : ¬IsSquare (d : ZMod p)) (z : QuadraticAlgebra ℤ d 0) (k : ℕ) :
    MvPolynomial.eval ![z, star z]
      ((MvPolynomial.pderiv 0)^[k]
        (MvPolynomial.X 0 ^ p - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (QuadraticAlgebra ℤ d 0))) ∈
      Ideal.span {(p : QuadraticAlgebra ℤ d 0)} := by
  cases k with
  | zero =>
    simpa [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X] using
      QuadraticAlgebra.frobenius_congruence hr z
  | succ k =>
    rw [Function.iterate_succ_apply]
    have hp1 : MvPolynomial.pderiv 0
        (MvPolynomial.X 0 ^ p - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (QuadraticAlgebra ℤ d 0)) =
        ((p : ℤ) : MvPolynomial (Fin 2) (QuadraticAlgebra ℤ d 0)) *
          MvPolynomial.X 0 ^ (p - 1) := by
      rw [map_sub, MvPolynomial.pderiv_X_of_ne (by decide), sub_zero, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_self, mul_one, Int.cast_natCast]
    rw [hp1, iterate_pderiv_intCast_mul, map_mul, map_intCast, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem dvd_sum_frobeniusBasisChange_jetEntry {d : ℤ} {p : ℕ} [Fact p.Prime]
    (hr : ¬IsSquare (d : ZMod p)) {R S N : ℕ} (a : Idx R S) (t : Pt N) :
    (p : ℤ) ^ rowOrder p S a ∣
        (∑ b : Idx R S, (frobeniusBasisChange p R S a b : QuadraticAlgebra ℤ d 0) *
          jetEntry d b t).re ∧
      (p : ℤ) ^ rowOrder p S a ∣
        (∑ b : Idx R S, (frobeniusBasisChange p R S a b : QuadraticAlgebra ℤ d 0) *
          jetEntry d b t).im := by
  set z : QuadraticAlgebra ℤ d 0 := ⟨(t.1 : ℤ), (t.2.1 : ℤ)⟩
  have hstar : (⟨(t.1 : ℤ), -(t.2.1 : ℤ)⟩ : QuadraticAlgebra ℤ d 0) = star z := by
    ext <;> simp [z]
  have heq : ∑ b : Idx R S,
      (frobeniusBasisChange p R S a b : QuadraticAlgebra ℤ d 0) * jetEntry d b t =
      MvPolynomial.eval ![z, star z]
        ((MvPolynomial.pderiv 0)^[t.2.2.val]
          ((MvPolynomial.X 0 ^ ((ofLex a).1.val - p * rowOrder p S a) *
              MvPolynomial.X 1 ^ (ofLex a).2.val) *
            ∏ _i : Fin (rowOrder p S a), (MvPolynomial.X 0 ^ p - MvPolynomial.X 1))) := by
    rw [← sum_frobeniusBasisChange_monomial p R S a]
    have hiter : (MvPolynomial.pderiv 0)^[t.2.2.val]
        (∑ b : Idx R S,
          (frobeniusBasisChange p R S a b : MvPolynomial (Fin 2) (QuadraticAlgebra ℤ d 0)) *
            (MvPolynomial.X 0 ^ (ofLex b).1.val * MvPolynomial.X 1 ^ (ofLex b).2.val)) =
        ∑ b : Idx R S,
          (frobeniusBasisChange p R S a b : MvPolynomial (Fin 2) (QuadraticAlgebra ℤ d 0)) *
            (MvPolynomial.pderiv 0)^[t.2.2.val]
              (MvPolynomial.X 0 ^ (ofLex b).1.val * MvPolynomial.X 1 ^ (ofLex b).2.val) := by
      induction t.2.2.val with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', ih, map_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        have hc : (frobeniusBasisChange p R S a b :
            MvPolynomial (Fin 2) (QuadraticAlgebra ℤ d 0)) =
            MvPolynomial.C (frobeniusBasisChange p R S a b : QuadraticAlgebra ℤ d 0) := by simp
        rw [hc, MvPolynomial.pderiv_C_mul, Function.iterate_succ_apply']
    rw [hiter, map_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    dsimp only [jetEntry]
    rw [map_mul, map_intCast, hstar]
  have hmem := MvPolynomial.pderiv_prod_mem_ideal_pow (0 : Fin 2)
    (fun _ : Fin (rowOrder p S a) ↦ MvPolynomial.X 0 ^ p - MvPolynomial.X 1)
    (MvPolynomial.X 0 ^ ((ofLex a).1.val - p * rowOrder p S a) *
      MvPolynomial.X 1 ^ (ofLex a).2.val)
    ![z, star z] (Ideal.span {(p : QuadraticAlgebra ℤ d 0)}) t.2.2.val
    (fun _ k _ ↦ eval_iterate_pderiv_frobeniusPoly_mem hr z k) t.2.2.val le_rfl
  rw [Fintype.card_fin, Ideal.span_singleton_pow, ← Nat.cast_pow, ← heq,
    QuadraticAlgebra.mem_span_natCast_iff, Nat.cast_pow] at hmem
  exact hmem

private theorem intPair_sum_intCast_mul {ι : Type*} (s : Finset ι) (d : ℤ)
    (u v : ι → ℤ) (z : ι → QuadraticAlgebra ℤ d 0) :
    intPair d (∑ i ∈ s, (u i : QuadraticAlgebra ℤ d 0) * z i)
      (∑ j ∈ s, (v j : QuadraticAlgebra ℤ d 0) * z j) =
      ∑ i ∈ s, ∑ j ∈ s, u i * intPair d (z i) (z j) * v j := by
  classical
  have hre : ∀ f : ι → QuadraticAlgebra ℤ d 0, (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
    intro f; induction s using Finset.induction with
    | empty => rfl
    | insert a t hat ih => simp [Finset.sum_insert hat, ih]
  have him : ∀ f : ι → QuadraticAlgebra ℤ d 0, (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
    clear hre
    intro f; induction s using Finset.induction with
    | empty => rfl
    | insert a t hat ih => simp [Finset.sum_insert hat, ih]
  have hre_mul : ∀ (c : ℤ) (q : QuadraticAlgebra ℤ d 0),
      ((c : QuadraticAlgebra ℤ d 0) * q).re = c * q.re := fun c q ↦ by simp
  have him_mul : ∀ (c : ℤ) (q : QuadraticAlgebra ℤ d 0),
      ((c : QuadraticAlgebra ℤ d 0) * q).im = c * q.im := fun c q ↦ by simp
  simp only [intPair, hre, him, hre_mul, him_mul, mul_assoc]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, mul_add, add_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Fact 3 (`p`-adic divisibility).** At every prime `p` modulo which `d` is not a square,
`p ^ (2 * ∑ a, rowOrder p S a)` divides `det (intGram d R S N)`. -/
private theorem pow_dvd_intGram_det_of_not_isSquare {d : ℤ} {p : ℕ} [Fact p.Prime]
    (hr : ¬IsSquare (d : ZMod p)) (R S N : ℕ) :
    (p : ℤ) ^ (2 * ∑ a : Idx R S, rowOrder p S a) ∣ (intGram d R S N).det := by
  set U := frobeniusBasisChange p R S
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hdetU : (U * intGram d R S N * Uᵀ).det = (intGram d R S N).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_frobeniusBasisChange hp_pos R S]
    ring
  rw [← hdetU]
  refine pow_two_mul_sum_dvd_det _ (rowOrder p S) (p : ℤ) fun a b ↦ ?_
  let w : Idx R S → Pt N → QuadraticAlgebra ℤ d 0 := fun x t ↦
    ∑ x' : Idx R S, (U x x' : QuadraticAlgebra ℤ d 0) * jetEntry d x' t
  have hentry : (U * intGram d R S N * Uᵀ) a b = ∑ t : Pt N, intPair d (w a t) (w b t) := by
    calc
      (U * intGram d R S N * Uᵀ) a b
        = ∑ x : Idx R S, ∑ y : Idx R S,
            U a x * (∑ t : Pt N, intPair d (jetEntry d x t) (jetEntry d y t)) * U b y := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply, intGram, Matrix.of_apply,
            Finset.sum_mul]
          exact Finset.sum_comm
      _ = ∑ x : Idx R S, ∑ y : Idx R S, ∑ t : Pt N,
            U a x * intPair d (jetEntry d x t) (jetEntry d y t) * U b y := by
          refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
          simp only [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ x : Idx R S, ∑ t : Pt N, ∑ y : Idx R S,
            U a x * intPair d (jetEntry d x t) (jetEntry d y t) * U b y :=
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm
      _ = ∑ t : Pt N, ∑ x : Idx R S, ∑ y : Idx R S,
            U a x * intPair d (jetEntry d x t) (jetEntry d y t) * U b y :=
          Finset.sum_comm
      _ = ∑ t : Pt N, intPair d (w a t) (w b t) := by
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          exact (intPair_sum_intCast_mul Finset.univ d (U a) (U b)
            (fun x ↦ jetEntry d x t)).symm
  rw [hentry]
  refine Finset.dvd_sum fun t _ ↦ ?_
  obtain ⟨hare, haim⟩ := dvd_sum_frobeniusBasisChange_jetEntry hr a t
  obtain ⟨hbre, hbim⟩ := dvd_sum_frobeniusBasisChange_jetEntry hr b t
  change (p : ℤ) ^ rowOrder p S a ∣ (w a t).re at hare
  change (p : ℤ) ^ rowOrder p S a ∣ (w a t).im at haim
  change (p : ℤ) ^ rowOrder p S b ∣ (w b t).re at hbre
  change (p : ℤ) ^ rowOrder p S b ∣ (w b t).im at hbim
  rw [pow_add]
  dsimp only [intPair]
  have h1 : (p : ℤ) ^ rowOrder p S a * (p : ℤ) ^ rowOrder p S b ∣ (w a t).re * (w b t).re :=
    mul_dvd_mul hare hbre
  have h2 : (p : ℤ) ^ rowOrder p S a * (p : ℤ) ^ rowOrder p S b ∣
      (d.natAbs : ℤ) * (w a t).im * (w b t).im := by
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul haim hbim) (d.natAbs : ℤ)
  exact dvd_mul_of_dvd_right (dvd_add h1 h2) 2

private theorem sum_primes_mul_log_le_log_intGram_det {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N : ℕ} (hdeg : 2 * R * S + N * (R + S) < N ^ 3)
    (P' : Finset ℕ) (hP' : ∀ p ∈ P', p.Prime ∧ ¬IsSquare (d : ZMod p)) :
    ∑ p ∈ P', (2 * ∑ a : Idx R S, rowOrder p S a : ℝ) * Real.log p ≤
      Real.log ((intGram d R S N).det : ℝ) := by
  have hdet_pos := intGram_det_pos hd hd1 hdeg
  set D : ℕ := (intGram d R S N).det.toNat
  have hD_eq : (D : ℤ) = (intGram d R S N).det := Int.toNat_of_nonneg hdet_pos.le
  have hD_pos : 0 < D := by omega
  have hdvd_prod : ∏ p ∈ P', p ^ (2 * ∑ a : Idx R S, rowOrder p S a) ∣ D := by
    have hmem_dvd : ∀ p ∈ P', p ^ (2 * ∑ a : Idx R S, rowOrder p S a) ∣ D := by
      intro p hp
      obtain ⟨hp_prime, hp_sq⟩ := hP' p hp
      have : Fact p.Prime := ⟨hp_prime⟩
      have hdvdZ := pow_dvd_intGram_det_of_not_isSquare hp_sq R S N
      rw [← hD_eq, ← Nat.cast_pow] at hdvdZ
      exact Int.ofNat_dvd.mp hdvdZ
    have hprime : ∀ p ∈ P', p.Prime := fun p hp ↦ (hP' p hp).1
    clear hP'
    induction P' using Finset.cons_induction with
    | empty => simp
    | cons p Q hpQ ih =>
      rw [Finset.prod_cons]
      have hcop : Nat.Coprime (p ^ (2 * ∑ a : Idx R S, rowOrder p S a))
          (∏ q ∈ Q, q ^ (2 * ∑ a : Idx R S, rowOrder q S a)) :=
        Nat.Coprime.prod_right fun q hq ↦
          ((Nat.coprime_primes (hprime p (Finset.mem_cons_self p Q))
            (hprime q (Finset.mem_cons_of_mem hq))).mpr
              (fun h ↦ hpQ (h ▸ hq))).pow _ _
      exact hcop.mul_dvd_of_dvd_of_dvd (hmem_dvd p (Finset.mem_cons_self p Q))
        (ih (fun q hq ↦ hmem_dvd q (Finset.mem_cons_of_mem hq))
          (fun q hq ↦ hprime q (Finset.mem_cons_of_mem hq)))
  have hprod_pos : 0 < ∏ p ∈ P', p ^ (2 * ∑ a : Idx R S, rowOrder p S a) :=
    Finset.prod_pos fun p hp ↦ pow_pos (hP' p hp).1.pos _
  have hle : (∏ p ∈ P', (p : ℝ) ^ (2 * ∑ a : Idx R S, rowOrder p S a)) ≤
      ((intGram d R S N).det : ℝ) := by
    have hZ : ((∏ p ∈ P', p ^ (2 * ∑ a : Idx R S, rowOrder p S a) : ℕ) : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hD_pos hdvd_prod
    simpa only [Nat.cast_prod, Nat.cast_pow, ← hD_eq, Int.cast_natCast] using hZ
  calc
    ∑ p ∈ P', (2 * ∑ a : Idx R S, rowOrder p S a : ℝ) * Real.log p
      = Real.log (∏ p ∈ P', (p : ℝ) ^ (2 * ∑ a : Idx R S, rowOrder p S a)) := by
        rw [Real.log_prod (fun p hp ↦ pow_ne_zero _ (Nat.cast_ne_zero.mpr (hP' p hp).1.ne_zero))]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Real.log_pow]; push_cast; rfl
    _ ≤ Real.log ((intGram d R S N).det : ℝ) :=
        Real.log_le_log (by exact_mod_cast hprod_pos) hle

/-! ### Combinatorial evaluation of `∑ rowOrder` and assembly -/

private theorem two_mul_sum_min_fin {S k : ℕ} (hk : k < S) :
    2 * (∑ s : Fin S, min k (S - 1 - s.val)) + k * (k + 1) = 2 * S * k := by
  have hrev : ∑ s : Fin S, min k (S - 1 - s.val) = ∑ u ∈ Finset.range S, min k u := by
    rw [← Equiv.sum_comp Fin.revPerm (fun s : Fin S ↦ min k (S - 1 - s.val))]
    have hcomp : ∀ s : Fin S, S - 1 - (Fin.revPerm s).val = s.val := fun s ↦ by
      simp only [Fin.revPerm_apply, Fin.val_rev]; have := s.isLt; omega
    simp_rw [hcomp]
    exact Fin.sum_univ_eq_sum_range (fun u ↦ min k u) S
  rw [hrev, show S = k + (S - k) by omega, Finset.sum_range_add]
  have h1 : ∑ u ∈ Finset.range k, min k u = ∑ u ∈ Finset.range k, u :=
    Finset.sum_congr rfl fun u hu ↦ min_eq_right (Finset.mem_range.mp hu).le
  have h2 : ∑ v ∈ Finset.range (S - k), min k (k + v) = (S - k) * k := by
    trans ∑ _v ∈ Finset.range (S - k), k
    · exact Finset.sum_congr rfl fun v _ ↦ min_eq_left (Nat.le_add_right k v)
    · simp
  rw [h1, h2, mul_add, ← mul_comm (∑ u ∈ Finset.range k, u) 2, Finset.sum_range_id_mul_two]
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  · zify [hk.le, (by omega : 1 ≤ k)]; ring

private theorem sum_range_mul_div (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ∑ r ∈ Finset.range (m * p), f (r / p) = ∑ k ∈ Finset.range m, p * f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    trans ∑ _u ∈ Finset.range p, f m
    · refine Finset.sum_congr rfl fun u hu ↦ ?_
      have hu_lt : u < p := Finset.mem_range.mp hu
      have hdiv : (m * p + u) / p = m := by
        rw [mul_comm, add_comm, Nat.add_mul_div_left _ _ hp,
          Nat.div_eq_zero_iff.mpr (Or.inr hu_lt), zero_add]
      rw [hdiv]
    · simp

private theorem three_mul_two_mul_sum_rowOrder_ge (X : ℕ) {C p : ℕ}
    (hC : 1 ≤ C) (hpC : C ≤ p) :
    3 * p * (X / C + 1) * (X / p) * (X / p - 1) ≤
      3 * (2 * ∑ a : Idx X (X / C + 1), rowOrder p (X / C + 1) a) + p * (X / p) ^ 3 := by
  set S := X / C + 1
  set m := X / p
  have hp_pos : 0 < p := by omega
  have hm_lt_S : m < S := by
    have : X / p ≤ X / C := Nat.div_le_div_left hpC hC
    omega
  have hdrop : ∑ k ∈ Finset.range m, p * (∑ s : Fin S, min k (S - 1 - s.val)) ≤
      ∑ a : Idx X S, rowOrder p S a := by
    rw [← Equiv.sum_comp (ofLex : Idx X S ≃ Fin X × Fin S).symm]
    simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type, rowOrder]
    rw [Fin.sum_univ_eq_sum_range (fun r ↦ ∑ s : Fin S, min (r / p) (S - 1 - s.val)) X,
      ← sum_range_mul_div (fun k ↦ ∑ s : Fin S, min k (S - 1 - s.val)) hp_pos m]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.div_mul_le_self X p))
  have hsum_id : p * S * (m * (m - 1)) =
      2 * (∑ k ∈ Finset.range m, p * (∑ s : Fin S, min k (S - 1 - s.val))) +
        p * ∑ k ∈ Finset.range m, k * (k + 1) := by
    calc
      p * S * (m * (m - 1))
        = p * (S * (2 * ∑ k ∈ Finset.range m, k)) := by
            rw [mul_comm 2, Finset.sum_range_id_mul_two, mul_assoc]
      _ = ∑ k ∈ Finset.range m, p * (2 * S * k) := by
            simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ ↦ by ring
      _ = ∑ k ∈ Finset.range m,
            (2 * (p * ∑ s : Fin S, min k (S - 1 - s.val)) + p * (k * (k + 1))) := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            rw [← two_mul_sum_min_fin ((Finset.mem_range.mp hk).trans hm_lt_S)]; ring
      _ = 2 * (∑ k ∈ Finset.range m, p * (∑ s : Fin S, min k (S - 1 - s.val))) +
            p * ∑ k ∈ Finset.range m, k * (k + 1) := by
            rw [Finset.sum_add_distrib]
            congr 1 <;> rw [← Finset.mul_sum]
  have hcube : 3 * ∑ k ∈ Finset.range m, k * (k + 1) ≤ m ^ 3 := by
    clear * -
    induction m with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add]; nlinarith
  nlinarith

private theorem mul_sq_log_div_le_rowOrder {X C p : ℕ}
    (hC : 1 ≤ C) (hpC : C ≤ p) (hpX : p ≤ X) :
    ((X / C + 1 : ℕ) : ℝ) * (X : ℝ) ^ 2 * (Real.log p / p) ≤
      (2 * ∑ a : Idx X (X / C + 1), rowOrder p (X / C + 1) a : ℝ) * Real.log p +
        4 * ((X / C + 1 : ℕ) : ℝ) * X * Real.log p +
        (X : ℝ) ^ 3 / 3 * (Real.log p / (p : ℝ) ^ 2) := by
  set S := X / C + 1
  set m := X / p
  have hp_pos : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by positivity
  have hm1 : 1 ≤ m := Nat.div_pos hpX hp_pos
  have hmR1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm_le : (m : ℝ) * p ≤ X := by exact_mod_cast Nat.div_mul_le_self X p
  have hX_lt : (X : ℝ) ≤ ((m : ℝ) + 1) * p := by
    have hlt : X < (m + 1) * p := by
      have h1 : p * m + X % p = X := Nat.div_add_mod X p
      have h2 : X % p < p := Nat.mod_lt X hp_pos
      nlinarith
    exact_mod_cast hlt.le
  have hnat_ineq : 3 * (p : ℝ) * S * m * ((m : ℝ) - 1) ≤
      3 * (2 * ∑ a : Idx X S, rowOrder p S a : ℝ) + (p : ℝ) * (m : ℝ) ^ 3 := by
    have h := three_mul_two_mul_sum_rowOrder_ge X hC hpC
    have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
    have hR : ((3 * p * S * m * (m - 1) : ℕ) : ℝ) ≤
        ((3 * (2 * ∑ a : Idx X S, rowOrder p S a) + p * m ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [hm_sub] at hR
    rw [← Nat.cast_sum] at hR
    linarith
  have hm_cube : (p : ℝ) * (m : ℝ) ^ 3 ≤ (X : ℝ) ^ 3 / (p : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    rw [show (p : ℝ) * (m : ℝ) ^ 3 * (p : ℝ) ^ 2 = ((m : ℝ) * p) ^ 3 by ring]
    exact pow_le_pow_left₀ (by positivity) hm_le 3
  have hSX2 : (S : ℝ) * (X : ℝ) ^ 2 / p ≤
      (2 * ∑ a : Idx X S, rowOrder p S a : ℝ) + 4 * (S : ℝ) * X +
        (X : ℝ) ^ 3 / (3 * (p : ℝ) ^ 2) := by
    have hX2 : (X : ℝ) ^ 2 ≤ ((m : ℝ) * ((m : ℝ) - 1) + 4 * m) * (p : ℝ) ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hX_lt 2
      nlinarith
    have hdiv : (S : ℝ) * (X : ℝ) ^ 2 / p ≤
        (p : ℝ) * S * m * ((m : ℝ) - 1) + 4 * (S : ℝ) * X := by
      rw [div_le_iff₀ hpR]
      have h4 : 4 * (S : ℝ) * ((m : ℝ) * p) ≤ 4 * (S : ℝ) * X :=
        mul_le_mul_of_nonneg_left hm_le (by positivity)
      nlinarith [show (0 : ℝ) ≤ S by positivity]
    linarith [show (X : ℝ) ^ 3 / (3 * (p : ℝ) ^ 2) = (X : ℝ) ^ 3 / (p : ℝ) ^ 2 / 3 by ring]
  calc
    (S : ℝ) * (X : ℝ) ^ 2 * (Real.log p / p)
      = ((S : ℝ) * (X : ℝ) ^ 2 / p) * Real.log p := by ring
    _ ≤ ((2 * ∑ a : Idx X S, rowOrder p S a : ℝ) + 4 * (S : ℝ) * X +
          (X : ℝ) ^ 3 / (3 * (p : ℝ) ^ 2)) * Real.log p :=
        mul_le_mul_of_nonneg_right hSX2 (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))
    _ = (2 * ∑ a : Idx X S, rowOrder p S a : ℝ) * Real.log p +
          4 * (S : ℝ) * X * Real.log p +
          (X : ℝ) ^ 3 / 3 * (Real.log p / (p : ℝ) ^ 2) := by ring

private theorem log_div_sq_le_four_mul_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / (n : ℝ) ^ 2 ≤
      4 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) := by
  have hn1_pos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hn_pos : (0 : ℝ) < n := by positivity
  have hsub_eq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hlog : Real.log n ≤ 2 * Real.sqrt n := by
    calc
      Real.log n = Real.log (Real.sqrt n ^ 2) := by rw [Real.sq_sqrt hn_pos.le]
      _ = 2 * Real.log (Real.sqrt n) := by rw [Real.log_pow]; ring
      _ ≤ 2 * (Real.sqrt n - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn_pos))
            (by norm_num)
      _ ≤ 2 * Real.sqrt n := by linarith
  have hstep : 2 * Real.sqrt n / (n : ℝ) ^ 2 ≤
      4 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) := by
    have hs1_pos : 0 < Real.sqrt ((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hn1_pos
    have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hs_le : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by rw [hsub_eq]; linarith)
    have hdiff : 1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ) =
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) /
          (Real.sqrt ((n - 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by field_simp
    rw [hdiff, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq_diff : (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) *
        (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) = 1 := by
      nlinarith [Real.sq_sqrt hn_pos.le, Real.sq_sqrt hn1_pos.le, hsub_eq]
    have hprod_le : Real.sqrt ((n - 1 : ℕ) : ℝ) *
        (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
      nlinarith [Real.sq_sqrt hn_pos.le]
    nlinarith [Real.sq_sqrt hn_pos.le]
  exact (div_le_div_of_nonneg_right hlog (by positivity)).trans hstep

private theorem sum_Icc_log_div_sq_le_four (X : ℕ) :
    ∑ n ∈ Finset.Icc 2 X, Real.log n / (n : ℝ) ^ 2 ≤ 4 := by
  by_cases hX : X < 2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; norm_num
  push Not at hX
  calc
    ∑ n ∈ Finset.Icc 2 X, Real.log n / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 2 X,
          4 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) :=
        Finset.sum_le_sum fun n hn ↦ log_div_sq_le_four_mul_sub (Finset.mem_Icc.mp hn).1
    _ = 4 * ∑ k ∈ Finset.range (X - 1),
          (1 / Real.sqrt ((k + 1 : ℕ) : ℝ) - 1 / Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
        rw [← Finset.mul_sum]
        congr 1
        have hIcc : Finset.Icc 2 X =
            (Finset.range (X - 1)).map ⟨fun k ↦ k + 2, add_left_injective 2⟩ := by
          ext m
          simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
          exact ⟨fun ⟨_, _⟩ ↦ ⟨m - 2, by omega, by omega⟩, fun ⟨_, _, _⟩ ↦ by omega⟩
        rw [hIcc, Finset.sum_map]
        rfl
    _ = 4 * (1 / Real.sqrt ((0 + 1 : ℕ) : ℝ) - 1 / Real.sqrt ((X - 1 + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_range_sub' (fun k ↦ 1 / Real.sqrt ((k + 1 : ℕ) : ℝ))]
    _ ≤ 4 := by
        have hpos : 0 ≤ 1 / Real.sqrt ((X - 1 + 1 : ℕ) : ℝ) := by positivity
        simp only [zero_add, Nat.cast_one, Real.sqrt_one, div_one]
        linarith

private theorem parameter_degree_lt {q c C : ℕ} (hq : 3 ≤ q) (hc : 6 ≤ c) (hC : C = 3 * c) :
    2 * q ^ C * (q ^ C / C + 1) + q ^ (2 * c) * (q ^ C + (q ^ C / C + 1)) <
      (q ^ (2 * c)) ^ 3 := by
  set X := q ^ C
  set S := X / C + 1
  set N := q ^ (2 * c)
  have hqc : 729 ≤ q ^ c :=
    (show 729 = 3 ^ 6 by norm_num) ▸
      (Nat.pow_le_pow_right (by omega) hc).trans (Nat.pow_le_pow_left hq c)
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hX_eq : X = N * q ^ c := by
    dsimp only [X, N]; rw [hC, show 3 * c = 2 * c + c by omega, pow_add]
  have hX729 : 729 ≤ X := by nlinarith
  have h4N : 4 * N ≤ X := by nlinarith
  have h18S : 18 * S ≤ X + 18 := by
    have h18C : 18 ≤ C := by omega
    have : 18 * (X / C) ≤ C * (X / C) := Nat.mul_le_mul_right _ h18C
    have : C * (X / C) ≤ X := Nat.mul_div_le X C
    dsimp only [S]; omega
  have hN3 : N ^ 3 = X ^ 2 := by
    dsimp only [X, N]; rw [← pow_mul, ← pow_mul, hC]; ring_nf
  rw [hN3]
  nlinarith

private theorem log_two_mul_mul_sqrt_eq {q c C : ℕ} (hq : 3 ≤ q) (hc : 6 ≤ c) (hC : C = 3 * c) :
    Real.log (2 * ((q ^ (2 * c) : ℕ) : ℝ) * Real.sqrt q) =
      Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q ^ C : ℕ) : ℝ) := by
  set X := q ^ C
  set N := q ^ (2 * c)
  have hN_pos : (0 : ℝ) < N := by positivity
  rw [mul_assoc, Real.log_mul (by norm_num) (by positivity),
    Real.log_mul hN_pos.ne' (Real.sqrt_pos.mpr (by positivity)).ne',
    Real.log_sqrt (by positivity)]
  have hlogN : Real.log N = (2 * c : ℕ) * Real.log q := by
    dsimp [N]; rw [Nat.cast_pow, Real.log_pow]
  have hlogX : Real.log X = (C : ℝ) * Real.log q := by
    dsimp [X]; rw [Nat.cast_pow, Real.log_pow]
  have hCR : (C : ℝ) = 3 * (c : ℝ) := by exact_mod_cast hC
  rw [hlogN, hlogX, Nat.cast_mul, Nat.cast_ofNat, hCR]
  field_simp [show (c : ℝ) ≠ 0 by positivity]

private theorem archimedean_main_term_le {q c C : ℕ} (hq : 3 ≤ q) (hc : 6 ≤ c) (hC : C = 3 * c) :
    let X := q ^ C
    let S := X / C + 1
    let N := q ^ (2 * c)
    (X * S * (X + S) : ℝ) * Real.log (2 * (N : ℝ) * Real.sqrt q) ≤
      3 / 4 * ((S : ℝ) * (X : ℝ) ^ 2) * Real.log X + 4 * ((S : ℝ) * (X : ℝ) ^ 2) := by
  intro X S N
  have hC18 : (18 : ℝ) ≤ C := by exact_mod_cast (by omega : 18 ≤ C)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast Nat.one_le_pow C q (by omega)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogX_le : Real.log X ≤ X := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < X)]
  have hlogX_nn : 0 ≤ Real.log X := Real.log_nonneg hX1
  have h1C : 1 / (C : ℝ) ≤ 1 / 18 := one_div_le_one_div_of_le (by norm_num) hC18
  have h2C : 1 / (2 * (C : ℝ)) ≤ 1 / 36 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hXS_le : (X + S : ℝ) ≤ (1 + 1 / (C : ℝ)) * X + 1 := by
    have hdiv : ((X / C : ℕ) : ℝ) ≤ (X : ℝ) / C := Nat.cast_div_le
    dsimp [S]; push_cast; linarith [show (X : ℝ) / C = 1 / (C : ℝ) * X by ring]
  rw [log_two_mul_mul_sqrt_eq hq hc hC]
  have hstep : (X * S * (X + S) : ℝ) *
        (Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log X) ≤
      ((X : ℝ) * S * ((1 + 1 / (C : ℝ)) * X + 1)) *
        (Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log X) := by
    gcongr
  have hsub1 : (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) *
        ((S : ℝ) * (X : ℝ) ^ 2) * Real.log X ≤
      3 / 4 * ((S : ℝ) * (X : ℝ) ^ 2) * Real.log X :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)) hlogX_nn
  have hsub2 : (1 + 1 / (C : ℝ)) * Real.log 2 * ((S : ℝ) * (X : ℝ) ^ 2) ≤
      2 * ((S : ℝ) * (X : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (by nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
      (by positivity)
  have hsub3 : ((X : ℝ) * S) * (Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log X) ≤
      2 * ((S : ℝ) * (X : ℝ) ^ 2) := by
    have : Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log X ≤ 2 * (X : ℝ) := by nlinarith
    nlinarith [show (0 : ℝ) ≤ (X : ℝ) * S by positivity]
  linarith [show ((X : ℝ) * S * ((1 + 1 / (C : ℝ)) * X + 1)) *
        (Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log X) =
      (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * ((S : ℝ) * (X : ℝ) ^ 2) * Real.log X +
        (1 + 1 / (C : ℝ)) * Real.log 2 * ((S : ℝ) * (X : ℝ) ^ 2) +
        ((X : ℝ) * S) * (Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log X) by ring]

private theorem archimedean_rhs_le {q c C : ℕ} (hq : 3 ≤ q) (hc : 6 ≤ c) (hC : C = 3 * c) :
    let X := q ^ C
    let S := X / C + 1
    let N := q ^ (2 * c)
    (X * S : ℝ) * Real.log (2 * (N : ℝ) ^ 3) +
        2 * (X * S * N : ℝ) * Real.log X +
        (X * S * (X + S) : ℝ) * Real.log (2 * (N : ℝ) * Real.sqrt q) ≤
      3 / 4 * ((S : ℝ) * (X : ℝ) ^ 2) * Real.log X +
        (7 + 2 * (C : ℝ)) * ((S : ℝ) * (X : ℝ) ^ 2) := by
  intro X S N
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast Nat.one_le_pow C q (by omega)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogX_le : Real.log X ≤ X := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < X)]
  have hterm1 : (X * S : ℝ) * Real.log (2 * (N : ℝ) ^ 3) ≤ 3 * ((S : ℝ) * (X : ℝ) ^ 2) := by
    have hN3 : (N : ℝ) ^ 3 = (X : ℝ) ^ 2 := by
      have : N ^ 3 = X ^ 2 := by dsimp [X, N]; rw [← pow_mul, ← pow_mul, hC]; ring_nf
      exact_mod_cast this
    rw [hN3, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (X : ℝ) * S by positivity]
  have hterm2 : 2 * (X * S * N : ℝ) * Real.log X ≤ 2 * (C : ℝ) * ((S : ℝ) * (X : ℝ) ^ 2) := by
    have hlogq : Real.log q ≤ (q : ℝ) ^ c := by
      have h1 : Real.log q ≤ q := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < q)]
      have h2 : (q : ℝ) ≤ (q : ℝ) ^ c := by
        simpa using pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) (by omega : 1 ≤ c)
      linarith
    have hX_eq : (X : ℝ) = (N : ℝ) * (q : ℝ) ^ c := by
      have : X = N * q ^ c := by dsimp [X, N]; rw [hC, show 3 * c = 2 * c + c by omega, pow_add]
      exact_mod_cast this
    have hlogX_eq : Real.log X = (C : ℝ) * Real.log q := by
      dsimp [X]; rw [Nat.cast_pow, Real.log_pow]
    have hNlogX : (N : ℝ) * Real.log X ≤ (C : ℝ) * X := by
      rw [hlogX_eq, hX_eq]
      exact (show (N : ℝ) * ((C : ℝ) * Real.log q) = ((C : ℝ) * N) * Real.log q by ring) ▸
        (show (C : ℝ) * ((N : ℝ) * (q : ℝ) ^ c) = ((C : ℝ) * N) * (q : ℝ) ^ c by ring) ▸
        mul_le_mul_of_nonneg_left hlogq (by positivity)
    exact (show 2 * (X * S * N : ℝ) * Real.log X = (2 * (X : ℝ) * S) * ((N : ℝ) * Real.log X) by
      ring) ▸
      (show 2 * (C : ℝ) * ((S : ℝ) * (X : ℝ) ^ 2) = (2 * (X : ℝ) * S) * ((C : ℝ) * X) by ring) ▸
      mul_le_mul_of_nonneg_left hNlogX (by positivity)
  linarith [archimedean_main_term_le hq hc hC]

private theorem sum_primes_log_le_two_mul {X : ℕ} {P' : Finset ℕ}
    (hsub : P' ⊆ Nat.primesLE X) :
    ∑ p ∈ P', Real.log p ≤ 2 * (X : ℝ) := by
  have h1 : ∑ p ∈ P', Real.log p ≤ Chebyshev.theta X := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Chebyshev.theta_le_log4_mul_x (by positivity : (0 : ℝ) ≤ X),
    show (0 : ℝ) ≤ X by positivity]

private theorem padic_lhs_le_log_intGram_det {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {q c C : ℕ} (hq : 3 ≤ q) (hc : 6 ≤ c) (hC : C = 3 * c)
    (P' : Finset ℕ) (hsub : P' ⊆ Nat.primesLE (q ^ C))
    (hP' : ∀ p ∈ P', C ≤ p ∧ ¬IsSquare (d : ZMod p)) :
    let X := q ^ C
    let S := X / C + 1
    let N := q ^ (2 * c)
    (S : ℝ) * (X : ℝ) ^ 2 * (∑ p ∈ P', Real.log p / p) ≤
      Real.log ((intGram d X S N).det : ℝ) +
        (8 + 4 / 3 * (C : ℝ)) * ((S : ℝ) * (X : ℝ) ^ 2) := by
  intro X S N
  have hdeg := parameter_degree_lt hq hc hC
  have hP'_inert : ∀ p ∈ P', p.Prime ∧ ¬IsSquare (d : ZMod p) := fun p hp ↦
    ⟨Nat.prime_of_mem_primesLE (hsub hp), (hP' p hp).2⟩
  rw [Finset.mul_sum]
  have hsum_le : ∑ p ∈ P', (S : ℝ) * (X : ℝ) ^ 2 * (Real.log p / p) ≤
      (∑ p ∈ P', (2 * ∑ a : Idx X S, rowOrder p S a : ℝ) * Real.log p) +
        4 * (S : ℝ) * X * (∑ p ∈ P', Real.log p) +
        (X : ℝ) ^ 3 / 3 * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) := by
    calc
      ∑ p ∈ P', (S : ℝ) * (X : ℝ) ^ 2 * (Real.log p / p)
        ≤ ∑ p ∈ P', ((2 * ∑ a : Idx X S, rowOrder p S a : ℝ) * Real.log p +
            4 * (S : ℝ) * X * Real.log p +
            (X : ℝ) ^ 3 / 3 * (Real.log p / (p : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun p hp ↦
            mul_sq_log_div_le_rowOrder (by omega) (hP' p hp).1 (Nat.le_of_mem_primesLE (hsub hp))
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsq_sum : ∑ p ∈ P', Real.log p / (p : ℝ) ^ 2 ≤ 4 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (s := P') (t := Finset.Icc 2 X) ?_ ?_).trans
      (sum_Icc_log_div_sq_le_four X)
    · exact fun p hp ↦ Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE (hsub hp)).two_le,
        Nat.le_of_mem_primesLE (hsub hp)⟩
    · intro n hn _
      have : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast this)) (by positivity)
  have hX_le_CS : (X : ℝ) ≤ (C : ℝ) * S := by
    have hle : X ≤ C * S := by
      have h1 : C * (X / C) + X % C = X := Nat.div_add_mod X C
      have h2 : X % C < C := Nat.mod_lt X (by omega : 0 < C)
      dsimp only [S]; nlinarith
    exact_mod_cast hle
  have hfact3 := sum_primes_mul_log_le_log_intGram_det hd hd1 hdeg P' hP'_inert
  have hterm_cheb : 4 * (S : ℝ) * X * (∑ p ∈ P', Real.log p) ≤
      8 * ((S : ℝ) * (X : ℝ) ^ 2) := by
    nlinarith [sum_primes_log_le_two_mul hsub, show (0 : ℝ) ≤ (S : ℝ) * X by positivity]
  have hterm_sq : (X : ℝ) ^ 3 / 3 * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤
      4 / 3 * (C : ℝ) * ((S : ℝ) * (X : ℝ) ^ 2) := by
    have hX3 : (X : ℝ) ^ 3 ≤ (C : ℝ) * ((S : ℝ) * (X : ℝ) ^ 2) := by
      nlinarith [show (0 : ℝ) ≤ (X : ℝ) ^ 2 by positivity]
    have : 0 ≤ ∑ p ∈ P', Real.log p / (p : ℝ) ^ 2 :=
      Finset.sum_nonneg fun p hp ↦ div_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE (hsub hp)).one_le))
        (by positivity)
    nlinarith [show (0 : ℝ) ≤ (X : ℝ) ^ 3 by positivity]
  linarith

private theorem nonsquare_of_jacobiSym_cast_eq_neg_one {R : Type*} [CommRing R] [NeZero (2 : R)]
    {d : ℤ} {p : ℕ} (hcast : (jacobiSym d p : R) = -1) : ¬IsSquare (d : ZMod p) := by
  refine ZMod.nonsquare_of_jacobiSym_eq_neg_one ?_
  rcases jacobiSym.trichotomy d p with h0 | h1' | hneg
  · rw [h0, Int.cast_zero] at hcast
    exact absurd (by linear_combination 2 * hcast : (2 : R) = 0) (NeZero.ne (2 : R))
  · rw [h1', Int.cast_one] at hcast
    exact absurd (by linear_combination hcast : (2 : R) = 0) (NeZero.ne (2 : R))
  · exact hneg

end InertPrimeSum

end TauCeti

/-- **Upper bound on the reciprocal-prime sum over inert primes of a primitive quadratic
character.** Let `χ` be a nontrivial primitive quadratic Dirichlet character modulo `q` with values
in a commutative ring `R` in which `2 ≠ 0`. For every `C ≥ 18` divisible by `3`, the sum of
`log p / p` over primes `p ≤ q ^ C` with `χ p = -1` is at most `3 / 4 * log (q ^ C) + K(C)` for an
explicit constant `K(C)` depending only on `C`. -/
theorem DirichletCharacter.IsPrimitive.sum_primesLE_log_div_le
    {R : Type*} [CommRing R] [DecidableEq R] [NeZero (2 : R)] {q : ℕ} [NeZero q]
    {χ : DirichletCharacter R q} (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (h1 : χ ≠ 1)
    {C : ℕ} (hC : 18 ≤ C) (h3 : 3 ∣ C) :
    ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1),
      Real.log p / p ≤
      3 / 4 * Real.log ((q : ℝ) ^ C) +
        ((∑ p ∈ Nat.primesLE C, Real.log p / p) + 15 + 10 / 3 * (C : ℝ)) := by
  open TauCeti.InertPrimeSum in
  have hq : 3 ≤ q := χ.three_le_of_ne_one h1
  obtain ⟨c, rfl⟩ := h3
  have hc : 6 ≤ c := by omega
  obtain ⟨d, hd_sqf, hd1, hdq, hχ_eq⟩ := hprim.exists_squarefree_apply_eq_jacobiSym hquad h1
  set C := 3 * c
  set X := q ^ C
  set S := X / C + 1
  set N := q ^ (2 * c)
  set P := (Nat.primesLE X).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1)
  set P' := P.filter (fun p : ℕ ↦ C ≤ p)
  have hP_split : ∑ p ∈ P, Real.log p / p ≤
      (∑ p ∈ Nat.primesLE C, Real.log p / p) + ∑ p ∈ P', Real.log p / p := by
    have hsmall : ∑ p ∈ P.filter (fun p : ℕ ↦ ¬C ≤ p), Real.log p / p ≤
        ∑ p ∈ Nat.primesLE C, Real.log p / p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ ↦ by positivity
      intro p hp
      obtain ⟨hpP, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, hp_prime⟩ := Nat.mem_primesLE.mp (Finset.mem_filter.mp hpP).1
      exact Nat.mem_primesLE.mpr ⟨by omega, hp_prime⟩
    have hpart := Finset.sum_filter_add_sum_filter_not P (fun p : ℕ ↦ C ≤ p)
      (fun p : ℕ ↦ Real.log p / p)
    change ∑ p ∈ P', Real.log p / p + ∑ p ∈ P.filter (fun p : ℕ ↦ ¬C ≤ p), Real.log p / p =
      ∑ p ∈ P, Real.log p / p at hpart
    linarith
  have hsub : P' ⊆ Nat.primesLE X := fun p hp ↦
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hP'_inert : ∀ p ∈ P', C ≤ p ∧ ¬IsSquare (d : ZMod p) := by
    intro p hp
    obtain ⟨hpP, hpC⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX, hχp⟩ := Finset.mem_filter.mp hpP
    have hodd := (Nat.prime_of_mem_primesLE hpX).odd_of_ne_two (by omega)
    exact ⟨hpC, nonsquare_of_jacobiSym_cast_eq_neg_one ((hχ_eq p hodd).symm.trans hχp)⟩
  have hdeg := parameter_degree_lt hq hc rfl
  have hpadic := padic_lhs_le_log_intGram_det hd_sqf hd1 hq hc rfl P' hsub hP'_inert
  have harch := (log_intGram_det_le hd_sqf hd1 (Nat.one_le_pow C q (by omega))
    (Nat.one_le_pow _ q (by omega)) hq hdq hdeg).trans (archimedean_rhs_le hq hc rfl)
  have hSX2_pos : 0 < (S : ℝ) * (X : ℝ) ^ 2 := by
    have : 1 ≤ X := Nat.one_le_pow C q (by omega)
    have : 0 < S := Nat.succ_pos _
    positivity
  have hP'_le : ∑ p ∈ P', Real.log p / p ≤
      3 / 4 * Real.log ((q : ℝ) ^ C) + (15 + 10 / 3 * (C : ℝ)) := by
    have hmul : (S : ℝ) * (X : ℝ) ^ 2 * (∑ p ∈ P', Real.log p / p) ≤
        (S : ℝ) * (X : ℝ) ^ 2 * (3 / 4 * Real.log X + (15 + 10 / 3 * (C : ℝ))) := by linarith
    simpa [X] using le_of_mul_le_mul_left hmul hSX2_pos
  change ∑ p ∈ P, Real.log p / p ≤ _
  linarith

namespace TauCeti

/-- **Inert primes carry at most three quarters of the Mertens mass.** There exists an absolute
threshold `C₀` (`C₀ = 18` suffices) such that for every `C ≥ C₀` divisible by `3`, there is a
constant `K` depending only on `C` with the property that for every modulus `q ≥ 3` and every
nontrivial primitive quadratic character `χ` modulo `q`,
`∑_{p ≤ q ^ C, χ p = -1} log p / p ≤ 3 / 4 * log (q ^ C) + K`. -/
theorem inert_prime_sum_le :
    ∃ C₀ : ℕ, ∀ C : ℕ, C₀ ≤ C → 3 ∣ C → ∃ K : ℝ,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        3 ≤ q → χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
          ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1),
            Real.log p / p ≤
            3 / 4 * Real.log ((q : ℝ) ^ C) + K :=
  ⟨18, fun C hC h3 ↦
    ⟨(∑ p ∈ Nat.primesLE C, Real.log p / p) + 15 + 10 / 3 * (C : ℝ),
      fun _ _ _ _ hprim hquad h1 ↦ hprim.sum_primesLE_log_div_le hquad h1 hC h3⟩⟩

end TauCeti
