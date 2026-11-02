/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Amice's polynomials on the discs of level `h`

For `h, n : ℕ` put `m_h(n) = ⌊n / pʰ⌋!`. Amice's basis of the analytic stage `LA_h` consists of
the polynomials

`e_{h,n}(x) = m_h(n) (x choose n)`.

On the disc `a + pʰℤ_p`, in the coordinate `w = (x - a) / pʰ`, the polynomial `e_{h,n}` is a
polynomial in `w`. Its coefficients lie in `ℤ_p`
(`TauCeti.exists_natDegree_le_and_eval_eq_factorial_mul_choose`). This is stronger than
`e_{h,n}` taking integral values, which already holds for `x choose n`, and it needs the factor
`m_h(n)`: the coefficient of `w` in `(pʰ w choose n)` is `(-1) ^ (n - 1) pʰ / n`, which is
`± p⁻¹` for `n = p ^ (h + 1)`. The proof factors
`n! (a + pʰ w choose n) = ∏_{i < n} (a - i + pʰ w)`. The factor of index `i` is divisible by
`p ^ min(v_p(a - i), h)`, and among `n` consecutive elements of `ℤ_p` at least `⌊n / pᵏ⌋` are
divisible by `pᵏ`, so the product is divisible by `p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`. By Legendre's
formula this exponent is `v_p(n!) - v_p(m_h(n))`.

Hence `e_{h,n}` has an expansion in `LA_h(ℤ_p)`, and more generally `e_{h,n} • e` has one in
`LA_h(E)` for every normed `ℤ_p`-module `E`, of norm at most `‖e‖` when the action is
contractive. For complete ultrametric `E`, summing these vectors gives a continuous linear map

`TauCeti.AnalyticStage.amiceMap : C₀(ℕ, E) → LA_h(E)`,  `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`,

which does not increase norms. Followed by evaluation, it is the Mahler series with
coefficients `m_h(n) • cₙ` (`TauCeti.AnalyticStage.eval_amiceMap`). Amice's theorem, which is not
proved here, asserts that `amiceMap` is an isometric isomorphism.

Its arithmetic input is the reduction of Amice's polynomials modulo `p`. Write `n = pʰ q + r`
with `r < pʰ`, and let `a` be a natural number. In `∏_{i < n} (a - i + pʰ w)`, the factors with
`i ≡ a mod pʰ` are `pʰ` times a monic linear polynomial, and each other factor is `a - i` times a
polynomial congruent to `1` modulo `p`. Hence Amice's polynomial on the disc of `a` is `c F`, where
`F` is congruent modulo `p` to a monic polynomial of degree `#{i < n | i ≡ a mod pʰ}`, which is
`q` or `q + 1`, and, by Legendre's formula, `v_p(c)` is the number of `k ∈ [1, h]` with
`a mod pᵏ < n mod pᵏ`. Consequently, modulo `p`, the expansion of `e_{h,n}` has degree at most
`q` on every disc, vanishes on the discs with `a mod pʰ < r`, and has a unit coefficient of `w^q`
on the disc of `r`. Ordering the coordinates `(a, j)` of `LA_h` by `j` and then by decreasing `a`,
and matching `n` with the coordinate `(r, q)`, the matrix of `amiceMap` is thus congruent modulo
`p` to an upper triangular matrix with unit diagonal.

## Main definitions

* `TauCeti.amicePolynomial p h n a`: the polynomial `w ↦ m_h(n) (a + pʰ w choose n)` over
  `ℤ_p`.
* `TauCeti.AnalyticStage.amiceTerm p h n e`: the expansion of `e_{h,n} • e` in `LA_h(E)`.
* `TauCeti.AnalyticStage.amiceMap p h S`: the map `C₀(ℕ, E) →L[S] LA_h(E)`, `c ↦ ∑ₙ e_{h,n} • cₙ`.

## Main results

* `TauCeti.exists_natDegree_le_and_eval_eq_factorial_mul_choose`: Amice's polynomials have
  integral coefficients on every disc.
* `TauCeti.eval_amicePolynomial`, `TauCeti.eq_amicePolynomial_of_eval`: `amicePolynomial` is the
  unique polynomial with these values.
* `TauCeti.AnalyticStage.eval_amiceTerm`: `amiceTerm` evaluates to the Mahler term of
  `m_h(n) • e`.
* `TauCeti.norm_coeff_amicePolynomial_lt_one_of_div_lt`: modulo `p`, Amice's polynomial on every
  disc has degree at most `⌊n / pʰ⌋`.
* `TauCeti.norm_coeff_amicePolynomial_lt_one_of_mod_lt`: modulo `p`, it vanishes on the disc of `a`
  when `a mod pʰ < n mod pʰ`.
* `TauCeti.norm_coeff_amicePolynomial_div_of_mod_le`: the norm of its coefficient of
  `w ^ ⌊n / pʰ⌋` on the other discs.
* `TauCeti.norm_coeff_amicePolynomial_mod_div`: that coefficient is a unit on the disc of
  `n mod pʰ`.
* `TauCeti.AnalyticStage.norm_amiceMap_le`, `TauCeti.AnalyticStage.eval_amiceMap`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Polynomial Nat
open scoped ZeroAtInfty Finset

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

/-! ### Integrality of the disc coefficients -/

section Integrality

open PadicInt

/-- The product `∏_{i < n} (a - i + pʰ X)`, whose value at `w` is `n! (a + pʰ w choose n)`. -/
private noncomputable def discProd (h n : ℕ) (a : ℤ_[p]) : ℤ_[p][X] :=
  ∏ i ∈ Finset.range n, (C (a - i) + C ((p : ℤ_[p]) ^ h) * X)

private theorem eval_discProd (h n : ℕ) (a w : ℤ_[p]) :
    (discProd h n a).eval w = n ! * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n := by
  have hchoose := Ring.descPochhammer_eq_factorial_smul_choose (a + (p : ℤ_[p]) ^ h * w) n
  rw [← aeval_eq_smeval, aeval_def, ← eval_map, descPochhammer_map,
    descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at hchoose
  rw [discProd, eval_prod, ← hchoose]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [eval_add, eval_C, eval_mul, eval_X]
  ring

private theorem natDegree_discProd_le (h n : ℕ) (a : ℤ_[p]) : (discProd h n a).natDegree ≤ n := by
  rw [discProd]
  refine (natDegree_prod_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ ?_).trans
    (Finset.sum_const_nat (m := 1) fun _ _ ↦ rfl).le |>.trans (by simp)
  exact (natDegree_add_le _ _).trans <| max_le ((natDegree_C _).le.trans zero_le_one)
    ((natDegree_C_mul_le _ _).trans natDegree_X_le)

open scoped Classical in
/-- The constant factored out of the term `a - i + pʰ X` of `discProd`: `pʰ` if `pʰ ∣ a - i`,
and `a - i` otherwise. -/
private noncomputable def discFactor (h : ℕ) (z : ℤ_[p]) : ℤ_[p] :=
  if (p : ℤ_[p]) ^ h ∣ z then (p : ℤ_[p]) ^ h else z

open scoped Classical in
/-- Modulo `p`, the term `z + pʰ X` is `discFactor h z` times a monic polynomial, of degree one
if `pʰ ∣ z` and of degree zero otherwise. -/
private theorem exists_C_add_eq_C_discFactor_mul (h : ℕ) (z : ℤ_[p]) :
    ∃ F : ℤ_[p][X], C z + C ((p : ℤ_[p]) ^ h) * X = C (discFactor h z) * F ∧
      (F.map toZMod).Monic ∧
      (F.map toZMod).natDegree = if (p : ℤ_[p]) ^ h ∣ z then 1 else 0 := by
  classical
  by_cases hz : (p : ℤ_[p]) ^ h ∣ z
  · obtain ⟨s, rfl⟩ := hz
    refine ⟨X + C s, ?_, ?_, ?_⟩
    · rw [discFactor, ite_eq_left (dvd_mul_right _ _), C_mul]
      ring
    · simpa using monic_X_add_C (toZMod s)
    · simp
  · -- Here `‖z‖ > p⁻ʰ`, so `p z` divides `pʰ`.
    obtain ⟨t, ht⟩ : (p : ℤ_[p]) * z ∣ (p : ℤ_[p]) ^ h := by
      refine PadicInt.dvd_of_norm_le ?_
      have hle : ¬ ‖z‖ ≤ (p : ℝ) ^ (-(h : ℤ)) := by
        rwa [norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
      rw [norm_le_pow_iff_norm_lt_pow_add_one, not_lt] at hle
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      rw [norm_mul, norm_p, norm_p_pow]
      calc (p : ℝ) ^ (-(h : ℤ)) = (p : ℝ)⁻¹ * (p : ℝ) ^ (-(h : ℤ) + 1) := by
            rw [zpow_add_one₀ hp0]
            field_simp
        _ ≤ (p : ℝ)⁻¹ * ‖z‖ := by gcongr
    refine ⟨1 + C ((p : ℤ_[p]) * t) * X, ?_, ?_, ?_⟩
    · rw [discFactor, ite_eq_right hz, ht]
      simp only [C_mul]
      ring
    · simp
    · simp [hz]

open scoped Classical in
/-- `discProd` is the product of the constants `discFactor` and of a polynomial whose reduction
modulo `p` is monic of degree `#{i < n | pʰ ∣ a - i}`. -/
private theorem exists_discProd_eq (h n : ℕ) (a : ℤ_[p]) :
    ∃ F : ℤ_[p][X],
      discProd h n a = C (∏ i ∈ Finset.range n, discFactor h (a - ((i : ℕ) : ℤ_[p]))) * F ∧
      (F.map toZMod).Monic ∧
      (F.map toZMod).natDegree =
        #{i ∈ Finset.range n | (p : ℤ_[p]) ^ h ∣ a - ((i : ℕ) : ℤ_[p])} := by
  classical
  choose F hF using fun i : ℕ ↦ exists_C_add_eq_C_discFactor_mul h (a - (i : ℤ_[p]))
  refine ⟨∏ i ∈ Finset.range n, F i, ?_, ?_, ?_⟩
  · rw [discProd, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ (hF i).1
  · rw [Polynomial.map_prod]
    exact monic_prod_of_monic _ _ fun i _ ↦ (hF i).2.1
  · rw [Polynomial.map_prod, natDegree_prod_of_monic _ _ fun i _ ↦ (hF i).2.1]
    simp_rw [fun i ↦ (hF i).2.2]
    rw [Finset.sum_boole]
    simp

open scoped Classical in
/-- The norm of `discFactor h z` is `‖p‖ ^ min(v_p(z), h)`, written as the number of `k < h`
with `pᵏ⁺¹ ∣ z`. -/
private theorem norm_discFactor (h : ℕ) (z : ℤ_[p]) :
    ‖discFactor h z‖ = ‖(p : ℤ_[p])‖ ^ #{k ∈ Finset.range h | (p : ℤ_[p]) ^ (k + 1) ∣ z} := by
  classical
  by_cases hz : (p : ℤ_[p]) ^ h ∣ z
  · rw [discFactor, ite_eq_left hz, norm_pow, Finset.filter_true_of_mem fun k hk ↦
      (pow_dvd_pow _ (Finset.mem_range.mp hk)).trans hz, Finset.card_range]
  · have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz (dvd_zero _)
    have hdvd (m : ℕ) : (p : ℤ_[p]) ^ m ∣ z ↔ m ≤ z.valuation := by
      rw [← Ideal.mem_span_singleton, mem_span_pow_iff_le_valuation z hz0]
    have hv : z.valuation < h := lt_of_not_ge fun hle ↦ hz ((hdvd h).mpr hle)
    rw [discFactor, ite_eq_right hz, norm_eq_zpow_neg_valuation hz0, ← norm_p_pow, norm_pow,
      Finset.filter_congr fun k _ ↦ hdvd (k + 1)]
    have hrange : {k ∈ Finset.range h | k + 1 ≤ z.valuation} = Finset.range z.valuation := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hrange, Finset.card_range]

open scoped Classical in
/-- The product of the constants `discFactor` has norm `‖p‖ ^ ∑_{k < h} #{i < n | pᵏ⁺¹ ∣ a - i}`,
counting the pairs `(k, i)` with `pᵏ⁺¹ ∣ a - i` by `i` and then by `k`. -/
private theorem norm_prod_discFactor (h n : ℕ) (a : ℤ_[p]) :
    ‖∏ i ∈ Finset.range n, discFactor h (a - ((i : ℕ) : ℤ_[p]))‖ =
      ‖(p : ℤ_[p])‖ ^ ∑ k ∈ Finset.range h,
        #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])} := by
  classical
  rw [norm_prod]
  simp_rw [norm_discFactor]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The product `∏_{i < n} (a - i + pʰ X)` is divisible by `p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`. -/
private theorem C_pow_dvd_discProd (h n : ℕ) (a : ℤ_[p]) :
    C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1)) ∣ discProd h n a := by
  obtain ⟨F, hF, -, -⟩ := exists_discProd_eq h n a
  rw [hF]
  refine dvd_mul_of_dvd_left (_root_.map_dvd C (dvd_of_norm_le ?_)) F
  rw [norm_prod_discFactor, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (norm_le_one _)
    (Finset.sum_le_sum fun k _ ↦ a.div_pow_le_card_filter_dvd n (k + 1))

/-- **Integrality of Amice's polynomials on discs.** For every centre `a ∈ ℤ_p`, the polynomial
`w ↦ ⌊n / pʰ⌋! (a + pʰ w choose n)` has coefficients in `ℤ_p`: it is the evaluation of a
polynomial over `ℤ_p` of degree at most `n`. -/
theorem exists_natDegree_le_and_eval_eq_factorial_mul_choose (h n : ℕ) (a : ℤ_[p]) :
    ∃ P : ℤ_[p][X], P.natDegree ≤ n ∧ ∀ w : ℤ_[p],
      P.eval w = ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n := by
  obtain ⟨P, hP⟩ : C (n ! : ℤ_[p]) ∣ C ((n / p ^ h)! : ℤ_[p]) * discProd h n a := by
    refine (_root_.map_dvd C (factorial_dvd_factorial_div_mul_pow h n)).trans ?_
    rw [C_mul]
    exact mul_dvd_mul_left _ (C_pow_dvd_discProd h n a)
  have hn : (n ! : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero n)
  refine ⟨P, ?_, fun w ↦ ?_⟩
  · rw [← natDegree_C_mul hn, ← hP]
    exact natDegree_C_mul_le _ _ |>.trans (natDegree_discProd_le h n a)
  · refine mul_left_cancel₀ hn ?_
    have := congrArg (eval w) hP
    rw [eval_mul, eval_mul, eval_C, eval_C, eval_discProd] at this
    rw [← this]
    ring

variable (p) in
/-- **Amice's polynomial on the disc of centre `a`.** The polynomial over `ℤ_p` whose value at
`w` is `⌊n / pʰ⌋! (a + pʰ w choose n)`: the expansion of Amice's basis polynomial
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)` in the coordinate `w = (x - a) / pʰ` of the disc
`a + pʰℤ_p`. -/
noncomputable def amicePolynomial (h n : ℕ) (a : ℤ_[p]) : ℤ_[p][X] :=
  (exists_natDegree_le_and_eval_eq_factorial_mul_choose h n a).choose

/-- Amice's polynomial on a disc has degree at most `n`. -/
theorem natDegree_amicePolynomial_le (h n : ℕ) (a : ℤ_[p]) :
    (amicePolynomial p h n a).natDegree ≤ n :=
  (exists_natDegree_le_and_eval_eq_factorial_mul_choose h n a).choose_spec.1

/-- The value of Amice's polynomial on the disc of centre `a` at `w` is
`⌊n / pʰ⌋! (a + pʰ w choose n)`. -/
@[simp]
theorem eval_amicePolynomial (h n : ℕ) (a w : ℤ_[p]) :
    (amicePolynomial p h n a).eval w =
      ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n :=
  (exists_natDegree_le_and_eval_eq_factorial_mul_choose h n a).choose_spec.2 w

/-- `amicePolynomial p h n a` is the only polynomial with values `⌊n / pʰ⌋! (a + pʰ w choose n)`.
-/
theorem eq_amicePolynomial_of_eval {h n : ℕ} {a : ℤ_[p]} {P : ℤ_[p][X]}
    (hP : ∀ w, P.eval w = ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n) :
    P = amicePolynomial p h n a :=
  Polynomial.funext fun w ↦ by rw [hP, eval_amicePolynomial]

/-- The coefficients of Amice's polynomial vanish above degree `n`. -/
theorem coeff_amicePolynomial_eq_zero {h n k : ℕ} (a : ℤ_[p]) (hk : n < k) :
    (amicePolynomial p h n a).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_amicePolynomial_le h n a).trans_lt hk)

/-- The disc expansion of Amice's polynomial: `∑_{k ≤ n} cₖ wᵏ = ⌊n / pʰ⌋! (a + pʰ w choose n)`,
where `cₖ` are the coefficients of `amicePolynomial p h n a`. -/
theorem sum_range_coeff_amicePolynomial_mul_pow (h n : ℕ) (a w : ℤ_[p]) :
    ∑ k ∈ Finset.range (n + 1), (amicePolynomial p h n a).coeff k * w ^ k =
      ((n / p ^ h)! : ℤ_[p]) * Ring.choose (a + (p : ℤ_[p]) ^ h * w) n := by
  rw [← eval_amicePolynomial,
    eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_amicePolynomial_le h n a))]

end Integrality

/-! ### Reduction modulo `p` -/

section Reduction

open PadicInt

/-- **Amice's polynomial modulo `p`.** On the disc of `a`, Amice's polynomial is `C c * F`, where
`F` is congruent modulo `p` to a monic polynomial of degree `N = ⌊n / pʰ⌋ + [a mod pʰ < n mod pʰ]`,
and `‖c‖` is `‖p‖ ^ e` with `e` the number of `k ∈ [1, h]` such that `a mod pᵏ < n mod pᵏ`. -/
private theorem exists_amicePolynomial_eq_C_mul (h n a : ℕ) :
    ∃ (c : ℤ_[p]) (F : ℤ_[p][X]), amicePolynomial p h n a = C c * F ∧
      ‖F.coeff (n / p ^ h + if a % p ^ h < n % p ^ h then 1 else 0)‖ = 1 ∧
      (∀ j, n / p ^ h + (if a % p ^ h < n % p ^ h then 1 else 0) < j → ‖F.coeff j‖ < 1) ∧
      ‖c‖ = ‖(p : ℤ_[p])‖ ^ #{k ∈ Finset.range h | a % p ^ (k + 1) < n % p ^ (k + 1)} := by
  classical
  obtain ⟨F, hprod, hmon, hdeg⟩ := exists_discProd_eq h n (a : ℤ_[p])
  rw [card_filter_pow_dvd_natCast_sub] at hdeg
  set N := n / p ^ h + (if a % p ^ h < n % p ^ h then 1 else 0)
  set K := ∏ i ∈ Finset.range n, discFactor h ((a : ℤ_[p]) - ((i : ℕ) : ℤ_[p]))
  -- `n! A = ⌊n / pʰ⌋! K F`, where `A` is Amice's polynomial.
  have hA : C (n ! : ℤ_[p]) * amicePolynomial p h n a = C (((n / p ^ h)! : ℤ_[p]) * K) * F := by
    rw [C_mul, mul_assoc, ← hprod]
    refine Polynomial.funext fun w ↦ ?_
    simp only [eval_mul, eval_C, eval_amicePolynomial, eval_discProd]
    ring
  -- Modulo `p`, the coefficient of `X ^ N` in `F` is one and the higher ones vanish.
  have hlead : ‖F.coeff N‖ = 1 := by
    refine (norm_le_one _).antisymm (not_lt.mp fun hlt ↦ one_ne_zero (α := ZMod p) ?_)
    rw [← hmon.leadingCoeff, leadingCoeff, hdeg, coeff_map]
    exact (toZMod_eq_zero_iff_dvd _).mpr ((norm_lt_one_iff_dvd _).mp hlt)
  have hhigh (j : ℕ) (hj : N < j) : ‖F.coeff j‖ < 1 := by
    rw [norm_lt_one_iff_dvd, ← toZMod_eq_zero_iff_dvd, ← coeff_map]
    exact coeff_eq_zero_of_natDegree_lt (hdeg ▸ hj)
  -- Hence `F.coeff N` is a unit, and `n!` divides `⌊n / pʰ⌋! K`.
  have hu : IsUnit (F.coeff N) := PadicInt.isUnit_iff.mpr hlead
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], (n ! : ℤ_[p]) * c = ((n / p ^ h)! : ℤ_[p]) * K := by
    refine ⟨(amicePolynomial p h n a).coeff N * ↑hu.unit⁻¹, ?_⟩
    have := congrArg (coeff · N) hA
    simp only [coeff_C_mul] at this
    rw [← mul_assoc, this, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hn : (n ! : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero n)
  refine ⟨c, F, ?_, hlead, hhigh, ?_⟩
  · refine mul_left_cancel₀ (C_ne_zero.mpr hn) ?_
    rw [hA, ← mul_assoc, ← C_mul, hc]
  -- Compare norms: `‖K‖ = ‖p‖ ^ ∑_{k < h} #{i < n | pᵏ⁺¹ ∣ a - i}` and Legendre's formula.
  have hK : ‖K‖ = _ := norm_prod_discFactor h n (a : ℤ_[p])
  simp_rw [card_filter_pow_dvd_natCast_sub] at hK
  rw [Finset.sum_add_distrib, Finset.sum_boole, pow_add] at hK
  have hnorm := congrArg norm hc
  rw [norm_mul, norm_mul, hK, norm_factorial_eq_norm_factorial_div_mul_pow h n, mul_assoc] at hnorm
  have hq : ‖((n / p ^ h)! : ℤ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr (factorial_ne_zero _))
  have hp0 : ‖(p : ℤ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  simpa using mul_left_cancel₀ (pow_ne_zero _ hp0) (mul_left_cancel₀ hq hnorm)

/-- If `a mod pʰ < n mod pʰ`, the level `k = h` contributes to the exponent `e` of
`exists_amicePolynomial_eq_C_mul`, so the constant `c` there has norm less than one. -/
private theorem norm_lt_one_of_mod_lt {h n a : ℕ} {c : ℤ_[p]} (ha : a % p ^ h < n % p ^ h)
    (hc : ‖c‖ = ‖(p : ℤ_[p])‖ ^ #{k ∈ Finset.range h | a % p ^ (k + 1) < n % p ^ (k + 1)}) :
    ‖c‖ < 1 := by
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := Nat.exists_eq_add_one.mpr <|
    Nat.pos_of_ne_zero fun h0 ↦ by simp [h0, Nat.mod_one] at ha
  rw [hc]
  exact pow_lt_one₀ (norm_nonneg _) (mem_nonunits.mp p_nonunit)
    (Finset.card_ne_zero.mpr ⟨h, by simpa using ha⟩)

/-- **Amice's polynomials modulo `p`: vanishing on earlier discs.** If `a mod pʰ < n mod pʰ`,
every coefficient of `⌊n / pʰ⌋! (a + pʰ w choose n)` as a polynomial in `w` lies in `pℤ_p`. -/
theorem norm_coeff_amicePolynomial_lt_one_of_mod_lt {h n a : ℕ} (ha : a % p ^ h < n % p ^ h)
    (j : ℕ) : ‖(amicePolynomial p h n a).coeff j‖ < 1 := by
  obtain ⟨c, F, hA, -, -, hc⟩ := exists_amicePolynomial_eq_C_mul (p := p) h n a
  rw [hA, coeff_C_mul, mul_comm]
  exact norm_lt_one_mul (norm_lt_one_of_mod_lt ha hc)

/-- **Amice's polynomials modulo `p`: degree bound.** On every disc `a + pʰℤ_p`, the coefficients
of `wʲ` in `⌊n / pʰ⌋! (a + pʰ w choose n)` with `j > ⌊n / pʰ⌋` lie in `pℤ_p`: modulo `p`, Amice's
polynomial has degree at most `⌊n / pʰ⌋`. -/
theorem norm_coeff_amicePolynomial_lt_one_of_div_lt {h n j : ℕ} (a : ℕ) (hj : n / p ^ h < j) :
    ‖(amicePolynomial p h n a).coeff j‖ < 1 := by
  by_cases ha : a % p ^ h < n % p ^ h
  · exact norm_coeff_amicePolynomial_lt_one_of_mod_lt ha j
  obtain ⟨c, F, hA, -, hhigh, -⟩ := exists_amicePolynomial_eq_C_mul (p := p) h n a
  rw [hA, coeff_C_mul]
  exact norm_lt_one_mul (hhigh j (by rwa [ite_eq_right ha, add_zero]))

/-- **Amice's polynomials modulo `p`: the coefficient of `w ^ ⌊n / pʰ⌋`.** If
`n mod pʰ ≤ a mod pʰ`, the coefficient of `w ^ ⌊n / pʰ⌋` in `⌊n / pʰ⌋! (a + pʰ w choose n)` has
norm `‖p‖ ^ e`, where `e` is the number of `k ∈ [1, h]` with `a mod pᵏ < n mod pᵏ`. -/
theorem norm_coeff_amicePolynomial_div_of_mod_le {h n a : ℕ} (ha : n % p ^ h ≤ a % p ^ h) :
    ‖(amicePolynomial p h n a).coeff (n / p ^ h)‖ =
      ‖(p : ℤ_[p])‖ ^ #{k ∈ Finset.range h | a % p ^ (k + 1) < n % p ^ (k + 1)} := by
  obtain ⟨c, F, hA, hlead, -, hc⟩ := exists_amicePolynomial_eq_C_mul (p := p) h n a
  rw [ite_eq_right ha.not_gt, add_zero] at hlead
  rw [hA, coeff_C_mul, norm_mul, hc, hlead, mul_one]

/-- **Amice's polynomials modulo `p`: the diagonal coefficient.** On the disc of `n mod pʰ`, the
coefficient of `w ^ ⌊n / pʰ⌋` in `⌊n / pʰ⌋! (n mod pʰ + pʰ w choose n)` is a unit of `ℤ_p`. -/
@[simp]
theorem norm_coeff_amicePolynomial_mod_div (h n : ℕ) :
    ‖(amicePolynomial p h n (n % p ^ h : ℕ)).coeff (n / p ^ h)‖ = 1 := by
  rw [norm_coeff_amicePolynomial_div_of_mod_le (Nat.mod_mod _ _).ge,
    Finset.filter_eq_empty_iff.mpr fun k hk ↦ ?_, Finset.card_empty, pow_zero]
  rw [Nat.mod_mod_of_dvd n (pow_dvd_pow p (Finset.mem_range.mp hk))]
  exact lt_irrefl _

end Reduction

/-! ### Amice's vectors in the analytic stages -/

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]

/-- The coefficients of `e_{h,n} • e` vanish outside the finitely many indices of degree `≤ n`. -/
private theorem tendsto_amiceCoeff (n : ℕ) (e : E) :
    Tendsto (fun i : ZMod (p ^ h) × ℕ ↦ (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • e)
      cofinite (𝓝 0) := by
  have hfin : {i : ZMod (p ^ h) × ℕ | i.2 ≤ n}.Finite :=
    (Set.finite_univ.prod (Set.finite_Iic n)).subset fun i hi ↦ by simpa using hi
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hfin.compl_mem_cofinite] with i hi
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hi
  simp [coeff_amicePolynomial_eq_zero _ hi]

variable (p h) in
/-- **Amice's vector** `e_{h,n} • e` in `LA_h(E)`: on the disc of `a ∈ ZMod (pʰ)` its coefficient
of `wᵏ` is the `k`-th coefficient of `amicePolynomial p h n a.val`, times `e`. -/
noncomputable def amiceTerm (n : ℕ) (e : E) : AnalyticStage p h E :=
  ZeroAtInftyContinuousMap.mkOfDiscrete _ (tendsto_amiceCoeff n e)

/-- The coefficients of Amice's vector `e_{h,n} • e`. -/
@[simp]
theorem amiceTerm_apply (n : ℕ) (e : E) (i : ZMod (p ^ h) × ℕ) :
    amiceTerm p h n e i = (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • e :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ (tendsto_amiceCoeff n e)) i

/-- Amice's vector of `0` is `0`. -/
@[simp]
theorem amiceTerm_zero (n : ℕ) : amiceTerm p h n (0 : E) = 0 := by
  ext i
  simp

/-- Amice's vector `e_{h,n} • e` is additive in `e`. -/
theorem amiceTerm_add (n : ℕ) (e f : E) :
    amiceTerm p h n (e + f) = amiceTerm p h n e + amiceTerm p h n f := by
  ext i
  simp [smul_add]

section Scalars

variable {S : Type*} [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Amice's vector `e_{h,n} • e` commutes with scalars acting on `E` compatibly with `ℤ_p`. -/
theorem amiceTerm_smul (n : ℕ) (s : S) (e : E) :
    amiceTerm p h n (s • e) = s • amiceTerm p h n e := by
  ext i
  simp [smul_comm _ s]

end Scalars

variable [IsBoundedSMul ℤ_[p] E]

/-- Amice's vectors have norm at most `‖e‖`: their coefficients are integral multiples of `e`. -/
theorem norm_amiceTerm_le (n : ℕ) (e : E) : ‖amiceTerm p h n e‖ ≤ ‖e‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg e)).mpr fun i ↦ by
    rw [amiceTerm_apply]
    exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg e) (PadicInt.norm_le_one _))

variable [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Amice's vector `e_{h,n} • e` evaluates to the Mahler term `x ↦ (x choose n) • ⌊n / pʰ⌋! • e`.
-/
@[simp]
theorem eval_amiceTerm (n : ℕ) (e : E) :
    eval S (amiceTerm p h n e) = PadicInt.mahlerTerm ((n / p ^ h)! • e) n := by
  ext x
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  rw [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul,
    tsum_eq_sum (s := Finset.range (n + 1)) fun k hk ↦ by
      simp [coeff_amicePolynomial_eq_zero _ (by simpa using hk : n < k)]]
  simp [smul_smul, ← Finset.sum_smul, mul_comm (w ^ _), sum_range_coeff_amicePolynomial_mul_pow,
    PadicInt.mahlerTerm_apply, mahler_apply, mul_comm (Ring.choose _ _),
    ← Nat.cast_smul_eq_nsmul ℤ_[p]]

private theorem summable_amiceTerm (c : C₀(ℕ, E)) : Summable fun n ↦ amiceTerm p h n (c n) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    squeeze_zero_norm (fun n ↦ norm_amiceTerm_le n (c n))
      (tendsto_zero_iff_norm_tendsto_zero.mp c.tendsto_cofinite)

omit [CompleteSpace E] in
private theorem norm_tsum_amiceTerm_le (c : C₀(ℕ, E)) : ‖∑' n, amiceTerm p h n (c n)‖ ≤ ‖c‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg c) fun n ↦
    (norm_amiceTerm_le n (c n)).trans (c.norm_coe_le_norm n)

variable (p h) in
/-- **Amice's map** `C₀(ℕ, E) → LA_h(E)`, `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`, sending a null sequence to
the expansion on the discs of level `h` of the series of Amice's polynomials
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)` with coefficients `cₙ`. -/
noncomputable def amiceMap : C₀(ℕ, E) →L[S] AnalyticStage p h E :=
  let L : C₀(ℕ, E) →ₗ[S] AnalyticStage p h E :=
    { toFun c := ∑' n, amiceTerm p h n (c n)
      map_add' c d := by
        simp only [FunLike.coe_add, Pi.add_apply, amiceTerm_add]
        exact (summable_amiceTerm c).tsum_add (summable_amiceTerm d)
      map_smul' s c := by
        simp only [FunLike.coe_smul, Pi.smul_apply, amiceTerm_smul,
          RingHom.id_apply]
        exact (summable_amiceTerm c).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      exact norm_tsum_amiceTerm_le c }

/-- Amice's map is the sum of Amice's vectors `e_{h,n} • cₙ`. -/
theorem hasSum_amiceMap (c : C₀(ℕ, E)) :
    HasSum (fun n ↦ amiceTerm p h n (c n)) (amiceMap p h S c) :=
  (summable_amiceTerm c).hasSum

/-- The coordinates of Amice's map: on the disc of `a`, the coefficient of `wᵏ` in `amiceMap c` is
the sum over `n` of the `k`-th coefficient of `amicePolynomial p h n a.val`, times `cₙ`. -/
theorem hasSum_amiceMap_apply (c : C₀(ℕ, E)) (i : ZMod (p ^ h) × ℕ) :
    HasSum (fun n ↦ (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • c n)
      (amiceMap p h S c i) := by
  simpa using (hasSum_amiceMap S c).mapL (ZeroAtInftyContinuousMap.evalCLM ℤ_[p] i)

/-- The coefficient of `wᵏ` on the disc of `a` in `amiceMap c`. -/
theorem amiceMap_apply (c : C₀(ℕ, E)) (i : ZMod (p ^ h) × ℕ) :
    amiceMap p h S c i = ∑' n, (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • c n :=
  (hasSum_amiceMap_apply S c i).tsum_eq.symm

/-- Amice's map sends the coordinate vector `single n e` to Amice's vector `e_{h,n} • e`. -/
@[simp]
theorem amiceMap_single (n : ℕ) (e : E) :
    amiceMap p h S (ZeroAtInftyContinuousMap.single n e) = amiceTerm p h n e := by
  classical
  refine (hasSum_amiceMap S _).unique ?_
  convert hasSum_single n (f := fun m ↦ amiceTerm p h m (ZeroAtInftyContinuousMap.single n e m))
    fun m hm ↦ by simp [ZeroAtInftyContinuousMap.single_eq_of_ne hm]
  simp

/-- Amice's map does not increase norms. -/
theorem norm_amiceMap_le (c : C₀(ℕ, E)) : ‖amiceMap p h S c‖ ≤ ‖c‖ :=
  norm_tsum_amiceTerm_le c

/-- Amice's map followed by evaluation is the Mahler series `x ↦ ∑ₙ (x choose n) • ⌊n / pʰ⌋! • cₙ`.
-/
theorem eval_amiceMap (c : C₀(ℕ, E)) :
    eval S (amiceMap p h S c) = PadicInt.mahlerSeries fun n ↦ (n / p ^ h)! • c n := by
  rw [PadicInt.mahlerSeries, ← ((hasSum_amiceMap S c).mapL (eval S)).tsum_eq]
  simp

end AnalyticStage

end TauCeti
