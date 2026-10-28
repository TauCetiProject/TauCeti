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
import TauCeti.Data.Nat.Choose.Lucas
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

Modulo `p` these disc expansions are explicit
(`TauCeti.map_toZMod_amicePolynomial`). Write `n = pʰ k + j` with `j < pʰ`, so `m_h(n) = k!`, and
let `a < pʰ`. Then on the disc `a + pʰℤ_p` the polynomial `e_{h,n}` reduces to
`(a choose j) (w)ₖ`, where `(w)ₖ = w (w - 1) ⋯ (w - k + 1)`. When `j ≤ a`, the factors of
`∏_{i < n} (a - i + pʰ w)` with `i ≡ a mod pʰ` are `pʰ (w - t)`, `t < k`, and every other factor
is `(a - i)` times a polynomial congruent to `1`; evaluating at `w = k` and Lucas' theorem in base
`pʰ` identify the constant. When `a < j`, there are `k + 1` indices `i ≡ a mod pʰ` below `n`, and
the count above gives one extra factor of `p`. Thus, modulo `p`, the vectors `e_{h,n}` with
`n` in the block `pʰ k ≤ n < pʰ (k + 1)` have degree at most `k` on every disc, and their
coefficients of degree `k` form the matrix `(a choose j)`, which is unitriangular. This is the
reduction step of Amice's theorem.

By integrality, `e_{h,n}` has an expansion in `LA_h(ℤ_p)`, and more generally `e_{h,n} • e` has
one in `LA_h(E)` for every normed `ℤ_p`-module `E`, of norm at most `‖e‖` when the action is
contractive. For complete ultrametric `E`, summing these vectors gives a continuous linear map

`TauCeti.AnalyticStage.amiceMap : C₀(ℕ, E) → LA_h(E)`,  `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`,

which does not increase norms. Followed by evaluation, it is the Mahler series with
coefficients `m_h(n) • cₙ` (`TauCeti.AnalyticStage.eval_amiceMap`). Amice's theorem, which is not
proved here, asserts that `amiceMap` is an isometric isomorphism.

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
* `TauCeti.map_toZMod_amicePolynomial`: modulo `p`, the expansion of `e_{h,n}` on the disc of `a`
  is `(a choose (n % pʰ)) (w)_{⌊n / pʰ⌋}`.
* `TauCeti.AnalyticStage.eval_amiceTerm`: `amiceTerm` evaluates to the Mahler term of
  `m_h(n) • e`.
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
/-- The product `∏_{i < n} (a - i + pʰ X)` is divisible by `p ^ e`, where `e` counts the pairs
`(k, i)` with `k < h`, `i < n` and `pᵏ⁺¹ ∣ a - i`. -/
private theorem C_pow_sum_card_dvd_discProd (h n : ℕ) (a : ℤ_[p]) :
    C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h,
        #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])}) ∣
      discProd h n a := by
  -- `d i = min(v_p(a - i), h)`, the largest `k ≤ h` with `pᵏ ∣ a - i`.
  set d : ℕ → ℕ := fun i ↦ Nat.findGreatest (fun k ↦ (p : ℤ_[p]) ^ k ∣ a - i) h
  have hd_le (i : ℕ) : d i ≤ h := Nat.findGreatest_le h
  have hd_dvd (i : ℕ) : (p : ℤ_[p]) ^ d i ∣ a - i :=
    Nat.findGreatest_spec (P := fun k ↦ (p : ℤ_[p]) ^ k ∣ a - i) (zero_le h) (by simp)
  have hfac (i : ℕ) : C ((p : ℤ_[p]) ^ d i) ∣ C (a - i) + C ((p : ℤ_[p]) ^ h) * X := by
    obtain ⟨s, hs⟩ := hd_dvd i
    refine ⟨C s + C ((p : ℤ_[p]) ^ (h - d i)) * X, ?_⟩
    rw [hs, mul_add, ← mul_assoc, ← C_mul, ← C_mul, ← pow_add, Nat.add_sub_cancel' (hd_le i)]
  -- Count the pairs `(k, i)` with `pᵏ⁺¹ ∣ a - i` in two ways.
  have hsum : ∑ k ∈ Finset.range h,
      #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])} ≤
        ∑ i ∈ Finset.range n, d i :=
    calc ∑ k ∈ Finset.range h,
          #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])}
        = ∑ i ∈ Finset.range n, #{k ∈ Finset.range h | (p : ℤ_[p]) ^ (k + 1) ∣ a - i} := by
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ ∑ i ∈ Finset.range n, d i := Finset.sum_le_sum fun i _ ↦ by
          calc #{k ∈ Finset.range h | (p : ℤ_[p]) ^ (k + 1) ∣ a - i}
              ≤ #(Finset.range (d i)) := Finset.card_le_card fun k hk ↦ by
                simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
                exact Nat.le_findGreatest (P := fun k ↦ (p : ℤ_[p]) ^ k ∣ a - i) hk.1 hk.2
            _ = d i := Finset.card_range _
  calc _ ∣ C ((p : ℤ_[p]) ^ ∑ i ∈ Finset.range n, d i) := _root_.map_dvd C (pow_dvd_pow _ hsum)
    _ = ∏ i ∈ Finset.range n, C ((p : ℤ_[p]) ^ d i) := by
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    _ ∣ discProd h n a := Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ hfac i

/-- The product `∏_{i < n} (a - i + pʰ X)` is divisible by `p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`: at least
`⌊n / pᵏ⌋` of the `n` consecutive elements `a - i` are divisible by `pᵏ`. -/
private theorem C_pow_dvd_discProd (h n : ℕ) (a : ℤ_[p]) :
    C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1)) ∣ discProd h n a := by
  classical
  exact (_root_.map_dvd C (pow_dvd_pow _ (Finset.sum_le_sum fun k _ ↦
    a.div_pow_le_card_filter_dvd n (k + 1)))).trans (C_pow_sum_card_dvd_discProd h n a)

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

/-! ### Reduction modulo `p` -/

/-- `n! · amicePolynomial p h n a = ⌊n / pʰ⌋! · ∏_{i < n} (a - i + pʰ X)`. -/
private theorem C_mul_amicePolynomial (h n : ℕ) (a : ℤ_[p]) :
    C (n ! : ℤ_[p]) * amicePolynomial p h n a = C ((n / p ^ h)! : ℤ_[p]) * discProd h n a :=
  Polynomial.funext fun w ↦ by
    simp only [eval_mul, eval_C, eval_amicePolynomial, eval_discProd]
    ring

private theorem C_natCast_factorial_ne_zero (n : ℕ) : C (n ! : ℤ_[p]) ≠ 0 :=
  C_ne_zero.mpr (Nat.cast_ne_zero.mpr (factorial_ne_zero n))

private theorem pow_mul_add_div_pow {h j : ℕ} (k : ℕ) (hj : j < p ^ h) :
    (p ^ h * k + j) / p ^ h = k := by
  rw [Nat.mul_add_div (pow_pos hp.out.pos h), Nat.div_eq_of_lt hj, add_zero]

/-- If `a < j < pʰ`, then `p` divides `amicePolynomial p h (pʰ k + j) a`: the `k + 1` indices
`i = a + pʰ t`, `t ≤ k`, below `pʰ k + j` all have `pʰ ∣ a - i`, one more than the
`⌊(pʰ k + j) / pʰ⌋ = k` used for integrality. -/
private theorem C_dvd_amicePolynomial_of_lt {h k a j : ℕ} (haj : a < j) (hj : j < p ^ h) :
    C (p : ℤ_[p]) ∣ amicePolynomial p h (p ^ h * k + j) a := by
  classical
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hj; omega)
  set n := p ^ (h + 1) * k + j
  have hP : 0 < p ^ (h + 1) := pow_pos hp.out.pos _
  have hcount : k + 1 ≤
      #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (h + 1) ∣ (a : ℤ_[p]) - ((i : ℕ) : ℤ_[p])} := by
    calc k + 1 = #(Finset.range (k + 1)) := (Finset.card_range _).symm
      _ ≤ _ := Finset.card_le_card_of_injOn (fun t ↦ a + p ^ (h + 1) * t) (fun t ht ↦ ?_)
          (fun s _ t _ hst ↦ ?_)
    · simp only [Finset.coe_range, Set.mem_Iio] at ht
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      have := Nat.mul_le_mul_left (p ^ (h + 1)) (Nat.lt_succ_iff.mp ht)
      refine ⟨by omega, ⟨-(t : ℤ_[p]), ?_⟩⟩
      push_cast
      ring
    · simpa [hp.out.ne_zero] using hst
  have hsum : ∑ s ∈ Finset.range (h + 1), n / p ^ (s + 1) + 1 ≤ ∑ s ∈ Finset.range (h + 1),
      #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (s + 1) ∣ (a : ℤ_[p]) - ((i : ℕ) : ℤ_[p])} := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_mul_add_div_pow k hj]
    have := Finset.sum_le_sum fun s (_ : s ∈ Finset.range h) ↦
      (a : ℤ_[p]).div_pow_le_card_filter_dvd n (s + 1)
    omega
  refine (mul_dvd_mul_iff_left (C_natCast_factorial_ne_zero n)).mp ?_
  rw [C_mul_amicePolynomial, pow_mul_add_div_pow k hj]
  calc C (n ! : ℤ_[p]) * C (p : ℤ_[p])
      ∣ C ((k ! : ℤ_[p]) * (p : ℤ_[p]) ^ ∑ s ∈ Finset.range (h + 1), n / p ^ (s + 1)) *
          C (p : ℤ_[p]) := by
        refine mul_dvd_mul_right (_root_.map_dvd C ?_) _
        simpa only [n, pow_mul_add_div_pow k hj] using
          factorial_dvd_factorial_div_mul_pow (p := p) (h + 1) n
    _ = C (k ! : ℤ_[p]) *
          C ((p : ℤ_[p]) ^ (∑ s ∈ Finset.range (h + 1), n / p ^ (s + 1) + 1)) := by
        rw [pow_succ, C_mul, C_mul, mul_assoc]
    _ ∣ C (k ! : ℤ_[p]) * discProd (h + 1) n a :=
        mul_dvd_mul_left _ ((_root_.map_dvd C (pow_dvd_pow _ hsum)).trans
          (C_pow_sum_card_dvd_discProd (h + 1) n a))

/-- If `i ≢ a mod pʰ`, where `a < pʰ`, then `v_p(a - i) < h`, so `(a - i) q = pʰ` for some `q`
divisible by `p`. -/
private theorem exists_natCast_sub_mul_eq_pow {h a i : ℕ} (ha : a < p ^ h) (hi : i % p ^ h ≠ a) :
    ∃ q : ℤ_[p], ((a : ℤ_[p]) - i) * q = (p : ℤ_[p]) ^ h ∧ PadicInt.toZMod q = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 ↦ hi (by
      subst h0
      rw [pow_zero, Nat.lt_one_iff] at ha
      rw [pow_zero, Nat.mod_one, ha])
  have hcast : (a : ℤ_[p]) - i = ((a - i : ℤ) : ℤ_[p]) := by push_cast; ring
  have hx : ¬(p : ℤ_[p]) ^ (m + 1) ∣ (a : ℤ_[p]) - i := by
    rw [hcast, PadicInt.pow_p_dvd_int_iff]
    intro hd
    exact hi (Eq.trans (Nat.modEq_iff_dvd.mpr (by exact_mod_cast hd) : i ≡ a [MOD p ^ (m + 1)])
      (Nat.mod_eq_of_lt ha))
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, not_lt] at hx
  obtain ⟨r, hr⟩ : (a : ℤ_[p]) - i ∣ (p : ℤ_[p]) ^ m :=
    PadicInt.dvd_of_norm_le (by
      rw [PadicInt.norm_p_pow]
      convert hx using 2
      push_cast
      ring)
  exact ⟨r * p, by rw [← mul_assoc, ← hr, pow_succ], by simp⟩

/-- If `j ≤ a < pʰ`, the indices `i < pʰ k + j` with `i ≡ a mod pʰ` are `a + pʰ t` for `t < k`, so
the corresponding factors `a - i + pʰ X = pʰ (X - t)` of `∏_{i < pʰ k + j} (a - i + pʰ X)` have
product `pʰᵏ (X)ₖ`, where `(X)ₖ = X (X - 1) ⋯ (X - k + 1)`. -/
private theorem prod_filter_mod_eq_C_add_C_mul_X {h k a j : ℕ} (ha : a < p ^ h) (hja : j ≤ a) :
    ∏ i ∈ Finset.range (p ^ h * k + j) with i % p ^ h = a,
      (C ((a : ℤ_[p]) - i) + C ((p : ℤ_[p]) ^ h) * X) =
        C ((p : ℤ_[p]) ^ h) ^ k * descPochhammer ℤ_[p] k := by
  have hP : 0 < p ^ h := pow_pos hp.out.pos h
  calc _ = ∏ t ∈ Finset.range k, C ((p : ℤ_[p]) ^ h) * (X - C (t : ℤ_[p])) := by
        refine Finset.prod_nbij' (fun i ↦ i / p ^ h) (fun t ↦ a + p ^ h * t) (fun i hi ↦ ?_)
          (fun t ht ↦ ?_) (fun i hi ↦ ?_) (fun t _ ↦ ?_) (fun i hi ↦ ?_)
        · simp only [Finset.mem_filter, Finset.mem_range] at hi
          have := Nat.mod_add_div i (p ^ h)
          simp only [Finset.mem_range]
          exact (Nat.mul_lt_mul_left hP).mp (by omega)
        · simp only [Finset.mem_range] at ht
          simp only [Finset.mem_filter, Finset.mem_range]
          have := Nat.mul_le_mul_left (p ^ h) (Nat.succ_le_of_lt ht)
          rw [Nat.mul_succ] at this
          refine ⟨by omega, ?_⟩
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
        · simp only [Finset.mem_filter, Finset.mem_range] at hi
          simpa [hi.2] using Nat.mod_add_div i (p ^ h)
        · simp [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt ha]
        · simp only [Finset.mem_filter, Finset.mem_range] at hi
          have hi' : (i : ℤ_[p]) = a + (p : ℤ_[p]) ^ h * (i / p ^ h : ℕ) := by
            exact_mod_cast (hi.2 ▸ Nat.mod_add_div i (p ^ h)).symm
          rw [hi']
          simp only [map_sub, map_add, map_mul, map_pow, map_natCast]
          ring
    _ = C ((p : ℤ_[p]) ^ h) ^ k * descPochhammer ℤ_[p] k := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        congr 1
        exact Polynomial.funext fun w ↦ by
          simp [eval_prod, descPochhammer_eval_eq_prod_range]

/-- If `j ≤ a < pʰ`, then `∏_{i < pʰ k + j} (a - i + pʰ X) = c · (X)ₖ · U` for some `c ∈ ℤ_p` and
some `U` congruent to `1` modulo `p`, where `(X)ₖ = X (X - 1) ⋯ (X - k + 1)`. The factors with
`i ≡ a mod pʰ` give `pʰᵏ (X)ₖ`; each other factor is `(a - i) (1 + q X)` with `p ∣ q`. -/
private theorem exists_discProd_eq_C_mul_descPochhammer_mul {h k a j : ℕ} (ha : a < p ^ h)
    (hja : j ≤ a) : ∃ (c : ℤ_[p]) (U : ℤ_[p][X]),
      discProd h (p ^ h * k + j) a = C c * descPochhammer ℤ_[p] k * U ∧
        U.map PadicInt.toZMod = 1 := by
  classical
  choose! q hq using fun i (hi : i % p ^ h ≠ a) ↦ exists_natCast_sub_mul_eq_pow ha hi
  set s := {i ∈ Finset.range (p ^ h * k + j) | ¬i % p ^ h = a}
  have hoff : ∏ i ∈ s, (C ((a : ℤ_[p]) - i) + C ((p : ℤ_[p]) ^ h) * X) =
      C (∏ i ∈ s, ((a : ℤ_[p]) - i)) * ∏ i ∈ s, (1 + C (q i) * X) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul, (hq i (Finset.mem_filter.mp hi).2).1]
  refine ⟨((p : ℤ_[p]) ^ h) ^ k * ∏ i ∈ s, ((a : ℤ_[p]) - i), ∏ i ∈ s, (1 + C (q i) * X), ?_, ?_⟩
  · rw [discProd, ← Finset.prod_filter_mul_prod_filter_not _ (· % p ^ h = a),
      prod_filter_mod_eq_C_add_C_mul_X ha hja, hoff, C_mul, map_pow C ((p : ℤ_[p]) ^ h) k]
    ring
  · rw [Polynomial.map_prod]
    exact Finset.prod_eq_one fun i hi ↦ by simp [(hq i (Finset.mem_filter.mp hi).2).2]

/-- The reduction of Amice's polynomials modulo `p`, for `n = pʰ k + j` with `j < pʰ`. -/
private theorem map_toZMod_amicePolynomial_pow_mul_add (k : ℕ) {h a j : ℕ} (ha : a < p ^ h)
    (hj : j < p ^ h) :
    (amicePolynomial p h (p ^ h * k + j) a).map PadicInt.toZMod =
      C (a.choose j : ZMod p) * descPochhammer (ZMod p) k := by
  rcases lt_or_ge a j with haj | hja
  · obtain ⟨Q, hQ⟩ := C_dvd_amicePolynomial_of_lt (k := k) haj hj
    simp [hQ, Nat.choose_eq_zero_of_lt haj]
  obtain ⟨c, U, hdisc, hU⟩ := exists_discProd_eq_C_mul_descPochhammer_mul (k := k) ha hja
  -- Lucas' theorem in base `pʰ`: `(pʰ k + a choose pʰ k + j) ≡ (a choose j) mod p`.
  have hL := Choose.choose_pow_mul_add_modEq_choose_mul_choose_nat (m := k) (l := k) ha hj
  rw [Nat.choose_self, one_mul] at hL
  set n := p ^ h * k + j
  have hdiv : n / p ^ h = k := pow_mul_add_div_pow k hj
  have hn : C (n ! : ℤ_[p]) * amicePolynomial p h n a =
      C ((k ! : ℤ_[p]) * c) * descPochhammer ℤ_[p] k * U := by
    rw [C_mul_amicePolynomial, hdiv, hdisc, C_mul]
    ring
  -- Evaluating at `w = k`, where `(w)ₖ = k!`, determines the constant `k! c`.
  have hchoose : Ring.choose ((a : ℤ_[p]) + (p : ℤ_[p]) ^ h * k) n =
      ((p ^ h * k + a).choose n : ℤ_[p]) := by
    rw [← Ring.choose_natCast]
    push_cast
    ring_nf
  have hc : (n ! : ℤ_[p]) * ((p ^ h * k + a).choose n : ℤ_[p]) =
      (k ! : ℤ_[p]) * c * U.eval (k : ℤ_[p]) := by
    have heval := congrArg (eval (k : ℤ_[p])) hn
    simp only [eval_mul, eval_C, eval_amicePolynomial, hdiv, hchoose,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self] at heval
    refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr (factorial_ne_zero k)) ?_
    linear_combination heval
  have key : amicePolynomial p h n a * C (U.eval (k : ℤ_[p])) =
      C ((p ^ h * k + a).choose n : ℤ_[p]) * descPochhammer ℤ_[p] k * U := by
    refine mul_left_cancel₀ (C_natCast_factorial_ne_zero n) ?_
    calc C (n ! : ℤ_[p]) * (amicePolynomial p h n a * C (U.eval (k : ℤ_[p])))
        = C ((k ! : ℤ_[p]) * c * U.eval (k : ℤ_[p])) * descPochhammer ℤ_[p] k * U := by
          rw [← mul_assoc, hn]
          simp only [C_mul]
          ring
      _ = _ := by
          rw [← hc, C_mul]
          ring
  -- Reduce modulo `p`: `U ≡ 1`, and Lucas' theorem computes the binomial coefficient.
  have hUk : PadicInt.toZMod (U.eval (k : ℤ_[p])) = 1 := by
    rw [← eval_natCast_map, hU, eval_one]
  have hmap := congrArg (Polynomial.map PadicInt.toZMod) key
  simpa [hU, hUk, CharP.natCast_eq_natCast' (ZMod p)[X] p hL, descPochhammer_map] using hmap

/-- **Reduction of Amice's polynomials modulo `p`.** Let `a < pʰ` be the natural representative of
a disc, and write `n = pʰ k + j` with `j < pʰ`. Modulo `p`, the expansion of
`e_{h,n}(x) = k! (x choose n)` on the disc `a + pʰℤ_p` is `(a choose j) (w)ₖ`, where
`(w)ₖ = w (w - 1) ⋯ (w - k + 1)` is the falling factorial. In particular it has degree at most `k`
modulo `p`, and vanishes modulo `p` when `a < j`. -/
theorem map_toZMod_amicePolynomial (h n : ℕ) {a : ℕ} (ha : a < p ^ h) :
    (amicePolynomial p h n a).map PadicInt.toZMod =
      C (a.choose (n % p ^ h) : ZMod p) * descPochhammer (ZMod p) (n / p ^ h) := by
  conv_lhs => rw [← Nat.div_add_mod n (p ^ h)]
  exact map_toZMod_amicePolynomial_pow_mul_add _ ha (Nat.mod_lt _ (pow_pos hp.out.pos h))

end Integrality

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
        simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, amiceTerm_add]
        exact (summable_amiceTerm c).tsum_add (summable_amiceTerm d)
      map_smul' s c := by
        simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, amiceTerm_smul,
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
