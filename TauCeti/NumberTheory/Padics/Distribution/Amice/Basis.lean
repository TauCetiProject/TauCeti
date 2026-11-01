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

Modulo `p` these expansions are nearly triangular. Write `n = pʰ q + r` with `r < pʰ`, and let
`a < pʰ` be a natural centre. The factors of index `i ≡ a (mod pʰ)` are `pʰ (w - ⌊i / pʰ⌋)`,
while the others are `(a - i)` times a polynomial congruent to `1` modulo `p`. Hence, for
`a ≥ r`, the expansion of `e_{h,n}` is congruent modulo `p` to a multiple of
`w (w - 1) ⋯ (w - q + 1)`, and its coefficients above degree `q` are divisible by `p`. For
`a < r` there are `q + 1` indices `i < n` with `i ≡ a (mod pʰ)`, which raises the exponent of `p`
in the product by one, and every coefficient is divisible by `p`. For `a = r`, evaluating at
`w = q` shows that the coefficient of `w ^ q` is a unit.

Hence `e_{h,n}` has an expansion in `LA_h(ℤ_p)`, and more generally `e_{h,n} • e` has one in
`LA_h(E)` for every normed `ℤ_p`-module `E`, of norm at most `‖e‖` when the action is
contractive. For complete ultrametric `E`, summing these vectors gives a continuous linear map

`TauCeti.AnalyticStage.amiceMap : C₀(ℕ, E) → LA_h(E)`,  `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`,

which does not increase norms. Followed by evaluation, it is the Mahler series with
coefficients `m_h(n) • cₙ` (`TauCeti.AnalyticStage.eval_amiceMap`). Amice's theorem, that
`amiceMap` is an isometric isomorphism, is `TauCeti.AnalyticStage.amiceEquiv` in
`TauCeti.NumberTheory.Padics.Distribution.Amice.Isometry`; it follows from the congruences above.

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
* `TauCeti.dvd_coeff_amicePolynomial_of_div_lt`, `TauCeti.dvd_coeff_amicePolynomial_of_lt_mod`,
  `TauCeti.isUnit_coeff_amicePolynomial_mod`: the congruences modulo `p` of the expansions.
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
/-- The product `∏_{i < n} (a - i + pʰ X)` is divisible by `p ^ (∑_{k = 1}^{h} cₖ)`, where `cₖ` is
the number of `i < n` with `pᵏ ∣ a - i`. -/
private theorem C_pow_sum_card_dvd_discProd (h n : ℕ) (a : ℤ_[p]) :
    C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h,
      #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])}) ∣ discProd h n a := by
  classical
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
  calc C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h,
        #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ a - ((i : ℕ) : ℤ_[p])})
      ∣ C ((p : ℤ_[p]) ^ ∑ i ∈ Finset.range n, d i) := _root_.map_dvd C (pow_dvd_pow _ hsum)
    _ = ∏ i ∈ Finset.range n, C ((p : ℤ_[p]) ^ d i) := by
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    _ ∣ discProd h n a := Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ hfac i

/-- The product `∏_{i < n} (a - i + pʰ X)` is divisible by `p ^ (∑_{k = 1}^{h} ⌊n / pᵏ⌋)`: among
`n` consecutive integers at least `⌊n / pᵏ⌋` are congruent to `a` modulo `pᵏ`. -/
private theorem C_pow_dvd_discProd (h n : ℕ) (a : ℤ_[p]) :
    C ((p : ℤ_[p]) ^ ∑ k ∈ Finset.range h, n / p ^ (k + 1)) ∣ discProd h n a :=
  (_root_.map_dvd C (pow_dvd_pow _ (Finset.sum_le_sum fun k _ ↦
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

end Integrality

/-! ### Reduction modulo `p` -/

section Reduction

/-- Amice's polynomial times `n!` is `⌊n / pʰ⌋!` times the product `∏_{i < n} (a - i + pʰ X)`. -/
private theorem C_mul_amicePolynomial (h n : ℕ) (a : ℤ_[p]) :
    C (n ! : ℤ_[p]) * amicePolynomial p h n a = C ((n / p ^ h)! : ℤ_[p]) * discProd h n a :=
  Polynomial.funext fun w ↦ by
    simp only [eval_mul, eval_C, eval_amicePolynomial, eval_discProd]
    ring

/-- If `i ≢ a (mod pʰ)` with `a < pʰ`, then `v_p(a - i) < h`, so `(a - i) p` divides `pʰ`. -/
private theorem exists_pow_eq_natCast_sub_mul {h a i : ℕ} (ha : a < p ^ h) (hi : i % p ^ h ≠ a) :
    ∃ t : ℤ_[p], (p : ℤ_[p]) ^ h = ((a : ℤ_[p]) - i) * p * t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hx : ¬(p : ℤ_[p]) ^ h ∣ (a : ℤ_[p]) - i := by
    have hcast : (a : ℤ_[p]) - i = (((a : ℤ) - i : ℤ) : ℤ_[p]) := by push_cast; ring
    rwa [hcast, PadicInt.pow_p_dvd_int_iff, ← Nat.cast_pow, ← Nat.modEq_iff_dvd, Nat.ModEq,
      Nat.mod_eq_of_lt ha]
  -- `pʰ ∤ a - i` means `‖a - i‖ ≥ p ^ (1 - h)`.
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, not_lt] at hx
  refine PadicInt.dvd_of_norm_le ?_
  rw [PadicInt.norm_p_pow, norm_mul, PadicInt.norm_p]
  calc (p : ℝ) ^ (-(h : ℤ)) = (p : ℝ) ^ (-(h : ℤ) + 1) * (p : ℝ)⁻¹ := by
        rw [zpow_add_one₀ hp0.ne', mul_inv_cancel_right₀ hp0.ne']
    _ ≤ ‖(a : ℤ_[p]) - i‖ * (p : ℝ)⁻¹ := by gcongr

/-- For `n % pʰ ≤ a < pʰ`, the indices `i < n` with `i ≡ a (mod pʰ)` are the `a + pʰ j` with
`j < ⌊n / pʰ⌋`, and their factors `a - i + pʰ X = pʰ (X - j)` multiply to
`p ^ (h ⌊n / pʰ⌋) ∏_{j < ⌊n / pʰ⌋} (X - j)`. -/
private theorem prod_filter_mod_eq_discFactor {h n a : ℕ} (ha : a < p ^ h)
    (hra : n % p ^ h ≤ a) :
    ∏ i ∈ Finset.range n with i % p ^ h = a, (C ((a : ℤ_[p]) - i) + C ((p : ℤ_[p]) ^ h) * X) =
      C ((p : ℤ_[p]) ^ (h * (n / p ^ h))) * descPochhammer ℤ_[p] (n / p ^ h) := by
  have hP : 0 < p ^ h := pow_pos hp.out.pos h
  have hD (m : ℕ) : descPochhammer ℤ_[p] m = ∏ j ∈ Finset.range m, (X - C (j : ℤ_[p])) := by
    induction m with
    | zero => simp
    | succ m ih => rw [descPochhammer_succ_right, ih, Finset.prod_range_succ, map_natCast]
  calc ∏ i ∈ Finset.range n with i % p ^ h = a, (C ((a : ℤ_[p]) - i) + C ((p : ℤ_[p]) ^ h) * X)
      = ∏ j ∈ Finset.range (n / p ^ h), (C ((p : ℤ_[p]) ^ h) * (X - C (j : ℤ_[p]))) := ?_
    _ = C ((p : ℤ_[p]) ^ (h * (n / p ^ h))) * descPochhammer ℤ_[p] (n / p ^ h) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← map_pow, ← pow_mul, hD]
  refine Finset.prod_nbij' (fun i ↦ i / p ^ h) (fun j ↦ a + p ^ h * j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    by_contra hle
    have h1 := Nat.mul_le_mul_left (p ^ h) (not_lt.1 hle)
    have h2 := Nat.div_add_mod i (p ^ h)
    have h3 := Nat.div_add_mod n (p ^ h)
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨?_, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]⟩
    calc a + p ^ h * j < p ^ h * (j + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ p ^ h * (n / p ^ h) := Nat.mul_le_mul_left _ hj
      _ ≤ n := Nat.mul_div_le n (p ^ h)
  · intro i hi
    simp only [Finset.mem_filter] at hi
    have := Nat.mod_add_div i (p ^ h)
    omega
  · intro j _
    simp [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt ha]
  · intro i hi
    simp only [Finset.mem_filter] at hi
    have hi' : (i : ℤ_[p]) = a + (p : ℤ_[p]) ^ h * ((i / p ^ h : ℕ) : ℤ_[p]) := by
      rw [← hi.2]
      exact_mod_cast (Nat.mod_add_div i (p ^ h)).symm
    rw [hi']
    simp only [map_sub, map_add, map_mul]
    ring

/-- For `n % pʰ ≤ a < pʰ`, the product `∏_{i < n} (a - i + pʰ X)` is `β G ∏_{j < ⌊n / pʰ⌋} (X - j)`
with `G ≡ 1 (mod p)`. The factors with `i ≡ a (mod pʰ)` give `∏_{j < ⌊n / pʰ⌋} (X - j)` up to a
power of `p`, and each other factor is `(a - i) (1 + p t X)` for some `t`. -/
private theorem exists_discProd_eq {h n a : ℕ} (ha : a < p ^ h) (hra : n % p ^ h ≤ a) :
    ∃ (β : ℤ_[p]) (G : ℤ_[p][X]), G.map PadicInt.toZMod = 1 ∧
      discProd h n a = C β * (G * descPochhammer ℤ_[p] (n / p ^ h)) := by
  classical
  choose! t ht using fun i (hi : i % p ^ h ≠ a) ↦ exists_pow_eq_natCast_sub_mul ha hi
  refine ⟨(p : ℤ_[p]) ^ (h * (n / p ^ h)) *
      ∏ i ∈ Finset.range n with ¬i % p ^ h = a, ((a : ℤ_[p]) - i),
    ∏ i ∈ Finset.range n with ¬i % p ^ h = a, (1 + C ((p : ℤ_[p]) * t i) * X), ?_, ?_⟩
  · simp [Polynomial.map_prod]
  have h2 : ∏ i ∈ Finset.range n with ¬i % p ^ h = a,
      (C ((a : ℤ_[p]) - i) + C ((p : ℤ_[p]) ^ h) * X) =
        C (∏ i ∈ Finset.range n with ¬i % p ^ h = a, ((a : ℤ_[p]) - i)) *
          ∏ i ∈ Finset.range n with ¬i % p ^ h = a, (1 + C ((p : ℤ_[p]) * t i) * X) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [ht i (Finset.mem_filter.1 hi).2]
    simp only [map_mul]
    ring
  rw [discProd, ← Finset.prod_filter_mul_prod_filter_not (Finset.range n)
    (fun i ↦ i % p ^ h = a), prod_filter_mod_eq_discFactor ha hra, h2, map_mul]
  ring

/-- If `G ≡ 1 (mod p)`, the coefficient of `X ^ q` in `G ∏_{j < q} (X - j)` is a unit. -/
private theorem isUnit_coeff_mul_descPochhammer {G : ℤ_[p][X]} (hG : G.map PadicInt.toZMod = 1)
    (q : ℕ) : IsUnit ((G * descPochhammer ℤ_[p] q).coeff q) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt ↦ ?_)
  have h0 := (PadicInt.toZMod_eq_zero_iff_dvd _).2 ((PadicInt.norm_lt_one_iff_dvd _).1 hlt)
  have hq := (monic_descPochhammer (ZMod p) q).coeff_natDegree
  rw [descPochhammer_natDegree] at hq
  rw [← coeff_map, Polynomial.map_mul, hG, one_mul, descPochhammer_map, hq] at h0
  exact one_ne_zero h0

/-- For `n % pʰ ≤ a < pʰ`, Amice's polynomial on the disc of centre `a` is
`c G ∏_{j < ⌊n / pʰ⌋} (X - j)` with `G ≡ 1 (mod p)`: modulo `p` it is a multiple of
`∏_{j < ⌊n / pʰ⌋} (X - j)`. -/
private theorem exists_amicePolynomial_eq {h n a : ℕ} (ha : a < p ^ h) (hra : n % p ^ h ≤ a) :
    ∃ (c : ℤ_[p]) (G : ℤ_[p][X]), G.map PadicInt.toZMod = 1 ∧
      amicePolynomial p h n a = C c * (G * descPochhammer ℤ_[p] (n / p ^ h)) := by
  obtain ⟨β, G, hG, hβ⟩ := exists_discProd_eq ha hra
  have key := C_mul_amicePolynomial h n (a : ℤ_[p])
  rw [hβ, ← mul_assoc, ← C_mul] at key
  -- Comparing the coefficients of `X ^ ⌊n / pʰ⌋` shows that `n!` divides `⌊n / pʰ⌋! β`.
  obtain ⟨u, hu⟩ := isUnit_coeff_mul_descPochhammer hG (n / p ^ h)
  have hcoeff := congrArg (coeff · (n / p ^ h)) key
  simp only [coeff_C_mul, ← hu] at hcoeff
  have hn : (n ! : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero n)
  have hc : (n ! : ℤ_[p]) * ((amicePolynomial p h n a).coeff (n / p ^ h) * ↑u⁻¹) =
      (n / p ^ h)! * β := by
    rw [← mul_assoc, hcoeff, Units.mul_inv_cancel_right]
  refine ⟨(amicePolynomial p h n a).coeff (n / p ^ h) * ↑u⁻¹, G, hG,
    mul_left_cancel₀ (C_ne_zero.2 hn) ?_⟩
  rw [key, ← hc, C_mul, mul_assoc]

/-- **Amice's polynomials modulo `p` on the discs below `n % pʰ`.** If `a < n % pʰ`, every
coefficient of `w ↦ ⌊n / pʰ⌋! (a + pʰ w choose n)` is divisible by `p`. -/
theorem dvd_coeff_amicePolynomial_of_lt_mod {h n a : ℕ} (ha : a < n % p ^ h) (j : ℕ) :
    (p : ℤ_[p]) ∣ (amicePolynomial p h n a).coeff j := by
  classical
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 ↦ by
    rw [h0, pow_zero, Nat.mod_one] at ha
    exact Nat.not_lt_zero _ ha
  have hP : 0 < p ^ (h + 1) := pow_pos hp.out.pos _
  -- The `⌊n / pʰ⌋ + 1` integers `a + pʰ j`, `j ≤ ⌊n / pʰ⌋`, are `< n` and `≡ a (mod pʰ)`.
  have hcard : n / p ^ (h + 1) + 1 ≤
      #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (h + 1) ∣ (a : ℤ_[p]) - ((i : ℕ) : ℤ_[p])} := by
    rw [← Finset.card_range (n / p ^ (h + 1) + 1)]
    refine Finset.card_le_card_of_injOn (fun j ↦ a + p ^ (h + 1) * j) ?_ ?_
    · intro j hj
      simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_filter, Finset.mem_range,
        Set.mem_ofPred_eq] at hj ⊢
      refine ⟨?_, ⟨-(j : ℤ_[p]), by push_cast; ring⟩⟩
      have h1 := Nat.mul_le_mul_left (p ^ (h + 1)) (Nat.le_of_lt_succ hj)
      have h2 := Nat.div_add_mod n (p ^ (h + 1))
      omega
    · intro j _ k _ hjk
      exact Nat.eq_of_mul_eq_mul_left hP (by simpa using hjk)
  -- Hence the exponent of `p` dividing `∏_{i < n} (a - i + pʰ X)` exceeds `v_p(n!/⌊n / pʰ⌋!)`.
  have hsum : ∑ k ∈ Finset.range (h + 1), n / p ^ (k + 1) + 1 ≤ ∑ k ∈ Finset.range (h + 1),
      #{i ∈ Finset.range n | (p : ℤ_[p]) ^ (k + 1) ∣ (a : ℤ_[p]) - ((i : ℕ) : ℤ_[p])} := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.range h) ↦
      (a : ℤ_[p]).div_pow_le_card_filter_dvd n (k + 1)
    omega
  have hdvd : C ((n ! : ℤ_[p]) * p) ∣ C (n ! : ℤ_[p]) * amicePolynomial p (h + 1) n a := by
    rw [C_mul_amicePolynomial]
    refine (_root_.map_dvd C (mul_dvd_mul_right
      (factorial_dvd_factorial_div_mul_pow (h + 1) n) _)).trans ?_
    rw [mul_assoc, ← pow_succ, C_mul]
    exact mul_dvd_mul_left _ ((_root_.map_dvd C (pow_dvd_pow _ hsum)).trans
      (C_pow_sum_card_dvd_discProd (h + 1) n a))
  rw [C_mul] at hdvd
  have hn : C (n ! : ℤ_[p]) ≠ 0 := C_ne_zero.2 (Nat.cast_ne_zero.mpr (factorial_ne_zero n))
  exact (C_dvd_iff_dvd_coeff _ _).1 ((mul_dvd_mul_iff_left hn).1 hdvd) j

/-- **Amice's polynomials modulo `p` above the block degree.** For `a < pʰ`, the coefficients of
`w ↦ ⌊n / pʰ⌋! (a + pʰ w choose n)` of degree greater than `⌊n / pʰ⌋` are divisible by `p`. -/
theorem dvd_coeff_amicePolynomial_of_div_lt {h n a j : ℕ} (ha : a < p ^ h) (hj : n / p ^ h < j) :
    (p : ℤ_[p]) ∣ (amicePolynomial p h n a).coeff j := by
  by_cases hra : n % p ^ h ≤ a
  · obtain ⟨c, G, hG, hc⟩ := exists_amicePolynomial_eq ha hra
    rw [← PadicInt.toZMod_eq_zero_iff_dvd, hc, coeff_C_mul, map_mul, ← coeff_map,
      Polynomial.map_mul, hG, one_mul, descPochhammer_map,
      coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]), mul_zero]
  · exact dvd_coeff_amicePolynomial_of_lt_mod (not_le.1 hra) j

/-- **The diagonal coefficients of Amice's basis.** On the disc of centre `r = n % pʰ`, the
coefficient of `w ^ ⌊n / pʰ⌋` in `w ↦ ⌊n / pʰ⌋! (r + pʰ w choose n)` is a unit of `ℤ_p`. -/
theorem isUnit_coeff_amicePolynomial_mod (h n : ℕ) :
    IsUnit ((amicePolynomial p h n (n % p ^ h : ℕ)).coeff (n / p ^ h)) := by
  obtain ⟨c, G, hG, hc⟩ := exists_amicePolynomial_eq (Nat.mod_lt n (pow_pos hp.out.pos h)) le_rfl
  -- Evaluating at `w = ⌊n / pʰ⌋`, where `r + pʰ w = n`, shows that `c` is a unit.
  have heval := congrArg (eval ((n / p ^ h : ℕ) : ℤ_[p])) hc
  have hn : ((n % p ^ h : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ h * ((n / p ^ h : ℕ) : ℤ_[p]) = n := by
    exact_mod_cast Nat.mod_add_div n (p ^ h)
  rw [eval_amicePolynomial, hn, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, mul_one,
    eval_mul, eval_C, eval_mul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_self] at heval
  have hq : ((n / p ^ h)! : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  have hcG : c * G.eval ((n / p ^ h : ℕ) : ℤ_[p]) = 1 :=
    mul_left_cancel₀ hq (by linear_combination -heval)
  rw [hc, coeff_C_mul]
  exact (IsUnit.of_mul_eq_one _ hcG).mul (isUnit_coeff_mul_descPochhammer hG _)

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
