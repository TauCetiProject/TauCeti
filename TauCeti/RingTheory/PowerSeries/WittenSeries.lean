/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Series
public import TauCeti.RingTheory.PowerSeries.CharacteristicSeries
public import TauCeti.RingTheory.PowerSeries.Expand
public import TauCeti.RingTheory.PowerSeries.Swap
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# The characteristic series of the Witten genus

Over a `ℚ`-algebra `A`, the Witten genus of a Spin manifold is the genus whose characteristic
power series is

`Q(x, q) = (x / 2) / sinh (x / 2) · ∏_{n ≥ 1} (1 - qⁿ)² / ((1 - eˣ qⁿ) (1 - e⁻ˣ qⁿ))`.

This file constructs `Q` as a power series in `x` whose coefficients are power series in `q`, and
proves that its logarithm is a generating function of Eisenstein series:

`log Q(x, q) = ∑_{k ≥ 1} (2 / (2k)!) G_{2k}(q) x^{2k}`,

where `G_k(q) = -B_k / (2k) + ∑_{n ≥ 1} σ_{k-1}(n) qⁿ` is `TauCeti.eisensteinGSeries`. Summed
over the formal Pontryagin roots `xᵢ` of a manifold, this identity expresses the Witten genus
through the `G_{2k}`, with `G₂` entering only through the factor `exp (G₂ p₁)`, since
`∑ xᵢ² = p₁`.

The `q`-constant part is the Â series, whose logarithm is computed in
`TauCeti.logOf_aHatSeries`. The product is formed in `A⟦x⟧⟦q⟧`, the power series in the outer
variable `q` with coefficients in `A⟦x⟧`. Its factor at `qⁿ` is the expansion
`f (qⁿ)` of a single factor `f(q) = (1 - q)² / ((1 - eˣ q) (1 - e⁻ˣ q))`, which is `1` modulo
`qⁿ`, so the product converges in the coefficientwise topology, and each coefficient of `qᴺ` is
that of a finite product. Exchanging the two variables with `PowerSeries.swap` makes `x` the
outer variable, in which the logarithm is taken.

The logarithm is identified through the logarithmic derivative in `x`. Writing the factor as
`(1 - q)² (∑ e^{mx} qᵐ) (∑ e^{-mx} qᵐ)` shows that its logarithmic derivative in `x` is
`∑ₘ (e^{mx} - e^{-mx}) qᵐ`. For the product, the logarithmic derivative is the sum of these
over the substitutions `q ↦ qⁿ`, whose coefficient of `qᴺ` is `∑_{d ∣ N} (e^{dx} - e^{-dx})`.
Its coefficient of `x^{2k-1}` is `2 σ_{2k-1}(N) / (2k-1)!`, and integrating in `x` gives the
divisor sums of `G_{2k}`.

## Main definitions

* `TauCeti.wittenFactor A`: the factor `(1 - q)² / ((1 - eˣ q) (1 - e⁻ˣ q))` in `A⟦x⟧⟦q⟧`.
* `TauCeti.wittenProduct A`: the product `∏_{n ≥ 1} (1 - qⁿ)² / ((1 - eˣ qⁿ) (1 - e⁻ˣ qⁿ))` in
  `A⟦x⟧⟦q⟧`.
* `TauCeti.wittenSeries A`: the characteristic series `Q(x, q)` of the Witten genus in
  `A⟦q⟧⟦x⟧`.

## Main results

* `TauCeti.wittenFactor_mul`: `f(q) (1 - eˣ q) (1 - e⁻ˣ q) = (1 - q)²`.
* `TauCeti.hasProd_wittenProduct`: `wittenProduct A` is the infinite product of the factors
  `f (qⁿ)` in the coefficientwise topology.
* `TauCeti.coeff_logOf_swap_wittenProduct_of_even`,
  `TauCeti.coeff_logOf_swap_wittenProduct_of_odd`: the logarithm of the product has
  `x^{2k}`-coefficient `(2 / (2k)!) ∑_{N ≥ 1} σ_{2k-1}(N) qᴺ` and no odd terms.
* `TauCeti.map_constantCoeff_wittenSeries`: at `q = 0`, `Q` is the Â series.
* `TauCeti.coeff_logOf_wittenSeries_of_even`, `TauCeti.coeff_logOf_wittenSeries_of_odd`:
  `log Q` has `x^{2k}`-coefficient `(2 / (2k)!) G_{2k}(q)` for `k ≥ 1`, and no odd terms.

## References

* E. Witten, *The index of the Dirac operator in loop space*, in *Elliptic curves and modular
  forms in algebraic topology* (Princeton, 1986), Lecture Notes in Math. 1326, Springer (1988),
  161–181.
* D. Zagier, *Note on the Landweber–Stong elliptic genus*, in *Elliptic curves and modular forms in
  algebraic topology* (Princeton, 1986), Lecture Notes in Math. 1326, Springer (1988), 216–224.
* F. Hirzebruch, T. Berger, R. Jung, *Manifolds and Modular Forms*, Aspects of Mathematics E20,
  Vieweg (1992).
-/

public section

open Nat PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-! ### The product over `n ≥ 1` -/

/-- The factor `(1 - q)² / ((1 - eˣ q) (1 - e⁻ˣ q))` of the characteristic series of the Witten
genus, a power series in the outer variable `q` with coefficients power series in `x`. It is
defined as `(1 - q)² (∑ e^{mx} qᵐ) (∑ e^{-mx} qᵐ)`; `TauCeti.wittenFactor_mul` proves that it is
the displayed quotient. -/
noncomputable def wittenFactor : A⟦X⟧⟦X⟧ :=
  (1 - X) ^ 2 * (mk fun m ↦ exp A ^ m) * mk fun m ↦ rescale (-1) (exp A) ^ m

/-- **The factor is `(1 - q)² / ((1 - eˣ q) (1 - e⁻ˣ q))`**: its product with
`(1 - eˣ q) (1 - e⁻ˣ q)` is `(1 - q)²`. -/
theorem wittenFactor_mul :
    wittenFactor A * ((1 - C (exp A) * X) * (1 - C (rescale (-1) (exp A)) * X)) =
      (1 - X) ^ 2 := by
  have h₁ := powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (exp A)
  have h₂ := powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (rescale (-1) (exp A))
  rw [wittenFactor]
  linear_combination (1 - X) ^ 2 * ((mk fun m ↦ rescale (-1) (exp A) ^ m) *
    (1 - C (rescale (-1) (exp A)) * X)) * h₁ + (1 - X) ^ 2 * h₂

/-- The factor is `1` at `q = 0`. -/
@[simp]
theorem constantCoeff_wittenFactor : constantCoeff (wittenFactor A) = 1 := by
  simp [wittenFactor]

/-- The factor is `1` at `x = 0`: setting `x = 0` in each coefficient gives
`(1 - q)² / (1 - q)²`. -/
@[simp]
theorem map_constantCoeff_wittenFactor : map constantCoeff (wittenFactor A) = 1 := by
  have h : (mk 1 : A⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one A
  have hm (c : A⟦X⟧) (hc : constantCoeff c = 1) :
      map constantCoeff (mk fun m ↦ c ^ m) = mk 1 := by
    ext m
    simp [hc]
  simp only [wittenFactor, map_mul, map_pow, map_sub, map_one, map_X]
  rw [hm _ constantCoeff_exp, hm _ (by simp [constantCoeff_rescale])]
  linear_combination (1 + (mk 1 : A⟦X⟧) * (1 - X)) * h

/-- The product `∏_{n ≥ 1} (1 - qⁿ)² / ((1 - eˣ qⁿ) (1 - e⁻ˣ qⁿ))` in the outer variable `q`, whose
factors are the expansions `f (qⁿ)` of `f = TauCeti.wittenFactor A`. Since `f (qⁿ)` is `1` modulo
`qⁿ`, the coefficient of `qᴺ` is that of the finite product over `n ≤ N`; this is the
definition. `TauCeti.hasProd_wittenProduct` shows that it is the infinite product. -/
noncomputable def wittenProduct : A⟦X⟧⟦X⟧ :=
  mk fun N ↦ coeff N (∏ n ∈ Finset.range N, expand (n + 1) n.succ_ne_zero (wittenFactor A))

private theorem X_pow_dvd_expand_wittenFactor_sub_one (n : ℕ) :
    X ^ (n + 1) ∣ expand (n + 1) n.succ_ne_zero (wittenFactor A) - 1 := by
  simpa using X_pow_dvd_expand_sub_C_constantCoeff (n + 1) n.succ_ne_zero (wittenFactor A)

/-- The coefficient of `qᴺ` in the product is that of the finite product over `n ≤ M`, for every
`M ≥ N`. -/
theorem coeff_wittenProduct {N M : ℕ} (h : N ≤ M) :
    coeff N (wittenProduct A) =
      coeff N (∏ n ∈ Finset.range M, expand (n + 1) n.succ_ne_zero (wittenFactor A)) := by
  rw [wittenProduct, coeff_mk]
  refine (coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one (Finset.range_subset_range.2 h)
    fun n hn ↦ (pow_dvd_pow X ?_).trans (X_pow_dvd_expand_wittenFactor_sub_one A n)).symm
  simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  omega

open scoped PowerSeries.WithPiTopology in
/-- **The product converges**: in the coefficientwise topology, for any topology on the
coefficients `A⟦x⟧`, `TauCeti.wittenProduct A` is the infinite product of the factors
`(1 - qⁿ)² / ((1 - eˣ qⁿ) (1 - e⁻ˣ qⁿ))`, `n ≥ 1`. -/
theorem hasProd_wittenProduct [TopologicalSpace A⟦X⟧] :
    HasProd (fun n : ℕ ↦ expand (n + 1) n.succ_ne_zero (wittenFactor A)) (wittenProduct A) :=
  WithPiTopology.hasProd_of_X_pow_dvd_sub_one Finset.range fun N n hn ↦
    (pow_dvd_pow X (by simpa using hn)).trans (X_pow_dvd_expand_wittenFactor_sub_one A n)

/-- The product is `1` at `q = 0`. -/
@[simp]
theorem constantCoeff_wittenProduct : constantCoeff (wittenProduct A) = 1 := by
  simp [wittenProduct, ← coeff_zero_eq_constantCoeff_apply]

/-- The product is `1` at `x = 0`. -/
@[simp]
theorem map_constantCoeff_wittenProduct : map constantCoeff (wittenProduct A) = 1 := by
  ext N
  rw [coeff_map, coeff_wittenProduct A le_rfl, ← coeff_map, map_prod]
  simp [map_expand]

/-- With `x` as the outer variable, the product is `1` at `x = 0`. -/
@[simp]
theorem constantCoeff_swap_wittenProduct : constantCoeff (swap (wittenProduct A)) = 1 := by
  ext a
  rw [coeff_constantCoeff_swap, ← coeff_map, map_constantCoeff_wittenProduct]

/-! ### The logarithmic derivative in `x`

The derivative in the inner variable `x` of `G : A⟦x⟧⟦q⟧` is written `swap (d⁄dX (swap G))`. -/

omit [Algebra ℚ A] in
private theorem swap_derivative_swap_expand (j : ℕ) (hj : j ≠ 0) (G : A⟦X⟧⟦X⟧) :
    swap (d⁄dX (swap (expand j hj G))) = expand j hj (swap (d⁄dX (swap G))) := by
  ext N : 1
  rw [coeff_swap_derivative_swap, coeff_expand, coeff_expand]
  split_ifs <;> simp

omit [Algebra ℚ A] in
/-- If `c' = u c`, then the derivative of `g = ∑ cᵐ qᵐ` in the inner variable is
`∑ m u cᵐ qᵐ = u g (g - 1)`. -/
private theorem swap_derivative_swap_mk_pow (c u : A⟦X⟧) (hc : d⁄dX c = u * c) :
    swap (d⁄dX (swap (mk fun m ↦ c ^ m))) =
      C u * ((mk fun m ↦ c ^ m) * ((mk fun m ↦ c ^ m) - 1)) := by
  set g : A⟦X⟧⟦X⟧ := mk fun m ↦ c ^ m
  have hg : g * (g - 1) = X * d⁄dX g := by
    rw [powerSeries_X_mul_derivative_mk_pow c]
    linear_combination g * powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one c
  rw [hg]
  ext (_ | N) : 1
  · simp [g]
  · rw [coeff_swap_derivative_swap, coeff_C_mul, coeff_succ_X_mul, coeff_derivative]
    simp only [g, coeff_mk, Derivation.leibniz_pow, hc, nsmul_eq_mul, smul_eq_mul,
      Nat.add_sub_cancel]
    push_cast
    ring

/-- The logarithmic derivative in `x` of the factor, `∑ₘ (e^{mx} - e^{-mx}) qᵐ`. -/
private noncomputable def wittenLogDerivFactor : A⟦X⟧⟦X⟧ :=
  (mk fun m ↦ exp A ^ m) - mk fun m ↦ rescale (-1) (exp A) ^ m

private theorem swap_derivative_swap_wittenFactor :
    swap (d⁄dX (swap (wittenFactor A))) = wittenLogDerivFactor A * wittenFactor A := by
  have hE := swap_derivative_swap_mk_pow A (exp A) 1 (by rw [derivative_exp, one_mul])
  have hE' := swap_derivative_swap_mk_pow A (rescale (-1) (exp A)) (-1)
    (by rw [derivative_rescale, derivative_exp, map_neg, map_one])
  have h₀ : swap (d⁄dX (swap ((1 - X) ^ 2 : A⟦X⟧⟦X⟧))) = 0 := by
    simp [swap_X]
  rw [wittenFactor, swap_derivative_swap_mul, swap_derivative_swap_mul, h₀, hE, hE',
    wittenLogDerivFactor]
  simp only [map_one, map_neg]
  ring

private theorem swap_derivative_swap_prod (M : ℕ) :
    swap (d⁄dX (swap (∏ n ∈ Finset.range M, expand (n + 1) n.succ_ne_zero (wittenFactor A)))) =
      (∑ n ∈ Finset.range M, expand (n + 1) n.succ_ne_zero (wittenLogDerivFactor A)) *
        ∏ n ∈ Finset.range M, expand (n + 1) n.succ_ne_zero (wittenFactor A) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, swap_derivative_swap_mul, ih,
      swap_derivative_swap_expand, swap_derivative_swap_wittenFactor, map_mul]
    ring

/-- The logarithmic derivative in `x` of the product: its coefficient of `qᴺ` is
`∑_{d ∣ N} (e^{(N/d)x} - e^{-(N/d)x})`. -/
private noncomputable def wittenLogDeriv : A⟦X⟧⟦X⟧ :=
  mk fun N ↦ ∑ d ∈ N.divisors, (exp A ^ (N / d) - rescale (-1) (exp A) ^ (N / d))

/-- Only the substitutions `q ↦ qⁿ` with `n ∣ N` contribute to the coefficient of `qᴺ`. -/
private theorem coeff_sum_expand_wittenLogDerivFactor {N M : ℕ} (h : N ≤ M) :
    coeff N (∑ n ∈ Finset.range M, expand (n + 1) n.succ_ne_zero (wittenLogDerivFactor A)) =
      coeff N (wittenLogDeriv A) := by
  have hΛ : coeff N (wittenLogDeriv A) =
      ∑ d ∈ N.divisors, coeff (N / d) (wittenLogDerivFactor A) := by
    simp [wittenLogDeriv, wittenLogDerivFactor]
  rw [hΛ, map_sum]
  simp only [coeff_expand]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [wittenLogDerivFactor]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- Reindex the factors `n + 1 ∣ N` by the divisors `d = n + 1` of `N`.
  refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp [Nat.mem_divisors, hn.2, hN.ne']
  · intro d hd
    have hd₀ := Nat.pos_of_mem_divisors hd
    have hdN := Nat.divisor_le hd
    simp only [Nat.mem_divisors] at hd
    simp only [Finset.mem_filter, Finset.mem_range, Nat.sub_add_cancel hd₀, hd.1, and_true]
    omega
  · intro n _
    simp
  · intro d hd
    simp [Nat.sub_add_cancel (Nat.pos_of_mem_divisors hd)]
  · intro n _
    simp

private theorem swap_derivative_swap_wittenProduct :
    swap (d⁄dX (swap (wittenProduct A))) = wittenLogDeriv A * wittenProduct A := by
  ext N : 1
  rw [coeff_swap_derivative_swap, coeff_wittenProduct A le_rfl, ← coeff_swap_derivative_swap,
    swap_derivative_swap_prod, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have h := Finset.mem_antidiagonal.1 hp
  rw [coeff_sum_expand_wittenLogDerivFactor A (by omega),
    coeff_wittenProduct A (M := N) (by omega)]

private theorem logOf_swap_wittenProduct :
    logOf (swap (wittenProduct A)) =
      mk fun n ↦ (n : ℚ)⁻¹ • coeff (n - 1) (swap (wittenLogDeriv A)) := by
  rw [logOf_eq_mk_iff (constantCoeff_swap_wittenProduct A),
    ← swap_swap (d⁄dX (swap (wittenProduct A))), swap_derivative_swap_wittenProduct, map_mul]
  congr 1
  ext n : 1
  simp

/-- The coefficient of `xʲ` in `e^{kx} - e^{-kx}` is `(kʲ - (-k)ʲ) / j!`. -/
private theorem coeff_exp_pow_sub (j k : ℕ) :
    coeff j (exp A ^ k - rescale (-1) (exp A) ^ k) =
      algebraMap ℚ A (((k : ℚ) ^ j - (-(k : ℚ)) ^ j) / j !) := by
  rw [← map_pow, exp_pow_eq_rescale_exp, rescale_rescale, map_sub, coeff_rescale, coeff_rescale,
    coeff_exp, div_eq_mul_one_div ((k : ℚ) ^ j - (-(k : ℚ)) ^ j), map_mul, map_sub, map_pow,
    map_pow, map_neg, map_natCast, mul_neg_one, sub_mul]

/-- **The logarithm of the product**: for even `n ≠ 0`, the coefficient of `xⁿ` in
`log ∏_{m ≥ 1} (1 - qᵐ)² / ((1 - eˣ qᵐ) (1 - e⁻ˣ qᵐ))` is `(2 / n!) ∑_{N ≥ 1} σ_{n-1}(N) qᴺ`. -/
theorem coeff_logOf_swap_wittenProduct_of_even {n : ℕ} (hn : Even n) (hn₀ : n ≠ 0) :
    coeff n (logOf (swap (wittenProduct A))) = (2 / n ! : ℚ) • divisorSumSeries (n - 1) := by
  have hodd : Odd (n - 1) := Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 hn₀) hn odd_one
  ext N
  rw [logOf_swap_wittenProduct, coeff_mk, map_rat_smul, coeff_coeff_swap, wittenLogDeriv,
    coeff_mk, map_sum, map_rat_smul, coeff_divisorSumSeries]
  simp only [coeff_exp_pow_sub, hodd.neg_pow, sub_neg_eq_add]
  rw [← map_sum, ← map_natCast (algebraMap ℚ A), Algebra.smul_def, Algebra.smul_def, ← map_mul,
    ← map_mul, ArithmeticFunction.sigma_apply, Nat.cast_sum,
    ← Nat.sum_div_divisors N fun d ↦ ((d ^ (n - 1) : ℕ) : ℚ)]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_pow, Nat.factorial_succ, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  field_simp
  ring

/-- The odd coefficients in `x` of the logarithm of the product vanish. -/
theorem coeff_logOf_swap_wittenProduct_of_odd {n : ℕ} (hn : Odd n) :
    coeff n (logOf (swap (wittenProduct A))) = 0 := by
  have heven : Even (n - 1) := Nat.Odd.sub_odd hn odd_one
  ext N
  rw [logOf_swap_wittenProduct, coeff_mk, map_rat_smul, coeff_coeff_swap, wittenLogDeriv,
    coeff_mk, map_sum]
  simp [coeff_exp_pow_sub, heven.neg_pow]

/-! ### The characteristic series `Q` -/

/-- **The characteristic series of the Witten genus**
`Q(x, q) = (x / 2) / sinh (x / 2) · ∏_{n ≥ 1} (1 - qⁿ)² / ((1 - eˣ qⁿ) (1 - e⁻ˣ qⁿ))`, a power
series in the outer variable `x` with coefficients power series in `q`. -/
noncomputable def wittenSeries : A⟦X⟧⟦X⟧ :=
  map C (aHatSeries A) * swap (wittenProduct A)

/-- `Q` is the Â series in `x`, times the product with `x` made the outer variable. -/
theorem wittenSeries_def : wittenSeries A = map C (aHatSeries A) * swap (wittenProduct A) :=
  (rfl)

private theorem constantCoeff_map_C_aHatSeries : constantCoeff (map C (aHatSeries A)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_aHatSeries, map_one]

/-- `Q` is `1` at `x = 0`. -/
@[simp]
theorem constantCoeff_wittenSeries : constantCoeff (wittenSeries A) = 1 := by
  rw [wittenSeries, map_mul, constantCoeff_map_C_aHatSeries, constantCoeff_swap_wittenProduct,
    mul_one]

/-- At `q = 0`, `Q` is the Â series `(x / 2) / sinh (x / 2)`. -/
@[simp]
theorem map_constantCoeff_wittenSeries : map constantCoeff (wittenSeries A) = aHatSeries A := by
  have h : map constantCoeff (swap (wittenProduct A)) = 1 := by
    ext a
    rw [coeff_map, ← coeff_zero_eq_constantCoeff_apply, coeff_coeff_swap,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_wittenProduct]
  rw [wittenSeries, map_mul, h, mul_one]
  ext n
  simp [coeff_map]

/-- The logarithm of `Q` is the sum of the logarithms of the Â series and of the product. -/
theorem logOf_wittenSeries :
    logOf (wittenSeries A) = map C (logOf (aHatSeries A)) + logOf (swap (wittenProduct A)) := by
  rw [wittenSeries, logOf_mul (constantCoeff_map_C_aHatSeries A)
    (constantCoeff_swap_wittenProduct A), map_logOf C (constantCoeff_aHatSeries A)]

/-- **The logarithm of the characteristic series of the Witten genus**: for even `n ≠ 0`, the
coefficient of `xⁿ` in `log Q(x, q)` is `(2 / n!) Gₙ(q)`, where
`Gₙ(q) = -Bₙ / (2n) + ∑_{N ≥ 1} σ_{n-1}(N) qᴺ` is the Eisenstein series. -/
theorem coeff_logOf_wittenSeries_of_even {n : ℕ} (hn : Even n) (hn₀ : n ≠ 0) :
    coeff n (logOf (wittenSeries A)) = (2 / n ! : ℚ) • eisensteinGSeries A n := by
  have h₁ : n ≠ 1 := by
    rintro rfl
    exact Nat.not_even_one hn
  rw [logOf_wittenSeries, map_add, coeff_map, coeff_logOf_aHatSeries A h₁,
    coeff_logOf_swap_wittenProduct_of_even A hn hn₀, eisensteinGSeries_def, smul_add]
  congr 1
  rw [← map_rat_smul C, Algebra.smul_def, ← map_mul]
  congr 2
  field_simp

/-- The odd coefficients in `x` of `log Q(x, q)` vanish. -/
theorem coeff_logOf_wittenSeries_of_odd {n : ℕ} (hn : Odd n) :
    coeff n (logOf (wittenSeries A)) = 0 := by
  rw [logOf_wittenSeries, map_add, coeff_map, coeff_logOf_aHatSeries_of_odd A hn,
    coeff_logOf_swap_wittenProduct_of_odd A hn, _root_.map_zero, add_zero]

end TauCeti
