/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
import TauCeti.Analysis.Asymptotics.Sum.Divergence
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.KummerLimit

/-!
# The continued fraction for the lower incomplete Gamma function (DLMF 8.9.1)

For a complex parameter `a ∉ {-1, -2, …}` and any complex argument `z`, the normalized Tricomi
function `Γ(a + 1) e^z γ*(a, z) = Γ(a + 1) 𝐌(1, a + 1, z)` admits the classical continued-fraction
expansion (DLMF 8.9.1)
$$
  \Gamma(a + 1)\,e^z\,\gamma^*(a, z)
    = \cfrac{1}{1 - \cfrac{z}{a + 1 + \cfrac{z}{a + 2 - \cfrac{(a + 1)z}{a + 3 +
        \cfrac{2z}{a + 4 - \cdots}}}}},
$$
so that for `a ∉ -ℕ`, `γ(a, z) = (z^a e^{-z} / a) (Γ(a + 1) e^z γ*(a, z))`.

Dividing the first two levels of DLMF 8.9.1 by `a` removes the removable singularity at `a = 0`,
yielding a generalized continued fraction `Complex.tricomiContFrac a z` with zero integer part,
partial numerators `a₁ = 1`, `a₂ = -z`, `a_{2k} = -(a + k - 1) z` (`k ≥ 2`), `a_{2k+1} = k z`
(`k ≥ 1`), and partial denominators `b₁ = 1`, `b_n = a + n - 1` (`n ≥ 2`).

At `z = 0`, all partial numerators from `a₂` onwards vanish, so every convergent from index `1`
onwards has numerator and denominator `(a + 1)_{n - 1}` and equals `1 = Γ(a + 1) γ*(a, 0)` whenever
`a ∉ {-1, -2, …}`.

For `z ≠ 0` and `a ∉ {-1, -2, …}`, we construct the explicit recessive solution
`Complex.tricomiContFracSolution a z` of the three-term recurrence
`f(n + 1) = b_n f(n) + a_n f(n - 1)` in terms of Kummer's regularized hypergeometric function:
`f(0) = 1` and
$$
  f(m) = (-1)^{\lceil m / 2 \rceil}\,\Gamma(a + 1)\,z^{m - 1}\,d_m\,
    \mathbf{M}\bigl(\lceil m / 2 \rceil, a + m, z\bigr) \qquad (m \ge 1),
$$
where `d_{2k} = (a + 1)_{k - 1} (k - 1)!` and `d_{2k + 1} = (a + 1)_{k - 1} k!`. Its initial ratio
`-f(1) / f(0)` equals `Γ(a + 1) e^z γ*(a, z)`. Using the Kummer contiguous relations for the
recurrence and the large-parameter limit `Γ(2k + c) 𝐌(k, 2k + c, z) → e^{z / 2}` for the tail
asymptotics, we show that consecutive reduction-of-order summands
`(-1)^m (∏_{j=1}^m a_j) / (f(m) f(m + 1))` have ratio `O(1 / m) → 0`, so their partial sums diverge
in norm for every starting index `N`.

## Main definitions

* `Complex.tricomiContFracPartNum a z n`, `Complex.tricomiContFracPartDen a n` — the partial
  numerators `aₙ` and partial denominators `bₙ` of DLMF 8.9.1 (`1`-indexed).
* `Complex.tricomiContFrac a z` — the generalized continued fraction (`GenContFract ℂ`) with head
  `0` and stream `n ↦ ⟨a_{n + 1}, b_{n + 1}⟩`.
* `Complex.tricomiContFracNorm a n` — the normalization factors `dₙ`.
* `Complex.tricomiContFracSolution a z` — the explicit Kummer sequence solving the three-term
  recurrence of `tricomiContFrac a z`.

## Main results

* `Complex.neg_tricomiContFracSolution_one_div_zero`:
  `-(f(1) / f(0)) = Γ(a + 1) e^z γ*(a, z)`, with corollaries for `regularizedGamma` and
  `lowerIncompleteGamma`.
* `Complex.tricomiContFrac_zero_convs_succ`, `Complex.tendsto_tricomiContFrac_zero_convs`:
  exact evaluation `(tricomiContFrac a 0).convs (k + 1) = 1` and convergence at `z = 0` for
  `a ∉ {-1, -2, …}`.
* `Complex.prod_Icc_tricomiContFracPartNum`:
  `∏_{j=1}^m a_j = (-1)^{⌊m/2⌋} z^{m - 1} d_m`.
* `Complex.tricomiContFracSolution_add_one`: the three-term recurrence
  `f(n + 1) = b_n f(n) + a_n f(n - 1)` for `n ≥ 1` and `a ∉ {-1, -2, …}` (and unconditionally for
  `n ≥ 2` in `Complex.tricomiContFracSolution_add_one_of_two_le`).
* `Complex.eventually_tricomiContFracSolution_ne_zero`: `f(n) ≠ 0` eventually for `z ≠ 0` and
  `a ∉ {-1, -2, …}`.
* `Complex.tendsto_norm_sum_tricomiContFrac_reductionOfOrder`: the reduction-of-order partial sums
  `‖∑_{m = N}^{n - 1} (-1)^m (∏_{j=1}^m a_j) / (f(m) f(m + 1))‖` tend to `+∞` as `n → ∞`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82.
* W. B. Jones and W. J. Thron, *Continued Fractions: Analytic Theory and Applications*,
  Addison-Wesley, 1980, §6.1.
-/

public section

noncomputable section

open Asymptotics Filter Finset
open scoped Nat Topology

namespace Complex

/-! ### Partial numerators, partial denominators, and the continued fraction -/

/-- The `1`-indexed partial numerators of the continued fraction for
`Γ(a + 1) e^z γ*(a, z)` (DLMF 8.9.1, divided by `a` at the top two levels): `a₀ = 0`, `a₁ = 1`,
`a₂ = -z`, `a_{2k} = -(a + k - 1) z` for `k ≥ 2`, and `a_{2k + 1} = k z` for `k ≥ 1`. -/
def tricomiContFracPartNum (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n = 2 then -z
  else if Even n then -(a + (n / 2 : ℕ) - 1) * z
  else ((n / 2 : ℕ) : ℂ) * z

/-- Unfolding `tricomiContFracPartNum`. -/
theorem tricomiContFracPartNum_def (a z : ℂ) (n : ℕ) :
    tricomiContFracPartNum a z n =
      if n = 0 then 0
      else if n = 1 then 1
      else if n = 2 then -z
      else if Even n then -(a + (n / 2 : ℕ) - 1) * z
      else ((n / 2 : ℕ) : ℂ) * z := (rfl)

/-- At index `0`, `tricomiContFracPartNum a z 0 = 0`. -/
@[simp]
theorem tricomiContFracPartNum_zero (a z : ℂ) : tricomiContFracPartNum a z 0 = 0 := by
  simp [tricomiContFracPartNum_def]

/-- The first partial numerator is `a₁ = 1`. -/
@[simp]
theorem tricomiContFracPartNum_one (a z : ℂ) : tricomiContFracPartNum a z 1 = 1 := by
  simp [tricomiContFracPartNum_def]

/-- The second partial numerator is `a₂ = -z`. -/
@[simp]
theorem tricomiContFracPartNum_two (a z : ℂ) : tricomiContFracPartNum a z 2 = -z := by
  simp [tricomiContFracPartNum_def]

/-- For `k ≥ 2`, the even partial numerator is `a_{2k} = -(a + k - 1) z`. -/
theorem tricomiContFracPartNum_two_mul (a z : ℂ) {k : ℕ} (hk : 2 ≤ k) :
    tricomiContFracPartNum a z (2 * k) = -(a + k - 1) * z := by
  have h0 : 2 * k ≠ 0 := by omega
  have h1 : 2 * k ≠ 1 := by omega
  have h2 : 2 * k ≠ 2 := by omega
  simp [tricomiContFracPartNum_def, h0, h1, h2]

/-- For `k ≥ 1`, the odd partial numerator is `a_{2k + 1} = k z`. -/
theorem tricomiContFracPartNum_two_mul_add_one (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFracPartNum a z (2 * k + 1) = k * z := by
  have hk0 : k ≠ 0 := by omega
  have h2 : 2 * k + 1 ≠ 2 := by omega
  have he : ¬Even (2 * k + 1) := by simp
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [tricomiContFracPartNum_def, hk0, h2, he, hdiv]

/-- At `z = 0`, every partial numerator from index `2` onwards vanishes. -/
theorem tricomiContFracPartNum_zero_right_of_two_le (a : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    tricomiContFracPartNum a 0 n = 0 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  by_cases h2 : n = 2
  · subst h2; simp
  · by_cases he : Even n <;> simp [tricomiContFracPartNum_def, h0, h1, h2, he]

/-- The `1`-indexed partial denominators of DLMF 8.9.1: `b₀ = 0`, `b₁ = 1`, and `b_n = a + n - 1`
for `n ≥ 2`. -/
def tricomiContFracPartDen (a : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else if n = 1 then 1 else a + n - 1

/-- Unfolding `tricomiContFracPartDen`. -/
theorem tricomiContFracPartDen_def (a : ℂ) (n : ℕ) :
    tricomiContFracPartDen a n = if n = 0 then 0 else if n = 1 then 1 else a + n - 1 := (rfl)

/-- At index `0`, `tricomiContFracPartDen a 0 = 0`. -/
@[simp]
theorem tricomiContFracPartDen_zero (a : ℂ) : tricomiContFracPartDen a 0 = 0 := by
  simp [tricomiContFracPartDen_def]

/-- The first partial denominator is `b₁ = 1`. -/
@[simp]
theorem tricomiContFracPartDen_one (a : ℂ) : tricomiContFracPartDen a 1 = 1 := by
  simp [tricomiContFracPartDen_def]

/-- For `n ≥ 2`, the `n`-th partial denominator is `b_n = a + n - 1`. -/
theorem tricomiContFracPartDen_of_two_le (a : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    tricomiContFracPartDen a n = a + n - 1 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [tricomiContFracPartDen_def, h0, h1]

/-- The generalized continued fraction (DLMF 8.9.1) for `Γ(a + 1) e^z γ*(a, z)`, with zero head
term and `(n + 1)`-th pair `⟨tricomiContFracPartNum a z (n + 1), tricomiContFracPartDen a (n + 1)⟩`
at stream index `n`. -/
def tricomiContFrac (a z : ℂ) : GenContFract ℂ :=
  ⟨0, Stream'.Seq.ofStream fun n ↦
    ⟨tricomiContFracPartNum a z (n + 1), tricomiContFracPartDen a (n + 1)⟩⟩

/-- Unfolding `tricomiContFrac`. -/
theorem tricomiContFrac_def (a z : ℂ) :
    tricomiContFrac a z =
      ⟨0, Stream'.Seq.ofStream fun n ↦
        ⟨tricomiContFracPartNum a z (n + 1), tricomiContFracPartDen a (n + 1)⟩⟩ := (rfl)

/-- The integer part (head term) of `tricomiContFrac a z` is `0`. -/
@[simp]
theorem tricomiContFrac_h (a z : ℂ) : (tricomiContFrac a z).h = 0 := (rfl)

/-- The `n`-th stream entry of `tricomiContFrac a z` is the `(n + 1)`-th partial numerator and
denominator pair. -/
@[simp]
theorem tricomiContFrac_s_get? (a z : ℂ) (n : ℕ) :
    (tricomiContFrac a z).s.get? n =
      some ⟨tricomiContFracPartNum a z (n + 1), tricomiContFracPartDen a (n + 1)⟩ := (rfl)

/-- The `n`-th partial numerator accessed via `GenContFract.partNums` is
`tricomiContFracPartNum a z (n + 1)`. -/
@[simp]
theorem tricomiContFrac_partNums_get? (a z : ℂ) (n : ℕ) :
    (tricomiContFrac a z).partNums.get? n = some (tricomiContFracPartNum a z (n + 1)) :=
  GenContFract.partNum_eq_s_a (tricomiContFrac_s_get? a z n)

/-- The `n`-th partial denominator accessed via `GenContFract.partDens` is
`tricomiContFracPartDen a (n + 1)`. -/
@[simp]
theorem tricomiContFrac_partDens_get? (a z : ℂ) (n : ℕ) :
    (tricomiContFrac a z).partDens.get? n = some (tricomiContFracPartDen a (n + 1)) :=
  GenContFract.partDen_eq_s_b (tricomiContFrac_s_get? a z n)

/-- The stream of `tricomiContFrac a z` never terminates in `GenContFract.TerminatedAt` sense. -/
@[simp]
theorem tricomiContFrac_not_terminatedAt (a z : ℂ) (n : ℕ) :
    ¬(tricomiContFrac a z).TerminatedAt n := by
  rw [GenContFract.terminatedAt_iff_s_none]
  simp

/-- The zeroth convergent of `tricomiContFrac a z` is `0`. -/
theorem tricomiContFrac_convs_zero (a z : ℂ) : (tricomiContFrac a z).convs 0 = 0 := by
  simp

/-- The first continuant pair of `tricomiContFrac a z` is `⟨1, 1⟩`. -/
@[simp]
theorem tricomiContFrac_conts_one (a z : ℂ) : (tricomiContFrac a z).conts 1 = ⟨1, 1⟩ := by
  rw [GenContFract.first_cont_eq (tricomiContFrac_s_get? a z 0)]
  simp

/-- The first continuant numerator of `tricomiContFrac a z` is `1`. -/
@[simp]
theorem tricomiContFrac_nums_one (a z : ℂ) : (tricomiContFrac a z).nums 1 = 1 := by
  rw [GenContFract.num_eq_conts_a, tricomiContFrac_conts_one]

/-- The first continuant denominator of `tricomiContFrac a z` is `1`. -/
@[simp]
theorem tricomiContFrac_dens_one (a z : ℂ) : (tricomiContFrac a z).dens 1 = 1 := by
  rw [GenContFract.den_eq_conts_b, tricomiContFrac_conts_one]

/-- The first convergent of `tricomiContFrac a z` is `1`. -/
@[simp]
theorem tricomiContFrac_convs_one (a z : ℂ) : (tricomiContFrac a z).convs 1 = 1 := by
  rw [GenContFract.conv_eq_num_div_den, tricomiContFrac_nums_one, tricomiContFrac_dens_one, div_one]

/-- The second continuant numerator of `tricomiContFrac a z` is `a + 1`. -/
theorem tricomiContFrac_nums_two (a z : ℂ) : (tricomiContFrac a z).nums 2 = a + 1 := by
  rw [GenContFract.nums_recurrence (tricomiContFrac_s_get? a z 1)
    (GenContFract.zeroth_num_eq_h (g := tricomiContFrac a z)) (tricomiContFrac_nums_one a z)]
  simp only [Nat.reduceAdd, tricomiContFracPartDen_of_two_le a (by norm_num : 2 ≤ 2),
    Nat.cast_ofNat, tricomiContFracPartNum_two, tricomiContFrac_h, mul_one, mul_zero, add_zero]
  ring

/-- The second continuant denominator of `tricomiContFrac a z` is `a + 1 - z`. -/
theorem tricomiContFrac_dens_two (a z : ℂ) : (tricomiContFrac a z).dens 2 = a + 1 - z := by
  rw [GenContFract.dens_recurrence (tricomiContFrac_s_get? a z 1)
    (GenContFract.zeroth_den_eq_one (g := tricomiContFrac a z)) (tricomiContFrac_dens_one a z)]
  simp only [Nat.reduceAdd, tricomiContFracPartDen_of_two_le a (by norm_num : 2 ≤ 2),
    Nat.cast_ofNat, tricomiContFracPartNum_two, mul_one]
  ring

/-! ### Terminating evaluation at `z = 0` -/

/-- At `z = 0`, both the numerator and denominator of the `(k + 1)`-th continuant of
`tricomiContFrac a 0` equal `(a + 1)_k`. -/
theorem tricomiContFrac_zero_conts_succ (a : ℂ) (k : ℕ) :
    (tricomiContFrac a 0).conts (k + 1) =
      ⟨(ascPochhammer ℂ k).eval (a + 1), (ascPochhammer ℂ k).eval (a + 1)⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := tricomiContFrac_s_get? a 0 (k + 1)
    obtain ⟨p₀, hp₀⟩ : ∃ p, (tricomiContFrac a 0).conts k = p := ⟨_, rfl⟩
    rw [GenContFract.conts_recurrence hs hp₀ ih,
      tricomiContFracPartNum_zero_right_of_two_le a (by omega),
      tricomiContFracPartDen_of_two_le a (by omega), ascPochhammer_succ_right,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
    push_cast
    congr 1 <;> ring

/-- At `z = 0`, the `(k + 1)`-th continuant numerator of `tricomiContFrac a 0` is `(a + 1)_k`. -/
theorem tricomiContFrac_zero_nums_succ (a : ℂ) (k : ℕ) :
    (tricomiContFrac a 0).nums (k + 1) = (ascPochhammer ℂ k).eval (a + 1) := by
  rw [GenContFract.num_eq_conts_a, tricomiContFrac_zero_conts_succ]

/-- At `z = 0`, the `(k + 1)`-th continuant denominator of `tricomiContFrac a 0` is `(a + 1)_k`. -/
theorem tricomiContFrac_zero_dens_succ (a : ℂ) (k : ℕ) :
    (tricomiContFrac a 0).dens (k + 1) = (ascPochhammer ℂ k).eval (a + 1) := by
  rw [GenContFract.den_eq_conts_b, tricomiContFrac_zero_conts_succ]

/-- For `a ∉ {-1, -2, …}`, every continuant denominator of `tricomiContFrac a 0` is nonzero. -/
theorem tricomiContFrac_zero_dens_ne_zero {a : ℂ} (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (n : ℕ) :
    (tricomiContFrac a 0).dens n ≠ 0 := by
  cases n with
  | zero => simp
  | succ k =>
    rw [tricomiContFrac_zero_dens_succ]
    rintro h
    obtain ⟨j, -, hj⟩ := (ascPochhammer_eval_eq_zero_iff k (a + 1)).mp h
    exact ha j (by linear_combination hj)

/-- For `a ∉ {-1, -2, …}`, every convergent of `tricomiContFrac a 0` from index `1` onwards equals
`1`. -/
theorem tricomiContFrac_zero_convs_succ {a : ℂ} (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (k : ℕ) :
    (tricomiContFrac a 0).convs (k + 1) = 1 := by
  have hden := tricomiContFrac_zero_dens_ne_zero ha (k + 1)
  rw [tricomiContFrac_zero_dens_succ] at hden
  rw [GenContFract.conv_eq_num_div_den, tricomiContFrac_zero_nums_succ,
    tricomiContFrac_zero_dens_succ, div_self hden]

/-- At `z = 0` and `a ∉ {-1, -2, …}`, the convergents of `tricomiContFrac a 0` are eventually
constant at `1 = Γ(a + 1) e^0 γ*(a, 0)` and therefore converge to DLMF 8.9.1's value. -/
theorem tendsto_tricomiContFrac_zero_convs {a : ℂ} (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) :
    Tendsto (tricomiContFrac a 0).convs atTop
      (𝓝 (Gamma (a + 1) * cexp 0 * tricomiIncompleteGamma a 0)) := by
  have hG : Gamma (a + 1) ≠ 0 := Gamma_ne_zero fun k hk ↦ ha k (by linear_combination hk)
  have hval : Gamma (a + 1) * cexp 0 * tricomiIncompleteGamma a 0 = 1 := by
    rw [exp_zero, mul_one, tricomiIncompleteGamma_zero_right, mul_inv_cancel₀ hG]
  rw [hval]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact (tricomiContFrac_zero_convs_succ ha k).symm

/-! ### Normalization factors and partial-numerator products -/

/-- The normalization factors `dₙ` in the explicit Kummer representation of the minimal solution of
DLMF 8.9.1: `d₁ = 1`, `d_{2k} = (a + 1)_{k - 1} (k - 1)!` for `k ≥ 1`, and
`d_{2k + 1} = (a + 1)_{k - 1} k!` for `k ≥ 1`. -/
def tricomiContFracNorm (a : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ ((n - 2) / 2)).eval (a + 1) * (((n - 1) / 2)! : ℂ)

/-- Unfolding `tricomiContFracNorm`. -/
theorem tricomiContFracNorm_def (a : ℂ) (n : ℕ) :
    tricomiContFracNorm a n =
      (ascPochhammer ℂ ((n - 2) / 2)).eval (a + 1) * (((n - 1) / 2)! : ℂ) := (rfl)

/-- `tricomiContFracNorm a 1 = 1`. -/
@[simp]
theorem tricomiContFracNorm_one (a : ℂ) : tricomiContFracNorm a 1 = 1 := by
  simp [tricomiContFracNorm_def]

/-- `tricomiContFracNorm a 2 = 1`. -/
@[simp]
theorem tricomiContFracNorm_two (a : ℂ) : tricomiContFracNorm a 2 = 1 := by
  simp [tricomiContFracNorm_def]

/-- `tricomiContFracNorm a 3 = 1`. -/
@[simp]
theorem tricomiContFracNorm_three (a : ℂ) : tricomiContFracNorm a 3 = 1 := by
  simp [tricomiContFracNorm_def]

/-- At even index `2k` (`k ≥ 1`), `d_{2k} = (a + 1)_{k - 1} (k - 1)!`. -/
theorem tricomiContFracNorm_two_mul (a : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFracNorm a (2 * k) =
      (ascPochhammer ℂ (k - 1)).eval (a + 1) * ((k - 1)! : ℂ) := by
  have h1 : (2 * k - 2) / 2 = k - 1 := by omega
  have h2 : (2 * k - 1) / 2 = k - 1 := by omega
  rw [tricomiContFracNorm_def, h1, h2]

/-- At odd index `2k + 1`, `d_{2k + 1} = (a + 1)_{k - 1} k!`. -/
theorem tricomiContFracNorm_two_mul_add_one (a : ℂ) (k : ℕ) :
    tricomiContFracNorm a (2 * k + 1) =
      (ascPochhammer ℂ (k - 1)).eval (a + 1) * (k ! : ℂ) := by
  have h1 : (2 * k + 1 - 2) / 2 = k - 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [tricomiContFracNorm_def, h1, h2]

/-- Step relation `d_{2k + 1} = k * d_{2k}` for `k ≥ 1`. -/
theorem tricomiContFracNorm_two_mul_add_one_eq_mul (a : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFracNorm a (2 * k + 1) = k * tricomiContFracNorm a (2 * k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [tricomiContFracNorm_two_mul_add_one, tricomiContFracNorm_two_mul a hk, Nat.add_sub_cancel,
    Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

/-- Step relation `d_{2(k + 1)} = (a + k) * d_{2k + 1}` for `k ≥ 1`. -/
theorem tricomiContFracNorm_two_mul_succ_eq_mul (a : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFracNorm a (2 * (k + 1)) = (a + k) * tricomiContFracNorm a (2 * k + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [tricomiContFracNorm_two_mul a (by omega), tricomiContFracNorm_two_mul_add_one,
    show j + 1 + 1 - 1 = j + 1 by omega, Nat.add_sub_cancel, ascPochhammer_succ_right,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
  push_cast
  ring

/-- For `a ∉ {-1, -2, …}`, every normalization factor `dₙ` is nonzero. -/
theorem tricomiContFracNorm_ne_zero {a : ℂ} (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (n : ℕ) :
    tricomiContFracNorm a n ≠ 0 := by
  refine mul_ne_zero (fun h ↦ ?_) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  obtain ⟨j, -, hj⟩ := (ascPochhammer_eval_eq_zero_iff ((n - 2) / 2) (a + 1)).mp h
  exact ha j (by linear_combination hj)

/-- For `a ∉ {-1, -2, …}` and `z ≠ 0`, every partial numerator `aₙ` (`n ≥ 1`) is nonzero. -/
theorem tricomiContFracPartNum_ne_zero {a z : ℂ} (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) : tricomiContFracPartNum a z n ≠ 0 := by
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · rcases eq_or_lt_of_le (show 1 ≤ k by omega) with rfl | hk
    · simpa using hz
    · rw [tricomiContFracPartNum_two_mul a z hk]
      refine mul_ne_zero (neg_ne_zero.mpr fun h ↦ ha (k - 2) ?_) hz
      have hk' : ((k - 2 : ℕ) : ℂ) + 1 = k - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hk']; linear_combination h
  · rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk
    · simp
    · rw [tricomiContFracPartNum_two_mul_add_one a z hk]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hz

/-- For `a ∉ {-1, -2, …}` and `z ≠ 0`, `∏ j ∈ Icc 1 m, a_j ≠ 0` for every `m : ℕ`. -/
theorem prod_Icc_tricomiContFracPartNum_ne_zero {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) (m : ℕ) :
    ∏ j ∈ Icc 1 m, tricomiContFracPartNum a z j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hj ↦
    tricomiContFracPartNum_ne_zero ha hz (Finset.mem_Icc.mp hj).1

/-- Closed form for the product of the first `m` partial numerators (`m ≥ 1`):
`∏_{j = 1}^m a_j = (-1)^{⌊m / 2⌋} z^{m - 1} d_m`. -/
theorem prod_Icc_tricomiContFracPartNum (a z : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    ∏ j ∈ Icc 1 m, tricomiContFracPartNum a z j =
      (-1) ^ (m / 2) * z ^ (m - 1) * tricomiContFracNorm a m := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    rcases m.even_or_odd' with ⟨k, rfl | rfl⟩
    · have hk : 1 ≤ k := by omega
      rw [tricomiContFracPartNum_two_mul_add_one a z hk,
        tricomiContFracNorm_two_mul_add_one_eq_mul a hk,
        show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega,
        show 2 * k + 1 - 1 = (2 * k - 1) + 1 by omega, pow_succ]
      ring
    · rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk
      · simp
      · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
          tricomiContFracPartNum_two_mul a z (by omega),
          tricomiContFracNorm_two_mul_succ_eq_mul a hk,
          show (2 * (k + 1)) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
          show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show 2 * k + 1 - 1 = 2 * k by omega]
        push_cast
        rw [pow_succ, pow_succ]
        ring

/-! ### Explicit Kummer solution and the three-term recurrence -/

/-- The explicit Kummer sequence solving the three-term recurrence of `tricomiContFrac a z`:
`f(0) = 1` and `f(m) = (-1)^{⌈m / 2⌉} Γ(a + 1) z^{m - 1} d_m 𝐌(⌈m / 2⌉, a + m, z)` for `m ≥ 1`. -/
def tricomiContFracSolution (a z : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => (-1) ^ ((m + 2) / 2) * Gamma (a + 1) * z ^ m * tricomiContFracNorm a (m + 1) *
      regularizedHGFun {(((m + 2) / 2 : ℕ) : ℂ)} {a + (m + 1 : ℕ)} z

/-- `tricomiContFracSolution a z 0 = 1`. -/
@[simp]
theorem tricomiContFracSolution_zero (a z : ℂ) : tricomiContFracSolution a z 0 = 1 := (rfl)

/-- Unfolding `tricomiContFracSolution` at `m + 1`. -/
theorem tricomiContFracSolution_succ_def (a z : ℂ) (m : ℕ) :
    tricomiContFracSolution a z (m + 1) =
      (-1) ^ ((m + 2) / 2) * Gamma (a + 1) * z ^ m * tricomiContFracNorm a (m + 1) *
        regularizedHGFun {(((m + 2) / 2 : ℕ) : ℂ)} {a + (m + 1 : ℕ)} z := (rfl)

/-- `f(1) = -Γ(a + 1) 𝐌(1, a + 1, z)`. -/
@[simp]
theorem tricomiContFracSolution_one (a z : ℂ) :
    tricomiContFracSolution a z 1 = -Gamma (a + 1) * regularizedHGFun {1} {a + 1} z := by
  simp [tricomiContFracSolution_succ_def]

/-- `f(2) = -Γ(a + 1) z 𝐌(1, a + 2, z)`. -/
theorem tricomiContFracSolution_two (a z : ℂ) :
    tricomiContFracSolution a z 2 = -Gamma (a + 1) * z * regularizedHGFun {1} {a + 2} z := by
  rw [tricomiContFracSolution_succ_def]
  simp only [Nat.reduceAdd, Nat.reduceDiv, pow_one, neg_mul, one_mul, tricomiContFracNorm_two,
    mul_one, Nat.cast_one, Nat.cast_ofNat]

/-- Evaluation of `tricomiContFracSolution` at even positive index `2k` (`k ≥ 1`). -/
theorem tricomiContFracSolution_two_mul (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFracSolution a z (2 * k) =
      (-1) ^ k * Gamma (a + 1) * z ^ (2 * k - 1) * tricomiContFracNorm a (2 * k) *
        regularizedHGFun {(k : ℂ)} {a + (2 * k : ℕ)} z := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ 2 * k by omega)
  rw [hm, tricomiContFracSolution_succ_def]
  have h1 : (m + 2) / 2 = k := by omega
  have h2 : m = 2 * k - 1 := by omega
  rw [h1, ← hm, h2]

/-- Evaluation of `tricomiContFracSolution` at odd index `2k + 1`. -/
theorem tricomiContFracSolution_two_mul_add_one (a z : ℂ) (k : ℕ) :
    tricomiContFracSolution a z (2 * k + 1) =
      (-1) ^ (k + 1) * Gamma (a + 1) * z ^ (2 * k) * tricomiContFracNorm a (2 * k + 1) *
        regularizedHGFun {((k + 1 : ℕ) : ℂ)} {a + (2 * k + 1 : ℕ)} z := by
  rw [tricomiContFracSolution_succ_def]
  have h1 : (2 * k + 2) / 2 = k + 1 := by omega
  rw [h1]

/-- The initial ratio `-(f(1) / f(0))` of `tricomiContFracSolution` equals the normalized Tricomi
function `Γ(a + 1) e^z γ*(a, z)` (DLMF 8.9.1). -/
theorem neg_tricomiContFracSolution_one_div_zero (a z : ℂ) :
    -(tricomiContFracSolution a z 1 / tricomiContFracSolution a z 0) =
      Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z := by
  rw [tricomiContFracSolution_one, tricomiContFracSolution_zero, div_one,
    tricomiIncompleteGamma_def]
  calc -(-Gamma (a + 1) * regularizedHGFun {1} {a + 1} z)
      = Gamma (a + 1) * (cexp z * cexp (-z)) * regularizedHGFun {1} {a + 1} z := by
          rw [← exp_add, add_neg_cancel, exp_zero, mul_one]; ring
    _ = Gamma (a + 1) * cexp z * (cexp (-z) * regularizedHGFun {1} {a + 1} z) := by ring

/-- Relation between the initial ratio of `tricomiContFracSolution` and the regularized lower
incomplete Gamma function `P(a, z)`:
`z^a e^{-z} (-(f(1) / f(0))) = Γ(a + 1) P(a, z)` for all complex `a` and `z`. -/
theorem mul_neg_tricomiContFracSolution_one_div_zero_eq_Gamma_mul_regularizedGamma (a z : ℂ) :
    z ^ a * cexp (-z) * -(tricomiContFracSolution a z 1 / tricomiContFracSolution a z 0) =
      Gamma (a + 1) * regularizedGamma a z := by
  rw [neg_tricomiContFracSolution_one_div_zero, regularizedGamma_def]
  calc z ^ a * cexp (-z) * (Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z)
      = Gamma (a + 1) * (cexp (-z) * cexp z) * (z ^ a * tricomiIncompleteGamma a z) := by ring
    _ = Gamma (a + 1) * (z ^ a * tricomiIncompleteGamma a z) := by
          rw [← exp_add, neg_add_cancel, exp_zero, mul_one]

/-- **DLMF 8.9.1** initial-ratio identity for the lower incomplete Gamma function `γ(a, z)`: for
`a ∉ -ℕ` and every complex `z`,
`(z^a e^{-z} / a) (-(f(1) / f(0))) = γ(a, z)`. -/
theorem mul_neg_tricomiContFracSolution_one_div_zero_eq_lowerIncompleteGamma
    {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (z : ℂ) :
    z ^ a * cexp (-z) / a * -(tricomiContFracSolution a z 1 / tricomiContFracSolution a z 0) =
      lowerIncompleteGamma a z := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  rw [div_mul_eq_mul_div,
    mul_neg_tricomiContFracSolution_one_div_zero_eq_Gamma_mul_regularizedGamma,
    Gamma_add_one a ha0, lowerIncompleteGamma_def]
  field_simp

/-- Even-index step of the three-term recurrence: `f(2k + 1) = b_{2k} f(2k) + a_{2k} f(2k - 1)` for
`k ≥ 1`, unconditionally on `a` and `z`. -/
private theorem tricomiContFracSolution_add_one_two_mul (a z : ℂ) {k : ℕ} (hk1 : 1 ≤ k) :
    tricomiContFracSolution a z (2 * k + 1) =
      tricomiContFracPartDen a (2 * k) * tricomiContFracSolution a z (2 * k) +
        tricomiContFracPartNum a z (2 * k) * tricomiContFracSolution a z (2 * k - 1) := by
  rcases eq_or_lt_of_le hk1 with rfl | hk
  · have hM := regularizedHGFun_singleton_eq_mul_add_mul 1 (a + 1) z
    rw [tricomiContFracSolution_two_mul_add_one a z 1, tricomiContFracSolution_two,
      tricomiContFracSolution_one, tricomiContFracPartDen_of_two_le a (by norm_num),
      tricomiContFracPartNum_two, tricomiContFracNorm_three]
    push_cast
    rw [show (1 : ℂ) + 1 = 2 by norm_num, show a + 1 + 1 = a + 2 by ring,
      show a + 1 + 2 = a + 3 by ring] at hM
    rw [show a + 2 - 1 = a + 1 by ring]
    linear_combination -Gamma (a + 1) * z * hM
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have hm : 1 ≤ j + 1 := Nat.le_add_left 1 j
    obtain ⟨m, hjm⟩ : ∃ m, j + 1 = m := ⟨j + 1, rfl⟩
    rw [show j + 2 = m + 1 by omega]
    rw [hjm] at hm
    have hM := regularizedHGFun_singleton_eq_mul_add_mul ((m + 1 : ℕ) : ℂ) (a + (2 * m + 1 : ℕ)) z
    rw [show ((m + 1 : ℕ) : ℂ) + 1 = ((m + 1 + 1 : ℕ) : ℂ) by push_cast; ring,
      show a + (2 * m + 1 : ℕ) + 1 = a + (2 * (m + 1) : ℕ) by push_cast; ring,
      show a + (2 * m + 1 : ℕ) + 2 = a + (2 * (m + 1) + 1 : ℕ) by push_cast; ring] at hM
    rw [tricomiContFracSolution_two_mul_add_one a z (m + 1),
      tricomiContFracSolution_two_mul a z (by omega),
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
      tricomiContFracSolution_two_mul_add_one a z m,
      tricomiContFracPartDen_of_two_le a (by omega),
      tricomiContFracPartNum_two_mul a z (by omega),
      tricomiContFracNorm_two_mul_add_one_eq_mul a (by omega),
      tricomiContFracNorm_two_mul_succ_eq_mul a hm,
      show a + ((2 * (m + 1) : ℕ) : ℂ) - 1 = a + (2 * m + 1 : ℕ) by push_cast; ring,
      show a + ((m + 1 : ℕ) : ℂ) - 1 = a + m by push_cast; ring,
      show z ^ (2 * (m + 1)) = z * (z * z ^ (2 * m)) by
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ', pow_succ'],
      pow_succ' z (2 * m), pow_succ (-1 : ℂ) (m + 1)]
    linear_combination ((-1 : ℂ) ^ (m + 1) * Gamma (a + 1) * (z * z ^ (2 * m)) *
      (a + m) * tricomiContFracNorm a (2 * m + 1)) * hM

/-- Odd-index step of the three-term recurrence:
`f(2k + 2) = b_{2k + 1} f(2k + 1) + a_{2k + 1} f(2k)`
for `k ≥ 1`, unconditionally on `a` and `z`. -/
private theorem tricomiContFracSolution_add_one_two_mul_add_one (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFracSolution a z (2 * k + 1 + 1) =
      tricomiContFracPartDen a (2 * k + 1) * tricomiContFracSolution a z (2 * k + 1) +
        tricomiContFracPartNum a z (2 * k + 1) * tricomiContFracSolution a z (2 * k) := by
  have hM := mul_regularizedHGFun_add_one_sub (k : ℂ) (a + (2 * k : ℕ)) z
  rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
    show a + (2 * k : ℕ) + 1 = a + (2 * k + 1 : ℕ) by push_cast; ring,
    show a + (2 * k : ℕ) + 2 = a + (2 * (k + 1) : ℕ) by push_cast; ring,
    show a + (2 * k : ℕ) - (k : ℂ) = a + k by push_cast; ring] at hM
  have hzpow' : z ^ (2 * k) = z * z ^ (2 * k - 1) := by
    rw [← pow_succ', show 2 * k - 1 + 1 = 2 * k by omega]
  have hzpow : z ^ (2 * k + 1) = z * (z * z ^ (2 * k - 1)) := by
    rw [pow_succ', hzpow']
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
    tricomiContFracSolution_two_mul a z (by omega),
    tricomiContFracSolution_two_mul_add_one a z k,
    tricomiContFracSolution_two_mul a z hk,
    tricomiContFracPartDen_of_two_le a (by omega),
    tricomiContFracPartNum_two_mul_add_one a z hk,
    tricomiContFracNorm_two_mul_succ_eq_mul a hk,
    tricomiContFracNorm_two_mul_add_one_eq_mul a hk,
    show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show a + ((2 * k + 1 : ℕ) : ℂ) - 1 = a + (2 * k : ℕ) by push_cast; ring,
    hzpow, hzpow', pow_succ (-1 : ℂ) k]
  linear_combination ((-1 : ℂ) ^ k * Gamma (a + 1) * (z * z ^ (2 * k - 1)) *
    (k : ℂ) * tricomiContFracNorm a (2 * k)) * hM

/-- Three-term recurrence `f(n + 1) = b_n f(n) + a_n f(n - 1)` for `n ≥ 2`, holding unconditionally
for all complex `a` and `z` (since `Γ(a + 1)` factors out of all three terms). -/
theorem tricomiContFracSolution_add_one_of_two_le (a z : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    tricomiContFracSolution a z (n + 1) =
      tricomiContFracPartDen a n * tricomiContFracSolution a z n +
        tricomiContFracPartNum a z n * tricomiContFracSolution a z (n - 1) := by
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · exact tricomiContFracSolution_add_one_two_mul a z (by omega)
  · simpa using tricomiContFracSolution_add_one_two_mul_add_one a z (by omega)

/-- Three-term recurrence `f(n + 1) = b_n f(n) + a_n f(n - 1)` for all `n ≥ 1` when
`a ∉ {-1, -2, …}` (at `n = 1` this uses `Γ(a + 1) (Γ(a + 1))⁻¹ = 1`). -/
theorem tricomiContFracSolution_add_one {a : ℂ} (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (z : ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    tricomiContFracSolution a z (n + 1) =
      tricomiContFracPartDen a n * tricomiContFracSolution a z n +
        tricomiContFracPartNum a z n * tricomiContFracSolution a z (n - 1) := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · have hG : Gamma (a + 1) ≠ 0 := Gamma_ne_zero fun k hk ↦ ha k (by linear_combination hk)
    have hM := regularizedHGFun_one_singleton_eq (a + 1) z
    rw [show a + 1 + 1 = a + 2 by ring] at hM
    rw [tricomiContFracSolution_two, tricomiContFracSolution_one, tricomiContFracSolution_zero,
      tricomiContFracPartDen_one, tricomiContFracPartNum_one, hM]
    calc -Gamma (a + 1) * z * regularizedHGFun {1} {a + 2} z
        = 1 * (-Gamma (a + 1) * ((Gamma (a + 1))⁻¹ + z * regularizedHGFun {1} {a + 2} z)) +
            Gamma (a + 1) * (Gamma (a + 1))⁻¹ := by ring
      _ = 1 * (-Gamma (a + 1) * ((Gamma (a + 1))⁻¹ + z * regularizedHGFun {1} {a + 2} z)) +
            1 * 1 := by rw [mul_inv_cancel₀ hG, mul_one]
  · exact tricomiContFracSolution_add_one_of_two_le a z hn2

/-! ### Kummer tail asymptotics and reduction-of-order divergence -/

/-- Even-index Kummer limit: `Γ(a + 2k) 𝐌(k, a + 2k, z) → e^{z / 2}` as `k → ∞`. -/
private theorem tendsto_Gamma_mul_regularizedHGFun_even (a z : ℂ) :
    Tendsto (fun k : ℕ ↦ Gamma (a + (2 * k : ℕ)) * regularizedHGFun {(k : ℂ)} {a + (2 * k : ℕ)} z)
      atTop (𝓝 (cexp (z / 2))) := by
  refine (tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two a z).congr fun k ↦ ?_
  have hk : 2 * (k : ℂ) + a = a + (2 * k : ℕ) := by push_cast; ring
  rw [hk]

/-- Odd-index Kummer limit: `Γ(a + 2k + 1) 𝐌(k + 1, a + 2k + 1, z) → e^{z / 2}` as `k → ∞`. -/
private theorem tendsto_Gamma_mul_regularizedHGFun_odd (a z : ℂ) :
    Tendsto (fun k : ℕ ↦ Gamma (a + (2 * k + 1 : ℕ)) *
        regularizedHGFun {((k + 1 : ℕ) : ℂ)} {a + (2 * k + 1 : ℕ)} z)
      atTop (𝓝 (cexp (z / 2))) := by
  have h := (tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two (a - 1) z).comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun k ↦ ?_
  simp only [Function.comp_apply]
  have hk : 2 * ((k + 1 : ℕ) : ℂ) + (a - 1) = a + (2 * k + 1 : ℕ) := by push_cast; ring
  rw [hk]

/-- For `a ∉ {-1, -2, …}` and `z ≠ 0`, `tricomiContFracSolution a z n` is eventually nonzero. -/
theorem eventually_tricomiContFracSolution_ne_zero {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) :
    ∀ᶠ n in atTop, tricomiContFracSolution a z n ≠ 0 := by
  have hG : Gamma (a + 1) ≠ 0 := Gamma_ne_zero fun k hk ↦ ha k (by linear_combination hk)
  have heven : ∀ᶠ k : ℕ in atTop, regularizedHGFun {(k : ℂ)} {a + (2 * k : ℕ)} z ≠ 0 := by
    filter_upwards [(tendsto_Gamma_mul_regularizedHGFun_even a z).eventually_ne
      (exp_ne_zero _)] with k hk h0
    exact hk (by rw [h0, mul_zero])
  have hodd : ∀ᶠ k : ℕ in atTop,
      regularizedHGFun {((k + 1 : ℕ) : ℂ)} {a + (2 * k + 1 : ℕ)} z ≠ 0 := by
    filter_upwards [(tendsto_Gamma_mul_regularizedHGFun_odd a z).eventually_ne
      (exp_ne_zero _)] with k hk h0
    exact hk (by rw [h0, mul_zero])
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 heven
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 hodd
  rw [eventually_atTop]
  refine ⟨2 * max (max K₁ K₂) 1, fun n hn ↦ ?_⟩
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · have hk1 : 1 ≤ k := by omega
    rw [tricomiContFracSolution_two_mul a z hk1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)
      (pow_ne_zero _ hz)) (tricomiContFracNorm_ne_zero ha _)) (hK₁ k (by omega))
  · rw [tricomiContFracSolution_two_mul_add_one]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)
      (pow_ne_zero _ hz)) (tricomiContFracNorm_ne_zero ha _)) (hK₂ k (by omega))

/-- The `m`-th summand `(-1)^m (∏_{j=1}^m a_j) / (f(m) f(m + 1))` of the reduction-of-order series
for `tricomiContFrac a z`. -/
private def reductionTerm (a z : ℂ) (m : ℕ) : ℂ :=
  (-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFracPartNum a z j) /
    (tricomiContFracSolution a z m * tricomiContFracSolution a z (m + 1))

/-- Algebraic simplification of consecutive reduction-of-order summands: whenever `f(m + 1) ≠ 0` and
`∏_{j=1}^m a_j ≠ 0`, `T m / T (m + 1) = -f(m + 2) / (a_{m + 1} f(m))`. -/
private theorem reductionTerm_div_succ {a z : ℂ} {m : ℕ}
    (hprod : ∏ j ∈ Icc 1 m, tricomiContFracPartNum a z j ≠ 0)
    (hf1 : tricomiContFracSolution a z (m + 1) ≠ 0) :
    reductionTerm a z m / reductionTerm a z (m + 1) =
      -tricomiContFracSolution a z (m + 2) /
        (tricomiContFracPartNum a z (m + 1) * tricomiContFracSolution a z m) := by
  simp only [reductionTerm]
  rw [prod_Icc_succ_top (Nat.le_add_left 1 m), pow_succ (-1 : ℂ) m]
  have hpow : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases h0 : tricomiContFracPartNum a z (m + 1) * tricomiContFracSolution a z m = 0
  · rcases mul_eq_zero.mp h0 with ha1 | hfm
    · simp [ha1]
    · simp [hfm]
  · by_cases hf2 : tricomiContFracSolution a z (m + 2) = 0
    · simp [hf2]
    · have ha1 : tricomiContFracPartNum a z (m + 1) ≠ 0 := left_ne_zero_of_mul h0
      have hfm : tricomiContFracSolution a z m ≠ 0 := right_ne_zero_of_mul h0
      field_simp

/-- For `0 < s.re`, cancelling `Γ(s)` via `Γ(s + 2) = (s + 1) s Γ(s)` simplifies
`w * (c / s) * (1 / (s + 1)) * ((Γ(s + 2) * M') / (Γ(s) * M))` to `w * c * M' / M`. -/
private theorem mul_div_Gamma_add_two_eq (w : ℂ) {s c M M' : ℂ} (hs : 0 < s.re) :
    w * (c / s) * (1 / (s + 1)) * ((Gamma (s + 2) * M') / (Gamma s * M)) = w * c * M' / M := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hs1 : s + 1 ≠ 0 := fun h ↦ by
    have := congrArg re h; simp only [add_re, one_re, zero_re] at this; linarith
  have hGs : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have hG2 : Gamma (s + 2) = (s + 1) * (s * Gamma s) := by
    rw [show s + 2 = (s + 1) + 1 by ring, Gamma_add_one (s + 1) hs1, Gamma_add_one s hs0]
  rw [hG2]
  generalize s + 1 = s₁ at hs1 ⊢
  by_cases hM : M = 0
  · simp [hM]
  · field_simp

/-- Even-index consecutive ratio limit: `reductionTerm a z (2k) / reductionTerm a z (2k + 1) → 0`
as `k → ∞` for `a ∉ {-1, -2, …}` and `z ≠ 0`. -/
private theorem tendsto_reductionTerm_div_succ_even {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) :
    Tendsto (fun k : ℕ ↦ reductionTerm a z (2 * k) / reductionTerm a z (2 * k + 1))
      atTop (𝓝 0) := by
  have hG : Gamma (a + 1) ≠ 0 := Gamma_ne_zero fun k hk ↦ ha k (by linear_combination hk)
  have hE := tendsto_Gamma_mul_regularizedHGFun_even a z
  have hrat1 := tendsto_add_mul_div_add_mul_atTop_nhds a a (1 : ℂ) (d := 2) (by norm_num)
  have hrat2 := tendsto_add_mul_div_add_mul_atTop_nhds 1 (a + 1) (0 : ℂ) (d := 2) (by norm_num)
  have hquot := (hE.comp (tendsto_add_atTop_nat 1)).div hE (exp_ne_zero _)
  have hlim : Tendsto (fun k : ℕ ↦
      z * ((a + 1 * (k : ℂ)) / (a + 2 * k)) * ((1 + 0 * (k : ℂ)) / (a + 1 + 2 * k)) *
        ((Gamma (a + (2 * (k + 1) : ℕ)) *
            regularizedHGFun {((k + 1 : ℕ) : ℂ)} {a + (2 * (k + 1) : ℕ)} z) /
          (Gamma (a + (2 * k : ℕ)) * regularizedHGFun {(k : ℂ)} {a + (2 * k : ℕ)} z)))
      atTop (𝓝 0) := by
    simpa [div_self (exp_ne_zero (z / 2))] using ((hrat1.const_mul z).mul hrat2).mul hquot
  refine hlim.congr' ?_
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_tricomiContFracSolution_ne_zero ha hz)
  filter_upwards [eventually_ge_atTop (max N₀ 1), hE.eventually_ne (exp_ne_zero _),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (-a.re))] with k hk hEk hre
  have hk1 : 1 ≤ k := (le_max_right N₀ 1).trans hk
  have hprod := prod_Icc_tricomiContFracPartNum_ne_zero ha hz (2 * k)
  have hf1 : tricomiContFracSolution a z (2 * k + 1) ≠ 0 :=
    hN₀ _ (by have := le_max_left N₀ 1; omega)
  have hMk : regularizedHGFun {(k : ℂ)} {a + (2 * k : ℕ)} z ≠ 0 := right_ne_zero_of_mul hEk
  have hs : 0 < (a + (2 * k : ℕ)).re := by
    simp only [add_re, natCast_re]; push_cast; linarith [k.cast_nonneg (α := ℝ)]
  rw [one_mul, zero_mul, add_zero,
    show a + 2 * (k : ℂ) = a + (2 * k : ℕ) by push_cast; ring,
    show a + 1 + 2 * (k : ℂ) = a + (2 * k : ℕ) + 1 by push_cast; ring,
    show Gamma (a + (2 * (k + 1) : ℕ)) = Gamma (a + (2 * k : ℕ) + 2) by congr 1; push_cast; ring,
    mul_div_Gamma_add_two_eq z hs, reductionTerm_div_succ hprod hf1,
    show 2 * k + 2 = 2 * (k + 1) by ring, tricomiContFracSolution_two_mul a z (by omega),
    tricomiContFracSolution_two_mul a z hk1, tricomiContFracPartNum_two_mul_add_one a z hk1,
    tricomiContFracNorm_two_mul_succ_eq_mul a hk1, tricomiContFracNorm_two_mul_add_one_eq_mul a hk1,
    show 2 * (k + 1) - 1 = (2 * k - 1) + 2 by omega, pow_add z (2 * k - 1) 2, sq,
    pow_succ (-1 : ℂ) k]
  have hd : tricomiContFracNorm a (2 * k) ≠ 0 := tricomiContFracNorm_ne_zero ha _
  have hknz : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hzpow0 : z ^ (2 * k - 1) ≠ 0 := pow_ne_zero _ hz
  have hp1 : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Odd-index consecutive ratio limit: `reductionTerm a z (2k + 1) / reductionTerm a z (2k + 2) → 0`
as `k → ∞` for `a ∉ {-1, -2, …}` and `z ≠ 0`. -/
private theorem tendsto_reductionTerm_div_succ_odd {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) :
    Tendsto (fun k : ℕ ↦ reductionTerm a z (2 * k + 1) / reductionTerm a z (2 * k + 2))
      atTop (𝓝 0) := by
  have hG : Gamma (a + 1) ≠ 0 := Gamma_ne_zero fun k hk ↦ ha k (by linear_combination hk)
  have hO := tendsto_Gamma_mul_regularizedHGFun_odd a z
  have hrat1 := tendsto_add_mul_div_add_mul_atTop_nhds 1 (a + 1) (1 : ℂ) (d := 2) (by norm_num)
  have hrat2 := tendsto_add_mul_div_add_mul_atTop_nhds 1 (a + 2) (0 : ℂ) (d := 2) (by norm_num)
  have hquot := (hO.comp (tendsto_add_atTop_nat 1)).div hO (exp_ne_zero _)
  have hlim : Tendsto (fun k : ℕ ↦
      -z * ((1 + 1 * (k : ℂ)) / (a + 1 + 2 * k)) * ((1 + 0 * (k : ℂ)) / (a + 2 + 2 * k)) *
        ((Gamma (a + (2 * (k + 1) + 1 : ℕ)) *
            regularizedHGFun {((k + 1 + 1 : ℕ) : ℂ)} {a + (2 * (k + 1) + 1 : ℕ)} z) /
          (Gamma (a + (2 * k + 1 : ℕ)) *
            regularizedHGFun {((k + 1 : ℕ) : ℂ)} {a + (2 * k + 1 : ℕ)} z)))
      atTop (𝓝 0) := by
    simpa [div_self (exp_ne_zero (z / 2))] using ((hrat1.const_mul (-z)).mul hrat2).mul hquot
  refine hlim.congr' ?_
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_tricomiContFracSolution_ne_zero ha hz)
  filter_upwards [eventually_ge_atTop (max N₀ 1), hO.eventually_ne (exp_ne_zero _),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (-a.re))] with k hk hOk hre
  have hk1 : 1 ≤ k := (le_max_right N₀ 1).trans hk
  have hprod := prod_Icc_tricomiContFracPartNum_ne_zero ha hz (2 * k + 1)
  have hf1 := hN₀ (2 * k + 2) (by have := le_max_left N₀ 1; omega)
  have hMk := right_ne_zero_of_mul hOk
  have hs : 0 < (a + (2 * k + 1 : ℕ)).re := by
    simp only [add_re, natCast_re]; push_cast; linarith [k.cast_nonneg (α := ℝ)]
  have hak : a + k ≠ 0 := fun h ↦ ha (k - 1) (by
    have : ((k - 1 : ℕ) : ℂ) + 1 = k := by rw [Nat.cast_sub hk1]; push_cast; ring
    rw [this]; linear_combination h)
  rw [one_mul, zero_mul, add_zero,
    show a + 1 + 2 * (k : ℂ) = a + (2 * k + 1 : ℕ) by push_cast; ring,
    show a + 2 + 2 * (k : ℂ) = a + (2 * k + 1 : ℕ) + 1 by push_cast; ring,
    show Gamma (a + (2 * (k + 1) + 1 : ℕ)) = Gamma (a + (2 * k + 1 : ℕ) + 2) by
      congr 1; push_cast; ring,
    mul_div_Gamma_add_two_eq (-z) hs, show 2 * k + 2 = 2 * k + 1 + 1 from rfl,
    reductionTerm_div_succ hprod hf1, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
    tricomiContFracSolution_two_mul_add_one a z (k + 1),
    tricomiContFracSolution_two_mul_add_one a z k, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
    tricomiContFracPartNum_two_mul a z (by omega),
    tricomiContFracNorm_two_mul_add_one_eq_mul a (by omega),
    tricomiContFracNorm_two_mul_succ_eq_mul a hk1,
    show 2 * (k + 1) = 2 * k + 2 by ring, pow_add z (2 * k) 2, sq, pow_succ (-1 : ℂ) (k + 1),
    show a + ((k + 1 : ℕ) : ℂ) - 1 = a + k by push_cast; ring]
  have hd : tricomiContFracNorm a (2 * k + 1) ≠ 0 := tricomiContFracNorm_ne_zero ha _
  have hzpow0 : z ^ (2 * k) ≠ 0 := pow_ne_zero _ hz
  have hp1 : (-1 : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  generalize a + (k : ℂ) = qk at hak ⊢
  field_simp
  rw [show ((k + 1 : ℕ) : ℂ) = k + 1 by push_cast; ring]; ring

/-- For `a ∉ {-1, -2, …}` and `z ≠ 0`, `reductionTerm a z m` is eventually nonzero. -/
private theorem eventually_reductionTerm_ne_zero {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) :
    ∀ᶠ m in atTop, reductionTerm a z m ≠ 0 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_tricomiContFracSolution_ne_zero ha hz)
  filter_upwards [eventually_ge_atTop N₀] with m hm
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_Icc_tricomiContFracPartNum_ne_zero ha hz m))
    (mul_ne_zero (hN₀ m hm) (hN₀ (m + 1) (by omega)))

/-- Each reduction-of-order summand is little-o of its successor as `m → ∞`. -/
private theorem isLittleO_reductionTerm_succ {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) :
    reductionTerm a z =o[atTop] fun m ↦ reductionTerm a z (m + 1) := by
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [(tendsto_add_atTop_nat 1).eventually
      (eventually_reductionTerm_ne_zero ha hz)] with m hm h0
    exact absurd h0 hm
  · intro s hs
    obtain ⟨K₁, hK₁⟩ := eventually_atTop.1
      ((tendsto_reductionTerm_div_succ_even ha hz).eventually hs)
    obtain ⟨K₂, hK₂⟩ := eventually_atTop.1
      ((tendsto_reductionTerm_div_succ_odd ha hz).eventually hs)
    rw [Filter.mem_map, mem_atTop_sets]
    refine ⟨2 * max K₁ K₂ + 1, fun m hm ↦ ?_⟩
    rcases m.even_or_odd' with ⟨k, rfl | rfl⟩
    · exact hK₁ k (by omega)
    · exact hK₂ k (by omega)

/-- **Reduction-of-order divergence for DLMF 8.9.1**: for `a ∉ {-1, -2, …}`, `z ≠ 0`, and every
starting index `N`, the norms of the partial sums
`∑_{m = N}^{n - 1} (-1)^m (∏_{j=1}^m a_j) / (f(m) f(m + 1))` tend to `+∞` as `n → ∞`, showing that
`tricomiContFracSolution a z` is the minimal (recessive) solution of the three-term recurrence of
`tricomiContFrac a z`. -/
theorem tendsto_norm_sum_tricomiContFrac_reductionOfOrder {a z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k + 1 : ℂ)) (hz : z ≠ 0) (N : ℕ) :
    Tendsto (fun n ↦ ‖∑ m ∈ Ico N n,
      (-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFracPartNum a z j) /
        (tricomiContFracSolution a z m * tricomiContFracSolution a z (m + 1))‖)
      atTop atTop :=
  (isLittleO_reductionTerm_succ ha hz).tendsto_norm_sum_Ico_atTop
    ((eventually_reductionTerm_ne_zero ha hz).mono fun _ hm ↦ norm_pos_iff.mpr hm).frequently N

end Complex
