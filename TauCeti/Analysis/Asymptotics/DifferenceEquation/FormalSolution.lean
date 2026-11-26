/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Binomial
import TauCeti.Analysis.Asymptotics.TruncatedPowerSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Formal solutions of second-order linear difference equations

Consider the difference equation

  `w (n + 2) + f n * w (n + 1) + g n * w n = 0`

whose coefficients have expansions `f n ∼ ∑ fₛ n⁻ˢ` and `g n ∼ ∑ gₛ n⁻ˢ` as `n → ∞`. Let `ρ` be
a root of the characteristic equation `ρ² + f₀ ρ + g₀ = 0`, and let `α` satisfy
`α (f₀ ρ + 2 g₀) = f₁ ρ + g₁`. Substituting the formal series `ρⁿ n^α ∑ aₛ n⁻ˢ` into the equation
leads to the recursion

  `ρ (f₀ + 2ρ) s aₛ = ∑_{r=1}^{s} (ρ² 2^{r+1} C(α+r-s, r+1)
    + ρ ∑_{q=0}^{r+1} C(α+r-s, r+1-q) f_q + g_{r+1}) a_{s-r}`

of DLMF 2.9.7, where `C(c, m)` is the binomial coefficient `Ring.choose c m`. This file proves
that the formal series then satisfies the equation to every order: if `f` and `g` are known up
to `O(n^{-N-1})`, the truncation after `N` terms leaves a residual
`O(|ρ|ⁿ n^{Re α - N - 1})` (`TauCeti.isBigO_formalDifferenceSolution_residual`).

When `ρ (f₀ + 2ρ) ≠ 0`, the recursion determines the coefficients once `a₀` is fixed
(`TauCeti.differenceCoeff`, normalized by `a₀ = 1`). For a root `ρ` of the characteristic equation
this is DLMF's case of distinct characteristic roots under its assumption `g₀ ≠ 0`: then `ρ ≠ 0`,
and `f₀ + 2ρ ≠ 0` says that `ρ` differs from the other root `-f₀ - ρ`. The actual
solutions with the expansions `w(n) ∼ ρⁿ n^α ∑ aₛ n⁻ˢ` (DLMF 2.9.8) are obtained from these
truncated formal solutions by solving a Volterra summation equation for the error, whose forcing
term is the residual estimated here (Wong and Li); for the root of smaller modulus this is done in
`TauCeti.Analysis.Asymptotics.DifferenceEquation.Recessive`.

## Main definitions

* `TauCeti.differenceKernel fs gs ρ c r`: the coefficient
  `ρ² 2^r C(c, r) + ρ ∑_{q ≤ r} f_q C(c, r - q) + g_r`, which multiplies `aₖ` in the coefficient
  of `ρⁿ n^{α-k-r}` after substitution, with `c = α - k`.
* `TauCeti.differenceResidualCoeff fs gs ρ α a t`: the coefficient of `ρⁿ n^{α-t}` in the
  residual of the formal series `ρⁿ n^α ∑ aₛ n⁻ˢ`.
* `TauCeti.formalDifferenceSolution a ρ α N n`: the truncation `ρⁿ n^α ∑_{s<N} aₛ n⁻ˢ`.
* `TauCeti.differenceCoeff fs gs ρ α`: the coefficients defined by DLMF 2.9.7 with `a₀ = 1`,
  which satisfy that recursion when `ρ (f₀ + 2ρ) ≠ 0`.

## Main results

* `TauCeti.isBigO_formalDifferenceSolution_sub`: for `N ≤ M`, the truncations after `M` and after
  `N` terms differ by `O(|ρ|ⁿ n^{Re α - N})`.
* `TauCeti.isEquivalent_formalDifferenceSolution`: for `M ≥ 1` and `a₀ = 1`, the truncation
  after `M` terms is asymptotic to `ρⁿ n^α`.
* `TauCeti.isBigO_formalDifferenceSolution_residual_sub`: for arbitrary coefficients `a`, the
  residual of the truncation after `N + 1` terms is
  `ρⁿ n^α ∑_{t ≤ N} (differenceResidualCoeff fs gs ρ α a t) n⁻ᵗ + O(|ρ|ⁿ n^{Re α - N - 1})`.
* `TauCeti.differenceResidualCoeff_congr`: for a root `ρ` of the characteristic equation, the
  coefficient of `ρⁿ n^{α-t}` in the residual depends only on `aₛ` for `s < t`.
* `TauCeti.differenceResidualCoeff_eq_zero`: under DLMF 2.9.5–2.9.7 the residual coefficients
  vanish.
* `TauCeti.isBigO_formalDifferenceSolution_residual`: under DLMF 2.9.5–2.9.7 the truncation after
  `N` terms has residual `O(|ρ|ⁿ n^{Re α - N - 1})`.
* `TauCeti.mul_differenceCoeff`: `TauCeti.differenceCoeff` satisfies DLMF 2.9.7 when
  `ρ (f₀ + 2ρ) ≠ 0`.
* `TauCeti.differenceCoeff_succ_eq_zero_of_const`: for constant coefficients and `α = 0` the
  coefficients `aₛ` with `s ≥ 1` vanish, so for a root `ρ` of the characteristic equation the formal
  solution is `ρⁿ`.

## Implementation notes

The residual is `ρⁿ n^α` times a function of `u = n⁻¹`, built from the binomial
expansions of `(1 + j u)^{α - s}` for `j = 0, 1, 2`
(`TauCeti.isBigO_one_add_mul_cpow_sub_eval_trunc`)
and the expansions of `f` and `g`. These are combined as finite-order power-series expansions
`F - (trunc (N + 1) P).eval u = O(u^{N+1})`, which are compatible with sums and products
(`PowerSeries.isBigO_mul_sub_eval_trunc_mul` and its companions).

## References

* NIST Digital Library of Mathematical Functions, §2.9(i), equations (2.9.1)–(2.9.8),
  <https://dlmf.nist.gov/2.9.i>.
* R. Wong and H. Li, Asymptotic expansions for second-order linear difference equations,
  *J. Comput. Appl. Math.* 41 (1992), 65–94.
-/

public section

open Filter Finset Asymptotics
open scoped Topology

namespace TauCeti

/-! ### The coefficients of the residual -/

/-- The coefficient `ρ² 2^r C(c, r) + ρ ∑_{q ≤ r} f_q C(c, r - q) + g_r`. In the residual of the
formal series `ρⁿ n^α ∑ aₖ n⁻ᵏ`, it multiplies `aₖ` in the coefficient of `ρⁿ n^{α-k-r}`, with
`c = α - k`. -/
noncomputable def differenceKernel (fs gs : ℕ → ℂ) (ρ c : ℂ) (r : ℕ) : ℂ :=
  ρ ^ 2 * 2 ^ r * Ring.choose c r + ρ * ∑ q ∈ range (r + 1), fs q * Ring.choose c (r - q) + gs r

theorem differenceKernel_def (fs gs : ℕ → ℂ) (ρ c : ℂ) (r : ℕ) :
    differenceKernel fs gs ρ c r =
      ρ ^ 2 * 2 ^ r * Ring.choose c r + ρ * ∑ q ∈ range (r + 1), fs q * Ring.choose c (r - q) +
        gs r := (rfl)

/-- The kernel of order zero is the characteristic polynomial `ρ² + f₀ ρ + g₀`. -/
@[simp]
theorem differenceKernel_zero (fs gs : ℕ → ℂ) (ρ c : ℂ) :
    differenceKernel fs gs ρ c 0 = ρ ^ 2 + fs 0 * ρ + gs 0 := by
  simp [differenceKernel]
  ring

/-- The coefficient of `ρⁿ n^{α-t}` in the residual
`w (n + 2) + f n * w (n + 1) + g n * w n` of the formal series `w n = ρⁿ n^α ∑ aₛ n⁻ˢ`, when
`f n = ∑ f_q n^{-q}` and `g n = ∑ g_q n^{-q}`. -/
noncomputable def differenceResidualCoeff (fs gs : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) (t : ℕ) : ℂ :=
  ∑ s ∈ range (t + 1), a s * differenceKernel fs gs ρ (α - s) (t - s)

theorem differenceResidualCoeff_def (fs gs : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) (t : ℕ) :
    differenceResidualCoeff fs gs ρ α a t =
      ∑ s ∈ range (t + 1), a s * differenceKernel fs gs ρ (α - s) (t - s) := (rfl)

/-- The right-hand side of DLMF 2.9.7, summed over `r ∈ [1, s]`, as a sum over `k = s - r`. -/
private lemma sum_Icc_differenceKernel (fs gs : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) (s : ℕ) :
    ∑ r ∈ Icc 1 s, differenceKernel fs gs ρ (α + r - s) (r + 1) * a (s - r) =
      ∑ k ∈ range s, differenceKernel fs gs ρ (α - k) (s + 1 - k) * a k := by
  have h := sum_Ico_reflect (fun k ↦ differenceKernel fs gs ρ (α - k) (s + 1 - k) * a k) 1
    (le_refl (s + 1))
  rw [Nat.sub_self, Nat.add_sub_cancel] at h
  rw [range_eq_Ico, ← h, ← Ico_add_one_right_eq_Icc]
  refine sum_congr rfl fun r hr ↦ ?_
  have hrs : r ≤ s := Nat.lt_succ_iff.1 (mem_Ico.1 hr).2
  have e1 : (α + r - s : ℂ) = α - ((s - r : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hrs]
    ring
  have e2 : r + 1 = s + 1 - (s - r) := by omega
  rw [e1, e2]

/-- If `ρ` is a root of the characteristic equation `ρ² + f₀ ρ + g₀ = 0` (DLMF 2.9.5), `α`
satisfies `α (f₀ ρ + 2 g₀) = f₁ ρ + g₁` (DLMF 2.9.6) and `a` satisfies the recursion DLMF 2.9.7,
for `s < t`, then the coefficient of `ρⁿ n^{α-t}` in the residual of the formal series
`ρⁿ n^α ∑ aₛ n⁻ˢ` vanishes. In particular, if DLMF 2.9.7 holds for every `s`, the formal series
solves the difference equation formally. -/
theorem differenceResidualCoeff_eq_zero {fs gs : ℕ → ℂ} {ρ α : ℂ} {a : ℕ → ℂ} {t : ℕ}
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1)
    (ha : ∀ s < t, ρ * (fs 0 + 2 * ρ) * s * a s =
      ∑ r ∈ Icc 1 s, differenceKernel fs gs ρ (α + r - s) (r + 1) * a (s - r)) :
    differenceResidualCoeff fs gs ρ α a t = 0 := by
  cases t with
  | zero => simp [differenceResidualCoeff, hρ]
  | succ t =>
    -- the coefficient of `a t` is `-t ρ (f₀ + 2ρ)`, and that of `a (t + 1)` vanishes
    have h1 : differenceKernel fs gs ρ (α - t) 1 = -(ρ * (fs 0 + 2 * ρ) * t) := by
      simp only [differenceKernel, sum_range_succ, sum_range_zero, Ring.choose_one_right,
        Ring.choose_zero_right, Nat.sub_self, Nat.sub_zero]
      linear_combination (2 * α) * hρ - hα
    -- the remaining terms are the right-hand side of DLMF 2.9.7 at `s = t`
    have hk : ∑ s ∈ range t, a s * differenceKernel fs gs ρ (α - s) (t + 1 - s) =
        ρ * (fs 0 + 2 * ρ) * t * a t := by
      rw [ha t (lt_add_one t), sum_Icc_differenceKernel]
      exact sum_congr rfl fun _ _ ↦ mul_comm _ _
    simp only [differenceResidualCoeff, sum_range_succ, hk, Nat.add_sub_cancel_left, h1,
      Nat.sub_self, differenceKernel_zero, hρ]
    ring

/-- If `ρ` is a root of the characteristic equation `ρ² + f₀ ρ + g₀ = 0`, the coefficient of
`ρⁿ n^{α-t}` in the residual depends only on the coefficients `aₛ` with `s < t`. -/
theorem differenceResidualCoeff_congr {fs gs : ℕ → ℂ} {ρ : ℂ} (α : ℂ) {a b : ℕ → ℂ} {t : ℕ}
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (h : ∀ s < t, a s = b s) :
    differenceResidualCoeff fs gs ρ α a t = differenceResidualCoeff fs gs ρ α b t := by
  simp only [differenceResidualCoeff, sum_range_succ, Nat.sub_self, differenceKernel_zero, hρ,
    mul_zero, add_zero]
  exact sum_congr rfl fun s hs ↦ by rw [h s (mem_range.1 hs)]

/-! ### The truncated formal solutions -/

/-- The truncation `ρⁿ n^α ∑_{s<N} aₛ n⁻ˢ` of the formal solution of a difference equation. -/
noncomputable def formalDifferenceSolution (a : ℕ → ℂ) (ρ α : ℂ) (N n : ℕ) : ℂ :=
  ρ ^ n * (n : ℂ) ^ α * ∑ s ∈ range N, a s * (n : ℂ)⁻¹ ^ s

theorem formalDifferenceSolution_def (a : ℕ → ℂ) (ρ α : ℂ) (N n : ℕ) :
    formalDifferenceSolution a ρ α N n = ρ ^ n * (n : ℂ) ^ α * ∑ s ∈ range N, a s * (n : ℂ)⁻¹ ^ s :=
  (rfl)

/-- For `n ≠ 0`, the shifted truncation at `n + j` is `ρⁿ n^α` times
`ρʲ ∑_{s<N} aₛ n⁻ˢ (1 + j n⁻¹)^{α-s}`. -/
private lemma formalDifferenceSolution_add (a : ℕ → ℂ) (ρ α : ℂ) (N : ℕ) {n : ℕ} (hn : n ≠ 0)
    (j : ℕ) : formalDifferenceSolution a ρ α N (n + j) = ρ ^ n * (n : ℂ) ^ α *
      (ρ ^ j * ∑ s ∈ range N, a s * (n : ℂ)⁻¹ ^ s * (1 + j * (n : ℂ)⁻¹) ^ (α - s)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hpos : (1 + j * (n : ℂ)⁻¹) ≠ 0 := by
    rw [show (1 + j * (n : ℂ)⁻¹) = ((n + j : ℕ) : ℂ) / n by field_simp; push_cast; ring]
    exact div_ne_zero (Nat.cast_ne_zero.2 (by omega)) hn'
  have hsplit : ((n + j : ℕ) : ℂ) = n * (1 + j * (n : ℂ)⁻¹) := by
    field_simp
    push_cast
    ring
  simp only [formalDifferenceSolution, hsplit, Complex.natCast_mul_cpow, mul_sum]
  refine sum_congr rfl fun s _ ↦ ?_
  simp only [Complex.cpow_sub _ _ hpos, Complex.cpow_natCast, mul_inv, mul_pow, div_eq_mul_inv]
  ring

/-- The left-hand side of the difference equation at the truncated formal solution is `ρⁿ n^α`
times a sum over `s < N` of `aₛ n⁻ˢ` times an expression in `(1 + j n⁻¹)^{α-s}`. -/
private lemma formalDifferenceSolution_residual_eq (f g a : ℕ → ℂ) (ρ α : ℂ) (N : ℕ) {n : ℕ}
    (hn : n ≠ 0) :
    formalDifferenceSolution a ρ α N (n + 2) + f n * formalDifferenceSolution a ρ α N (n + 1) +
        g n * formalDifferenceSolution a ρ α N n =
      ρ ^ n * (n : ℂ) ^ α * ∑ s ∈ range N, a s * (n : ℂ)⁻¹ ^ s *
        (ρ ^ 2 * (1 + ((2 : ℕ) : ℂ) * (n : ℂ)⁻¹) ^ (α - s) +
          ρ * f n * (1 + ((1 : ℕ) : ℂ) * (n : ℂ)⁻¹) ^ (α - s) +
          g n * (1 + ((0 : ℕ) : ℂ) * (n : ℂ)⁻¹) ^ (α - s)) := by
  have h0 := formalDifferenceSolution_add a ρ α N hn 0
  rw [add_zero] at h0
  rw [formalDifferenceSolution_add a ρ α N hn 2, formalDifferenceSolution_add a ρ α N hn 1, h0]
  simp only [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun s _ ↦ by ring

private lemma mk_choose_mul_zero_pow (c : ℂ) :
    PowerSeries.mk (fun m ↦ Ring.choose c m * ((0 : ℕ) : ℂ) ^ m) = 1 := by
  ext m
  rcases m with _ | m <;> simp [PowerSeries.coeff_one]

/-- The power series `ρ² B₂ + ρ F B₁ + G B₀`, where `Bⱼ = ∑ C(c, m) jᵐ Xᵐ` is the binomial
series of `(1 + j X)^c`, `F = ∑ f_q X^q` and `G = ∑ g_q X^q`. Its coefficients are the kernels
`differenceKernel fs gs ρ c r` (`coeff_kernelSeries`). -/
private noncomputable def kernelSeries (fs gs : ℕ → ℂ) (ρ c : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (ρ ^ 2) * PowerSeries.mk (fun m ↦ Ring.choose c m * ((2 : ℕ) : ℂ) ^ m) +
    PowerSeries.C ρ * PowerSeries.mk fs *
      PowerSeries.mk (fun m ↦ Ring.choose c m * ((1 : ℕ) : ℂ) ^ m) +
    PowerSeries.mk gs * PowerSeries.mk (fun m ↦ Ring.choose c m * ((0 : ℕ) : ℂ) ^ m)

private lemma coeff_kernelSeries (fs gs : ℕ → ℂ) (ρ c : ℂ) (r : ℕ) :
    PowerSeries.coeff r (kernelSeries fs gs ρ c) = differenceKernel fs gs ρ c r := by
  simp only [kernelSeries, mk_choose_mul_zero_pow, mul_one, mul_assoc, map_add,
    PowerSeries.coeff_C_mul]
  simp [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, differenceKernel]
  ring

/-- The coefficients of `∑_{s<N} aₛ Xˢ Lₛ`, where `Lₛ` is the kernel series at `c = α - s`. -/
private lemma coeff_sum_kernelSeries (fs gs : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) {N t : ℕ}
    (ht : t < N) :
    PowerSeries.coeff t (∑ s ∈ range N, PowerSeries.C (a s) * PowerSeries.X ^ s *
        kernelSeries fs gs ρ (α - s)) = differenceResidualCoeff fs gs ρ α a t := by
  simp only [map_sum, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  rw [differenceResidualCoeff, ← sum_range_add_sum_Ico _ (Nat.succ_le_of_lt ht),
    sum_eq_zero (s := Ico (t + 1) N) fun k hk ↦ ?_, add_zero]
  · refine sum_congr rfl fun s hs ↦ ?_
    simp only [Nat.lt_succ_iff.1 (mem_range.1 hs), ↓reduceIte, coeff_kernelSeries]
  · have hk' : ¬k ≤ t := by have := (mem_Ico.1 hk).1; omega
    simp [hk']

/-- If `f` and `g` have the expansions `∑ f_q n^{-q}` and `∑ g_q n^{-q}` to order `M + 1`, then
`ρ² (1 + 2n⁻¹)^c + ρ f n (1 + n⁻¹)^c + g n` has the expansion `kernelSeries fs gs ρ c`. -/
private lemma isBigO_sub_eval_trunc_kernelSeries {f g fs gs : ℕ → ℂ} (ρ c : ℂ) {M : ℕ}
    (hF : (fun n : ℕ ↦ f n - (PowerSeries.trunc (M + 1) (PowerSeries.mk fs)).eval (n : ℂ)⁻¹)
      =O[atTop] fun n ↦ (n : ℂ)⁻¹ ^ (M + 1))
    (hG : (fun n : ℕ ↦ g n - (PowerSeries.trunc (M + 1) (PowerSeries.mk gs)).eval (n : ℂ)⁻¹)
      =O[atTop] fun n ↦ (n : ℂ)⁻¹ ^ (M + 1)) :
    (fun n : ℕ ↦ ρ ^ 2 * (1 + ((2 : ℕ) : ℂ) * (n : ℂ)⁻¹) ^ c +
        ρ * f n * (1 + ((1 : ℕ) : ℂ) * (n : ℂ)⁻¹) ^ c +
        g n * (1 + ((0 : ℕ) : ℂ) * (n : ℂ)⁻¹) ^ c -
      (PowerSeries.trunc (M + 1) (kernelSeries fs gs ρ c)).eval (n : ℂ)⁻¹) =O[atTop]
      fun n ↦ (n : ℂ)⁻¹ ^ (M + 1) := by
  have hu : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hC (z : ℂ) := Polynomial.isBigO_eval_sub_eval_trunc_coe hu (M + 1) (Polynomial.C z)
  have hB (j : ℕ) := isBigO_one_add_mul_cpow_sub_eval_trunc hu (j : ℂ) c (M + 1)
  refine (PowerSeries.isBigO_add_sub_eval_trunc_add (PowerSeries.isBigO_add_sub_eval_trunc_add
    (PowerSeries.isBigO_mul_sub_eval_trunc_mul hu (hC (ρ ^ 2))
      (hB 2))
    (PowerSeries.isBigO_mul_sub_eval_trunc_mul hu
      (PowerSeries.isBigO_mul_sub_eval_trunc_mul hu (hC ρ) hF)
      (hB 1)))
    (PowerSeries.isBigO_mul_sub_eval_trunc_mul hu hG
      (hB 0))).congr_left fun n ↦ ?_
  simp only [Polynomial.coe_C, Polynomial.eval_C, kernelSeries]

/-- For `N ≤ M`, the truncations of `ρⁿ n^α ∑ aₛ n⁻ˢ` after `M` and after `N` terms differ by
`O(|ρ|ⁿ n^{Re α - N})`. -/
theorem isBigO_formalDifferenceSolution_sub (a : ℕ → ℂ) (ρ α : ℂ) {N M : ℕ} (h : N ≤ M) :
    (fun n ↦ formalDifferenceSolution a ρ α M n - formalDifferenceSolution a ρ α N n) =O[atTop]
      fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - N) := by
  refine IsBigO.of_bound (∑ s ∈ Ico N M, ‖a s‖) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [formalDifferenceSolution_def, formalDifferenceSolution_def, ← mul_sub, ← sum_Ico_eq_sub _ h,
    mul_sum, Real.norm_of_nonneg (by positivity), sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s hs ↦ ?_)
  rw [show ρ ^ n * (n : ℂ) ^ α * (a s * (n : ℂ)⁻¹ ^ s) =
      a s * (ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ s) by ring, norm_mul,
    norm_pow_mul_cpow_mul_inv_pow ρ α s (by omega)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn' ?_) (by positivity)) (norm_nonneg _)
  have := (mem_Ico.1 hs).1
  have : (N : ℝ) ≤ s := by exact_mod_cast this
  linarith

/-- For `M ≥ 1` and `a₀ = 1`, the truncation `ρⁿ n^α ∑_{s < M} aₛ n⁻ˢ` is asymptotic to its
leading term `ρⁿ n^α`. -/
theorem isEquivalent_formalDifferenceSolution {a : ℕ → ℂ} (ha : a 0 = 1) (ρ α : ℂ) {M : ℕ}
    (hM : 1 ≤ M) :
    formalDifferenceSolution a ρ α M ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α := by
  have hu₁ : formalDifferenceSolution a ρ α 1 = fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α := by
    ext n
    simp [formalDifferenceSolution_def, ha]
  have h := isBigO_formalDifferenceSolution_sub a ρ α hM
  rw [hu₁, Nat.cast_one] at h
  exact h.trans_isLittleO (isLittleO_norm_pow_mul_rpow_pow_mul_cpow ρ (sub_one_lt α.re))

/-- **Residual of a truncated formal solution.** Let `f` and `g` have the expansions
`f n = ∑_{q ≤ N} f_q n^{-q} + O(n^{-N-1})` and `g n = ∑_{q ≤ N} g_q n^{-q} + O(n^{-N-1})`. For
any coefficients `a`, the truncation `w n = ρⁿ n^α ∑_{s ≤ N} aₛ n⁻ˢ` satisfies

  `w (n + 2) + f n * w (n + 1) + g n * w n = ρⁿ n^α ∑_{t ≤ N} cₜ n⁻ᵗ + O(|ρ|ⁿ n^{Re α - N - 1})`,

where `cₜ = differenceResidualCoeff fs gs ρ α a t` are the coefficients obtained by formal
substitution. -/
theorem isBigO_formalDifferenceSolution_residual_sub {f g fs gs : ℕ → ℂ} (ρ α : ℂ)
    (a : ℕ → ℂ) {N : ℕ}
    (hf : (fun n : ℕ ↦ f n - ∑ q ∈ range (N + 1), ((n : ℂ) ^ q)⁻¹ • fs q) =O[atTop]
      fun n ↦ ((n : ℂ) ^ (N + 1))⁻¹)
    (hg : (fun n : ℕ ↦ g n - ∑ q ∈ range (N + 1), ((n : ℂ) ^ q)⁻¹ • gs q) =O[atTop]
      fun n ↦ ((n : ℂ) ^ (N + 1))⁻¹) :
    (fun n : ℕ ↦ formalDifferenceSolution a ρ α (N + 1) (n + 2) +
        f n * formalDifferenceSolution a ρ α (N + 1) (n + 1) +
        g n * formalDifferenceSolution a ρ α (N + 1) n -
        ρ ^ n * (n : ℂ) ^ α *
          ∑ t ∈ range (N + 1), differenceResidualCoeff fs gs ρ α a t * (n : ℂ)⁻¹ ^ t) =O[atTop]
      fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - (N + 1)) := by
  have hu : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hF := PowerSeries.isBigO_sub_eval_trunc_mk_of_isBigO_sub_sum_inv_pow hf
  have hG := PowerSeries.isBigO_sub_eval_trunc_mk_of_isBigO_sub_sum_inv_pow hg
  -- each term `aₛ n⁻ˢ (ρ² (1 + 2n⁻¹)^{α-s} + ρ f (1 + n⁻¹)^{α-s} + g)` and its series
  have hterm := PowerSeries.isBigO_sum_sub_eval_trunc_sum (range (N + 1)) fun s _ ↦
    PowerSeries.isBigO_mul_sub_eval_trunc_mul hu
      (Polynomial.isBigO_eval_sub_eval_trunc_coe hu (N + 1) (Polynomial.C (a s) * Polynomial.X ^ s))
      (isBigO_sub_eval_trunc_kernelSeries ρ (α - s) hF hG)
  have hmain := (isBigO_refl (fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) atTop).mul hterm
  refine (hmain.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)).trans ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      PowerSeries.eval_trunc]
    rw [formalDifferenceSolution_residual_eq f g a ρ α (N + 1) hn, ← mul_sub]
    congr 2
    exact sum_congr rfl fun t ht ↦ by rw [coeff_sum_kernelSeries fs gs ρ α a (mem_range.1 ht)]
  · refine IsBigO.of_bound' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [norm_pow_mul_cpow_mul_inv_pow ρ α (N + 1) hn, Real.norm_of_nonneg (by positivity),
      Nat.cast_add_one]

/-- **The formal solutions satisfy the difference equation to every order** (DLMF 2.9.4–2.9.7).
Let `f n = ∑_{q ≤ N} f_q n^{-q} + O(n^{-N-1})` and `g n = ∑_{q ≤ N} g_q n^{-q} + O(n^{-N-1})`,
let `ρ` be a root of the characteristic equation `ρ² + f₀ ρ + g₀ = 0` (DLMF 2.9.5), let
`α (f₀ ρ + 2 g₀) = f₁ ρ + g₁` (DLMF 2.9.6), and let the coefficients `a` satisfy the recursion
DLMF 2.9.7. Then the truncation `w n = ρⁿ n^α ∑_{s<N} aₛ n⁻ˢ` satisfies

  `w (n + 2) + f n * w (n + 1) + g n * w n = O(|ρ|ⁿ n^{Re α - N - 1})`. -/
theorem isBigO_formalDifferenceSolution_residual {f g fs gs : ℕ → ℂ} {ρ α : ℂ} {a : ℕ → ℂ}
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1)
    {N : ℕ} (ha : ∀ s < N, ρ * (fs 0 + 2 * ρ) * s * a s =
      ∑ r ∈ Icc 1 s, differenceKernel fs gs ρ (α + r - s) (r + 1) * a (s - r))
    (hf : (fun n : ℕ ↦ f n - ∑ q ∈ range (N + 1), ((n : ℂ) ^ q)⁻¹ • fs q) =O[atTop]
      fun n ↦ ((n : ℂ) ^ (N + 1))⁻¹)
    (hg : (fun n : ℕ ↦ g n - ∑ q ∈ range (N + 1), ((n : ℂ) ^ q)⁻¹ • gs q) =O[atTop]
      fun n ↦ ((n : ℂ) ^ (N + 1))⁻¹) :
    (fun n : ℕ ↦ formalDifferenceSolution a ρ α N (n + 2) +
        f n * formalDifferenceSolution a ρ α N (n + 1) +
        g n * formalDifferenceSolution a ρ α N n) =O[atTop]
      fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - (N + 1)) := by
  -- extend the truncated coefficients by `0` at index `N`
  set a' : ℕ → ℂ := fun s ↦ if s < N then a s else 0
  have hsol (n : ℕ) :
      formalDifferenceSolution a' ρ α (N + 1) n = formalDifferenceSolution a ρ α N n := by
    simp only [formalDifferenceSolution, sum_range_succ, a', lt_irrefl, ↓reduceIte, zero_mul,
      add_zero]
    exact congrArg _ (sum_congr rfl fun s hs ↦ by simp [mem_range.1 hs])
  -- the residual coefficients of `a'` vanish, since they do not see `a' N`
  have hres (t : ℕ) (ht : t ∈ range (N + 1)) : differenceResidualCoeff fs gs ρ α a' t = 0 := by
    have htN := Nat.lt_succ_iff.1 (mem_range.1 ht)
    rw [differenceResidualCoeff_congr (a := a') (b := a) α hρ fun s hs ↦ by
      simp [a', hs.trans_le htN]]
    exact differenceResidualCoeff_eq_zero hρ hα fun s hs ↦ ha s (hs.trans_le htN)
  have hzero (n : ℕ) : ∑ t ∈ range (N + 1),
      differenceResidualCoeff fs gs ρ α a' t * (n : ℂ)⁻¹ ^ t = 0 :=
    sum_eq_zero fun t ht ↦ by rw [hres t ht, zero_mul]
  have h := isBigO_formalDifferenceSolution_residual_sub ρ α a' hf hg
  simp only [hsol, hzero, mul_zero, sub_zero] at h
  exact h

/-! ### The coefficients of DLMF 2.9.7 -/

/-- The coefficients `aₛ` of the formal solution `ρⁿ n^α ∑ aₛ n⁻ˢ` of a difference equation,
defined by the recursion of DLMF 2.9.7 with `a₀ = 1`. When `ρ (f₀ + 2ρ) ≠ 0`, which for a root `ρ`
of `ρ² + f₀ ρ + g₀ = 0` with `g₀ ≠ 0` means that the characteristic roots are distinct, they
satisfy that recursion (`TauCeti.mul_differenceCoeff`). -/
noncomputable def differenceCoeff (fs gs : ℕ → ℂ) (ρ α : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 => (ρ * (fs 0 + 2 * ρ) * (s + 1))⁻¹ *
      ∑ k : Fin (s + 1), differenceKernel fs gs ρ (α - k) (s + 2 - k) * differenceCoeff fs gs ρ α k

@[simp]
theorem differenceCoeff_zero (fs gs : ℕ → ℂ) (ρ α : ℂ) : differenceCoeff fs gs ρ α 0 = 1 := by
  rw [differenceCoeff]

theorem differenceCoeff_succ (fs gs : ℕ → ℂ) (ρ α : ℂ) (s : ℕ) :
    differenceCoeff fs gs ρ α (s + 1) = (ρ * (fs 0 + 2 * ρ) * (s + 1))⁻¹ *
      ∑ k ∈ range (s + 1), differenceKernel fs gs ρ (α - k) (s + 2 - k) *
        differenceCoeff fs gs ρ α k := by
  rw [differenceCoeff, Fin.sum_univ_eq_sum_range
    (fun k ↦ differenceKernel fs gs ρ (α - k) (s + 2 - k) * differenceCoeff fs gs ρ α k)]

/-- `TauCeti.differenceCoeff` satisfies the recursion DLMF 2.9.7
`ρ (f₀ + 2ρ) s aₛ = ∑_{r=1}^{s} (ρ² 2^{r+1} C(α+r-s, r+1) + ρ ∑_{q=0}^{r+1} C(α+r-s, r+1-q) f_q
+ g_{r+1}) a_{s-r}`. -/
theorem mul_differenceCoeff {fs gs : ℕ → ℂ} {ρ : ℂ} (hρ₀ : ρ * (fs 0 + 2 * ρ) ≠ 0) (α : ℂ)
    (s : ℕ) : ρ * (fs 0 + 2 * ρ) * s * differenceCoeff fs gs ρ α s =
      ∑ r ∈ Icc 1 s, differenceKernel fs gs ρ (α + r - s) (r + 1) *
        differenceCoeff fs gs ρ α (s - r) := by
  rw [sum_Icc_differenceKernel]
  cases s with
  | zero => simp
  | succ s =>
    rw [differenceCoeff_succ, ← mul_assoc, Nat.cast_succ,
      mul_inv_cancel₀ (mul_ne_zero hρ₀ (Nat.cast_add_one_ne_zero s)), one_mul]

/-- For an equation with constant coefficients, `f n = f₀` and `g n = g₀`, and `α = 0`, all the
coefficients `aₛ` with `s ≥ 1` vanish, for every `ρ`. So when `ρ` is a root of the characteristic
equation `ρ² + f₀ ρ + g₀ = 0` (and `α = 0` satisfies DLMF 2.9.6), the formal solution is `ρⁿ`,
which is an exact solution. For instance, for
`w (n + 2) - 3 w (n + 1) + 2 w n = 0` the roots are `ρ = 1, 2`, DLMF 2.9.6 gives `α = 0`, and the
formal solutions are `1` and `2ⁿ`. -/
theorem differenceCoeff_succ_eq_zero_of_const {fs gs : ℕ → ℂ} (hf : ∀ q ≠ 0, fs q = 0)
    (hg : ∀ q ≠ 0, gs q = 0) (ρ : ℂ) (s : ℕ) : differenceCoeff fs gs ρ 0 (s + 1) = 0 := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    -- the terms with `k ≥ 1` vanish by induction, and the kernel multiplying `a₀` vanishes
    have hsum : ∑ k ∈ range s,
        differenceKernel fs gs ρ (0 - ((k + 1 : ℕ) : ℂ)) (s + 2 - (k + 1)) *
          differenceCoeff fs gs ρ 0 (k + 1) = 0 :=
      sum_eq_zero fun k hk ↦ by rw [ih k (mem_range.1 hk), mul_zero]
    have hfq : ∑ q ∈ range (s + 3), fs q * Ring.choose (0 : ℂ) (s + 2 - q) = 0 :=
      sum_eq_zero fun q _ ↦ by
        rcases eq_or_ne q 0 with rfl | hq
        · rw [Ring.choose_zero_pos ℂ (by omega), mul_zero]
        · rw [hf q hq, zero_mul]
    have hker : differenceKernel fs gs ρ 0 (s + 2) = 0 := by
      simp [differenceKernel, hfq, Ring.choose_zero_pos ℂ (show 0 < s + 2 by omega), hg]
    rw [differenceCoeff_succ, sum_range_succ', hsum]
    simp [hker]

end TauCeti
