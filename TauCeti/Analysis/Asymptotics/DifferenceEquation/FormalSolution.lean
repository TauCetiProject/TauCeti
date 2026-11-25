/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Topology.Algebra.Polynomial

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
term is the residual estimated here (Wong and Li).

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

* `TauCeti.isBigO_formalDifferenceSolution_residual_sub`: for arbitrary coefficients `a`, the
  residual of the truncation after `N + 1` terms is
  `ρⁿ n^α ∑_{t ≤ N} (differenceResidualCoeff fs gs ρ α a t) n⁻ᵗ + O(|ρ|ⁿ n^{Re α - N - 1})`.
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
expansions of `(1 + j u)^{α - s}` for `j = 0, 1, 2` (`Complex.one_add_cpow_hasFPowerSeriesAt_zero`)
and the expansions of `f` and `g`. These are combined as truncated power series: a function `F`
approximates `P : PowerSeries ℂ` to order `M` when `F - (trunc (M + 1) P).eval u = O(u^{M+1})`,
and this relation is compatible with sums and products. It is a private device of this file for
expansions known only to finitely many orders; the notion of an asymptotic power series is
`Asymptotics.HasAsymptoticExpansion` with the scale `uⁿ`.

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

/-! ### Truncated power-series approximations -/

section Approx

variable {ι : Type*} {l : Filter ι} {w : ι → ℂ}

/-- `F` agrees with the truncation of `P` below degree `M + 1`, evaluated at `w`, up to
`O(w ^ (M + 1))`. -/
private def ApproxTo (l : Filter ι) (w : ι → ℂ) (M : ℕ) (F : ι → ℂ) (P : PowerSeries ℂ) :
    Prop :=
  (fun i ↦ F i - (PowerSeries.trunc (M + 1) P).eval (w i)) =O[l] fun i ↦ w i ^ (M + 1)

/-- `PowerSeries.eval₂_trunc_eq_sum_range` for `Polynomial.eval`. -/
private lemma eval_trunc (n : ℕ) (P : PowerSeries ℂ) (x : ℂ) :
    (PowerSeries.trunc n P).eval x = ∑ i ∈ range n, PowerSeries.coeff i P * x ^ i := by
  simpa using PowerSeries.eval₂_trunc_eq_sum_range x (RingHom.id ℂ) n P

private lemma isBigO_one_eval (hw : Tendsto w l (𝓝 0)) (p : Polynomial ℂ) :
    (fun i ↦ p.eval (w i)) =O[l] fun _ ↦ (1 : ℂ) :=
  ((p.continuous.tendsto 0).comp hw).isBigO_one ℂ

private lemma isBigO_eval_of_X_pow_dvd (hw : Tendsto w l (𝓝 0)) {M : ℕ} {p : Polynomial ℂ}
    (hp : Polynomial.X ^ M ∣ p) : (fun i ↦ p.eval (w i)) =O[l] fun i ↦ w i ^ M := by
  obtain ⟨q, rfl⟩ := hp
  simpa using (isBigO_refl (fun i ↦ w i ^ M) l).mul (isBigO_one_eval hw q)

/-- A polynomial approximates itself to every order. -/
private lemma approxTo_coe (hw : Tendsto w l (𝓝 0)) (M : ℕ) (p : Polynomial ℂ) :
    ApproxTo l w M (fun i ↦ p.eval (w i)) p := by
  refine IsBigO.congr_left (isBigO_eval_of_X_pow_dvd hw
    (p := p - PowerSeries.trunc (M + 1) (p : PowerSeries ℂ))
    (Polynomial.X_pow_dvd_iff.2 fun d hd ↦ ?_)) fun i ↦ by simp
  simp [PowerSeries.coeff_trunc, hd]

private lemma approxTo_add {M : ℕ} {F G : ι → ℂ} {P Q : PowerSeries ℂ}
    (hF : ApproxTo l w M F P) (hG : ApproxTo l w M G Q) :
    ApproxTo l w M (fun i ↦ F i + G i) (P + Q) :=
  (IsBigO.add hF hG).congr_left fun i ↦ by simp only [map_add, Polynomial.eval_add]; ring

/-- A function approximated by a power series is bounded. -/
private lemma isBigO_one_of_approxTo (hw : Tendsto w l (𝓝 0)) {M : ℕ} {F : ι → ℂ}
    {P : PowerSeries ℂ} (hF : ApproxTo l w M F P) : F =O[l] fun _ ↦ (1 : ℂ) := by
  have hpow : (fun i ↦ w i ^ (M + 1)) =O[l] fun _ ↦ (1 : ℂ) := by
    simpa using (((continuous_pow (M + 1)).tendsto 0).comp hw).isBigO_one ℂ
  exact ((IsBigO.trans hF hpow).add (isBigO_one_eval hw _)).congr_left fun i ↦ by ring

private lemma approxTo_mul (hw : Tendsto w l (𝓝 0)) {M : ℕ} {F G : ι → ℂ}
    {P Q : PowerSeries ℂ} (hF : ApproxTo l w M F P) (hG : ApproxTo l w M G Q) :
    ApproxTo l w M (fun i ↦ F i * G i) (P * Q) := by
  set tP := PowerSeries.trunc (M + 1) P
  set tQ := PowerSeries.trunc (M + 1) Q
  -- the product of the truncations agrees with the truncated product below degree `M + 1`
  have hdvd : Polynomial.X ^ (M + 1) ∣ tP * tQ - PowerSeries.trunc (M + 1) (P * Q) := by
    refine Polynomial.X_pow_dvd_iff.2 fun d hd ↦ ?_
    rw [Polynomial.coeff_sub, ← PowerSeries.trunc_trunc_mul_trunc, PowerSeries.coeff_trunc]
    simp only [hd, ite_true]
    rw [← Polynomial.coe_mul, Polynomial.coeff_coe, sub_self]
  have h1 := (IsBigO.mul hF (isBigO_one_of_approxTo hw hG)).congr_right fun i ↦ mul_one _
  have h2 := (IsBigO.mul (isBigO_one_eval hw tP) hG).congr_right fun i ↦ one_mul _
  have h3 := isBigO_eval_of_X_pow_dvd hw hdvd
  refine IsBigO.congr_left ((h1.add h2).add h3) fun i ↦ ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, tP, tQ]
  ring

private lemma approxTo_sum (hw : Tendsto w l (𝓝 0)) {M : ℕ} {κ : Type*} (s : Finset κ)
    {F : κ → ι → ℂ} {P : κ → PowerSeries ℂ} (h : ∀ k ∈ s, ApproxTo l w M (F k) (P k)) :
    ApproxTo l w M (fun i ↦ ∑ k ∈ s, F k i) (∑ k ∈ s, P k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using approxTo_coe hw M 0
  | insert k s hk ih =>
    simp only [sum_insert hk]
    exact approxTo_add (h k (mem_insert_self k s)) (ih fun k' hk' ↦ h k' (mem_insert_of_mem hk'))

/-- The binomial expansion `(1 + j w)^c ≈ ∑ C(c, m) jᵐ wᵐ`. -/
private lemma approxTo_one_add_mul_cpow (hw : Tendsto w l (𝓝 0)) (M : ℕ) (j c : ℂ) :
    ApproxTo l w M (fun i ↦ (1 + j * w i) ^ c)
      (PowerSeries.mk fun m ↦ Ring.choose c m * j ^ m) := by
  have hjw : Tendsto (fun i ↦ j * w i) l (𝓝 0) := by simpa using hw.const_mul j
  have h := ((Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := c)).isBigO_sub_partialSum_pow
    (M + 1)).comp_tendsto hjw
  have hcmp : (fun i ↦ ‖j * w i‖ ^ (M + 1)) =O[l] fun i ↦ w i ^ (M + 1) := by
    simpa [mul_pow] using
      (isBigO_const_mul_self (‖j‖ ^ (M + 1)) (fun i ↦ ‖w i‖ ^ (M + 1)) l).trans
        (isBigO_norm_left.2 (isBigO_refl (fun i ↦ w i ^ (M + 1)) l) |>.congr_left
          fun i ↦ by simp [norm_pow])
  refine IsBigO.congr_left (h.trans hcmp) fun i ↦ ?_
  simp only [zero_add, FormalMultilinearSeries.partialSum, binomialSeries,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const, card_univ, Fintype.card_fin,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, Function.comp_apply, eval_trunc,
    PowerSeries.coeff_mk, sub_right_inj]
  exact sum_congr rfl fun _ _ ↦ by ring

end Approx

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
    have hk := ha t (lt_add_one t)
    rw [sum_Icc_differenceKernel] at hk
    rw [differenceResidualCoeff, sum_range_succ, sum_range_succ, Nat.sub_self,
      differenceKernel_zero, hρ, mul_zero, add_zero, Nat.add_sub_cancel_left, h1]
    rw [show ∑ s ∈ range t, a s * differenceKernel fs gs ρ (α - s) (t + 1 - s) =
      ∑ k ∈ range t, differenceKernel fs gs ρ (α - k) (t + 1 - k) * a k from
        sum_congr rfl fun _ _ ↦ mul_comm _ _, ← hk]
    ring

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
  rw [formalDifferenceSolution, hsplit, Complex.natCast_mul_cpow, pow_add, mul_sum, mul_sum,
    mul_sum]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [Complex.cpow_sub _ _ hpos, Complex.cpow_natCast, mul_inv, mul_pow, div_eq_mul_inv,
    ← inv_pow]
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

/-- The power series whose coefficients are the kernels `differenceKernel fs gs ρ c r`. -/
private lemma coeff_kernelSeries (fs gs : ℕ → ℂ) (ρ c : ℂ) (r : ℕ) :
    PowerSeries.coeff r
        (PowerSeries.C (ρ ^ 2) * PowerSeries.mk (fun m ↦ Ring.choose c m * ((2 : ℕ) : ℂ) ^ m) +
          PowerSeries.C ρ * PowerSeries.mk fs *
            PowerSeries.mk (fun m ↦ Ring.choose c m * ((1 : ℕ) : ℂ) ^ m) +
          PowerSeries.mk gs * PowerSeries.mk (fun m ↦ Ring.choose c m * ((0 : ℕ) : ℂ) ^ m)) =
      differenceKernel fs gs ρ c r := by
  rw [mk_choose_mul_zero_pow, mul_one, mul_assoc, map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ PowerSeries.coeff i (PowerSeries.mk fs) *
      PowerSeries.coeff j (PowerSeries.mk fun m ↦ Ring.choose c m * ((1 : ℕ) : ℂ) ^ m))]
  simp only [PowerSeries.coeff_mk, Nat.cast_one, one_pow, mul_one, differenceKernel]
  push_cast
  ring

/-- The coefficients of `∑_{s<N} aₛ Xˢ Lₛ`, where `Lₛ` is the kernel series at `c = α - s`. -/
private lemma coeff_sum_kernelSeries (fs gs : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) {N t : ℕ}
    (ht : t < N) :
    PowerSeries.coeff t (∑ s ∈ range N, PowerSeries.C (a s) * PowerSeries.X ^ s *
        (PowerSeries.C (ρ ^ 2) *
            PowerSeries.mk (fun m ↦ Ring.choose (α - s) m * ((2 : ℕ) : ℂ) ^ m) +
          PowerSeries.C ρ * PowerSeries.mk fs *
            PowerSeries.mk (fun m ↦ Ring.choose (α - s) m * ((1 : ℕ) : ℂ) ^ m) +
          PowerSeries.mk gs *
            PowerSeries.mk (fun m ↦ Ring.choose (α - s) m * ((0 : ℕ) : ℂ) ^ m))) =
      differenceResidualCoeff fs gs ρ α a t := by
  simp only [map_sum, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  rw [differenceResidualCoeff, ← sum_range_add_sum_Ico _ (Nat.succ_le_of_lt ht),
    sum_eq_zero (s := Ico (t + 1) N) fun k hk ↦ ?_, add_zero]
  · refine sum_congr rfl fun s hs ↦ ?_
    simp only [Nat.lt_succ_iff.1 (mem_range.1 hs), ↓reduceIte]
    rw [← mul_assoc (PowerSeries.C ρ), coeff_kernelSeries]
  · have hk' : ¬k ≤ t := by have := (mem_Ico.1 hk).1; omega
    simp [hk']

private lemma norm_pow_mul_cpow_mul_inv_pow (ρ α : ℂ) (M : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ‖ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ M‖ = ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - M) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    norm_pow, norm_inv, Complex.norm_natCast, Real.rpow_sub hn', Real.rpow_natCast, inv_pow,
    div_eq_mul_inv, mul_assoc]

/-- **Residual of a truncated formal solution.** Let `f` and `g` have the expansions
`f n = ∑_{q ≤ N} f_q n^{-q} + O(n^{-N-1})` and `g n = ∑_{q ≤ N} g_q n^{-q} + O(n^{-N-1})`. For
any coefficients `a`, the truncation `w n = ρⁿ n^α ∑_{s ≤ N} aₛ n⁻ˢ` satisfies

  `w (n + 2) + f n * w (n + 1) + g n * w n = ρⁿ n^α ∑_{t ≤ N} cₜ n⁻ᵗ + O(|ρ|ⁿ n^{Re α - N - 1})`,

where `cₜ = differenceResidualCoeff fs gs ρ α a t` are the coefficients obtained by formal
substitution. -/
theorem isBigO_formalDifferenceSolution_residual_sub {f g fs gs : ℕ → ℂ} (ρ α : ℂ)
    (a : ℕ → ℂ) {N : ℕ}
    (hf : (fun n : ℕ ↦ f n - ∑ q ∈ range (N + 1), (n : ℂ)⁻¹ ^ q • fs q) =O[atTop]
      fun n ↦ (n : ℂ)⁻¹ ^ (N + 1))
    (hg : (fun n : ℕ ↦ g n - ∑ q ∈ range (N + 1), (n : ℂ)⁻¹ ^ q • gs q) =O[atTop]
      fun n ↦ (n : ℂ)⁻¹ ^ (N + 1)) :
    (fun n : ℕ ↦ formalDifferenceSolution a ρ α (N + 1) (n + 2) +
        f n * formalDifferenceSolution a ρ α (N + 1) (n + 1) +
        g n * formalDifferenceSolution a ρ α (N + 1) n -
        ρ ^ n * (n : ℂ) ^ α *
          ∑ t ∈ range (N + 1), differenceResidualCoeff fs gs ρ α a t * (n : ℂ)⁻¹ ^ t) =O[atTop]
      fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - (N + 1)) := by
  set u : ℕ → ℂ := fun n ↦ (n : ℂ)⁻¹
  have hu : Tendsto u atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hF : ApproxTo atTop u N f (PowerSeries.mk fs) :=
    hf.congr_left fun n ↦ by simp [eval_trunc, u, mul_comm]
  have hG : ApproxTo atTop u N g (PowerSeries.mk gs) :=
    hg.congr_left fun n ↦ by simp [eval_trunc, u, mul_comm]
  have hbin := approxTo_one_add_mul_cpow hu N
  -- each term `aₛ n⁻ˢ (ρ² (1 + 2n⁻¹)^{α-s} + ρ f (1 + n⁻¹)^{α-s} + g)` and its series
  have hterm := approxTo_sum hu (range (N + 1)) fun s _ ↦ approxTo_mul hu
    (by simpa using approxTo_coe hu N (Polynomial.C (a s) * Polynomial.X ^ s))
    (approxTo_add (approxTo_add
      (approxTo_mul hu (approxTo_coe hu N (Polynomial.C (ρ ^ 2))) (hbin ((2 : ℕ) : ℂ) (α - s)))
      (approxTo_mul hu (approxTo_mul hu (approxTo_coe hu N (Polynomial.C ρ)) hF)
        (hbin ((1 : ℕ) : ℂ) (α - s))))
      (approxTo_mul hu hG (hbin ((0 : ℕ) : ℂ) (α - s))))
  have hmain := (isBigO_refl (fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) atTop).mul hterm
  refine (hmain.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)).trans ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_trunc,
      u]
    rw [formalDifferenceSolution_residual_eq f g a ρ α (N + 1) hn, ← mul_sub]
    congr 2
    exact sum_congr rfl fun t ht ↦ by rw [coeff_sum_kernelSeries fs gs ρ α a (mem_range.1 ht)]
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [u]
    rw [one_mul, norm_pow_mul_cpow_mul_inv_pow ρ α (N + 1) hn, Real.norm_of_nonneg
      (by positivity)]
    push_cast
    rfl

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
    (hf : (fun n : ℕ ↦ f n - ∑ q ∈ range (N + 1), (n : ℂ)⁻¹ ^ q • fs q) =O[atTop]
      fun n ↦ (n : ℂ)⁻¹ ^ (N + 1))
    (hg : (fun n : ℕ ↦ g n - ∑ q ∈ range (N + 1), (n : ℂ)⁻¹ ^ q • gs q) =O[atTop]
      fun n ↦ (n : ℂ)⁻¹ ^ (N + 1)) :
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
  -- the residual coefficients of `a'` vanish: the coefficient of `a N` is `ρ² + f₀ ρ + g₀ = 0`
  have hres (t : ℕ) (ht : t ∈ range (N + 1)) : differenceResidualCoeff fs gs ρ α a' t = 0 := by
    have htN := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h := differenceResidualCoeff_eq_zero hρ hα fun s hs ↦ ha s (hs.trans_le htN)
    rw [differenceResidualCoeff, sum_range_succ] at h ⊢
    rcases htN.lt_or_eq with htN | rfl
    · rw [← h]
      refine congrArg₂ (· + ·) (sum_congr rfl fun s hs ↦ ?_) ?_
      · simp [a', (mem_range.1 hs).trans htN]
      · simp [a', htN]
    · rw [Nat.sub_self, differenceKernel_zero, hρ, mul_zero, add_zero] at h
      rw [← h, Nat.sub_self, differenceKernel_zero, hρ, mul_zero, add_zero]
      exact sum_congr rfl fun s hs ↦ by simp [a', mem_range.1 hs]
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
    rw [differenceCoeff_succ, sum_range_succ', sum_eq_zero fun k hk ↦ by
      rw [ih k (mem_range.1 hk), mul_zero], zero_add, Nat.cast_zero, sub_zero, Nat.sub_zero,
      differenceKernel, sum_eq_zero fun q _ ↦ ?_, Ring.choose_zero_pos ℂ (by omega),
      hg _ (by omega)]
    · simp
    · rcases eq_or_ne q 0 with rfl | hq
      · rw [Ring.choose_zero_pos ℂ (by omega), mul_zero]
      · rw [hf q hq, zero_mul]

end TauCeti
