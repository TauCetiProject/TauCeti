/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import TauCeti.Analysis.Asymptotics.DifferenceEquation.FormalSolution
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Algebra.ContinuedFractions.ReductionOfOrder
import TauCeti.Analysis.Asymptotics.DiscreteVolterra
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Recessive solutions of second-order linear difference equations

Consider the difference equation

  `w (n + 2) + f n * w (n + 1) + g n * w n = 0`

whose coefficients have Poincaré expansions `f n ∼ ∑ fₛ n⁻ˢ` and `g n ∼ ∑ gₛ n⁻ˢ` as `n → ∞`.
Let `ρ` be a root of the characteristic equation `ρ² + f₀ ρ + g₀ = 0` (DLMF 2.9.5) of strictly
smaller modulus than the other root `g₀ / ρ`, that is `‖ρ‖ ^ 2 < ‖g₀‖`, and let `α` and the
coefficients `aₛ = TauCeti.differenceCoeff fs gs ρ α` be given by DLMF 2.9.6 and 2.9.7. This file
proves that the equation has a solution with the asymptotic expansion

  `w n ∼ ρⁿ n^α ∑ aₛ n⁻ˢ`

of DLMF 2.9.8, and that two solutions asymptotic to `ρⁿ n^α` agree for large `n`. More
generally, two solutions that are `O(rⁿ)` with `r ^ 2 < ‖g₀‖` are proportional for large `n`, the
first being eventually nonzero; so the solution above is the recessive solution, unique up to a
constant factor among the solutions of this size.

## Main results

* `TauCeti.exists_eventually_difference_solution_of_norm_sq_lt`: a solution for large `n` with the
  expansion `ρⁿ n^α ∑ aₛ n⁻ˢ`.
* `TauCeti.exists_difference_solution_of_norm_sq_lt`: if moreover `g` vanishes nowhere, a solution
  for all `n` with that expansion.
* `TauCeti.difference_solution_unique_of_norm_sq_lt`: two solutions asymptotic to `ρⁿ n^α` agree
  for large `n`.
* `TauCeti.exists_eventuallyEq_const_mul_of_isBigO_pow`: if `‖g n‖ ≥ γ` for large `n`, a solution
  that is `O(rⁿ)` with `r ^ 2 < γ` is, for large `n`, a constant multiple of any eventually nonzero
  solution of the same size.

## Implementation notes

Let `u` be the truncation of the formal solution after `M` terms, whose residual
`r n = u (n + 2) + f n * u (n + 1) + g n * u n` is `O(|ρ|ⁿ n^{Re α - M - 1})` by
`TauCeti.isBigO_formalDifferenceSolution_residual`. Writing a solution as `w = u * x`, reduction of
order turns the equation into the summation equation

  `x n - 1 = -∑_{m ≥ n} K n m * r m * x (m + 1)`,
  `K n m = u (m + 1) * ∑_{k = n}^{m} (u k * u (k + 1) * g k ⋯ g m)⁻¹`,

which is solved by `TauCeti.exists_discrete_volterra_solution`. When `‖g k‖ ≥ γ > |ρ|²`, the sum
over `k` is dominated by a geometric series in `|ρ|² / γ`, so that
`|K n m| ≤ C (2m)^{3 |Re α|} |ρ|⁻ᵐ` and the forcing is summable once `M` is large. Each order of
the expansion needs its own `M`; the solutions so obtained coincide, because the Casoratian of two
solutions is multiplied by `g n` at each step and so cannot be `O((r ^ 2)ⁿ)` without vanishing.

The solution for the root of larger modulus, and the case of roots of equal modulus, are not
treated here.

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

/-! ### Reduction to a summation equation -/

/-- The product `g k * g (k + 1) * ⋯ * g m`. -/
private noncomputable def gProd (g : ℕ → ℂ) (k m : ℕ) : ℂ := ∏ j ∈ Ico k (m + 1), g j

/-- The kernel `u (m + 1) * ∑_{k = n}^{m} (u k * u (k + 1) * g k ⋯ g m)⁻¹` of the summation
equation for `w / u`, where `u` is an approximate solution. -/
private noncomputable def kernel (g u : ℕ → ℂ) (n m : ℕ) : ℂ :=
  u (m + 1) * ∑ k ∈ Ico n (m + 1), (u k * u (k + 1) * gProd g k m)⁻¹

private lemma kernel_of_lt {g u : ℕ → ℂ} {n m : ℕ} (h : m < n) : kernel g u n m = 0 := by
  simp [kernel, Ico_eq_empty_of_le (show m + 1 ≤ n by omega)]

private lemma kernel_sub_kernel_succ (g u : ℕ → ℂ) {n m : ℕ} (h : n ≤ m) :
    kernel g u n m - kernel g u (n + 1) m = u (m + 1) * (u n * u (n + 1) * gProd g n m)⁻¹ := by
  rw [kernel, kernel, sum_eq_sum_Ico_succ_bot (show n < m + 1 by omega)]
  ring

private lemma gProd_self (g : ℕ → ℂ) (n : ℕ) : gProd g n n = g n := by
  simp [gProd]

private lemma gProd_eq_mul (g : ℕ → ℂ) {n m : ℕ} (h : n < m) :
    gProd g n m = g n * gProd g (n + 1) m :=
  prod_eq_prod_Ico_succ_bot (by omega) g

private lemma kernel_shift (g u : ℕ → ℂ) (n₀ p m : ℕ) :
    kernel (fun k ↦ g (k + n₀)) (fun k ↦ u (k + n₀)) p m = kernel g u (p + n₀) (m + n₀) := by
  simp only [kernel, gProd]
  rw [show m + n₀ + 1 = m + 1 + n₀ by omega, ← sum_Ico_add']
  refine congrArg₂ _ rfl (sum_congr rfl fun k _ ↦ ?_)
  rw [← prod_Ico_add', show k + 1 + n₀ = k + n₀ + 1 by omega]

/-- The terms `u (m + 1) * (g (p + 1) ⋯ g m)⁻¹ * F m` for `m > p`, extended by `0`. -/
private noncomputable def tailTerm (g u F : ℕ → ℂ) (p m : ℕ) : ℂ :=
  if p < m then u (m + 1) * (gProd g (p + 1) m)⁻¹ * F m else 0

private lemma kernel_mul_sub_kernel_mul (g u F : ℕ → ℂ) (p m : ℕ) :
    kernel g u (p + 1) m * F m - kernel g u (p + 1 + 1) m * F m =
      (u (p + 1) * u (p + 2))⁻¹ * tailTerm g u F p m := by
  rcases lt_or_ge p m with hpm | hpm
  · rw [← sub_mul, kernel_sub_kernel_succ g u (show p + 1 ≤ m by omega)]
    simp only [tailTerm, hpm, ↓reduceIte, mul_inv]
    ring
  · simp [tailTerm, kernel_of_lt (show m < p + 1 by omega),
      kernel_of_lt (show m < p + 1 + 1 by omega), not_lt.2 hpm]

private lemma mul_tailTerm {g : ℕ → ℂ} (u F : ℕ → ℂ) {p : ℕ} (hg : g (p + 1) ≠ 0) (m : ℕ) :
    g (p + 1) * tailTerm g u F p m =
      (if m = p + 1 then u (p + 2) * F (p + 1) else 0) + tailTerm g u F (p + 1) m := by
  rcases lt_trichotomy m (p + 1) with hm | rfl | hm
  · simp [tailTerm, show ¬p < m by omega, show m ≠ p + 1 by omega, show ¬p + 1 < m by omega]
  · simp only [tailTerm, Nat.lt_succ_self p, gProd_self, lt_irrefl, ↓reduceIte, add_zero]
    field_simp [hg]
  · simp only [tailTerm, show p < m by omega, hm, show m ≠ p + 1 by omega, ↓reduceIte,
      zero_add, gProd_eq_mul g hm, mul_inv]
    field_simp [hg]

/-- A sequence `h` given by the kernel sums `h p = ∑ m, K (p + 1) m * F m`, with
`F m = -r m * (1 + h m)` and `r` the residual of `u`, makes `n ↦ u (n + 1) * (1 + h n)` a solution
of the shifted difference equation. -/
private lemma difference_eq_of_eq_tsum_kernel {f g u h F : ℕ → ℂ} (hu : ∀ n, u n ≠ 0)
    (hg : ∀ n, g n ≠ 0) (hF : ∀ m, F m = -(u (m + 2) + f m * u (m + 1) + g m * u m) * (1 + h m))
    (hsum : ∀ p, Summable fun m ↦ kernel g u (p + 1) m * F m)
    (hrep : ∀ p, h p = ∑' m, kernel g u (p + 1) m * F m)
    (n : ℕ) : u (n + 3) * (1 + h (n + 2)) + f (n + 1) * (u (n + 2) * (1 + h (n + 1))) +
      g (n + 1) * (u (n + 1) * (1 + h n)) = 0 := by
  set t := tailTerm g u F
  have hkt (p m : ℕ) : u (p + 1) * u (p + 2) *
      (kernel g u (p + 1) m * F m - kernel g u (p + 1 + 1) m * F m) = t p m := by
    rw [kernel_mul_sub_kernel_mul, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (hu _) (hu _)),
      one_mul]
  have ht_summ (p : ℕ) : Summable (t p) :=
    (((hsum p).sub (hsum (p + 1))).mul_left (u (p + 1) * u (p + 2))).congr (hkt p)
  -- `u (p + 1) * u (p + 2) * (h p - h (p + 1)) = T p` with `T p = ∑ m, t p m`, and
  -- `g (p + 1) * T p = u (p + 2) * F (p + 1) + T (p + 1)`
  have hstep₁ (p : ℕ) : u (p + 1) * u (p + 2) * (h p - h (p + 1)) = ∑' m, t p m := by
    rw [hrep p, hrep (p + 1), ← (hsum p).tsum_sub (hsum (p + 1)), ← tsum_mul_left]
    exact tsum_congr (hkt p)
  have hstep₂ (p : ℕ) :
      g (p + 1) * ∑' m, t p m = u (p + 2) * F (p + 1) + ∑' m, t (p + 1) m := by
    rw [← tsum_mul_left, tsum_congr (mul_tailTerm u F (hg (p + 1))),
      ((hasSum_ite_eq (p + 1) _).summable).tsum_add (ht_summ (p + 1)), tsum_ite_eq]
  -- the recursion for the differences is the difference equation
  have hA := hstep₁ n
  have hB := hstep₁ (n + 1)
  have hC := hstep₂ n
  rw [hF] at hC
  have key : u (n + 2) * (u (n + 3) * (1 + h (n + 2)) + f (n + 1) * (u (n + 2) * (1 + h (n + 1))) +
      g (n + 1) * (u (n + 1) * (1 + h n))) = 0 := by
    linear_combination g (n + 1) * hA - hB + hC
  exact (mul_eq_zero.1 key).resolve_left (hu (n + 2))

/-- **Reduction to a summation equation.** Let `u` be an approximate solution of
`w (n + 2) + f n * w (n + 1) + g n * w n = 0` with residual `r`, and let `u` and `g` vanish
nowhere. If the kernel is bounded by `Q m` and `∑ Q m * ‖r m‖` converges, then there is a sequence
`h`, bounded by the tails of that series, such that `n ↦ u (n + 1) * (1 + h n)` solves the
shifted equation. -/
private theorem exists_solution_of_norm_kernel_le {f g u : ℕ → ℂ} (hu : ∀ n, u n ≠ 0)
    (hg : ∀ n, g n ≠ 0) {Q : ℕ → ℝ} (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖kernel g u (n + 1) m‖ ≤ Q m)
    (hr : Summable fun m ↦ Q m * ‖u (m + 2) + f m * u (m + 1) + g m * u m‖) :
    ∃ h : ℕ → ℂ, (∀ n, u (n + 3) * (1 + h (n + 2)) + f (n + 1) * (u (n + 2) * (1 + h (n + 1))) +
        g (n + 1) * (u (n + 1) * (1 + h n)) = 0) ∧
      ∀ n, ‖h n‖ ≤ (∑' m : Set.Ioi n, Q m * ‖u (m + 2) + f m * u (m + 1) + g m * u m‖) *
        Real.exp (∑' m : Set.Ioi n, Q m * ‖u (m + 2) + f m * u (m + 1) + g m * u m‖) := by
  set r : ℕ → ℂ := fun m ↦ u (m + 2) + f m * u (m + 1) + g m * u m
  have hr' : Summable fun m ↦ Q m * ‖-r m‖ := by simpa using hr
  obtain ⟨h, h_eq, h_le⟩ := exists_discrete_volterra_solution (E := ℂ)
    (K := fun n m ↦ kernel g u (n + 1) m) (J := fun m ↦ -r m) (ψ := fun m ↦ -r m)
    (P := fun _ ↦ 1) (fun _ ↦ zero_le_one) hQ (fun n m hnm ↦ by simpa using hK n m hnm) hr'
    (by simpa using hr')
  have h_le' (n : ℕ) : ‖h n‖ ≤ (∑' m : Set.Ioi n, Q m * ‖r m‖) *
      Real.exp (∑' m : Set.Ioi n, Q m * ‖r m‖) := by simpa using h_le n
  -- `h` is bounded by `S * exp S`
  have hw0 (m : ℕ) : 0 ≤ Q m * ‖r m‖ := mul_nonneg (hQ m) (norm_nonneg _)
  set S := ∑' m, Q m * ‖r m‖
  have hS (n : ℕ) : ∑' m : Set.Ioi n, Q m * ‖r m‖ ≤ S := hr.tsum_subtype_le _ _ hw0
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  have hB (m : ℕ) : ‖h m‖ ≤ S * Real.exp S :=
    (h_le' m).trans (mul_le_mul (hS m) (Real.exp_le_exp.2 (hS m)) (Real.exp_pos _).le hS0)
  -- the summation equation as a series over all of `ℕ`
  set F : ℕ → ℂ := fun m ↦ -r m * (1 + h m)
  have hsum (p : ℕ) : Summable fun m ↦ kernel g u (p + 1) m * F m := by
    refine Summable.of_norm_bounded (hr.mul_left (1 + S * Real.exp S)) fun m ↦ ?_
    rcases lt_or_ge p m with hpm | hpm
    · calc ‖kernel g u (p + 1) m * F m‖ = ‖kernel g u (p + 1) m‖ * (‖r m‖ * ‖1 + h m‖) := by
            simp [F]
        _ ≤ Q m * (‖r m‖ * (1 + S * Real.exp S)) :=
            mul_le_mul (hK p m hpm) (mul_le_mul_of_nonneg_left
              ((norm_add_le _ _).trans (by simpa using hB m)) (norm_nonneg _)) (by positivity)
              (hQ m)
        _ = (1 + S * Real.exp S) * (Q m * ‖r m‖) := by ring
    · rw [kernel_of_lt (by omega), zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (hw0 m)
  have hrep (p : ℕ) : h p = ∑' m, kernel g u (p + 1) m * F m := by
    calc h p = ∑' m : Set.Ioi p, kernel g u (p + 1) m * F m := by
          rw [h_eq p]
          exact tsum_congr fun m ↦ by simp only [smul_eq_mul, F]; ring
      _ = _ := tsum_subtype_eq_of_support_subset (s := Set.Ioi p)
          (f := fun m ↦ kernel g u (p + 1) m * F m) fun m hm ↦ by
          by_contra hmp
          exact hm (by simp only; rw [kernel_of_lt (by simp at hmp; omega), zero_mul])
  exact ⟨h, difference_eq_of_eq_tsum_kernel hu hg (fun _ ↦ rfl) hsum hrep, h_le'⟩

/-! ### The kernel bound for the recessive root -/

/-- One term of the kernel: if `‖u k‖` is comparable to `R ^ k * k ^ a` and `‖g k‖ ≥ γ` beyond
`n₀`, then for `n₀ ≤ k ≤ m` the term of index `k` is at most
`8 (2m)^{3|a|} / (γ R^m) * (R² / γ)^{m - k}`. -/
private lemma norm_kernel_term_le {g u : ℕ → ℂ} {R γ a : ℝ} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hR : 0 < R)
    (hγ : 0 < γ)
    (hu : ∀ k, n₀ ≤ k → R ^ k * (k : ℝ) ^ a / 2 ≤ ‖u k‖ ∧ ‖u k‖ ≤ 2 * (R ^ k * (k : ℝ) ^ a))
    (hg : ∀ k, n₀ ≤ k → γ ≤ ‖g k‖) {k m : ℕ} (hk : n₀ ≤ k) (hkm : k ≤ m) :
    ‖u (m + 1) * (u k * u (k + 1) * gProd g k m)⁻¹‖ ≤
      8 * (2 * m : ℝ) ^ (3 * |a|) / (γ * R ^ m) * (R ^ 2 / γ) ^ (m - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hn₀.trans hk
  -- the product of the `g j` is at least `γ ^ (d + 1)`
  have hG : γ ^ (d + 1) ≤ ‖gProd g k (k + d)‖ := by
    rw [gProd, norm_prod]
    calc γ ^ (d + 1) = ∏ _j ∈ Ico k (k + d + 1), γ := by
          rw [prod_const, Nat.card_Ico]; congr 1; omega
      _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ hγ.le) fun j hj ↦ hg j (hk.trans (mem_Ico.1 hj).1)
  have hu0 := (hu k hk).1
  have hu1 := (hu (k + 1) (by omega)).1
  have hu2 := (hu (k + d + 1) (by omega)).2
  rw [norm_mul, norm_inv, norm_mul, norm_mul, ← div_eq_mul_inv]
  -- bound the norms of `u` and of the product
  calc ‖u (k + d + 1)‖ / (‖u k‖ * ‖u (k + 1)‖ * ‖gProd g k (k + d)‖)
      ≤ 2 * (R ^ (k + d + 1) * ((k + d + 1 : ℕ) : ℝ) ^ a) /
          (R ^ k * (k : ℝ) ^ a / 2 * (R ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ a / 2) * γ ^ (d + 1)) := by
        gcongr
    _ = 8 * (((k + d + 1 : ℕ) : ℝ) ^ a * (k : ℝ) ^ (-a) * ((k + 1 : ℕ) : ℝ) ^ (-a)) *
          ((R ^ 2 / γ) ^ d / (γ * R ^ (k + d))) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), div_pow]
        field_simp
        ring
    _ ≤ 8 * ((2 * (k + d : ℕ) : ℝ) ^ |a| * (2 * (k + d : ℕ) : ℝ) ^ |-a| *
          (2 * (k + d : ℕ) : ℝ) ^ |-a|) * ((R ^ 2 / γ) ^ d / (γ * R ^ (k + d))) := by
        -- each base lies in `[1, 2 (k + d)]`
        have hle {y : ℝ} (hy : 1 ≤ y) (hyX : y ≤ 2 * ((k + d : ℕ) : ℝ)) (t : ℝ) :
            y ^ t ≤ (2 * ((k + d : ℕ) : ℝ)) ^ |t| :=
          Real.rpow_le_rpow_abs (by linarith) hyX ((inv_le_one_of_one_le₀ hy).trans (by linarith)) t
        gcongr
        · exact hle (by push_cast; linarith) (by push_cast; linarith) a
        · exact hle hk1 (by push_cast; linarith) (-a)
        · exact hle (by push_cast; linarith) (by push_cast; linarith) (-a)
    _ = _ := by
        have hX : (0 : ℝ) < 2 * ((k + d : ℕ) : ℝ) := by push_cast; linarith
        rw [abs_neg, ← Real.rpow_add hX, ← Real.rpow_add hX, Nat.add_sub_cancel_left]
        push_cast
        ring_nf

/-- **The kernel bound for the recessive root.** If `‖u k‖` is comparable to `R ^ k * k ^ a` and
`‖g k‖ ≥ γ > R²` beyond `n₀`, then for `n₀ ≤ p` the kernel is at most
`8 / (γ - R²) * (2m)^{3|a|} / R^m`. -/
private lemma norm_kernel_le {g u : ℕ → ℂ} {R γ a : ℝ} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hR : 0 < R)
    (hγ : R ^ 2 < γ)
    (hu : ∀ k, n₀ ≤ k → R ^ k * (k : ℝ) ^ a / 2 ≤ ‖u k‖ ∧ ‖u k‖ ≤ 2 * (R ^ k * (k : ℝ) ^ a))
    (hg : ∀ k, n₀ ≤ k → γ ≤ ‖g k‖) {p : ℕ} (hp : n₀ ≤ p) (m : ℕ) :
    ‖kernel g u p m‖ ≤ 8 / (γ - R ^ 2) * ((2 * m : ℝ) ^ (3 * |a|) / R ^ m) := by
  have hγ0 : 0 < γ := (pow_pos hR 2).trans hγ
  rcases lt_or_ge m p with hmp | -
  · rw [kernel_of_lt hmp, norm_zero]
    positivity
  set q := R ^ 2 / γ
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hγ0).2 hγ
  set c := 8 * (2 * m : ℝ) ^ (3 * |a|) / (γ * R ^ m)
  have hc : 0 ≤ c := by positivity
  rw [kernel, mul_sum]
  calc ‖∑ k ∈ Ico p (m + 1), u (m + 1) * (u k * u (k + 1) * gProd g k m)⁻¹‖
      ≤ ∑ k ∈ Ico p (m + 1), c * q ^ (m - k) := (norm_sum_le _ _).trans <| sum_le_sum fun k hk ↦
        norm_kernel_term_le hn₀ hR hγ0 hu hg (hp.trans (mem_Ico.1 hk).1)
          (Nat.lt_succ_iff.1 (mem_Ico.1 hk).2)
    _ ≤ ∑ k ∈ range (m + 1), c * q ^ (m - k) :=
        sum_le_sum_of_subset_of_nonneg (fun k hk ↦ mem_range.2 (mem_Ico.1 hk).2)
          fun _ _ _ ↦ by positivity
    _ = c * ∑ j ∈ Ico 0 (m + 1), q ^ j := by
        rw [← mul_sum, ← range_eq_Ico, ← sum_range_reflect]
        exact congrArg _ (sum_congr rfl fun j hj ↦ by
          rw [show m - (m + 1 - 1 - j) = j by have := mem_range.1 hj; omega])
    _ ≤ c * (q ^ 0 / (1 - q)) := mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) hc
    _ = _ := by
        simp only [c, q, pow_zero]
        field_simp

/-! ### Solutions near an approximate solution -/

/-- Undoing the shift: if `n ↦ u (n + 1 + n₀) * (1 + h n)` solves the difference equation shifted
by `n₀`, then `w k = u k * (1 + h (k - (n₀ + 1)))` solves it for `k > n₀`, and a bound on `h`
gives one on `w - u`. -/
private lemma exists_solution_of_shift {f g u h : ℕ → ℂ} {R a e B : ℝ} {n₀ : ℕ} (hR : 0 ≤ R)
    (hrec : ∀ n, u (n + 3 + n₀) * (1 + h (n + 2)) +
      f (n + 1 + n₀) * (u (n + 2 + n₀) * (1 + h (n + 1))) +
        g (n + 1 + n₀) * (u (n + 1 + n₀) * (1 + h n)) = 0)
    (hu : ∀ k, n₀ < k → ‖u k‖ ≤ 2 * (R ^ k * (k : ℝ) ^ a))
    (hh : ∀ n, ‖h n‖ ≤ B * ((n + 1 + n₀ : ℕ) : ℝ) ^ e) :
    ∃ w : ℕ → ℂ, (∀ k, n₀ < k → w (k + 2) + f k * w (k + 1) + g k * w k = 0) ∧
      ∀ k, n₀ < k → ‖w k - u k‖ ≤ 2 * B * (R ^ k * (k : ℝ) ^ (a + e)) := by
  refine ⟨fun k ↦ u k * (1 + h (k - (n₀ + 1))), fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
    have := hrec n
    simp only
    rw [show n₀ + n + 1 + 2 - (n₀ + 1) = n + 2 by omega,
      show n₀ + n + 1 + 1 - (n₀ + 1) = n + 1 by omega, show n₀ + n + 1 - (n₀ + 1) = n by omega,
      show n₀ + n + 1 + 2 = n + 3 + n₀ by omega, show n₀ + n + 1 + 1 = n + 2 + n₀ by omega,
      show n₀ + n + 1 = n + 1 + n₀ by omega]
    exact this
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
    have hk0 : (0 : ℝ) < ((n₀ + n + 1 : ℕ) : ℝ) := by positivity
    simp only
    rw [show n₀ + n + 1 - (n₀ + 1) = n by omega, mul_add, mul_one, add_sub_cancel_left,
      norm_mul, Real.rpow_add hk0]
    have hhn := hh n
    rw [show n + 1 + n₀ = n₀ + n + 1 by omega] at hhn
    calc _ ≤ 2 * (R ^ (n₀ + n + 1) * ((n₀ + n + 1 : ℕ) : ℝ) ^ a) *
          (B * ((n₀ + n + 1 : ℕ) : ℝ) ^ e) :=
          mul_le_mul (hu _ hk) hhn (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- The bound `Q * y ≤ E * x ^ (t + 3|a|)` for the weighted residual, where
`Q = 8 / (γ - R²) * (2x)^{3|a|} / R^j` is the kernel bound at `x = j` and `y ≤ C R^j x^t`. -/
private lemma weight_mul_le {R γ a t C x y : ℝ} {j : ℕ} (hx : 0 < x) (hR : 0 < R)
    (hγ : R ^ 2 < γ) (hy : y ≤ C * (R ^ j * x ^ t)) :
    8 / (γ - R ^ 2) * ((2 * x) ^ (3 * |a|) / R ^ j) * y ≤
      8 * 2 ^ (3 * |a|) / (γ - R ^ 2) * C * x ^ (t + 3 * |a| + 2 - 2) := by
  calc _ ≤ 8 / (γ - R ^ 2) * ((2 * x) ^ (3 * |a|) / R ^ j) * (C * (R ^ j * x ^ t)) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
    _ = 8 * 2 ^ (3 * |a|) / (γ - R ^ 2) * C * (x ^ (3 * |a|) * x ^ t) := by
        rw [Real.mul_rpow zero_le_two hx.le]
        field_simp
    _ = _ := by
        rw [← Real.rpow_add hx]
        congr 2
        ring

/-- **A solution near an approximate solution.** Let `u` be comparable to `R ^ k * k ^ a`, let
`‖g k‖ ≥ γ > R²`, and let the residual of `u` be at most `C * R ^ k * k ^ t` beyond `n₀ ≥ 1`, where
`t + 3|a| + 2 ≤ 0`. Then the difference equation has a solution on `k > n₀` with
`‖w k - u k‖ ≤ D * R ^ k * k ^ (a + t + 3|a| + 2)`. -/
private theorem exists_solution_of_tail_bounds {f g u : ℕ → ℂ} {R γ a t C : ℝ} {n₀ : ℕ}
    (hn₀ : 1 ≤ n₀) (hR : 0 < R) (hγ : R ^ 2 < γ) (hC : 0 ≤ C)
    (hu : ∀ k, n₀ ≤ k → R ^ k * (k : ℝ) ^ a / 2 ≤ ‖u k‖ ∧ ‖u k‖ ≤ 2 * (R ^ k * (k : ℝ) ^ a))
    (hg : ∀ k, n₀ ≤ k → γ ≤ ‖g k‖)
    (hr : ∀ k, n₀ ≤ k → ‖u (k + 2) + f k * u (k + 1) + g k * u k‖ ≤ C * (R ^ k * (k : ℝ) ^ t))
    (ht : t + 3 * |a| + 2 ≤ 0) :
    ∃ w : ℕ → ℂ, (∀ k, n₀ < k → w (k + 2) + f k * w (k + 1) + g k * w k = 0) ∧
      ∃ D, ∀ k, n₀ < k → ‖w k - u k‖ ≤ D * (R ^ k * (k : ℝ) ^ (a + (t + 3 * |a| + 2))) := by
  set e := t + 3 * |a| + 2
  have hγ0 : 0 < γ := (pow_pos hR 2).trans hγ
  have hcast (m : ℕ) : (1 : ℝ) ≤ ((m + n₀ : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + n₀)
  -- the shifted problem has nonvanishing `u` and `g`
  have hu' (k : ℕ) : u (k + n₀) ≠ 0 := by
    refine norm_pos_iff.1 (lt_of_lt_of_le ?_ (hu (k + n₀) (by omega)).1)
    exact div_pos (mul_pos (pow_pos hR _) (Real.rpow_pos_of_pos (by linarith [hcast k]) a)) two_pos
  have hg' (k : ℕ) : g (k + n₀) ≠ 0 :=
    norm_pos_iff.1 (hγ0.trans_le (hg (k + n₀) (by omega)))
  set Q : ℕ → ℝ := fun m ↦ 8 / (γ - R ^ 2) * ((2 * ((m + n₀ : ℕ) : ℝ)) ^ (3 * |a|) / R ^ (m + n₀))
  have hQ (m : ℕ) : 0 ≤ Q m := by positivity
  have hK (n m : ℕ) (_ : n < m) :
      ‖kernel (fun k ↦ g (k + n₀)) (fun k ↦ u (k + n₀)) (n + 1) m‖ ≤ Q m := by
    rw [kernel_shift]
    exact norm_kernel_le hn₀ hR hγ hu hg (by omega) _
  -- the weighted residual is at most `E * (m + n₀) ^ (e - 2)`
  set E := 8 * 2 ^ (3 * |a|) / (γ - R ^ 2) * C
  have hres (m : ℕ) : Q m * ‖u (m + 2 + n₀) + f (m + n₀) * u (m + 1 + n₀) +
      g (m + n₀) * u (m + n₀)‖ ≤ E * ((m + n₀ : ℕ) : ℝ) ^ (e - 2) := by
    have h := hr (m + n₀) (by omega)
    rw [show m + n₀ + 2 = m + 2 + n₀ by omega, show m + n₀ + 1 = m + 1 + n₀ by omega] at h
    exact weight_mul_le (by linarith [hcast m]) hR hγ h
  have hsumm : Summable fun m : ℕ ↦ ((m + n₀ : ℕ) : ℝ) ^ (e - 2) :=
    (summable_nat_add_iff n₀).2 (Real.summable_nat_rpow.2 (by linarith))
  have hE : 0 ≤ E := by positivity
  have hr' : Summable fun m ↦ Q m * ‖u (m + 2 + n₀) + f (m + n₀) * u (m + 1 + n₀) +
      g (m + n₀) * u (m + n₀)‖ :=
    (hsumm.mul_left E).of_nonneg_of_le (fun m ↦ mul_nonneg (hQ m) (norm_nonneg _)) hres
  obtain ⟨h, hrec, hle⟩ := exists_solution_of_norm_kernel_le (f := fun k ↦ f (k + n₀))
    (g := fun k ↦ g (k + n₀)) (u := fun k ↦ u (k + n₀)) hu' hg' hQ hK hr'
  -- the tails of the weighted residual decay like `(n + 1 + n₀) ^ e`
  set S := ∑' m : ℕ, ((m + n₀ : ℕ) : ℝ) ^ (-2 : ℝ)
  have htail := tsum_Ioi_le_of_le_rpow hE ht (fun m ↦ mul_nonneg (hQ m) (norm_nonneg _)) hres
  have hpow_le (n : ℕ) : ((n + 1 + n₀ : ℕ) : ℝ) ^ e ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega)) ht
  have hh (n : ℕ) : ‖h n‖ ≤ E * S * Real.exp (E * S) * ((n + 1 + n₀ : ℕ) : ℝ) ^ e := by
    refine (hle n).trans ?_
    have h1 := htail n
    have h2 : E * S * ((n + 1 + n₀ : ℕ) : ℝ) ^ e ≤ E * S :=
      mul_le_of_le_one_right (by positivity) (hpow_le n)
    calc _ ≤ E * S * ((n + 1 + n₀ : ℕ) : ℝ) ^ e * Real.exp (E * S) :=
          mul_le_mul h1 (Real.exp_le_exp.2 (h1.trans h2)) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  obtain ⟨w, hw, hwu⟩ := exists_solution_of_shift hR.le hrec
    (fun k hk ↦ (hu k hk.le).2) hh
  exact ⟨w, hw, _, hwu⟩

/-! ### Uniqueness of small solutions -/

/-- **Small solutions are proportional.** Let `‖g n‖ ≥ γ` for large `n` and let `w₁` and `w` be
solutions of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for large `n`, both `O(r ^ n)` with
`r ^ 2 < γ`. If `w₁` is eventually nonzero, then `w` is eventually a constant multiple of `w₁`.

The Casoratian `w₁ n * w (n + 1) - w₁ (n + 1) * w n` is multiplied by `g n` at each step, so it
is either eventually zero or at least of the order `γ ^ n`; the bound `O((r ^ 2) ^ n)` excludes
the second case. -/
theorem exists_eventuallyEq_const_mul_of_isBigO_pow {𝕜 : Type*} [NormedField 𝕜]
    {f g w₁ w : ℕ → 𝕜} {r γ : ℝ}
    (hrγ : r ^ 2 < γ) (hgγ : ∀ᶠ n in atTop, γ ≤ ‖g n‖)
    (hw₁ : ∀ᶠ n in atTop, w₁ (n + 2) + f n * w₁ (n + 1) + g n * w₁ n = 0)
    (hw : ∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0)
    (hw₁0 : ∀ᶠ n in atTop, w₁ n ≠ 0) (hw₁r : w₁ =O[atTop] fun n ↦ r ^ n)
    (hwr : w =O[atTop] fun n ↦ r ^ n) :
    ∃ c : 𝕜, w =ᶠ[atTop] fun n ↦ c * w₁ n := by
  set C : ℕ → 𝕜 := fun n ↦ w₁ n * w (n + 1) - w₁ (n + 1) * w n with hC_def
  have hγ0 : 0 < γ := (sq_nonneg r).trans_lt hrγ
  -- the Casoratian is `o(γ ^ n)`
  have hshift {v : ℕ → 𝕜} (hv : v =O[atTop] fun n ↦ r ^ n) :
      (fun n ↦ v (n + 1)) =O[atTop] fun n ↦ r ^ n :=
    (hv.comp_tendsto (tendsto_add_atTop_nat 1)).trans
      ((isBigO_const_mul_self r _ _).congr_left fun n ↦ by simp [pow_succ, mul_comm])
  have hCo : C =o[atTop] fun n ↦ γ ^ n := by
    have hCO : C =O[atTop] fun n ↦ (r ^ 2) ^ n :=
      ((hw₁r.mul (hshift hwr)).sub ((hshift hw₁r).mul hwr)).congr_right fun n ↦ by ring
    exact hCO.trans_isLittleO (isLittleO_pow_pow_of_lt_left (sq_nonneg r) hrγ)
  -- beyond `n₁` the Casoratian is multiplied by `g n` with `‖g n‖ ≥ γ`
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hw₁.and (hw.and hgγ))
  have hCrec (n : ℕ) (hn : n₁ ≤ n) : C (n + 1) = g n * C n := by
    obtain ⟨h₁, h₂, -⟩ := hn₁ n hn
    simp only [hC_def]
    linear_combination w₁ (n + 1) * h₂ - w (n + 1) * h₁
  have hCgrowth (n : ℕ) (hn : n₁ ≤ n) (k : ℕ) : γ ^ k * ‖C n‖ ≤ ‖C (n + k)‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, hCrec _ (by omega), norm_mul, pow_succ, mul_right_comm, mul_comm ‖g _‖]
      exact mul_le_mul ih (hn₁ (n + k) (by omega)).2.2 hγ0.le (norm_nonneg _)
  have hCzero (n : ℕ) (hn : n₁ ≤ n) : C n = 0 := by
    by_contra hne
    have hpos : 0 < ‖C n‖ := norm_pos_iff.2 hne
    -- otherwise `γ ^ m = O(C m)`, against `C = o(γ ^ m)`
    have hO : (fun m ↦ γ ^ m) =O[atTop] C := by
      refine IsBigO.of_bound (γ ^ n / ‖C n‖) ?_
      filter_upwards [eventually_ge_atTop n] with m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [Real.norm_of_nonneg (by positivity), pow_add, div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact (mul_le_mul_of_nonneg_left (hCgrowth n hn k) (by positivity)).trans_eq' (by ring)
    exact isLittleO_irrefl (.of_forall fun m ↦ (pow_pos hγ0 m).ne') (hO.trans_isLittleO hCo)
  exact exists_eventuallyEq_const_mul_of_casoratian hw₁0
    (eventually_atTop.2 ⟨n₁, hCzero⟩)

/-- **Uniqueness of the recessive solution.** Let `g n → g₀` and `‖ρ‖ ^ 2 < ‖g₀‖`. Two solutions
of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for large `n` that are both asymptotic to
`ρ ^ n * n ^ α` agree for large `n`. -/
theorem difference_solution_unique_of_norm_sq_lt {f g w w' : ℕ → ℂ} {g₀ ρ α : ℂ}
    (hg : Tendsto g atTop (𝓝 g₀)) (hlt : ‖ρ‖ ^ 2 < ‖g₀‖)
    (hw : ∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0)
    (hw' : ∀ᶠ n in atTop, w' (n + 2) + f n * w' (n + 1) + g n * w' n = 0)
    (hwl : (fun n ↦ w n - ρ ^ n * (n : ℂ) ^ α) =o[atTop] fun n ↦ ρ ^ n * (n : ℂ) ^ α)
    (hw'l : (fun n ↦ w' n - ρ ^ n * (n : ℂ) ^ α) =o[atTop] fun n ↦ ρ ^ n * (n : ℂ) ^ α) :
    w =ᶠ[atTop] w' := by
  set φ : ℕ → ℂ := fun n ↦ ρ ^ n * (n : ℂ) ^ α with hφ_def
  -- for `ρ = 0` both solutions vanish for large `n`
  rcases eq_or_ne ρ 0 with rfl | hρ
  · have hφz : φ =ᶠ[atTop] 0 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp [hφ_def, zero_pow (show n ≠ 0 by omega)]
    have hz {v : ℕ → ℂ} (hv : (fun n ↦ v n - φ n) =o[atTop] φ) : v =ᶠ[atTop] 0 := by
      filter_upwards [isLittleO_zero_right_iff.1 (hv.congr' .rfl hφz), hφz] with n h₁ h₂
      simpa [h₂] using h₁
    exact (hz hwl).trans (hz hw'l).symm
  have hφ0 : ∀ᶠ n in atTop, φ n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_ne_zero (pow_ne_zero _ hρ) (norm_ne_zero_iff.1
      (Complex.norm_natCast_cpow_pos_of_pos hn α).ne')
  -- `w` is eventually nonzero, and `w` and `w'` are `O(φ)`
  have hw0 : ∀ᶠ n in atTop, w n ≠ 0 := by
    filter_upwards [hwl.bound (by norm_num : (0 : ℝ) < 1 / 2), hφ0] with n hn hφn h0
    rw [h0, zero_sub, norm_neg] at hn
    exact hφn (norm_eq_zero.1 (by linarith [norm_nonneg (φ n)]))
  have hO {v : ℕ → ℂ} (hv : (fun n ↦ v n - φ n) =o[atTop] φ) : v =O[atTop] φ :=
    (hv.isBigO.add (isBigO_refl φ atTop)).congr_left fun n ↦ by ring
  -- `φ = O(r ^ n)` for some `r` with `r ^ 2 < ‖g₀‖`
  obtain ⟨r, hRr, hr⟩ := exists_between ((Real.lt_sqrt (norm_nonneg ρ)).2 hlt)
  have hr2 : r ^ 2 < ‖g₀‖ := (Real.lt_sqrt ((norm_nonneg ρ).trans hRr.le)).1 hr
  have hφr : φ =O[atTop] fun n ↦ r ^ n := isBigO_pow_mul_cpow_pow_of_norm_lt α hRr
  obtain ⟨γ, hrγ, hγg⟩ := exists_between hr2
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_mul_of_isBigO_pow hrγ
    (hg.norm.eventually (eventually_ge_nhds hγg)) hw hw' hw0
    ((hO hwl).trans hφr) ((hO hw'l).trans hφr)
  -- the constant is `1`, since `(c - 1) φ = o(φ)`
  obtain rfl : c = 1 := by
    by_contra hc1
    have hsmall : (fun n ↦ (c - 1) * φ n) =o[atTop] φ := by
      refine ((hw'l.sub hwl).sub (hwl.const_mul_left (c - 1))).congr' ?_ EventuallyEq.rfl
      filter_upwards [hc] with n hn
      rw [hn]
      ring
    exact isLittleO_irrefl hφ0.frequently ((isLittleO_const_mul_left_iff (sub_ne_zero.2 hc1)).1
      hsmall)
  filter_upwards [hc] with n hn
  rw [hn, one_mul]

/-! ### The recessive solution -/

/-- The characteristic root `ρ` with `‖ρ‖ ^ 2 < ‖g₀‖` is nonzero and simple. -/
private lemma mul_ne_zero_of_norm_sq_lt {fs gs : ℕ → ℂ} {ρ : ℂ} (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0)
    (hlt : ‖ρ‖ ^ 2 < ‖gs 0‖) : ρ * (fs 0 + 2 * ρ) ≠ 0 := by
  refine mul_ne_zero (fun h ↦ ?_) fun h ↦ ?_
  · subst h
    have : gs 0 = 0 := by linear_combination hρ
    rw [this, norm_zero] at hlt
    exact (sq_nonneg _).not_gt hlt
  · have : gs 0 = ρ ^ 2 := by linear_combination hρ - ρ * h
    rw [this, norm_pow] at hlt
    exact lt_irrefl _ hlt

/-- For `M ≥ 1` and `a₀ = 1`, the truncation `ρⁿ n^α ∑_{s < M} aₛ n⁻ˢ` is eventually between
half and twice `|ρ|ⁿ n^{Re α}` in norm. -/
private lemma eventually_norm_formalDifferenceSolution {a : ℕ → ℂ} (ha : a 0 = 1) (ρ α : ℂ)
    {M : ℕ} (hM : 1 ≤ M) : ∀ᶠ k : ℕ in atTop,
      ‖ρ‖ ^ k * (k : ℝ) ^ α.re / 2 ≤ ‖formalDifferenceSolution a ρ α M k‖ ∧
        ‖formalDifferenceSolution a ρ α M k‖ ≤ 2 * (‖ρ‖ ^ k * (k : ℝ) ^ α.re) := by
  filter_upwards [(isEquivalent_formalDifferenceSolution ha ρ α hM).isLittleO.bound
    (by norm_num : (0 : ℝ) < 1 / 2), eventually_ne_atTop 0] with k hk hk0
  rw [Pi.sub_apply] at hk
  rw [← norm_pow_mul_cpow ρ α hk0]
  have h₁ := norm_sub_norm_le (ρ ^ k * (k : ℂ) ^ α) (formalDifferenceSolution a ρ α M k)
  have h₂ := norm_le_norm_add_norm_sub' (formalDifferenceSolution a ρ α M k) (ρ ^ k * (k : ℂ) ^ α)
  rw [norm_sub_rev] at h₁
  constructor <;> linarith [norm_nonneg (ρ ^ k * (k : ℂ) ^ α)]

/-- **A solution to a given order.** For every `N`, there is a solution for large `n` whose
difference from each truncation `ρⁿ n^α ∑_{s < N'} aₛ n⁻ˢ` with `N' ≤ N` is
`O(|ρ|ⁿ n^{Re α - N'})`. -/
private theorem exists_eventually_solution_isBigO {f g fs gs : ℕ → ℂ} {ρ α : ℂ}
    (hf : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) fs f)
    (hg : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) gs g)
    (hg₀ : Tendsto g atTop (𝓝 (gs 0)))
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1)
    (hlt : ‖ρ‖ ^ 2 < ‖gs 0‖) (N : ℕ) :
    ∃ w : ℕ → ℂ, (∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      ∀ N' ≤ N, (fun n ↦ w n - formalDifferenceSolution (differenceCoeff fs gs ρ α) ρ α N' n)
        =O[atTop] fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - N') := by
  set a := differenceCoeff fs gs ρ α
  have hρ₀ := mul_ne_zero_of_norm_sq_lt hρ hlt
  have hR : 0 < ‖ρ‖ := norm_pos_iff.2 (left_ne_zero_of_mul hρ₀)
  -- the comparison function `u` is the truncation after `M` terms
  set M := N + ⌈α.re + 3 * |α.re|⌉₊ + 1
  have hM : α.re + 3 * |α.re| + 1 + N ≤ M := by
    have := Nat.le_ceil (α.re + 3 * |α.re|)
    simp only [M]
    push_cast
    linarith
  obtain ⟨u, hu_def⟩ : ∃ u, u = formalDifferenceSolution a ρ α M := ⟨_, rfl⟩
  -- its residual is `O(|ρ|ⁿ n^{Re α - M - 1})`
  have hres := isBigO_formalDifferenceSolution_residual (a := a) (N := M) hρ hα
    (fun s _ ↦ mul_differenceCoeff hρ₀ α s) (by simpa [inv_pow] using hf.isBigO (M + 1))
    (by simpa [inv_pow] using hg.isBigO (M + 1))
  rw [← hu_def] at hres
  obtain ⟨Cr, hCr0, hCr⟩ := hres.exists_nonneg
  -- `g` is bounded below by `γ > |ρ|²`
  set γ := (‖ρ‖ ^ 2 + ‖gs 0‖) / 2
  have hγ : ‖ρ‖ ^ 2 < γ := by simp only [γ]; linarith
  have hgγ : ∀ᶠ n in atTop, γ ≤ ‖g n‖ :=
    hg₀.norm.eventually (eventually_ge_nhds (by simp only [γ]; linarith))
  have hU := eventually_norm_formalDifferenceSolution (differenceCoeff_zero fs gs ρ α) ρ α
    (show 1 ≤ M by omega)
  rw [← hu_def] at hU
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hCr.bound.and (hU.and hgγ))
  set n₀ := n₁ + 1
  have hu (k : ℕ) (hk : n₀ ≤ k) := (hn₁ k (by omega)).2.1
  have hgn (k : ℕ) (hk : n₀ ≤ k) : γ ≤ ‖g k‖ := (hn₁ k (by omega)).2.2
  have hr (k : ℕ) (hk : n₀ ≤ k) : ‖u (k + 2) + f k * u (k + 1) + g k * u k‖ ≤
      Cr * (‖ρ‖ ^ k * (k : ℝ) ^ (α.re - ((M : ℝ) + 1))) := by
    have := (hn₁ k (by omega)).1
    rwa [Real.norm_of_nonneg (by positivity)] at this
  have ht : α.re - ((M : ℝ) + 1) + 3 * |α.re| + 2 ≤ 0 := by linarith
  obtain ⟨w, hrec, D, hD⟩ := exists_solution_of_tail_bounds (by omega) hR hγ hCr0 hu hgn hr ht
  refine ⟨w, eventually_atTop.2 ⟨n₀ + 1, fun k hk ↦ hrec k (by omega)⟩, fun N' hN' ↦ ?_⟩
  -- `w - u` is `O(|ρ|ⁿ n^{Re α - N})`, and so is `u` minus each shorter truncation
  have hwu : (fun n ↦ w n - u n) =O[atTop] fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - N') := by
    refine IsBigO.of_bound |D| ?_
    filter_upwards [eventually_gt_atTop n₀] with k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hN'N : (N' : ℝ) ≤ N := by exact_mod_cast hN'
    rw [Real.norm_of_nonneg (by positivity)]
    refine (hD k hk).trans ((mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity)).trans ?_)
    gcongr
    linarith
  have hut := isBigO_formalDifferenceSolution_sub a ρ α (show N' ≤ M by omega)
  rw [← hu_def] at hut
  exact (hwu.add hut).congr_left fun n ↦ by ring

/-- **The recessive solution of a difference equation, for large `n`** (DLMF 2.9.8). Let
`f n ∼ ∑ fₛ n⁻ˢ` and `g n ∼ ∑ gₛ n⁻ˢ`, let `ρ` be a root of `ρ² + f₀ ρ + g₀ = 0` (DLMF 2.9.5)
with `‖ρ‖ ^ 2 < ‖g₀‖`, that is, of strictly smaller modulus than the other root, and let `α`
satisfy DLMF 2.9.6. Then there is a solution of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for
large `n` with the expansion `w n ∼ ρⁿ n^α ∑ aₛ n⁻ˢ`, the coefficients `aₛ` being those of
DLMF 2.9.7 (`TauCeti.differenceCoeff`). By `TauCeti.difference_solution_unique_of_norm_sq_lt` it
is unique for large `n`. -/
theorem exists_eventually_difference_solution_of_norm_sq_lt {f g fs gs : ℕ → ℂ} {ρ α : ℂ}
    (hf : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) fs f)
    (hg : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) gs g)
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1)
    (hlt : ‖ρ‖ ^ 2 < ‖gs 0‖) :
    ∃ w : ℕ → ℂ, (∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      HasAsymptoticExpansion atTop (fun s (n : ℕ) ↦ ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ s)
        (differenceCoeff fs gs ρ α) w := by
  set a := differenceCoeff fs gs ρ α
  have hg₀ : Tendsto g atTop (𝓝 (gs 0)) := by
    have h := (hg.isBigO 1).trans_tendsto
      (by simpa using tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    simpa using h.add_const (gs 0)
  -- a remainder `O(|ρ|ⁿ n^{Re α - 1})` after the leading term is `o(ρⁿ n^α)`
  have hlead {v : ℕ → ℂ}
      (hv : (fun n ↦ v n - formalDifferenceSolution a ρ α 1 n) =O[atTop]
        fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - (1 : ℕ))) :
      (fun n ↦ v n - ρ ^ n * (n : ℂ) ^ α) =o[atTop] fun n ↦ ρ ^ n * (n : ℂ) ^ α := by
    refine (hv.trans_isLittleO (isLittleO_norm_pow_mul_rpow_pow_mul_cpow ρ ?_)).congr_left
      fun n ↦ ?_
    · simp
    · simp [formalDifferenceSolution_def, a]
  obtain ⟨w, hw, hwO⟩ := exists_eventually_solution_isBigO hf hg hg₀ hρ hα hlt 1
  refine ⟨w, hw, .of_isBigO fun N ↦ ?_⟩
  -- the solution built to order `N + 1` is `w`
  obtain ⟨w', hw', hw'O⟩ := exists_eventually_solution_isBigO hf hg hg₀ hρ hα hlt (N + 1)
  have heq := difference_solution_unique_of_norm_sq_lt hg₀ hlt hw hw' (hlead (hwO 1 le_rfl))
    (hlead (hw'O 1 (by omega)))
  refine ((hw'O N (by omega)).trans (IsBigO.of_bound 1 ?_)).congr' ?_ EventuallyEq.rfl
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [one_mul, norm_pow_mul_cpow_mul_inv_pow ρ α N (by omega),
      Real.norm_of_nonneg (by positivity)]
  · filter_upwards [heq] with n hn
    rw [hn, formalDifferenceSolution_def, mul_sum]
    exact congrArg _ (sum_congr rfl fun s _ ↦ by rw [smul_eq_mul]; ring)

/-- **The recessive solution of a difference equation** (DLMF 2.9.8). Under the hypotheses of
`TauCeti.exists_eventually_difference_solution_of_norm_sq_lt`, if moreover `g` vanishes nowhere,
there is a solution of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for all `n` with the
expansion `w n ∼ ρⁿ n^α ∑ aₛ n⁻ˢ`. -/
theorem exists_difference_solution_of_norm_sq_lt {f g fs gs : ℕ → ℂ} {ρ α : ℂ}
    (hf : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) fs f)
    (hg : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) gs g)
    (hg0 : ∀ n, g n ≠ 0) (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0)
    (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1) (hlt : ‖ρ‖ ^ 2 < ‖gs 0‖) :
    ∃ w : ℕ → ℂ, (∀ n, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      HasAsymptoticExpansion atTop (fun s (n : ℕ) ↦ ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ s)
        (differenceCoeff fs gs ρ α) w := by
  obtain ⟨w, hw, hexp⟩ := exists_eventually_difference_solution_of_norm_sq_lt hf hg hρ hα hlt
  obtain ⟨w', hw', hw'w⟩ := exists_difference_solution_eventuallyEq hg0 hw
  exact ⟨w', hw', hexp.congr' hw'w.symm⟩

end TauCeti
