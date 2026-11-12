/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Volterra summation equations with separable kernel bounds

Let `K n m` be a kernel defined for `n < m` with a separable bound `‖K n m‖ ≤ P n * Q m`, where
`P, Q ≥ 0`, and let `J`, `ψ` be sequences such that `∑ m, Q m * ‖J m‖` and
`∑ m, P m * Q m * ‖ψ m‖` converge. Writing

* `Φ n = ∑_{m > n} Q m * ‖J m‖` and
* `Ψ n = ∑_{m > n} P m * Q m * ‖ψ m‖`,

the summation equation

  `h n = ∑_{m > n} K n m • (J m + ψ m • h m)`

has a solution with `‖h n‖ ≤ P n * Φ n * exp (Ψ n)` for every `n`, and this is the only solution
which is `O(P)` at infinity.

This is the discrete analogue of the theorem on Volterra integral equations with separable
kernel bounds (Olver, Chapter 6, §10). The asymptotic theory of second-order linear difference
equations `w (n + 2) + f n * w (n + 1) + g n * w n = 0` whose coefficients have asymptotic
expansions in powers of `n⁻¹` reduces the construction of solutions with prescribed asymptotic
behaviour to equations of this form (Wong and Li).

The kernel `K` and the coefficient `ψ` take values in any normed field `𝕜`, and the forcing `J`
and the unknown `h` in any Banach space over `𝕜`.

## Main results

* `TauCeti.exists_discrete_volterra_solution`: existence of a solution with the bound
  `‖h n‖ ≤ P n * Φ n * exp (Ψ n)`.
* `TauCeti.discrete_volterra_solution_unique`: two solutions that are `O(P)` at infinity
  coincide.
* `TauCeti.existsUnique_discrete_volterra_solution`: exactly one solution is `O(P)` at infinity.
* `TauCeti.summable_discrete_volterra_of_isBigO`: for a sequence that is `O(P)` at infinity,
  every series in the equation converges absolutely.
* `Summable.tsum_Ioi_mul_pow_tsum_Ioi_le`: the estimate
  `∑_{m > n} a m * (∑_{j > m} a j) ^ k ≤ (∑_{m > n} a m) ^ (k + 1) / (k + 1)` for a nonnegative
  summable sequence `a`, which controls the iterates of the equation.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
* R. Wong and H. Li, Asymptotic expansions for second-order linear difference equations,
  *J. Comput. Appl. Math.* 41 (1992), 65–94.
* NIST Digital Library of Mathematical Functions, §2.9, <https://dlmf.nist.gov/2.9>.
-/

public section

open Filter Set Asymptotics
open scoped Nat

namespace TauCeti

/-- A sum over the natural numbers greater than `n` is the sum of the family shifted by
`n + 1`. -/
theorem tsum_Ioi_eq_tsum_nat_add {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    (f : ℕ → α) (n : ℕ) : ∑' m : Ioi n, f m = ∑' j, f (j + (n + 1)) := by
  have hrange : range (fun j : ℕ ↦ j + (n + 1)) = Ioi n := by
    ext m
    simp only [mem_range, mem_Ioi]
    exact ⟨fun ⟨j, hj⟩ ↦ by omega, fun hm ↦ ⟨m - (n + 1), by omega⟩⟩
  rw [← hrange, tsum_range f (add_left_injective (n + 1))]

section Tail

/-- The tail `∑_{m > n} f m` of a summable family splits off its first term `f (n + 1)`. -/
theorem _root_.Summable.tsum_Ioi_eq_add {α : Type*} [AddCommGroup α] [TopologicalSpace α]
    [IsTopologicalAddGroup α] [T2Space α] {f : ℕ → α} (hf : Summable f) (n : ℕ) :
    ∑' m : Ioi n, f m = f (n + 1) + ∑' m : Ioi (n + 1), f m := by
  rw [tsum_Ioi_eq_tsum_nat_add, tsum_Ioi_eq_tsum_nat_add,
    ((summable_nat_add_iff (n + 1)).2 hf).tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  exact tsum_congr fun j ↦ by congr 1; omega

variable {a : ℕ → ℝ}

/-- The tails `∑_{m > n} a m` of a nonnegative summable sequence decrease with `n`. -/
private lemma tsum_Ioi_le_tsum_Ioi (ha : Summable a) (ha0 : ∀ m, 0 ≤ a m) {n m : ℕ}
    (hnm : n ≤ m) : ∑' j : Ioi m, a j ≤ ∑' j : Ioi n, a j :=
  have hsub : Ioi m ⊆ Ioi n := Ioi_subset_Ioi hnm
  (ha.subtype _).tsum_le_tsum_of_inj (inclusion hsub) (inclusion_injective hsub)
    (fun j _ ↦ ha0 j) (fun _ ↦ le_rfl) (ha.subtype _)

/-- For a nonnegative summable sequence `a` with tails `Ψ n = ∑_{m > n} a m`,
`∑_{m > n} a m * Ψ m ^ k ≤ Ψ n ^ (k + 1) / (k + 1)`. This is the discrete counterpart of
`∫_x^∞ a(v) Ψ(v)^k dv = Ψ(x)^(k+1)/(k+1)` for `Ψ(x) = ∫_x^∞ a`. -/
theorem _root_.Summable.tsum_Ioi_mul_pow_tsum_Ioi_le (ha : Summable a) (ha0 : ∀ m, 0 ≤ a m)
    (n k : ℕ) :
    ∑' m : Ioi n, a m * (∑' j : Ioi (m : ℕ), a j) ^ k ≤
      (∑' m : Ioi n, a m) ^ (k + 1) / (k + 1) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, ∑' m : Ioi n, a m = Ψ n := ⟨_, fun _ ↦ rfl⟩
  simp only [hΨ]
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n ↦ hΨ n ▸ tsum_nonneg fun m ↦ ha0 m
  -- the tangent-line inequality `(k + 1) y x ^ k ≤ (x + y) ^ (k + 1) - x ^ (k + 1)`
  have hpow : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      (k + 1) * (y * x ^ k) ≤ (x + y) ^ (k + 1) - x ^ (k + 1) := by
    intro x y hx hy
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast at ih ⊢
      rw [pow_succ x k] at ih
      rw [pow_succ (x + y) (k + 1), pow_succ x (k + 1), pow_succ x k]
      have hk0 : (0 : ℝ) ≤ k + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right ih (add_nonneg hx hy),
        mul_nonneg hk0 (mul_nonneg (mul_nonneg hy hy) (pow_nonneg hx k))]
  -- telescoping over the partial sums, using `Ψ (m - 1) = Ψ m + a m`
  have hpartial : ∀ M, (k + 1) * ∑ j ∈ Finset.range M,
      a (j + (n + 1)) * Ψ (j + (n + 1)) ^ k ≤ Ψ n ^ (k + 1) - Ψ (n + M) ^ (k + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hsplit : Ψ (n + M) = Ψ (n + M + 1) + a (n + M + 1) := by
        rw [← hΨ, ← hΨ, ha.tsum_Ioi_eq_add]
        ring
      have hstep := hpow (Ψ (n + M + 1)) (a (n + M + 1)) (hΨ0 _) (ha0 _)
      rw [← hsplit] at hstep
      rw [Finset.sum_range_succ, mul_add, show M + (n + 1) = n + M + 1 by omega,
        show n + (M + 1) = n + M + 1 by omega]
      linarith
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [tsum_Ioi_eq_tsum_nat_add (fun m ↦ a m * Ψ m ^ k)]
  refine Real.tsum_le_of_sum_range_le (fun j ↦ mul_nonneg (ha0 _) (pow_nonneg (hΨ0 _) k))
    fun M ↦ ?_
  rw [le_div_iff₀ hk]
  linarith [hpartial M, pow_nonneg (hΨ0 (n + M)) (k + 1)]

end Tail

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {K : ℕ → ℕ → 𝕜} {J : ℕ → E} {ψ : ℕ → 𝕜} {P Q : ℕ → ℝ}

/-- One step of the iteration: if `‖x m‖ ≤ c * P m * Ψ m ^ k / k!` for every `m > n`, then
`‖∑_{m > n} K n m • ψ m • x m‖ ≤ c * P n * Ψ n ^ (k + 1) / (k + 1)!`. -/
private lemma norm_tsum_smul_smul_le (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) {x : ℕ → E} {c : ℝ} (hc : 0 ≤ c) (n k : ℕ)
    (hx : ∀ m, n < m → ‖x m‖ ≤
      c * P m * (∑' j : Ioi m, P j * Q j * ‖ψ j‖) ^ k / k !) :
    ‖∑' m : Ioi n, K n m • ψ m • x m‖ ≤
      c * P n * (∑' m : Ioi n, P m * Q m * ‖ψ m‖) ^ (k + 1) / (k + 1)! := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ m, P m * Q m * ‖ψ m‖ = a m := ⟨_, fun _ ↦ rfl⟩
  have ha0 : ∀ m, 0 ≤ a m := fun m ↦
    ha m ▸ mul_nonneg (mul_nonneg (hP m) (hQ m)) (norm_nonneg _)
  simp only [ha] at hψ hx ⊢
  have hS := hψ.tsum_Ioi_mul_pow_tsum_Ioi_le ha0 n k
  have hmono : ∀ m : Ioi n, ∑' j : Ioi (m : ℕ), a j ≤ ∑' j : Ioi n, a j :=
    fun m ↦ tsum_Ioi_le_tsum_Ioi hψ ha0 m.2.le
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, ∑' m : Ioi n, a m = Ψ n := ⟨_, fun _ ↦ rfl⟩
  simp only [hΨ] at hx hS hmono ⊢
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n ↦ hΨ n ▸ tsum_nonneg fun m ↦ ha0 m
  have hg : Summable fun m : Ioi n ↦ a m * Ψ m ^ k :=
    ((hψ.subtype (· ∈ Ioi n)).mul_right (Ψ n ^ k)).of_nonneg_of_le
      (fun m ↦ mul_nonneg (ha0 m) (pow_nonneg (hΨ0 m) k)) fun m ↦
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΨ0 m) (hmono m) k) (ha0 m)
  have hbound : ∀ m : Ioi n, ‖K n m • ψ m • x m‖ ≤ c * P n / k ! * (a m * Ψ m ^ k) := by
    intro m
    rw [norm_smul, norm_smul]
    calc ‖K n m‖ * (‖ψ m‖ * ‖x m‖)
        ≤ (P n * Q m) * (‖ψ m‖ * (c * P m * Ψ m ^ k / k !)) :=
          mul_le_mul (hK n m m.2) (mul_le_mul_of_nonneg_left (hx m m.2) (norm_nonneg _))
            (by positivity) (mul_nonneg (hP n) (hQ m))
      _ = c * P n / k ! * (a m * Ψ m ^ k) := by rw [← ha]; ring
  have hc' : 0 ≤ c * P n / k ! := by have := hP n; positivity
  refine (tsum_of_norm_bounded (hg.hasSum.mul_left (c * P n / k !)) hbound).trans ?_
  calc c * P n / k ! * ∑' m : Ioi n, a m * Ψ m ^ k
      ≤ c * P n / k ! * (Ψ n ^ (k + 1) / (k + 1)) := mul_le_mul_of_nonneg_left hS hc'
    _ = c * P n * Ψ n ^ (k + 1) / (k + 1)! := by
        rw [Nat.factorial_succ]; push_cast; field_simp

/-- The increments of the Picard iteration for the summation equation: the `0`-th is
`∑_{m > n} K n m • J m`, and each further one applies `x ↦ ∑_{m > n} K n m • ψ m • x m` to
the previous one. -/
private noncomputable def picardTerm (K : ℕ → ℕ → 𝕜) (J : ℕ → E) (ψ : ℕ → 𝕜) : ℕ → ℕ → E
  | 0, n => ∑' m : Ioi n, K n m • J m
  | k + 1, n => ∑' m : Ioi n, K n m • ψ m • picardTerm K J ψ k m

private lemma norm_picardTerm_le (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) (k n : ℕ) :
    ‖picardTerm K J ψ k n‖ ≤ (∑' m : Ioi n, Q m * ‖J m‖) * P n *
      ((∑' m : Ioi n, P m * Q m * ‖ψ m‖) ^ k / k !) := by
  have hb0 : ∀ m, 0 ≤ Q m * ‖J m‖ := fun m ↦ mul_nonneg (hQ m) (norm_nonneg _)
  induction k generalizing n with
  | zero =>
    have hbound : ∀ m : Ioi n, ‖K n m • J m‖ ≤ P n * (Q m * ‖J m‖) := fun m ↦ by
      rw [norm_smul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hK n m m.2) (norm_nonneg _)
    simpa [picardTerm, mul_comm] using
      tsum_of_norm_bounded ((hJ.subtype (· ∈ Ioi n)).hasSum.mul_left (P n)) hbound
  | succ k ih =>
    rw [picardTerm, mul_div_assoc']
    refine norm_tsum_smul_smul_le hP hQ hK hψ (tsum_nonneg fun m : Ioi n ↦ hb0 m) n k
      fun m hm ↦ ?_
    have hPm := hP m
    have hΨm : 0 ≤ ∑' j : Ioi m, P j * Q j * ‖ψ j‖ :=
      tsum_nonneg fun j ↦ mul_nonneg (mul_nonneg (hP j) (hQ j)) (norm_nonneg _)
    calc ‖picardTerm K J ψ k m‖
        ≤ (∑' j : Ioi m, Q j * ‖J j‖) * (P m * ((∑' j : Ioi m, P j * Q j * ‖ψ j‖) ^ k / k !)) :=
          by rw [← mul_assoc]; exact ih m
      _ ≤ (∑' j : Ioi n, Q j * ‖J j‖) * (P m * ((∑' j : Ioi m, P j * Q j * ‖ψ j‖) ^ k / k !)) :=
          mul_le_mul_of_nonneg_right (tsum_Ioi_le_tsum_Ioi hJ hb0 hm.le) (by positivity)
      _ = _ := by ring

/-- The double series `∑_{m > n} ∑_k K n m • ψ m • picardTerm K J ψ k m` converges
absolutely. -/
private lemma summable_uncurry_smul_smul_picardTerm (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) [CompleteSpace E] (n : ℕ) :
    Summable (Function.uncurry fun (m : Ioi n) (k : ℕ) ↦ K n m • ψ m • picardTerm K J ψ k m) := by
  set Φ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, Q m * ‖J m‖
  set Ψ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, P m * Q m * ‖ψ m‖
  set a : ℕ → ℝ := fun m ↦ P m * Q m * ‖ψ m‖ with ha_def
  have hb0 : ∀ m, 0 ≤ Q m * ‖J m‖ := fun m ↦ mul_nonneg (hQ m) (norm_nonneg _)
  have ha0 : ∀ m, 0 ≤ a m := fun m ↦ mul_nonneg (mul_nonneg (hP m) (hQ m)) (norm_nonneg _)
  have hΦ0 : ∀ n, 0 ≤ Φ n := fun n ↦ tsum_nonneg fun m ↦ hb0 m
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n ↦ tsum_nonneg fun m ↦ ha0 m
  have hbound : ∀ (m : Ioi n) (k : ℕ), ‖K n m • ψ m • picardTerm K J ψ k m‖ ≤
      Φ n * P n * (a m * (Ψ n ^ k / k !)) := fun m k ↦ by
    have hm := m.2
    have hPm := hP m
    have := hΦ0 n
    have := hΨ0 m
    rw [norm_smul, norm_smul]
    calc ‖K n m‖ * (‖ψ m‖ * ‖picardTerm K J ψ k m‖)
        ≤ (P n * Q m) * (‖ψ m‖ * (Φ m * P m * (Ψ m ^ k / k !))) :=
          mul_le_mul (hK n m hm) (mul_le_mul_of_nonneg_left
            (norm_picardTerm_le hP hQ hK hJ hψ k m) (norm_nonneg _))
            (by positivity) (mul_nonneg (hP n) (hQ m))
      _ ≤ (P n * Q m) * (‖ψ m‖ * (Φ n * P m * (Ψ n ^ k / k !))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul
            (mul_le_mul_of_nonneg_right (tsum_Ioi_le_tsum_Ioi hJ hb0 hm.le) hPm)
            (div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (hΨ0 m) (tsum_Ioi_le_tsum_Ioi hψ ha0 hm.le) k) (by positivity))
            (by positivity) (by positivity))
            (norm_nonneg _)) (mul_nonneg (hP n) (hQ m))
      _ = Φ n * P n * (a m * (Ψ n ^ k / k !)) := by simp only [ha_def]; ring
  refine Summable.of_norm_bounded ?_ fun p ↦ hbound p.1 p.2
  exact ((hψ.subtype (· ∈ Ioi n)).mul_of_nonneg (Real.summable_pow_div_factorial (Ψ n))
    (fun m ↦ ha0 m) fun k ↦ by have := hΨ0 n; positivity).mul_left _

omit [NormedSpace 𝕜 E] in
/-- A sequence with `‖h n‖ ≤ P n * Φ n * exp (Ψ n)` is `O(P)` at infinity. -/
private lemma isBigO_of_norm_le (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hJ : Summable fun m ↦ Q m * ‖J m‖) (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖)
    {h : ℕ → E} (hh : ∀ n, ‖h n‖ ≤ P n * (∑' m : Ioi n, Q m * ‖J m‖) *
      Real.exp (∑' m : Ioi n, P m * Q m * ‖ψ m‖)) :
    h =O[atTop] P := by
  have hb0 : ∀ m, 0 ≤ Q m * ‖J m‖ := fun m ↦ mul_nonneg (hQ m) (norm_nonneg _)
  have ha0 : ∀ m, 0 ≤ P m * Q m * ‖ψ m‖ := fun m ↦
    mul_nonneg (mul_nonneg (hP m) (hQ m)) (norm_nonneg _)
  refine IsBigO.of_bound ((∑' m : Ioi 0, Q m * ‖J m‖) *
    Real.exp (∑' m : Ioi 0, P m * Q m * ‖ψ m‖)) (Eventually.of_forall fun n ↦ ?_)
  rw [Real.norm_of_nonneg (hP n)]
  refine (hh n).trans ?_
  rw [mul_assoc, mul_comm (P n)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (tsum_Ioi_le_tsum_Ioi hJ hb0 (Nat.zero_le n))
    (Real.exp_le_exp.2 (tsum_Ioi_le_tsum_Ioi hψ ha0 (Nat.zero_le n))) (Real.exp_pos _).le
    (tsum_nonneg fun m ↦ hb0 m)) (hP n)

variable [CompleteSpace E]

/-- For a sequence `h` that is `O(P)` at infinity, every series of the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` converges absolutely. -/
theorem summable_discrete_volterra_of_isBigO (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) {h : ℕ → E} (hh : h =O[atTop] P) (n : ℕ) :
    Summable fun m : Ioi n ↦ K n m • (J m + ψ m • h m) := by
  obtain ⟨C, hC⟩ := hh.bound
  have hev' : ∀ᶠ m in cofinite, ‖h m‖ ≤ max C 0 * P m := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hC] with m hm
    rw [Real.norm_of_nonneg (hP m)] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hP m))
  have hev : ∀ᶠ m : Ioi n in cofinite, ‖h m‖ ≤ max C 0 * P m :=
    Subtype.val_injective.tendsto_cofinite.eventually hev'
  refine Summable.of_norm_bounded_eventually (g := fun m : Ioi n ↦
      P n * (Q m * ‖J m‖ + max C 0 * (P m * Q m * ‖ψ m‖)))
    (((hJ.add (hψ.mul_left (max C 0))).subtype (· ∈ Ioi n)).mul_left (P n)) ?_
  filter_upwards [hev] with m hm
  rw [norm_smul]
  calc ‖K n m‖ * ‖J m + ψ m • h m‖
      ≤ (P n * Q m) * (‖J m‖ + ‖ψ m‖ * (max C 0 * P m)) := by
        refine mul_le_mul (hK n m m.2) ((norm_add_le _ _).trans ?_) (norm_nonneg _)
          (mul_nonneg (hP n) (hQ m))
        rw [norm_smul]
        gcongr
    _ = P n * (Q m * ‖J m‖ + max C 0 * (P m * Q m * ‖ψ m‖)) := by ring

/-- **Volterra summation equations, existence.** If `‖K n m‖ ≤ P n * Q m` for `n < m`, with
`P, Q ≥ 0`, and the series `∑ Q ‖J‖` and `∑ P Q ‖ψ‖` converge, then the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` has a solution such that
`‖h n‖ ≤ P n * Φ n * exp (Ψ n)`, where `Φ n = ∑_{m > n} Q m * ‖J m‖` and
`Ψ n = ∑_{m > n} P m * Q m * ‖ψ m‖`. Its series converge absolutely, by
`summable_discrete_volterra_of_isBigO`. -/
theorem exists_discrete_volterra_solution (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) :
    ∃ h : ℕ → E, (∀ n, h n = ∑' m : Ioi n, K n m • (J m + ψ m • h m)) ∧
      ∀ n, ‖h n‖ ≤ P n * (∑' m : Ioi n, Q m * ‖J m‖) *
        Real.exp (∑' m : Ioi n, P m * Q m * ‖ψ m‖) := by
  set Φ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, Q m * ‖J m‖
  set Ψ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, P m * Q m * ‖ψ m‖
  set T := picardTerm K J ψ
  -- the increments are dominated by the exponential series
  have hexp : ∀ n, HasSum (fun k ↦ Φ n * P n * (Ψ n ^ k / k !))
      (Φ n * P n * Real.exp (Ψ n)) := fun n ↦ by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (Ψ n)).mul_left _
  have hT : ∀ n, Summable fun k ↦ T k n := fun n ↦
    (hexp n).summable.of_norm_bounded fun k ↦ norm_picardTerm_le hP hQ hK hJ hψ k n
  set h : ℕ → E := fun n ↦ ∑' k, T k n with h_def
  have hh : ∀ n, ‖h n‖ ≤ P n * Φ n * Real.exp (Ψ n) := fun n ↦ by
    rw [mul_comm (P n)]
    exact tsum_of_norm_bounded (hexp n) fun k ↦ norm_picardTerm_le hP hQ hK hJ hψ k n
  refine ⟨h, fun n ↦ ?_, hh⟩
  -- split the series into its `J`-part and its `h`-part
  have hKJ : Summable fun m : Ioi n ↦ K n m • J m :=
    ((hJ.subtype (· ∈ Ioi n)).mul_left (P n)).of_norm_bounded fun m ↦ by
      rw [Function.comp_apply, norm_smul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hK n m m.2) (norm_nonneg _)
  have hsum := summable_discrete_volterra_of_isBigO hP hQ hK hJ hψ
    (isBigO_of_norm_le hP hQ hJ hψ hh) n
  simp only [smul_add] at hsum ⊢
  rw [hKJ.tsum_add (by simpa using hsum.sub hKJ)]
  -- expand `h m` as the series of increments and interchange the two sums
  have hinner : ∀ m : Ioi n, K n m • ψ m • h m = ∑' k, K n m • ψ m • T k m := fun m ↦ by
    rw [h_def, tsum_const_smul'', tsum_const_smul'']
  simp only [hinner]
  rw [(summable_uncurry_smul_smul_picardTerm hP hQ hK hJ hψ n).tsum_comm.symm]
  calc h n = T 0 n + ∑' k, T (k + 1) n := (hT n).tsum_eq_zero_add
    _ = _ := by simp only [T, picardTerm]

/-- **Volterra summation equations, uniqueness.** Under the hypotheses of
`exists_discrete_volterra_solution`, two solutions of the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` that are `O(P)` at infinity coincide. -/
theorem discrete_volterra_solution_unique (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) {h₁ h₂ : ℕ → E}
    (h₁_eq : ∀ n, h₁ n = ∑' m : Ioi n, K n m • (J m + ψ m • h₁ m))
    (h₂_eq : ∀ n, h₂ n = ∑' m : Ioi n, K n m • (J m + ψ m • h₂ m))
    (h₁_isBigO : h₁ =O[atTop] P) (h₂_isBigO : h₂ =O[atTop] P) : h₁ = h₂ := by
  set d : ℕ → E := h₁ - h₂ with hd_def
  -- the difference solves the homogeneous equation
  have hd : ∀ n, d n = ∑' m : Ioi n, K n m • ψ m • d m := fun n ↦ by
    rw [hd_def, Pi.sub_apply, h₁_eq, h₂_eq,
      ← (summable_discrete_volterra_of_isBigO hP hQ hK hJ hψ h₁_isBigO n).tsum_sub
        (summable_discrete_volterra_of_isBigO hP hQ hK hJ hψ h₂_isBigO n)]
    refine tsum_congr fun m ↦ ?_
    rw [← smul_sub, add_sub_add_left_eq_sub, ← smul_sub, Pi.sub_apply]
  obtain ⟨C, hC⟩ := (h₁_isBigO.sub h₂_isBigO).bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hC
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  set Ψ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, P m * Q m * ‖ψ m‖
  -- beyond `N`, the iterated estimates give `‖d n‖ ≤ C' * P n * Ψ n ^ k / k!` for every `k`
  have hiter : ∀ k n, N ≤ n → ‖d n‖ ≤ C' * P n * Ψ n ^ k / k ! := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have := hN n hn
      rw [Real.norm_of_nonneg (hP n)] at this
      rw [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hP n))
    | succ k ih =>
      intro n hn
      rw [hd n]
      exact norm_tsum_smul_smul_le hP hQ hK hψ hC' n k fun m hm ↦ ih m (hn.trans hm.le)
  have hzero : ∀ n, N ≤ n → d n = 0 := by
    intro n hn
    have hlim : Tendsto (fun k ↦ C' * P n * (Ψ n ^ k / k !)) atTop (nhds 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (Ψ n)).const_mul (C' * P n)
    refine norm_le_zero_iff.1 (ge_of_tendsto' hlim fun k ↦ ?_)
    rw [← mul_div_assoc]
    exact hiter k n hn
  -- below `N`, the homogeneous equation propagates the vanishing downwards
  have hdown : ∀ i n, N ≤ n + i → d n = 0 := by
    intro i
    induction i with
    | zero => exact hzero
    | succ i ih =>
      intro n hn
      rw [hd n]
      refine (tsum_congr fun m ↦ ?_).trans tsum_zero
      rw [ih m (by have := m.2; simp only [mem_Ioi] at this; omega), smul_zero, smul_zero]
  funext n
  exact sub_eq_zero.1 (hdown N n (by omega))

/-- **Volterra summation equations.** Under the hypotheses of
`exists_discrete_volterra_solution`, the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` has exactly one solution that is `O(P)` at
infinity. -/
theorem existsUnique_discrete_volterra_solution (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) :
    ∃! h : ℕ → E, (∀ n, h n = ∑' m : Ioi n, K n m • (J m + ψ m • h m)) ∧ h =O[atTop] P := by
  obtain ⟨h, hh_eq, hh_le⟩ := exists_discrete_volterra_solution hP hQ hK hJ hψ
  have hh_isBigO := isBigO_of_norm_le hP hQ hJ hψ hh_le
  exact ⟨h, ⟨hh_eq, hh_isBigO⟩, fun h' ⟨hh'_eq, hh'_isBigO⟩ ↦
    discrete_volterra_solution_unique hP hQ hK hJ hψ hh'_eq hh_eq hh'_isBigO hh_isBigO⟩

end TauCeti
