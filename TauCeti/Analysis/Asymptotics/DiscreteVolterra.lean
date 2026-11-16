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
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.Topology.Algebra.InfiniteSum.Real

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
* `TauCeti.norm_discrete_volterra_solution_le`: every solution that is `O(P)` at infinity
  satisfies the bound `‖h n‖ ≤ P n * Φ n * exp (Ψ n)`.
* `TauCeti.isBigO_of_norm_le_discrete_volterra_bound`: conversely, every sequence satisfying
  this bound is `O(P)` at infinity.
* `TauCeti.summable_norm_discrete_volterra_of_isBigO`: for a sequence that is `O(P)` at
  infinity, every series in the equation converges absolutely.
* `TauCeti.summable_discrete_volterra_of_isBigO`: hence, in a Banach space, every series in the
  equation is summable.

The iterates of the equation are controlled by the estimate
`Summable.tsum_Ioi_mul_pow_tsum_Ioi_le`.

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

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {K : ℕ → ℕ → 𝕜} {J : ℕ → E} {ψ : ℕ → 𝕜} {P Q : ℕ → ℝ}

omit [NormedSpace 𝕜 E] in
/-- The weights `Q m * ‖J m‖` of the forcing series are nonnegative. -/
private lemma forcing_weight_nonneg (hQ : ∀ m, 0 ≤ Q m) (m : ℕ) : 0 ≤ Q m * ‖J m‖ :=
  mul_nonneg (hQ m) (norm_nonneg _)

/-- The weights `P m * Q m * ‖ψ m‖` of the coefficient series are nonnegative. -/
private lemma coeff_weight_nonneg (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m) (m : ℕ) :
    0 ≤ P m * Q m * ‖ψ m‖ :=
  mul_nonneg (mul_nonneg (hP m) (hQ m)) (norm_nonneg _)

/-- The separable kernel bound applied to a vector: `‖K n m • y‖ ≤ P n * (Q m * ‖y‖)`. -/
private lemma norm_kernel_smul_le (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) {n m : ℕ}
    (hnm : n < m) (y : E) : ‖K n m • y‖ ≤ P n * (Q m * ‖y‖) := by
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hK n m hnm) (norm_nonneg _)

/-- The separable kernel bound applied to `ψ m • y`:
`‖K n m • ψ m • y‖ ≤ P n * (Q m * ‖ψ m‖ * ‖y‖)`. -/
private lemma norm_kernel_smul_smul_le (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) {n m : ℕ}
    (hnm : n < m) (y : E) : ‖K n m • ψ m • y‖ ≤ P n * (Q m * ‖ψ m‖ * ‖y‖) :=
  (norm_kernel_smul_le hK hnm _).trans_eq (by rw [norm_smul, mul_assoc])

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
  have ha0 : ∀ m, 0 ≤ a m := fun m ↦ ha m ▸ coeff_weight_nonneg hP hQ m
  simp only [ha] at hψ hx ⊢
  have hS := hψ.tsum_Ioi_mul_pow_tsum_Ioi_le ha0 n k
  have hg : Summable fun m : Ioi n ↦ a m * (∑' j : Ioi (m : ℕ), a j) ^ k :=
    (hψ.mul_pow_tsum_Ioi ha0 k).subtype _
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, ∑' m : Ioi n, a m = Ψ n := ⟨_, fun _ ↦ rfl⟩
  simp only [hΨ] at hx hS hg ⊢
  have hbound : ∀ m : Ioi n, ‖K n m • ψ m • x m‖ ≤ c * P n / k ! * (a m * Ψ m ^ k) := fun m ↦
    calc ‖K n m • ψ m • x m‖
        ≤ P n * (Q m * ‖ψ m‖ * (c * P m * Ψ m ^ k / k !)) :=
          (norm_kernel_smul_smul_le hK m.2 _).trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hx m m.2) (mul_nonneg (hQ m) (norm_nonneg _))) (hP n))
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
  induction k generalizing n with
  | zero =>
    simpa [picardTerm, mul_comm] using
      tsum_of_norm_bounded ((hJ.subtype (· ∈ Ioi n)).hasSum.mul_left (P n))
        fun m : Ioi n ↦ norm_kernel_smul_le hK m.2 (J m)
  | succ k ih =>
    rw [picardTerm, mul_div_assoc']
    refine norm_tsum_smul_smul_le hP hQ hK hψ
      (tsum_nonneg fun m : Ioi n ↦ forcing_weight_nonneg hQ m) n k fun m hm ↦ ?_
    have hPm := hP m
    have hΨm : 0 ≤ ∑' j : Ioi m, P j * Q j * ‖ψ j‖ :=
      tsum_nonneg fun j ↦ coeff_weight_nonneg hP hQ j
    calc ‖picardTerm K J ψ k m‖
        ≤ (∑' j : Ioi m, Q j * ‖J j‖) * (P m * ((∑' j : Ioi m, P j * Q j * ‖ψ j‖) ^ k / k !)) :=
          by rw [← mul_assoc]; exact ih m
      _ ≤ (∑' j : Ioi n, Q j * ‖J j‖) * (P m * ((∑' j : Ioi m, P j * Q j * ‖ψ j‖) ^ k / k !)) :=
          mul_le_mul_of_nonneg_right (hJ.antitone_tsum_Ioi (forcing_weight_nonneg hQ) hm.le)
            (by positivity)
      _ = _ := by ring

/-- The family `(m, k) ↦ K n m • ψ m • picardTerm K J ψ k m` on `Ioi n × ℕ` is summable. -/
private lemma summable_uncurry_smul_smul_picardTerm (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) [CompleteSpace E] (n : ℕ) :
    Summable (Function.uncurry fun (m : Ioi n) (k : ℕ) ↦ K n m • ψ m • picardTerm K J ψ k m) := by
  set Φ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, Q m * ‖J m‖
  set Ψ : ℕ → ℝ := fun n ↦ ∑' m : Ioi n, P m * Q m * ‖ψ m‖
  set a : ℕ → ℝ := fun m ↦ P m * Q m * ‖ψ m‖ with ha_def
  have ha0 : ∀ m, 0 ≤ a m := coeff_weight_nonneg hP hQ
  have hΦ0 : ∀ n, 0 ≤ Φ n := fun n ↦ tsum_nonneg fun m ↦ forcing_weight_nonneg hQ m
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n ↦ tsum_nonneg fun m ↦ ha0 m
  have hbound : ∀ (m : Ioi n) (k : ℕ), ‖K n m • ψ m • picardTerm K J ψ k m‖ ≤
      Φ n * P n * (a m * (Ψ n ^ k / k !)) := fun m k ↦ by
    have hm := m.2
    have hPm := hP m
    have := hΦ0 n
    have := hΨ0 m
    have := hP n
    have hQψ : 0 ≤ Q m * ‖ψ m‖ := mul_nonneg (hQ m) (norm_nonneg _)
    calc ‖K n m • ψ m • picardTerm K J ψ k m‖
        ≤ P n * (Q m * ‖ψ m‖ * (Φ m * P m * (Ψ m ^ k / k !))) :=
          (norm_kernel_smul_smul_le hK hm _).trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_picardTerm_le hP hQ hK hJ hψ k m) hQψ) (hP n))
      _ ≤ P n * (Q m * ‖ψ m‖ * (Φ n * P m * (Ψ n ^ k / k !))) := by
          gcongr
          · exact hJ.antitone_tsum_Ioi (forcing_weight_nonneg hQ) hm.le
          · exact hψ.antitone_tsum_Ioi ha0 hm.le
      _ = Φ n * P n * (a m * (Ψ n ^ k / k !)) := by simp only [ha_def]; ring
  refine Summable.of_norm_bounded ?_ fun p ↦ hbound p.1 p.2
  exact ((hψ.subtype (· ∈ Ioi n)).mul_of_nonneg (Real.summable_pow_div_factorial (Ψ n))
    (fun m ↦ ha0 m) fun k ↦ by have := hΨ0 n; positivity).mul_left _

omit [NormedSpace 𝕜 E] in
/-- A sequence satisfying the bound `‖h n‖ ≤ P n * Φ n * exp (Ψ n)` of
`exists_discrete_volterra_solution`, where `Φ n = ∑_{m > n} Q m * ‖J m‖` and
`Ψ n = ∑_{m > n} P m * Q m * ‖ψ m‖`, is `O(P)` at infinity. -/
theorem isBigO_of_norm_le_discrete_volterra_bound (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hJ : Summable fun m ↦ Q m * ‖J m‖) (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖)
    {h : ℕ → E} (hh : ∀ n, ‖h n‖ ≤ P n * (∑' m : Ioi n, Q m * ‖J m‖) *
      Real.exp (∑' m : Ioi n, P m * Q m * ‖ψ m‖)) :
    h =O[atTop] P := by
  have hb0 : ∀ m, 0 ≤ Q m * ‖J m‖ := forcing_weight_nonneg hQ
  refine IsBigO.of_bound ((∑' m : Ioi 0, Q m * ‖J m‖) *
    Real.exp (∑' m : Ioi 0, P m * Q m * ‖ψ m‖)) (Eventually.of_forall fun n ↦ ?_)
  rw [Real.norm_of_nonneg (hP n)]
  refine (hh n).trans ?_
  rw [mul_assoc, mul_comm (P n)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hJ.antitone_tsum_Ioi hb0 (Nat.zero_le n))
    (Real.exp_le_exp.2 (hψ.antitone_tsum_Ioi (coeff_weight_nonneg hP hQ) (Nat.zero_le n)))
    (Real.exp_pos _).le (tsum_nonneg fun m ↦ hb0 m)) (hP n)

/-- For a sequence `h` that is `O(P)` at infinity, every series of the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` converges absolutely. -/
theorem summable_norm_discrete_volterra_of_isBigO (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) {h : ℕ → E} (hh : h =O[atTop] P) (n : ℕ) :
    Summable fun m : Ioi n ↦ ‖K n m • (J m + ψ m • h m)‖ := by
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
  rw [norm_norm]
  calc ‖K n m • (J m + ψ m • h m)‖
      ≤ P n * (Q m * (‖J m‖ + ‖ψ m‖ * (max C 0 * P m))) := by
        refine (norm_kernel_smul_le hK m.2 _).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (hQ m)) (hP n))
        rw [norm_smul]
        gcongr
    _ = P n * (Q m * ‖J m‖ + max C 0 * (P m * Q m * ‖ψ m‖)) := by ring

variable [CompleteSpace E]

/-- For a sequence `h` that is `O(P)` at infinity, every series of the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` is summable in the Banach space `E`. -/
theorem summable_discrete_volterra_of_isBigO (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) {h : ℕ → E} (hh : h =O[atTop] P) (n : ℕ) :
    Summable fun m : Ioi n ↦ K n m • (J m + ψ m • h m) :=
  (summable_norm_discrete_volterra_of_isBigO hP hQ hK hJ hψ hh n).of_norm

/-- **Volterra summation equations, existence.** If `‖K n m‖ ≤ P n * Q m` for `n < m`, with
`P, Q ≥ 0`, and the series `∑ Q ‖J‖` and `∑ P Q ‖ψ‖` converge, then the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` has a solution such that
`‖h n‖ ≤ P n * Φ n * exp (Ψ n)`, where `Φ n = ∑_{m > n} Q m * ‖J m‖` and
`Ψ n = ∑_{m > n} P m * Q m * ‖ψ m‖`. By `existsUnique_discrete_volterra_solution`, it is the
only solution that is `O(P)` at infinity. -/
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
    ((hJ.subtype (· ∈ Ioi n)).mul_left (P n)).of_norm_bounded fun m ↦
      norm_kernel_smul_le hK m.2 (J m)
  have hsum := summable_discrete_volterra_of_isBigO hP hQ hK hJ hψ
    (isBigO_of_norm_le_discrete_volterra_bound hP hQ hJ hψ hh) n
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

/-- **Volterra summation equations, bound.** Under the hypotheses of
`exists_discrete_volterra_solution`, every solution of the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` that is `O(P)` at infinity satisfies
`‖h n‖ ≤ P n * Φ n * exp (Ψ n)`, where `Φ n = ∑_{m > n} Q m * ‖J m‖` and
`Ψ n = ∑_{m > n} P m * Q m * ‖ψ m‖`. -/
theorem norm_discrete_volterra_solution_le (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) {h : ℕ → E}
    (h_eq : ∀ n, h n = ∑' m : Ioi n, K n m • (J m + ψ m • h m)) (h_isBigO : h =O[atTop] P)
    (n : ℕ) :
    ‖h n‖ ≤ P n * (∑' m : Ioi n, Q m * ‖J m‖) * Real.exp (∑' m : Ioi n, P m * Q m * ‖ψ m‖) := by
  obtain ⟨h₀, h₀_eq, h₀_le⟩ := exists_discrete_volterra_solution hP hQ hK hJ hψ
  rw [discrete_volterra_solution_unique hP hQ hK hJ hψ h_eq h₀_eq h_isBigO
    (isBigO_of_norm_le_discrete_volterra_bound hP hQ hJ hψ h₀_le)]
  exact h₀_le n

/-- **Volterra summation equations.** Under the hypotheses of
`exists_discrete_volterra_solution`, the summation equation
`h n = ∑_{m > n} K n m • (J m + ψ m • h m)` has exactly one solution that is `O(P)` at
infinity. -/
theorem existsUnique_discrete_volterra_solution (hP : ∀ n, 0 ≤ P n) (hQ : ∀ m, 0 ≤ Q m)
    (hK : ∀ n m, n < m → ‖K n m‖ ≤ P n * Q m) (hJ : Summable fun m ↦ Q m * ‖J m‖)
    (hψ : Summable fun m ↦ P m * Q m * ‖ψ m‖) :
    ∃! h : ℕ → E, (∀ n, h n = ∑' m : Ioi n, K n m • (J m + ψ m • h m)) ∧ h =O[atTop] P := by
  obtain ⟨h, hh_eq, hh_le⟩ := exists_discrete_volterra_solution hP hQ hK hJ hψ
  have hh_isBigO := isBigO_of_norm_le_discrete_volterra_bound hP hQ hJ hψ hh_le
  exact ⟨h, ⟨hh_eq, hh_isBigO⟩, fun h' ⟨hh'_eq, hh'_isBigO⟩ ↦
    discrete_volterra_solution_unique hP hQ hK hJ hψ hh'_eq hh_eq hh'_isBigO hh_isBigO⟩

end TauCeti
