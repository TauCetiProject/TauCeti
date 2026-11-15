/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Baker.CoordinateDivision

/-!
# Schwarz's lemma for Cartesian products

Let `f : (Fin n → ℂ) → ℂ` be an entire function bounded by `M` on the closed polydisc
`closedBall c R` of radius `R ≥ r` around `c`. Suppose that for each coordinate `i : Fin n` we are
given a finite set `E i ⊆ closedBall (c i) r` and multiplicities `k i : ℂ → ℕ` of total weight
`∑ ζ ∈ E i, k i ζ = p`, and that every mixed partial derivative `mDeriv σ f ξ` with
`∀ i, σ i < k i (ξ i)` vanishes on the Cartesian product `{ξ | ∀ i, ξ i ∈ E i}`.

Dividing `f` by the monic coordinate polynomials `P i = ∏ ζ ∈ E i, (X - C ζ) ^ k i ζ` of degree `p`
expresses `f(z)` as `∑ i, g i z * (P i).eval (z i)` with controlled supremum norms on
`closedBall c R`, yielding the sharp estimate `‖f z‖ ≤ M * (6 ^ n * r / R) ^ p` on `closedBall c r`
(including the degenerate cases `p = 0`, `n = 0`, `r = 0`, and `r ≤ R < 5 * r`). For finite sets of
cardinality `#(E i) ≥ S₁` and uniform coordinate multiplicity `S₀`, this specialises directly to
Waldschmidt's Schwarz lemma for Cartesian products `‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁)` — the
analytic extrapolation tool in several-variable transcendence proofs such as the Schneider–Lang
criterion and Baker's theorem on linear forms in logarithms.

## Main results

* `TauCeti.Baker.norm_le_mul_six_pow_mul_div_pow_of_sum_eq`: weighted Cartesian zero-set Schwarz
  lemma with factor `(6 ^ n * r / R) ^ p` when `∀ i, ∑ ζ ∈ E i, k i ζ = p` and `r ≤ R`.
* `TauCeti.Baker.norm_le_mul_eighteen_pow_mul_div_pow`: Waldschmidt's Schwarz lemma for Cartesian
  products (`W00`, §4.3, Proposition 4.7), bounding `‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁)` on
  `closedBall c r` whenever `∀ i, S₁ ≤ #(E i)`, `∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r`, `r ≤ R`,
  and `mDeriv σ f ξ = 0` on `E 0 × ⋯ × E (n - 1)` for `∀ i, σ i < S₀`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Proposition 4.7, p. 122, and its proof, pp. 129–130.
-/

public section

open Finset Metric Polynomial

namespace TauCeti.Baker

/-- **Weighted Schwarz's lemma for Cartesian products.**
Let `f : (Fin n → ℂ) → ℂ` be entire and bounded by `M` on `closedBall c R` with `r ≤ R`. Suppose
`E : Fin n → Finset ℂ` and `k : Fin n → ℂ → ℕ` satisfy `∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r`
and `∀ i, ∑ ζ ∈ E i, k i ζ = p`. If `mDeriv σ f ξ = 0` whenever `∀ i, ξ i ∈ E i` and
`∀ i, σ i < k i (ξ i)`, then for every `z ∈ closedBall c r`,
`‖f z‖ ≤ M * (6 ^ n * r / R) ^ p`. -/
theorem norm_le_mul_six_pow_mul_div_pow_of_sum_eq {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {E : Fin n → Finset ℂ} {k : Fin n → ℂ → ℕ} {p : ℕ}
    (hsum : ∀ i, ∑ ζ ∈ E i, k i ζ = p)
    {c : Fin n → ℂ} {r R M : ℝ} (hE : ∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r)
    (hrR : r ≤ R)
    (hzero : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) →
      ∀ σ : Fin n → ℕ, (∀ i, σ i < k i (ξ i)) → mDeriv σ f ξ = 0)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ M * (6 ^ n * r / R) ^ p := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hz)
  have _hR0 : 0 ≤ R := hr.trans hrR
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hfz : ‖f z‖ ≤ M := hM z hzR
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans hfz
  -- Handle the degenerate cases `p = 0`, `n = 0`, `r = 0`, and `R < 5 * r` first.
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simpa using hfz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hf0 : f z = 0 := by
      have h := hzero z (fun i ↦ i.elim0) 0 (fun i ↦ i.elim0)
      rwa [mDeriv_zero] at h
    rw [hf0, norm_zero]
    positivity
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · have hz_eq : z = c := dist_le_zero.mp (mem_closedBall.mp hz)
    have hz_mem : ∀ i, z i ∈ E i ∧ 0 < k i (z i) := fun i ↦ by
      obtain ⟨a, haE, hka⟩ := exists_ne_zero_of_sum_ne_zero ((hsum i).trans_ne hp.ne')
      have hac : a = c i := dist_le_zero.mp (mem_closedBall.mp (hE i haE))
      rw [hz_eq, ← hac]
      exact ⟨haE, Nat.pos_of_ne_zero hka⟩
    have hf0 : f z = 0 := by
      have h := hzero z (fun i ↦ (hz_mem i).1) 0 (fun i ↦ (hz_mem i).2)
      rwa [mDeriv_zero] at h
    rw [hf0, norm_zero]
    positivity
  rcases lt_or_ge R (5 * r) with hR_small | hR_large
  · have hR_pos : 0 < R := hr_pos.trans_le hrR
    have h6 : (6 : ℝ) ≤ (6 : ℝ) ^ n := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6) hn
    have h1 : 1 ≤ 6 ^ n * r / R := by
      rw [one_le_div hR_pos]
      nlinarith
    calc ‖f z‖ ≤ M := hfz
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (6 ^ n * r / R) ^ p := mul_le_mul_of_nonneg_left (one_le_pow₀ h1) hM0
  -- Main case: `0 < p`, `0 < n`, `0 < r`, and `5 * r ≤ R`. Divide `f` by the monic coordinate
  -- polynomials `P i = ∏ ζ ∈ E i, (X - C ζ) ^ k i ζ` of degree `p`.
  have hR_pos : 0 < R := by linarith
  let P : Fin n → ℂ[X] := fun i ↦ ∏ ζ ∈ E i, (X - C ζ) ^ k i ζ
  have hP_monic (i : Fin n) : (P i).Monic :=
    monic_prod_of_monic (E i) _ fun ζ _ ↦ (monic_X_sub_C ζ).pow (k i ζ)
  have hP_deg (i : Fin n) : (P i).natDegree = p := by
    dsimp only [P]
    calc (∏ ζ ∈ E i, (X - C ζ) ^ k i ζ).natDegree
        = ∑ ζ ∈ E i, ((X - C ζ) ^ k i ζ).natDegree :=
          natDegree_prod_of_monic _ _ fun ζ _ ↦ (monic_X_sub_C ζ).pow (k i ζ)
      _ = ∑ ζ ∈ E i, k i ζ := by
          refine sum_congr rfl fun ζ _ ↦ ?_
          rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      _ = p := hsum i
  have hP_root_mem (i : Fin n) (ζ : ℂ) (hζ : (P i).IsRoot ζ) : ζ ∈ E i := by
    rw [isRoot_prod] at hζ
    obtain ⟨η, hηE, hη⟩ := hζ
    rw [IsRoot.def, eval_pow, eval_sub, eval_X, eval_C] at hη
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hη) ▸ hηE
  have hP_roots (i : Fin n) (ζ : ℂ) (hζ : (P i).IsRoot ζ) : ζ ∈ closedBall (c i) r :=
    hE i (hP_root_mem i ζ hζ)
  have hP_mult (i : Fin n) (a : ℂ) (ha : a ∈ E i) : (P i).rootMultiplicity a = k i a := by
    have hsplit : P i = (∏ ζ ∈ (E i).erase a, (X - C ζ) ^ k i ζ) * (X - C a) ^ k i a := by
      dsimp only [P]
      rw [← mul_prod_erase (E i) _ ha, mul_comm]
    set q : ℂ[X] := ∏ ζ ∈ (E i).erase a, (X - C ζ) ^ k i ζ
    have hq_monic : q.Monic :=
      monic_prod_of_monic _ _ fun ζ _ ↦ (monic_X_sub_C ζ).pow (k i ζ)
    have hq_not_root : ¬ q.IsRoot a := by
      rw [isRoot_prod]
      rintro ⟨ζ, hζ, hroot⟩
      rw [IsRoot.def, eval_pow, eval_sub, eval_X, eval_C] at hroot
      exact (ne_of_mem_erase hζ) (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hroot)).symm
    rw [hsplit, rootMultiplicity_mul_X_sub_C_pow hq_monic.ne_zero,
      rootMultiplicity_eq_zero hq_not_root, zero_add]
  -- Vanishing on the Cartesian product kills the remainder `f₀`; bound `g i` on `closedBall c R`
  -- and `(P i).eval (z i)` on `closedBall c r`.
  obtain ⟨f₀, g, hf₀, hg, hdiv, hdeg₀, hdeg_g⟩ :=
    exists_eq_add_sum_mul_eval_of_monic hf hP_monic
  have hf₀_zero : f₀ = 0 :=
    eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero hf₀ hg (fun i ↦ (hP_monic i).ne_zero)
      hdiv hdeg₀ fun ξ hξ κ hκ ↦ by
        have hξE : ∀ i, ξ i ∈ E i := fun i ↦ hP_root_mem i (ξ i) (hξ i)
        exact hzero ξ hξE κ fun i ↦ hP_mult i (ξ i) (hξE i) ▸ hκ i
  obtain ⟨-, hg_bound⟩ := norm_le_of_eq_add_sum_mul_eval_of_monic hf₀ hg hP_monic hdiv hdeg₀
    hdeg_g hR_pos hR_large hP_roots hM hzR
  have hsum_deg : ∑ j : Fin n, (P j).natDegree = n * p := by
    simp [hP_deg]
  have hP_eval (i : Fin n) : ‖(P i).eval (z i)‖ ≤ (2 * r) ^ p := by
    have hzi : dist (z i) (c i) ≤ r := (dist_pi_le_iff hr).mp (mem_closedBall.mp hz) i
    dsimp only [P]
    rw [eval_prod, norm_prod]
    calc ∏ ζ ∈ E i, ‖((X - C ζ) ^ k i ζ).eval (z i)‖
        ≤ ∏ ζ ∈ E i, (2 * r) ^ k i ζ := by
          refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun ζ hζ ↦ ?_
          rw [eval_pow, eval_sub, eval_X, eval_C, norm_pow, ← dist_eq_norm]
          refine pow_le_pow_left₀ dist_nonneg ?_ _
          linarith [dist_triangle_right (z i) ζ (c i), mem_closedBall.mp (hE i hζ)]
      _ = (2 * r) ^ (∑ ζ ∈ E i, k i ζ) := prod_pow_eq_pow_sum _ _ _
      _ = (2 * r) ^ p := by rw [hsum i]
  -- Combine the `n` summands via `n * 2 ^ p * 3 ^ (n * p) ≤ 6 ^ (n * p)`.
  have hn2 : ∀ m : ℕ, m + 1 ≤ 2 ^ m := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih =>
      calc m + 1 + 1 ≤ (m + 1) + (m + 1) := by omega
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add ih ih
        _ = 2 ^ (m + 1) := by ring
  have hconst_nat : n * 2 ^ p * 3 ^ (n * p) ≤ 6 ^ (n * p) := by
    have hn_pow : n ≤ 2 ^ (n - 1) := by
      simpa [Nat.sub_add_cancel hn] using hn2 (n - 1)
    have hpow_mono : 2 ^ (n - 1) ≤ 2 ^ ((n - 1) * p) :=
      Nat.pow_le_pow_right (by positivity) (by simpa using Nat.mul_le_mul_left (n - 1) hp)
    calc n * 2 ^ p * 3 ^ (n * p)
        ≤ 2 ^ ((n - 1) * p) * 2 ^ p * 3 ^ (n * p) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hn_pow.trans hpow_mono))
      _ = 2 ^ (n * p) * 3 ^ (n * p) := by
          have hn1 : n - 1 + 1 = n := by omega
          rw [← pow_add, ← add_one_mul, hn1]
      _ = 6 ^ (n * p) := by rw [← mul_pow]; rfl
  have hconst : (n : ℝ) * 2 ^ p * 3 ^ (n * p) ≤ (6 : ℝ) ^ (n * p) := by
    exact_mod_cast hconst_nat
  have hf_sum : f z = ∑ i : Fin n, g i z * (P i).eval (z i) := by
    rw [hdiv z, hf₀_zero, Pi.zero_apply, zero_add]
  calc ‖f z‖
      = ‖∑ i : Fin n, g i z * (P i).eval (z i)‖ := by rw [hf_sum]
    _ ≤ ∑ i : Fin n, ‖g i z * (P i).eval (z i)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, ((3 : ℝ) ^ (n * p) / R ^ p * M) * (2 * r) ^ p := by
        refine sum_le_sum fun i _ ↦ ?_
        rw [norm_mul]
        have hgi : ‖g i z‖ ≤ (3 : ℝ) ^ (n * p) / R ^ p * M := by
          simpa [hsum_deg, hP_deg i] using hg_bound i
        exact mul_le_mul hgi (hP_eval i) (norm_nonneg _) (by positivity)
    _ = M * ((n : ℝ) * 2 ^ p * 3 ^ (n * p)) * (r / R) ^ p := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, div_pow]
        ring
    _ ≤ M * (6 : ℝ) ^ (n * p) * (r / R) ^ p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hconst hM0) (by positivity)
    _ = M * (6 ^ n * r / R) ^ p := by
        rw [pow_mul, mul_div_assoc, mul_pow, mul_assoc]

/-- **Schwarz's lemma for Cartesian products (Waldschmidt, Proposition 4.7).**
Let `f : (Fin n → ℂ) → ℂ` be an entire function bounded by `M` on `closedBall c R` with `r ≤ R`.
Suppose `E : Fin n → Finset ℂ` satisfies `S₁ ≤ #(E i)` and `(E i : Set ℂ) ⊆ closedBall (c i) r`
for every `i : Fin n`, and `mDeriv σ f ξ = 0` at every point `ξ` with `∀ i, ξ i ∈ E i` and every
multi-index `σ : Fin n → ℕ` with `∀ i, σ i < S₀`. Then for every `z ∈ closedBall c r`,
`‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁)`. -/
theorem norm_le_mul_eighteen_pow_mul_div_pow {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {E : Fin n → Finset ℂ} {S₀ S₁ : ℕ}
    (hcard : ∀ i, S₁ ≤ #(E i))
    {c : Fin n → ℂ} {r R M : ℝ} (hE : ∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r)
    (hrR : r ≤ R)
    (hzero : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) →
      ∀ σ : Fin n → ℕ, (∀ i, σ i < S₀) → mDeriv σ f ξ = 0)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁) := by
  choose E' hE'_sub hE'_card using fun i ↦ exists_subset_card_eq (hcard i)
  have hsix := norm_le_mul_six_pow_mul_div_pow_of_sum_eq hf (E := E') (k := fun _ _ ↦ S₀)
    (p := S₀ * S₁) (fun i ↦ by simp [hE'_card i, mul_comm])
    (fun i ↦ Set.Subset.trans (coe_subset.mpr (hE'_sub i)) (hE i)) hrR
    (fun ξ hξ σ hσ ↦ hzero ξ (fun i ↦ hE'_sub i (hξ i)) σ hσ) hM hz
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hz)
  have _hR0 : 0 ≤ R := hr.trans hrR
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z (closedBall_subset_closedBall hrR hz))
  refine hsix.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hM0)
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hr) (by positivity)
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end TauCeti.Baker
