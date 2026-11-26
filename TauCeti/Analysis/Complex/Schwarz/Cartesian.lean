/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.MDeriv.Basic
import TauCeti.Analysis.Complex.CoordinateDivision.Basic
import TauCeti.Analysis.Complex.CoordinateDivision.MDeriv
import TauCeti.Analysis.Polynomial.OfMultiset
import TauCeti.Data.Finsupp.Multiset
import TauCeti.Data.Finsupp.Weight
import TauCeti.Data.Nat.Pow

/-!
# Schwarz's lemma for Cartesian products

Let `f : (Fin n → ℂ) → ℂ` be an entire function bounded by `M` on the closed polydisc
`closedBall c R` of radius `R ≥ r` around `c`. Suppose that for each coordinate `i : Fin n` we are
given a finite set `E i ⊆ closedBall (c i) r` and multiplicities `k i : ℂ → ℕ` of total weight
`p ≤ ∑ ζ ∈ E i, k i ζ`, and that when `0 < p` every mixed partial derivative `mDeriv σ f ξ` with
`∀ i, σ i < k i (ξ i)` vanishes on the Cartesian product `{ξ | ∀ i, ξ i ∈ E i}`.

Trimming the weights `k i` via `Finsupp.exists_le_degree_eq` to finitely supported weights `k' i`
of total degree `p` and dividing `f` by the monic coordinate polynomials
`P i = Polynomial.ofMultiset (k' i).toMultiset` of degree `p` expresses `f(z)` as
`∑ i, g i z * (P i).eval (z i)` with controlled supremum norms on `closedBall c R`, yielding the
estimate `‖f z‖ ≤ M * (6 ^ n * r / R) ^ p` on `closedBall c r` (including the degenerate cases
`p = 0`, `n = 0`, `r = 0`, and `r ≤ R < 5 * r`). For finite sets of cardinality `#(E i) ≥ S₁` and
uniform coordinate multiplicity `S₀`, this specialises directly to Waldschmidt's Schwarz lemma for
Cartesian products `‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁)` — the analytic extrapolation tool in
several-variable transcendence proofs such as the Schneider–Lang criterion and Baker's theorem on
linear forms in logarithms.

## Main results

* `TauCeti.norm_le_mul_six_pow_mul_div_pow_of_le_sum`: weighted Cartesian zero-set Schwarz lemma
  with factor `(6 ^ n * r / R) ^ p` when `∀ i, p ≤ ∑ ζ ∈ E i, k i ζ` and `r ≤ R`.
* `TauCeti.norm_le_mul_eighteen_pow_mul_div_pow`: Waldschmidt's Schwarz lemma for Cartesian
  products (Waldschmidt 2000, §4.3, Proposition 4.7), bounding
  `‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁)` on `closedBall c r` whenever `∀ i, S₁ ≤ #(E i)`,
  `∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r`, `r ≤ R`, and (for `0 < S₀ * S₁`) `mDeriv σ f ξ = 0` on
  `E 0 × ⋯ × E (n - 1)` for `∀ i, σ i < S₀`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Proposition 4.7, p. 122, and its proof, pp. 129–130.
-/

public section

open Finset Metric Polynomial

namespace TauCeti

/-! ### Preliminary helpers -/

/-- Core `0 < n`, `0 < p`, `0 < r`, `5 * r ≤ R` regime of the weighted Cartesian Schwarz lemma. -/
private theorem norm_le_mul_six_pow_mul_div_pow_of_five_mul_le {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {E : Fin n → Finset ℂ} {k : Fin n → ℂ → ℕ} {p : ℕ}
    (hp : 0 < p) (hsum : ∀ i, p ≤ ∑ ζ ∈ E i, k i ζ)
    {c : Fin n → ℂ} {r R M : ℝ} (hE : ∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r)
    (hr : 0 < r) (hrR : 5 * r ≤ R)
    (hzero : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) →
      ∀ σ : Fin n → ℕ, (∀ i, σ i < k i (ξ i)) → mDeriv σ f ξ = 0)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ M * (6 ^ n * r / R) ^ p := by
  classical
  have hR_pos : 0 < R := by linarith
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall (by linarith) hz
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hzR)
  let K (i : Fin n) : ℂ →₀ ℕ := Finsupp.indicator (E i) fun a _ ↦ k i a
  have hK_deg (i : Fin n) : (K i).degree = ∑ ζ ∈ E i, k i ζ := by
    simp [K, Finset.sum_attach]
  choose k' hk'_le hk'_deg using fun i ↦
    Finsupp.exists_le_degree_eq (K i) p ((hK_deg i).symm ▸ hsum i)
  let P (i : Fin n) : ℂ[X] := Polynomial.ofMultiset (k' i).toMultiset
  have hP_monic (i : Fin n) : (P i).Monic := monic_multisetProd_X_sub_C _
  have hcard (i : Fin n) : (k' i).toMultiset.card = p :=
    (Finsupp.card_toMultiset_eq_degree (k' i)).trans (hk'_deg i)
  have hP_deg (i : Fin n) : (P i).natDegree = p :=
    (natDegree_multiset_prod_X_sub_C_eq_card _).trans (hcard i)
  have hmem (i : Fin n) {ζ : ℂ} (hζ : ζ ∈ (k' i).toMultiset) : ζ ∈ E i :=
    Finsupp.support_indicator_subset _ _ <|
      Finsupp.support_mono (hk'_le i) ((Finsupp.mem_toMultiset _ _).mp hζ)
  have hP_mem (i : Fin n) {ζ : ℂ} (hζ : (P i).IsRoot ζ) : ζ ∈ E i :=
    hmem i (roots_ofMultiset (k' i).toMultiset ▸ (mem_roots (hP_monic i).ne_zero).mpr hζ)
  obtain ⟨f₀, g, hf₀, hg, hdiv, hdeg₀, hdeg_g⟩ :=
    exists_eq_add_sum_mul_eval_of_ne_zero hf fun i ↦ (hP_monic i).ne_zero
  have hf₀_zero : f₀ = 0 :=
    eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero hf₀ hg hdiv hdeg₀ fun ξ hξ κ hκ ↦
      hzero ξ (fun i ↦ hP_mem i (hξ i)) κ fun i ↦ (hκ i).trans_le <| by
        rw [← count_roots, roots_ofMultiset, Finsupp.count_toMultiset]
        simpa [K, hP_mem i (hξ i)] using hk'_le i (ξ i)
  obtain ⟨-, hg_bound⟩ := norm_le_of_eq_add_sum_mul_eval_of_monic hf₀ hg hP_monic
    hdiv hdeg₀ hdeg_g hR_pos hrR (fun i ζ hζ ↦ hE i (hP_mem i hζ)) hM hzR
  have hsum_deg : ∑ j : Fin n, (P j).natDegree = n * p := by simp [hP_deg]
  have hconst : (n : ℝ) * 2 ^ p * 3 ^ (n * p) ≤ (6 : ℝ) ^ (n * p) := by
    exact_mod_cast (Nat.mul_le_mul_right (3 ^ (n * p))
      (Nat.mul_pow_le_pow_mul n (by norm_num) hp)).trans_eq (by rw [← mul_pow]; norm_num)
  calc ‖f z‖ = ‖∑ i : Fin n, g i z * (P i).eval (z i)‖ := by simp [hdiv z, hf₀_zero]
    _ ≤ ∑ i : Fin n, ‖g i z * (P i).eval (z i)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, ((3 : ℝ) ^ (n * p) / R ^ p * M) * (2 * r) ^ p :=
        sum_le_sum fun i _ ↦ by
          rw [norm_mul]
          have hPi : ‖(P i).eval (z i)‖ ≤ (2 * r) ^ p := hcard i ▸
            norm_eval_ofMultiset_le_two_mul_pow (fun ζ hζ ↦ hE i (hmem i hζ))
              (mem_closedBall.mpr ((dist_le_pi_dist z c i).trans (mem_closedBall.mp hz)))
          exact mul_le_mul (by simpa [hsum_deg, hP_deg i] using hg_bound i) hPi
            (norm_nonneg _) (by positivity)
    _ = M * ((n : ℝ) * 2 ^ p * 3 ^ (n * p)) * (r / R) ^ p := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, div_pow]; ring
    _ ≤ M * (6 : ℝ) ^ (n * p) * (r / R) ^ p := by gcongr
    _ = M * (6 ^ n * r / R) ^ p := by rw [pow_mul, mul_div_assoc, mul_pow, mul_assoc]

/-! ### Schwarz's lemma for Cartesian products -/

/-- **Weighted Schwarz's lemma for Cartesian products.**
Let `f : (Fin n → ℂ) → ℂ` be entire and bounded by `M` on `closedBall c R` with `r ≤ R`. Suppose
`E : Fin n → Finset ℂ` and `k : Fin n → ℂ → ℕ` satisfy `∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r`
and `∀ i, p ≤ ∑ ζ ∈ E i, k i ζ`. If `0 < p` implies `mDeriv σ f ξ = 0` whenever `∀ i, ξ i ∈ E i`
and `∀ i, σ i < k i (ξ i)`, then for every `z ∈ closedBall c r`,
`‖f z‖ ≤ M * (6 ^ n * r / R) ^ p`. -/
theorem norm_le_mul_six_pow_mul_div_pow_of_le_sum {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {E : Fin n → Finset ℂ} {k : Fin n → ℂ → ℕ} {p : ℕ}
    (hsum : ∀ i, p ≤ ∑ ζ ∈ E i, k i ζ)
    {c : Fin n → ℂ} {r R M : ℝ} (hE : ∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r)
    (hrR : r ≤ R)
    (hzero : 0 < p → ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) →
      ∀ σ : Fin n → ℕ, (∀ i, σ i < k i (ξ i)) → mDeriv σ f ξ = 0)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ M * (6 ^ n * r / R) ^ p := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hz)
  have hR0 : 0 ≤ R := hr.trans hrR -- consumed by `positivity` below
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hfz : ‖f z‖ ≤ M := hM z hzR
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans hfz
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simpa using hfz
  -- Needed for the `R < 5 * r` branch below, where `6 ^ n * r / R ≥ 1` requires `0 < n`.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hf0 : f z = 0 := by
      have h := hzero hp z (fun i ↦ i.elim0) 0 (fun i ↦ i.elim0)
      rwa [mDeriv_zero] at h
    rw [hf0, norm_zero]
    positivity
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · have hz_eq : z = c := dist_le_zero.mp (mem_closedBall.mp hz)
    have hz_mem : ∀ i, z i ∈ E i ∧ 0 < k i (z i) := fun i ↦ by
      obtain ⟨a, haE, hka⟩ := exists_ne_zero_of_sum_ne_zero ((hp.trans_le (hsum i)).ne')
      have hac : a = c i := dist_le_zero.mp (mem_closedBall.mp (hE i haE))
      rw [hz_eq, ← hac]
      exact ⟨haE, Nat.pos_of_ne_zero hka⟩
    have hf0 : f z = 0 := by
      have h := hzero hp z (fun i ↦ (hz_mem i).1) 0 (fun i ↦ (hz_mem i).2)
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
  exact norm_le_mul_six_pow_mul_div_pow_of_five_mul_le hf hp hsum hE hr_pos hR_large
    (hzero hp) hM hz

/-- **Schwarz's lemma for Cartesian products (Waldschmidt, Proposition 4.7).**
Let `f : (Fin n → ℂ) → ℂ` be an entire function bounded by `M` on `closedBall c R` with `r ≤ R`.
Suppose `E : Fin n → Finset ℂ` satisfies `S₁ ≤ #(E i)` and `(E i : Set ℂ) ⊆ closedBall (c i) r`
for every `i : Fin n`, and whenever `0 < S₀ * S₁`, `mDeriv σ f ξ = 0` at every point `ξ` with
`∀ i, ξ i ∈ E i` and every multi-index `σ : Fin n → ℕ` of max-norm `maxᵢ σᵢ < S₀` (i.e.
`∀ i, σ i < S₀`, matching Waldschmidt's coordinatewise derivative-order hypothesis `|σ| < S₀`).
Then for every `z ∈ closedBall c r`, `‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁)`. -/
theorem norm_le_mul_eighteen_pow_mul_div_pow {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {E : Fin n → Finset ℂ} {S₀ S₁ : ℕ}
    (hcard : ∀ i, S₁ ≤ #(E i))
    {c : Fin n → ℂ} {r R M : ℝ} (hE : ∀ i, (E i : Set ℂ) ⊆ closedBall (c i) r)
    (hrR : r ≤ R)
    (hzero : 0 < S₀ * S₁ → ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) →
      ∀ σ : Fin n → ℕ, (∀ i, σ i < S₀) → mDeriv σ f ξ = 0)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ M * (18 ^ n * r / R) ^ (S₀ * S₁) := by
  have hsix := norm_le_mul_six_pow_mul_div_pow_of_le_sum hf (E := E) (k := fun _ _ ↦ S₀)
    (p := S₀ * S₁) (fun i ↦ by simpa [mul_comm] using Nat.mul_le_mul_left S₀ (hcard i))
    hE hrR hzero hM hz
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hz)
  have hR0 : 0 ≤ R := hr.trans hrR -- consumed by `positivity` below
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z (closedBall_subset_closedBall hrR hz))
  refine hsix.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hM0)
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hr) (by positivity)
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end TauCeti
