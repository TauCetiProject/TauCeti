/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CoordinateDivision.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.DividedDifference.Analytic
import TauCeti.Analysis.Complex.DividedDifference.Estimate
import TauCeti.Topology.MetricSpace.Pseudo.Pi

/-!
# Polydisc supremum bounds for univariate coordinate polynomial division

For finite `ι`, a complete complex normed space `E`, and a monic polynomial `P ∈ ℂ[X]` of
degree `p` whose roots lie in `closedBall (c i) r`, this file establishes polydisc supremum
estimates for the univariate quotient `TauCeti.partialDivByMonic` and remainder
`TauCeti.partialModByMonic` of an entire function `f : (ι → ℂ) → E`:

* for `r < R` and `‖f‖ ≤ M` on `closedBall c R`, we have
  `‖f₁‖ ≤ (2 / (R - r)) ^ p M` and `‖f₀‖ ≤ (∑_{j < p} (2 (R + r) / (R - r)) ^ j) M` there;
* under `0 < R` and `5 r ≤ R`, these simplify to `‖f₁‖ ≤ (3 / R) ^ p M` and `‖f₀‖ ≤ 3 ^ p M`.

## Main results

* `TauCeti.norm_partialDivByMonic_le`, `TauCeti.norm_partialModByMonic_le`: the bounds
  `‖f₁‖ ≤ (2 / (R - r)) ^ p M` and `‖f₀‖ ≤ (∑_{j < p} (2 (R + r) / (R - r)) ^ j) M` on
  `closedBall c R` for `r < R`.
* `TauCeti.norm_partialDivByMonic_le_of_five_mul_le`,
  `TauCeti.norm_partialModByMonic_le_of_five_mul_le`: simplified bounds `(3 / R) ^ p M` and
  `3 ^ p M` for `0 < R` and `5 r ≤ R`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, §4.3, Lemma 4.8 and its proof (pp. 123–126).
-/

public section

open Function Metric Polynomial

namespace TauCeti

section List

variable {ι E : Type*} [DecidableEq ι] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- The bound `(2 / (R - r)) ^ (length l) M` for `partialDivByList` along `l`. -/
private theorem norm_partialDivByList_le {i : ι} {f : (ι → ℂ) → E} {c : ι → ℂ} {r R M : ℝ}
    (hf : Differentiable ℂ f) {l : List ℂ} (hl : ∀ ζ ∈ l, ζ ∈ closedBall (c i) r) (hrR : r < R)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖partialDivByList i f l z‖ ≤ (2 / (R - r)) ^ l.length * M := by
  induction l generalizing f M with
  | nil => simpa [partialDivByList_nil] using hM z hz
  | cons ζ l ih =>
    have hq := ih (differentiable_partialDslope hf i ζ)
      (fun ζ' h ↦ hl ζ' (List.mem_cons_of_mem _ h))
      (fun w hw ↦ norm_partialDslope_le_of_mem_closedBall hf.differentiableOn
        (hl ζ List.mem_cons_self) hrR hM hw)
    calc ‖partialDivByList i f (ζ :: l) z‖
        = ‖partialDivByList i (partialDslope i f ζ) l z‖ := by rw [partialDivByList_cons]
      _ ≤ (2 / (R - r)) ^ l.length * (2 * M / (R - r)) := hq
      _ = (2 / (R - r)) ^ (ζ :: l).length * M := by
        rw [List.length_cons, pow_succ]
        ring

/-- The bound `(∑_{j < length l} (2 (R + r) / (R - r)) ^ j) M` for `partialModByList` along `l`. -/
private theorem norm_partialModByList_le {i : ι} {f : (ι → ℂ) → E} {c : ι → ℂ}
    {r R M : ℝ} (hf : Differentiable ℂ f) {l : List ℂ}
    (hl : ∀ ζ ∈ l, ζ ∈ closedBall (c i) r) (hrR : r < R)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖partialModByList i f l z‖ ≤
      (∑ j ∈ Finset.range l.length, (2 * (R + r) / (R - r)) ^ j) * M := by
  induction l generalizing f M with
  | nil => simp [partialModByList_nil]
  | cons ζ l ih =>
    have hζ := hl ζ List.mem_cons_self
    have hRr : R - r ≠ 0 := (sub_pos.2 hrR).ne'
    have h₁ := ih (differentiable_partialDslope hf i ζ)
      (fun ζ' h ↦ hl ζ' (List.mem_cons_of_mem _ h))
      (fun w hw ↦ norm_partialDslope_le_of_mem_closedBall hf.differentiableOn hζ hrR hM hw)
    have h₂ := hM _ (update_mem_closedBall (closedBall_subset_closedBall hrR.le hζ) hz)
    have hzc : ‖z i - c i‖ ≤ R := by
      simpa [dist_eq_norm] using (dist_le_pi_dist z c i).trans (mem_closedBall.mp hz)
    have hζc : ‖c i - ζ‖ ≤ r := by
      simpa [dist_eq_norm, norm_sub_rev] using mem_closedBall.mp hζ
    have h₃ : ‖z i - ζ‖ ≤ R + r :=
      (norm_sub_le_norm_sub_add_norm_sub _ (c i) _).trans (add_le_add hzc hζc)
    set a := 2 * (R + r) / (R - r)
    set S := ∑ j ∈ Finset.range l.length, a ^ j
    have hS : ∑ j ∈ Finset.range (ζ :: l).length, a ^ j = 1 + a * S := by
      rw [List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ', pow_zero]
      ring
    rw [partialModByList_cons, hS]
    calc ‖f (update z i ζ) + (z i - ζ) • partialModByList i (partialDslope i f ζ) l z‖
        ≤ M + (R + r) * (S * (2 * M / (R - r))) := by
          refine (norm_add_le _ _).trans (add_le_add h₂ ?_)
          rw [norm_smul]
          exact mul_le_mul h₃ h₁ (norm_nonneg _) ((norm_nonneg _).trans h₃)
      _ = (1 + a * S) * M := by
        simp only [a]
        field_simp

end List

section Bounds

variable {ι E : Type*} [DecidableEq ι] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] {i : ι} {f : (ι → ℂ) → E} {P : ℂ[X]} {c z : ι → ℂ} {r R M : ℝ}

/-- **Size of the quotient.** If `f` is entire, the roots of `P` lie in `closedBall (c i) r` with
`r < R` and `‖f‖ ≤ M` on `closedBall c R`, then the quotient of `f` by `P(zᵢ)` is bounded by
`(2 / (R - r)) ^ p M` there, where `p = natDegree P`. -/
theorem norm_partialDivByMonic_le (hf : Differentiable ℂ f)
    (hroots : ∀ ζ ∈ P.roots, ζ ∈ closedBall (c i) r) (hrR : r < R)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) (hz : z ∈ closedBall c R) :
    ‖partialDivByMonic i f P z‖ ≤ (2 / (R - r)) ^ P.natDegree * M := by
  rw [partialDivByMonic_eq_partialDivByList, ← IsAlgClosed.card_roots_eq_natDegree,
    ← Multiset.length_toList]
  exact norm_partialDivByList_le hf (fun ζ hζ ↦ hroots ζ (Multiset.mem_toList.1 hζ)) hrR hM hz

/-- **Size of the remainder.** If `P` is monic, `f` is entire, the roots of `P` lie in
`closedBall (c i) r` with `r < R` and `‖f‖ ≤ M` on `closedBall c R`, then the remainder of `f`
modulo `P(zᵢ)` is bounded by `(∑_{j < p} (2 (R + r) / (R - r)) ^ j) M` there, where
`p = natDegree P`. -/
theorem norm_partialModByMonic_le (hP : P.Monic) (hf : Differentiable ℂ f)
    (hroots : ∀ ζ ∈ P.roots, ζ ∈ closedBall (c i) r) (hrR : r < R)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) (hz : z ∈ closedBall c R) :
    ‖partialModByMonic i f P z‖ ≤
      (∑ j ∈ Finset.range P.natDegree, (2 * (R + r) / (R - r)) ^ j) * M := by
  rw [partialModByMonic_eq_partialModByList hP, ← IsAlgClosed.card_roots_eq_natDegree,
    ← Multiset.length_toList]
  exact norm_partialModByList_le hf (fun ζ hζ ↦ hroots ζ (Multiset.mem_toList.1 hζ)) hrR hM hz

/-- **Size of the quotient, Waldschmidt's form.** If `f` is entire, the roots of `P` lie in
`closedBall (c i) r`, `0 < R`, `5 r ≤ R` and `‖f‖ ≤ M` on `closedBall c R`, then the quotient of
`f` by `P(zᵢ)` is bounded by `(3 / R) ^ p M` there, where `p = natDegree P`. -/
theorem norm_partialDivByMonic_le_of_five_mul_le (hf : Differentiable ℂ f)
    (hroots : ∀ ζ ∈ P.roots, ζ ∈ closedBall (c i) r) (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) (hz : z ∈ closedBall c R) :
    ‖partialDivByMonic i f P z‖ ≤ (3 / R) ^ P.natDegree * M := by
  have hr : 3 * r ≤ R ∧ r < R := by
    rcases le_or_gt 0 r with _ | _ <;> constructor <;> linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  refine (norm_partialDivByMonic_le hf hroots hr.2 hM hz).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by have := sub_pos.2 hr.2; positivity) ?_ _)
      hM0)
  rw [div_le_div_iff₀ (sub_pos.2 hr.2) hR]
  linarith [hr.1]

/-- **Size of the remainder, Waldschmidt's form.** If `P` is monic, `f` is entire, the roots of
`P` lie in `closedBall (c i) r`, `0 < R`, `5 r ≤ R` and `‖f‖ ≤ M` on `closedBall c R`, then the
remainder of `f` modulo `P(zᵢ)` is bounded by `3 ^ p M` there, where `p = natDegree P`. -/
theorem norm_partialModByMonic_le_of_five_mul_le (hP : P.Monic) (hf : Differentiable ℂ f)
    (hroots : ∀ ζ ∈ P.roots, ζ ∈ closedBall (c i) r) (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) (hz : z ∈ closedBall c R) :
    ‖partialModByMonic i f P z‖ ≤ 3 ^ P.natDegree * M := by
  have hlt : r < R := by rcases le_or_gt 0 r with _ | _ <;> linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  refine (norm_partialModByMonic_le hP hf hroots hlt hM hz).trans
    (mul_le_mul_of_nonneg_right ?_ hM0)
  rcases P.roots.empty_or_exists_mem with h | ⟨ζ, hζ⟩
  · -- Without roots `P` has degree `0` and the sum is empty.
    rw [← IsAlgClosed.card_roots_eq_natDegree, h]
    simp
  -- With a root, `0 ≤ r`, so the ratio `2 (R + r) / (R - r)` lies in `[0, 3]`.
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp (hroots ζ hζ))
  have ha : 2 * (R + r) / (R - r) ≤ 3 := by
    rw [div_le_iff₀ (sub_pos.2 hlt)]
    linarith
  calc ∑ j ∈ Finset.range P.natDegree, (2 * (R + r) / (R - r)) ^ j
      ≤ ∑ j ∈ Finset.range P.natDegree, (3 : ℝ) ^ j :=
        Finset.sum_le_sum fun j _ ↦
          pow_le_pow_left₀ (by have := sub_pos.2 hlt; positivity) ha j
    _ ≤ 3 ^ P.natDegree := by
        rw [geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1)]
        have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) P.natDegree
        linarith

end Bounds

end TauCeti
