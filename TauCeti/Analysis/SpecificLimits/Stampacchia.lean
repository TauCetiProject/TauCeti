/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecificLimits.FastGeometric

/-!
# Stampacchia's lemma

Let `φ` be nonnegative and nonincreasing on `[k₀, ∞)`, and suppose that

`φ h ≤ (M / (h - k)) ^ α * φ k ^ β` whenever `k₀ ≤ k < h`,

with `M > 0`, `α > 0` and `β > 1`. Then `φ` vanishes at the finite level

`k₀ + d`, where `d = M * φ k₀ ^ ((β - 1) / α) * 2 ^ (β / (β - 1))`.

This is the numerical lemma behind Stampacchia's proof of global boundedness for weak solutions
of elliptic equations. There `φ h` is the measure of the superlevel set `{u > h}` of a weak
subsolution `u`, and testing the equation against `(u - k)⁺`, combined with the Sobolev and
Chebyshev inequalities, gives the recursive inequality. The conclusion `φ (k₀ + d) = 0` says that
`u ≤ k₀ + d` almost everywhere.

The proof evaluates `φ` along the levels `kⱼ = k₀ + d (1 - 2⁻ʲ)`, which increase to `k₀ + d`. The
values `φ kⱼ` satisfy the superlinear recurrence of `TauCeti.le_geom_of_le_mul_pow_mul_rpow`, with
the choice of `d` making the starting value exactly small enough, so they decay geometrically; since
`φ (k₀ + d) ≤ φ kⱼ` for every `j`, it vanishes.

## Main declarations

* `TauCeti.apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow`: Stampacchia's lemma.

## References

* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965).
* D. Kinderlehrer, G. Stampacchia, *An Introduction to Variational Inequalities and Their
  Applications*, Chapter II, Appendix B, Lemma B.1.
-/

public section

namespace TauCeti

open Filter Set Topology

/-- **Stampacchia's lemma.** Let `φ` be nonnegative and antitone on `[k₀, ∞)`, with

`φ h ≤ (M / (h - k)) ^ α * φ k ^ β` whenever `k₀ ≤ k < h`,

for constants `M > 0`, `α > 0` and `β > 1`. Then `φ (k₀ + d) = 0`, where
`d = M * φ k₀ ^ ((β - 1) / α) * 2 ^ (β / (β - 1))`. -/
theorem apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow {φ : ℝ → ℝ} {k₀ M α β : ℝ}
    (hM : 0 < M) (hα : 0 < α) (hβ : 1 < β) (hφ : ∀ h, k₀ ≤ h → 0 ≤ φ h)
    (hanti : AntitoneOn φ (Ici k₀))
    (hrec : ∀ k h, k₀ ≤ k → k < h → φ h ≤ (M / (h - k)) ^ α * φ k ^ β) :
    φ (k₀ + M * φ k₀ ^ ((β - 1) / α) * 2 ^ (β / (β - 1))) = 0 := by
  set P := φ k₀
  have hP : 0 ≤ P := hφ k₀ le_rfl
  have hβ1 : 0 < β - 1 := sub_pos.2 hβ
  rcases hP.eq_or_lt with hP0 | hPpos
  · -- If `φ` already vanishes at `k₀`, then so does the shift `d`.
    rw [← hP0, Real.zero_rpow (div_pos hβ1 hα).ne', mul_zero, zero_mul, add_zero]
    exact hP0.symm
  set d := M * P ^ ((β - 1) / α) * 2 ^ (β / (β - 1))
  have hd : 0 < d := by positivity
  -- The levels `kⱼ = k₀ + d (1 - 2⁻ʲ)` increase from `k₀` to `k₀ + d`.
  set k : ℕ → ℝ := fun j => k₀ + d * (1 - (2 ^ j)⁻¹)
  have hk₀ : ∀ j, k₀ ≤ k j := fun j => by
    have : (2 ^ j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
    have : 0 ≤ d * (1 - (2 ^ j)⁻¹) := mul_nonneg hd.le (by linarith)
    simp only [k]
    linarith
  have hkd : ∀ j, k j ≤ k₀ + d := fun j => by
    have : 0 ≤ d * (2 ^ j)⁻¹ := by positivity
    simp only [k]
    nlinarith
  have hgap : ∀ j, k (j + 1) - k j = d / 2 / 2 ^ j := fun j => by
    simp only [k, pow_succ]
    field_simp
    ring
  -- Along these levels the recursive inequality is a superlinear recurrence.
  set Y : ℕ → ℝ := fun j => φ (k j)
  have hY : ∀ j, 0 ≤ Y j := fun j => hφ _ (hk₀ j)
  have hY0 : Y 0 = P := by simp [Y, k, P]
  have hrecY : ∀ j, Y (j + 1) ≤ (2 * M / d) ^ α * (2 ^ α) ^ j * Y j ^ (1 + (β - 1)) := by
    intro j
    have hlt : k j < k (j + 1) := by
      rw [← sub_pos, hgap]
      positivity
    have h := hrec (k j) (k (j + 1)) (hk₀ j) hlt
    rw [hgap] at h
    have hdiv : M / (d / 2 / 2 ^ j) = 2 * M / d * 2 ^ j := by field_simp
    have hsplit : (M / (d / 2 / 2 ^ j)) ^ α = (2 * M / d) ^ α * (2 ^ α) ^ j := by
      rw [hdiv, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_mul zero_le_two,
        mul_comm α]
    simpa only [Y, hsplit, add_sub_cancel] using h
  -- The choice of `d` makes the starting value small enough for geometric decay.
  set q : ℝ := 2 ^ (-(α / (β - 1)))
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 (div_pos hα hβ1))
  have hbq : 2 ^ α * q ^ (β - 1) ≤ 1 := by
    rw [← Real.rpow_mul zero_le_two, neg_mul, div_mul_cancel₀ _ hβ1.ne', ← Real.rpow_add two_pos,
      add_neg_cancel, Real.rpow_zero]
  have hstart : (2 * M / d) ^ α * Y 0 ^ (β - 1) ≤ q := by
    have hdα : d ^ α = M ^ α * P ^ (β - 1) * 2 ^ (α * β / (β - 1)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hP,
        ← Real.rpow_mul zero_le_two, div_mul_cancel₀ _ hα.ne', mul_comm (β / (β - 1)),
        mul_div_assoc]
    have hexp : α - α * β / (β - 1) = -(α / (β - 1)) := by
      field_simp
      ring
    apply le_of_eq
    rw [hY0, Real.div_rpow (by positivity) hd.le, hdα, Real.mul_rpow zero_le_two hM.le]
    simp only [q, ← hexp, Real.rpow_sub two_pos]
    field_simp
  have hlim : Tendsto Y atTop (𝓝 0) :=
    tendsto_atTop_zero_of_le_mul_pow_mul_rpow_of_ratio_lt_one hY (by positivity) hq0 hq1
      hβ1.le hbq hstart hrecY
  -- `φ (k₀ + d)` lies below every `φ kⱼ`, and these tend to zero.
  refine le_antisymm (ge_of_tendsto' hlim fun j => ?_) (hφ _ (by linarith))
  have hk₀d : k₀ ≤ k₀ + d := by linarith
  exact hanti (hk₀ j) hk₀d (hkd j)

end TauCeti
