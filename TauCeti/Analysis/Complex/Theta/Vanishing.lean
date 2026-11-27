/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Analysis.Complex.Theta.Fourier
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Boundary vanishing and level-0 classification of theta sections

Using the twisted Fourier expansion and shift-by-`k` recurrence from
`TauCeti.Analysis.Complex.Theta.Fourier`, this file classifies the section space
`thetaSections k τ α β` at the boundary `τ.im ≤ 0` and at level `k = 0`:

* When `k > 0` and `τ.im ≤ 0`, the shift recurrence forces `‖c (n + j k)‖ ≥ ‖c n‖` for large
  `n`, contradicting Riemann–Lebesgue decay (`tendsto_thetaFourierCoeff_zero`), so
  `thetaSections k τ α β = ⊥` (`TauCeti.thetaSections_eq_bot_of_im_nonpos`).
* When `k = 0` and `τ.im ≠ 0`, the recurrence reads `c m = exp (2πi(m + α)τ - 2πiβ) * c m`.
  For integer characteristics `(α, β) ∈ ℤ × ℤ`, only the mode `m = -α` can be nonzero, so the
  sections are precisely the constant functions (`TauCeti.mem_thetaSections_zero_iff_const`);
  otherwise all sections vanish (`TauCeti.thetaSections_zero_eq_bot_of_not_int`).

## Main results

* `TauCeti.thetaSections_eq_bot_of_im_nonpos`: vanishing for `0 < k` and `τ.im ≤ 0`.
* `TauCeti.mem_thetaSections_zero_iff_const`: at level `0` with `τ.im ≠ 0` and integer
  characteristics, the theta sections are the constant functions.
* `TauCeti.thetaSections_zero_eq_bot_of_not_int`: at level `0` with `τ.im ≠ 0` and non-integer
  characteristics, `thetaSections 0 τ α β = ⊥`.
* `TauCeti.finrank_thetaSections_of_im_nonpos`: vanishing dimension for `0 < k` and `τ.im ≤ 0`.
* `TauCeti.finrank_thetaSections_zero`: complete dimension formula at level `k = 0` for `τ.im ≠ 0`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

open Complex Filter
open scoped Real Topology

namespace TauCeti

private lemma norm_thetaFourierCoeff_add_level {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n : ℤ) :
    ‖thetaFourierCoeff α s (n + k)‖ =
      Real.exp (-2 * π * ((n : ℝ) + α + (k : ℝ) / 2) * τ.im) * ‖thetaFourierCoeff α s n‖ := by
  rw [thetaFourierCoeff_add_of_mem_thetaSections hs n, norm_mul, Complex.norm_exp]
  congr 2
  have hexp : 2 * π * I * ((n : ℂ) + α) * τ - 2 * π * I * β + π * I * k * τ =
      (↑(2 * π * ((n : ℝ) + α + (k : ℝ) / 2)) * τ - ↑(2 * π * β)) * I := by
    push_cast
    ring
  rw [hexp, Complex.mul_I_re, Complex.sub_im, Complex.im_ofReal_mul, Complex.ofReal_im]
  ring

private lemma norm_thetaFourierCoeff_le_add_nat_mul {k : ℕ} {τ : ℂ} (hτ : τ.im ≤ 0) {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) {n : ℤ}
    (hn : 0 ≤ (n : ℝ) + α + (k : ℝ) / 2) (j : ℕ) :
    ‖thetaFourierCoeff α s n‖ ≤ ‖thetaFourierCoeff α s (n + j * k)‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hidx : n + ((j + 1 : ℕ) : ℤ) * k = (n + j * k) + k := by push_cast; ring
    rw [hidx, norm_thetaFourierCoeff_add_level hs]
    have hpos : 0 ≤ ((n + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2 := by
      push_cast
      have hjk : (0 : ℝ) ≤ (j : ℝ) * (k : ℝ) := by positivity
      linarith
    have harg : 0 ≤ -2 * π * (((n + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2) * τ.im :=
      mul_nonneg_of_nonpos_of_nonpos (by nlinarith [Real.pi_pos, hpos]) hτ
    exact ih.trans (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp harg))

/-- When `k > 0` and `τ.im ≤ 0`, there are no nonzero holomorphic theta sections. -/
theorem thetaSections_eq_bot_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : thetaSections k τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α) (mem_thetaSections_iff.mp hs).left
    fun m => ?_
  have hzero_ge : ∀ n : ℤ, 0 ≤ (n : ℝ) + α + (k : ℝ) / 2 → thetaFourierCoeff α s n = 0 := by
    intro n hn
    have hinj : Function.Injective (fun j : ℕ => n + (j : ℤ) * k) := fun j₁ j₂ h => by
      have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
      exact Int.natCast_inj.mp (mul_right_cancel₀ hk0 (add_left_cancel h))
    have htend : Tendsto (fun j : ℕ => ‖thetaFourierCoeff α s (n + j * k)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (tendsto_thetaFourierCoeff_zero α s).norm.comp
          (Nat.cofinite_eq_atTop ▸ hinj.tendsto_cofinite)
    have hnorm0 : ‖thetaFourierCoeff α s n‖ ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds htend
        (norm_thetaFourierCoeff_le_add_nat_mul hτ hs hn)
    exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
  obtain ⟨j, hj⟩ := exists_nat_gt (-(m : ℝ) - α - (k : ℝ) / 2)
  have hge : 0 ≤ ((m + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2 := by
    push_cast
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hj0 : thetaFourierCoeff α s (m + j * k) = 0 := hzero_ge _ hge
  exact (thetaFourierCoeff_add_int_mul_eq_zero_iff hs m j).mp hj0

private lemma thetaFourierCoeff_zero_level_eq_zero_of_ne {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections 0 τ α β) {m : ℤ} (hm : thetaFourierCoeff α s m ≠ 0) :
    (m : ℝ) + α = 0 ∧ ∃ b : ℤ, (b : ℝ) = β := by
  have hrec := thetaFourierCoeff_add_of_mem_thetaSections hs m
  simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul] at hrec
  have hexp : cexp (2 * π * I * (m + α) * τ - 2 * π * I * β) = 1 :=
    mul_right_cancel₀ hm (by simpa only [one_mul] using hrec.symm)
  have hnorm_eq := norm_thetaFourierCoeff_add_level hs m
  simp only [Nat.cast_zero, add_zero, zero_div] at hnorm_eq
  have hnorm : Real.exp (-2 * π * ((m : ℝ) + α) * τ.im) = 1 :=
    mul_right_cancel₀ (norm_ne_zero_iff.mpr hm) (by simpa only [one_mul] using hnorm_eq.symm)
  have hma : (m : ℝ) + α = 0 := by
    have hmul : -2 * π * ((m : ℝ) + α) * τ.im = 0 :=
      Real.exp_injective (by simpa only [Real.exp_zero] using hnorm)
    have hne : -2 * π * τ.im ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Real.pi_pos.ne') hτ
    have : (-2 * π * τ.im) * ((m : ℝ) + α) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hne
  have hmaC : ((m : ℂ) + α) = 0 := by exact_mod_cast hma
  have hneg : 2 * π * I * (m + α) * τ - 2 * π * I * β = -2 * π * I * (β : ℂ) := by
    rw [hmaC]
    ring
  rw [hneg, Complex.exp_neg_two_pi_mul_I_mul_ofReal_eq_one_iff] at hexp
  exact ⟨hma, hexp⟩

/-- At level `k = 0` with `τ.im ≠ 0` and integer characteristics `(α, β) ∈ ℤ × ℤ`, the theta
sections are precisely the constant functions. -/
theorem mem_thetaSections_zero_iff_const {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (hα : ∃ a : ℤ, (a : ℝ) = α) (hβ : ∃ b : ℤ, (b : ℝ) = β) {s : ℂ → ℂ} :
    s ∈ thetaSections 0 τ α β ↔ ∃ c : ℂ, s = fun _ => c := by
  rcases hα with ⟨a, rfl⟩
  rcases hβ with ⟨b, rfl⟩
  constructor
  · intro hs
    rcases mem_thetaSections_iff.mp hs with ⟨hd, h1, _⟩
    refine ⟨thetaFourierCoeff a s (-a), ?_⟩
    ext z
    have hsum := hasSum_thetaFourierCoeff hd h1 z
    have hsingle : HasSum
        (fun m : ℤ => thetaFourierCoeff a s m * cexp (2 * π * I * (m + a) * z))
        (thetaFourierCoeff a s (-a)) := by
      have hterm : thetaFourierCoeff a s (-a) * cexp (2 * π * I * (((-a : ℤ) : ℂ) + a) * z) =
          thetaFourierCoeff a s (-a) := by
        simp
      rw [← hterm]
      refine hasSum_ite_eq (-a) _ |>.congr_fun fun m => ?_
      by_cases hm : m = -a
      · subst hm; simp
      · rw [ite_eq_right hm]
        by_contra hne
        have hcne : thetaFourierCoeff a s m ≠ 0 := left_ne_zero_of_mul hne
        have hma := (thetaFourierCoeff_zero_level_eq_zero_of_ne hτ hs hcne).left
        have hmaZ : m + a = 0 := by exact_mod_cast hma
        exact hm (eq_neg_of_add_eq_zero_left hmaZ)
    exact hsum.unique hsingle
  · rintro ⟨c, rfl⟩
    refine mem_thetaSections_iff.mpr ⟨differentiable_const c, fun _ => ?_, fun _ => ?_⟩
    · have ha : cexp (2 * π * I * (a : ℂ)) = 1 := by
        simpa [mul_comm] using Complex.exp_int_mul_two_pi_mul_I a
      simp [ha]
    · have hb : cexp (2 * π * I * (b : ℂ)) = 1 := by
        simpa [mul_comm] using Complex.exp_int_mul_two_pi_mul_I b
      simp [hb]

/-- At level `k = 0` with `τ.im ≠ 0`, non-trivial flat characteristics (`α ∉ ℤ` or `β ∉ ℤ`) admit
no nonzero holomorphic theta sections. -/
theorem thetaSections_zero_eq_bot_of_not_int {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (h : ¬ ((∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β))) :
    thetaSections 0 τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α) (mem_thetaSections_iff.mp hs).left
    fun m => ?_
  by_contra hm
  obtain ⟨hma, hb⟩ := thetaFourierCoeff_zero_level_eq_zero_of_ne hτ hs hm
  exact h ⟨⟨-m, by push_cast; linarith⟩, hb⟩

/-- For positive level `k > 0` and `τ.im ≤ 0`, `thetaSections k τ α β` has dimension `0`. -/
theorem finrank_thetaSections_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : Module.finrank ℂ (thetaSections k τ α β) = 0 := by
  rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, finrank_bot]

open scoped Classical in
/-- **Complete dimension formula at level `k = 0`.** For any non-real period `τ` (`τ.im ≠ 0`), the
space `thetaSections 0 τ α β` has dimension `1` when both characteristics are integers (the
trivial flat line bundle) and dimension `0` otherwise. -/
theorem finrank_thetaSections_zero (τ : ℂ) (hτ : τ.im ≠ 0) (α β : ℝ) :
    Module.finrank ℂ (thetaSections 0 τ α β) =
      if (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β) then 1 else 0 := by
  by_cases h : (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β)
  · rw [ite_eq_left h]
    have h1 : (fun _ : ℂ => (1 : ℂ)) ∈ thetaSections 0 τ α β :=
      (mem_thetaSections_zero_iff_const hτ h.left h.right).mpr ⟨1, rfl⟩
    refine finrank_eq_one ⟨fun _ => 1, h1⟩ ?_ fun s => ?_
    · intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      exact one_ne_zero this
    · obtain ⟨c, hc⟩ := (mem_thetaSections_zero_iff_const hτ h.left h.right).mp s.property
      refine ⟨c, Subtype.ext ?_⟩
      ext z
      simp [hc]
  · rw [ite_eq_right h, thetaSections_zero_eq_bot_of_not_int hτ h, finrank_bot]

end TauCeti
