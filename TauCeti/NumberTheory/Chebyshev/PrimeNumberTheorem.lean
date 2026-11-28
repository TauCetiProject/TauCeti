/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.ResidueClass
import TauCeti.NumberTheory.DirichletCharacter.LFunction.PrimeNumberTheorem

/-!
# The prime number theorem in fixed arithmetic progressions

In a reduced residue class modulo a fixed `q`, the von Mangoldt sum `ψ(x; q, a)` has main
term `x / φ(q)` with an error saving every prescribed power of `log x`. The constants may
be taken simultaneously over all reduced classes of `q`. Orthogonality expresses the sum
in terms of the fixed-character prime number theorem.
-/

public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace Chebyshev

/-- For each fixed modulus, the prime-power counting error in reduced residue classes saves
any prescribed power of the logarithm, with the same constant for all reduced classes. -/
theorem exists_abs_psiAP_sub_div_totient_le_div_log_pow (q k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (a : ZMod q), IsUnit a → ∀ x : ℝ, 3 ≤ x →
      |psiAP q a x - x / q.totient| ≤ C * x / Real.log x ^ k := by
  classical
  obtain rfl | hq := eq_or_ne q 0
  · refine ⟨1, one_pos, fun a ha x hx ↦ ?_⟩
    have hψ : psiAP 0 a x = 0 := by
      rw [psiAP_def]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      have hu : IsUnit (n : ZMod 0) := (Finset.mem_filter.1 hn).2 ▸ ha
      have hn₁ := (Nat.coprime_zero_right n).1 ((ZMod.isUnit_iff_coprime n 0).1 hu)
      simp [hn₁]
    simp only [hψ, Nat.totient_zero, Nat.cast_zero, div_zero, sub_zero, abs_zero, one_mul]
    exact div_nonneg (by linarith) (pow_nonneg (Real.log_nonneg (by linarith)) _)
  have : NeZero q := ⟨hq⟩
  choose C hC₀ hC using fun χ : DirichletCharacter ℂ q ↦
    χ.exists_norm_sum_mul_vonMangoldt_sub_le_div_log_pow k
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hS : 0 < ∑ χ, C χ := Finset.sum_pos (fun χ _ ↦ hC₀ χ) Finset.univ_nonempty
  refine ⟨(∑ χ, C χ) / q.totient, div_pos hS hφ, fun a ha x hx ↦ ?_⟩
  let S := Icc 1 ⌊x⌋₊
  let E (χ : DirichletCharacter ℂ q) : ℂ :=
    (∑ n ∈ S, χ n * (Λ n : ℂ)) - (if χ = 1 then (x : ℂ) else 0)
  have hψ : (psiAP q a x : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ∑ n ∈ S, χ n * (Λ n : ℂ) := by
    rw [psiAP_eq_sum_residueClass, ← Finset.Icc_add_one_left_eq_Ioc, zero_add, Complex.ofReal_sum]
    simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun χ _ ↦ by simp only [S, Finset.mul_sum, mul_assoc]
  have hmain : (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0)) = x := by
    have hi := IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      MulChar.one_apply (R' := ℂ) hi, one_mul]
  have herror : ((psiAP q a x - x / q.totient : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast, hψ, E,
      mul_sub, Finset.sum_sub_distrib, hmain]
    ring
  calc
    _ = ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * E χ‖ := by
      rw [← herror, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * E χ‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      gcongr
      exact norm_sum_le _ _
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ χ, C χ * x / Real.log x ^ k := by
      gcongr with χ _
      exact ((norm_mul _ _).le.trans
        (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _))).trans (hC χ x hx)
    _ = _ := by rw [← Finset.sum_div, ← Finset.sum_mul]; ring

end Chebyshev
