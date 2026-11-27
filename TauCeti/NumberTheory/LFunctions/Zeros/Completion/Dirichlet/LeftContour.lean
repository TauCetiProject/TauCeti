/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Logarithmic derivatives on left-hand Dirichlet contours

For primitive nonprincipal characters, the logarithmic functional equation and the reflection
formula for digamma give a conductor-uniform bound on `L′/L` to the left of `Re s = -1`, at a
fixed distance from the trivial zeros. In particular the bound applies on the distant vertical
edges and on the leftward horizontal extensions used in moving Perron contours.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Chapter 8, proof of Theorem 5.1.
-/

public section

open Complex
open scoped Real

namespace DirichletCharacter

open scoped Classical in
/-- On `Re s ≤ 0`, away from the poles of the parity-shifted cotangent, a primitive nonprincipal
`L(s, χ)` is nonzero. Its logarithmic derivative is expressed in terms of digamma and the
logarithmic derivative of the inverse character, both evaluated at `1 - s`. -/
theorem IsPrimitive.logDeriv_LFunction_eq_of_re_nonpos {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : s.re ≤ 0) (hu : ∀ n : ℤ, (s + (if χ.Even then 0 else 1 : ℂ)) / 2 ≠ n) :
    χ.LFunction s ≠ 0 ∧
      logDeriv χ.LFunction s = (Real.log Real.pi : ℂ) + Complex.log 2 - (Real.log (N : ℝ) : ℂ) -
        digamma (1 - s) + (π * cot (π * ((s + (if χ.Even then 0 else 1 : ℂ)) / 2))) / 2 -
        logDeriv (χ⁻¹).LFunction (1 - s) := by
  classical
  let a : ℂ := if χ.Even then 0 else 1
  have hΓ : χ.gammaFactor s = Gammaℝ (s + a) := by
    by_cases he : χ.Even <;> simp [gammaFactor, a, he]
  have hL : χ.LFunction s ≠ 0 := by
    intro h
    have hz := ((LFunction_eq_zero_iff_of_re_nonpos hχ hs).mp h).1
    rw [hΓ, Gammaℝ_eq_zero_iff] at hz
    obtain ⟨n, hn⟩ := hz
    exact hu (-(n : ℤ)) (by push_cast; rw [hn]; ring)
  have ht : 1 ≤ (1 - s).re := by simpa
  have hinv : χ⁻¹ ≠ 1 := by simpa using hne
  have hLt := (χ⁻¹).LFunction_ne_zero_of_one_le_re (.inl hinv) ht
  have hf := TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion_one_sub χ hχ (1 - s)
  rw [sub_sub_cancel,
    TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion_eq_digamma χ hχ hne hL,
    TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion_eq_digamma χ⁻¹ hχ.inv hinv hLt,
    even_inv_iff] at hf
  have htwo : 2 * ((1 - s) / 2) = 1 - s := by ring
  have hd := digamma_two_mul (s := (1 - s) / 2) (fun n hn ↦ by
    rw [htwo] at hn
    have hn' := congrArg Complex.re hn
    simp at hn'
    linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [htwo] at hd
  have hadd : digamma (1 - (s + a) / 2) + digamma ((1 - s + a) / 2) =
      digamma ((1 - s) / 2) + digamma ((1 - s) / 2 + 1 / 2) := by
    have h₁ : 1 - s / 2 = (1 - s) / 2 + 1 / 2 := by ring
    have h₂ : 1 - (s + 1) / 2 = (1 - s) / 2 := by ring
    have h₃ : (1 - s + 1) / 2 = (1 - s) / 2 + 1 / 2 := by ring
    by_cases he : χ.Even
    · simp only [a, ite_eq_left he, add_zero, h₁]
      ac_rfl
    · simp only [a, ite_eq_right he, h₂, h₃]
  refine ⟨hL, ?_⟩
  have hr := digamma_one_sub hu
  -- Duplication combines the two reflected gamma terms, independently of the parity.
  dsimp only [a] at hadd
  linear_combination hf + hd + (hr - hadd) / 2

open scoped Classical in
/-- On `Re s ≤ -1`, if `(s + a) / 2` is at least `δ` from every integer (where `a` is the
parity), a primitive nonprincipal `L(s, χ)` is nonzero and its logarithmic derivative is
bounded by `C log(N(‖s‖ + 2))`, uniformly in the conductor and character. -/
theorem exists_norm_logDeriv_LFunction_le_of_re_le_neg_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
      χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, s.re ≤ -1 →
      (∀ n : ℤ, δ ≤ ‖(s + (if χ.Even then 0 else 1 : ℂ)) / 2 - n‖) →
      χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ C * Real.log (N * (‖s‖ + 2)) := by
  classical
  obtain ⟨B, hB, hcot⟩ := TauCeti.exists_norm_pi_mul_cot_pi_mul_le_of_forall_le_norm_sub_intCast hδ
  let D := |Real.log Real.pi| + ‖Complex.log 2‖ + (5 + Real.pi / 2) + B / 2 +
    ‖logDeriv riemannZeta 2‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + D / Real.log 2, by positivity, ?_⟩
  intro N _ χ hχ hne s hs hsep
  let a : ℂ := if χ.Even then 0 else 1
  let u := (s + a) / 2
  have hu (n : ℤ) : u ≠ n := by
    intro h
    have hsep' : δ ≤ ‖u - n‖ := hsep n
    simp only [h, sub_self, norm_zero] at hsep'
    exact hδ.not_ge hsep'
  obtain ⟨hL, he⟩ := hχ.logDeriv_LFunction_eq_of_re_nonpos hne (by linarith : s.re ≤ 0) hu
  have ht : 2 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
  have hψ := norm_digamma_le_log_norm_add_const (by linarith : 1 ≤ (1 - s).re)
  have hlogψ : Real.log ‖(1 : ℂ) - s‖ ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by linarith [re_le_norm ((1 : ℂ) - s)])
      (by simpa using (norm_sub_le (1 : ℂ) s).trans (by simp; linarith))
  refine ⟨hL, ?_⟩
  have hE := (χ⁻¹).norm_logDeriv_LFunction_le_of_le_re (by norm_num : (1 : ℝ) < 2) ht
  have hE' : ‖logDeriv (χ⁻¹).LFunction (1 - s)‖ ≤ ‖logDeriv riemannZeta 2‖ :=
    hE.trans ((neg_le_abs _).trans (abs_re_le_norm _))
  have hR : 1 ≤ (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hlogN := Real.log_nonneg hR
  have hnorm : ‖logDeriv χ.LFunction s‖ ≤ Real.log (N * (‖s‖ + 2)) + D := by
    rw [he, Real.log_mul (by positivity) (by positivity)]
    calc
      _ ≤ |Real.log Real.pi| + ‖Complex.log 2‖ + Real.log N + ‖digamma (1 - s)‖ +
          ‖π * cot (π * u)‖ / 2 + ‖logDeriv (χ⁻¹).LFunction (1 - s)‖ := by
        have h₁ := norm_add_le (Real.log Real.pi : ℂ) (Complex.log 2)
        have h₂ := norm_sub_le ((Real.log Real.pi : ℂ) + Complex.log 2) (Real.log (N : ℝ) : ℂ)
        have h₃ := norm_sub_le ((Real.log Real.pi : ℂ) + Complex.log 2 -
          (Real.log (N : ℝ) : ℂ)) (digamma (1 - s))
        have h₄ := norm_add_le ((Real.log Real.pi : ℂ) + Complex.log 2 -
          (Real.log (N : ℝ) : ℂ) - digamma (1 - s)) ((π * cot (π * u)) / 2)
        have h₅ := norm_sub_le ((Real.log Real.pi : ℂ) + Complex.log 2 -
          (Real.log (N : ℝ) : ℂ) - digamma (1 - s) + (π * cot (π * u)) / 2)
          (logDeriv (χ⁻¹).LFunction (1 - s))
        simp only [norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
          at h₁ h₂ h₃ h₄ h₅ ⊢
        linarith only [h₁, h₂, h₃, h₄, h₅]
      _ ≤ _ := by
        dsimp [D]
        linarith [hcot u hsep]
  have hlog : Real.log 2 ≤ Real.log (N * (‖s‖ + 2)) :=
    Real.log_le_log two_pos (by nlinarith [norm_nonneg s])
  refine hnorm.trans ?_
  rw [add_mul, one_mul, add_le_add_iff_left, div_mul_eq_mul_div, le_div_iff₀ hlog2]
  exact mul_le_mul_of_nonneg_left hlog hD

/-- One absolute constant bounds `L′/L` on both types of left edge in a Dirichlet Perron
contour: vertical edges with half-integer real part and horizontal edges with absolute
height at least `1/2`, in the region `Re s ≤ -1`. These edges contain no zeros. -/
theorem exists_norm_logDeriv_LFunction_le_on_left_edges :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
      χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, s.re ≤ -1 →
      ((∃ j : ℤ, s.re = (j : ℝ) - 1 / 2) ∨ 1 / 2 ≤ |s.im|) →
      χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ C * Real.log (N * (‖s‖ + 2)) := by
  classical
  obtain ⟨C, hC, h⟩ := exists_norm_logDeriv_LFunction_le_of_re_le_neg_one
    (δ := 1 / 4) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N _ χ hp hnp s hs hedge
  refine h hp hnp s hs fun n ↦ ?_
  let a : ℤ := if χ.Even then 0 else 1
  have ha : (a : ℂ) = (if χ.Even then 0 else 1 : ℂ) := by
    by_cases he : χ.Even <;> simp [a, he]
  rw [← ha]
  rcases hedge with ⟨j, hj⟩ | him
  · set k : ℤ := j + a - 2 * n
    have hre : (((s + (a : ℂ)) / 2) - (n : ℂ)).re = ((k : ℝ) - 1 / 2) / 2 := by
      simp only [sub_re, div_ofNat_re, add_re, intCast_re, hj, k, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_ofNat]
      ring
    apply le_trans _ (abs_re_le_norm _)
    rw [hre, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rcases le_or_gt k 0 with hk | hk
    · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      linarith [neg_le_abs ((k : ℝ) - 1 / 2)]
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (Int.add_one_le_of_lt hk)
      linarith [le_abs_self ((k : ℝ) - 1 / 2)]
  · refine le_trans ?_ (abs_im_le_norm _)
    simp only [sub_im, div_ofNat_im, add_im, intCast_im, add_zero, sub_zero, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

end DirichletCharacter
