/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

/-!
# Logarithmic derivatives of completed Dirichlet functions

Let `χ` be a nonprincipal primitive Dirichlet character of conductor `N`, and write
`Λ₀ = (dirichletData χ hχ).entireCompletion`, so that `Λ₀ s = N ^ (s / 2) Λ(χ, s)`. On the
positive half-plane, away from the zeros of `L(χ, ·)`,
`Λ₀'/Λ₀ (s) = ½ log N + Γℝ'/Γℝ (s + a) + L'/L (s, χ)`, where `a` is `0` for even and `1` for odd
characters; the gamma term equals `ψ((s + a)/2)/2 − ½ log π`. These are the terms of the
partial-fraction expansion of `Λ₀'/Λ₀` other than its sum over zeros.

The functional equation gives `Λ₀'/Λ₀(χ, 1 − s) = −Λ₀'/Λ₀(χ⁻¹, s)` and conjugation gives
`Λ₀'/Λ₀(χ⁻¹, conj s) = conj (Λ₀'/Λ₀(χ, s))`. Both hold at every `s`, including zeros, where every
logarithmic derivative involved is zero. For a quadratic character `Λ₀'/Λ₀` is therefore real on
the real axis.

On each compact subset of the positive half-plane, away from the zeros of `L(χ, ·)`, the
difference `Λ₀'/Λ₀ (s) − ½ log N − L'/L (s, χ)` is bounded by one constant, chosen before the
modulus and the character. On `[1, 2]` the condition `L(χ, σ) ≠ 0` holds automatically, so this
compares `Re Λ₀'/Λ₀(σ)` with `½ log N + Re L'/L(σ, χ)` everywhere there, as in the real-zero
estimates for Dirichlet L-functions.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §§10.2 and 11.2.
-/

public section

open Complex ComplexConjugate Filter Topology

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- The conductor factor contributes `½ log N` to the logarithmic derivative of the entire
completion. -/
theorem logDeriv_dirichletData_entireCompletion_eq_completed (hne : χ ≠ 1) {s : ℂ}
    (hs : χ.completedLFunction s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      (Real.log N : ℂ) / 2 + logDeriv χ.completedLFunction s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow : logDeriv (fun z : ℂ ↦ (N : ℂ) ^ (z / 2)) s = (Real.log N : ℂ) / 2 := by
    rw [logDeriv_fun_comp (f := fun w : ℂ ↦ (N : ℂ) ^ w) (g := fun z : ℂ ↦ z / 2)
      (by fun_prop (disch := exact Or.inl hN)) (by fun_prop)]
    simp only [logDeriv_const_cpow hN, deriv_div_const, deriv_id'']
    rw [natCast_log]
    ring
  rw [dirichletData_entireCompletion_eq χ hχ hne,
    logDeriv_fun_mul (f := fun z : ℂ ↦ (N : ℂ) ^ (z / 2)) s (by simp [hN]) hs
      (by fun_prop (disch := exact Or.inl hN))
      ((DirichletCharacter.differentiable_completedLFunction hne) s), hpow]

/-- **The logarithmic derivative of the completed Dirichlet function.** On the positive
half-plane, away from the zeros of `L(χ, ·)`, it is `½ log N + Γℝ'/Γℝ (s + a) + L'/L (s, χ)`,
where `a` is the parity of `χ`. -/
theorem logDeriv_dirichletData_entireCompletion (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hL : χ.LFunction s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      (Real.log N : ℂ) / 2 + logDeriv χ.gammaFactor s + logDeriv χ.LFunction s := by
  have hΛ : χ.completedLFunction s ≠ 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl fun h ↦ by simp [h] at hs)] at hL
    exact left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using hL)
  rw [logDeriv_dirichletData_entireCompletion_eq_completed χ hχ hne hΛ,
    χ.logDeriv_completedLFunction hs (.inr hne) hL, add_assoc]

open scoped Classical in
/-- The logarithmic derivative of the completed Dirichlet function with the explicit digamma
form of its gamma term. -/
theorem logDeriv_dirichletData_entireCompletion_eq_digamma (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      (Real.log N : ℂ) / 2 + (digamma ((s + if χ.Even then 0 else 1) / 2) / 2 -
        (Real.log Real.pi : ℂ) / 2) + logDeriv χ.LFunction s := by
  rw [logDeriv_dirichletData_entireCompletion χ hχ hne hs hL,
    χ.logDeriv_gammaFactor_eq_digamma (χ.gammaFactor_ne_zero_of_re_pos hs)]

/-- The functional equation reflects the logarithmic derivative of the entire completion to
that of the inverse character. -/
theorem logDeriv_dirichletData_entireCompletion_one_sub (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (dirichletData χ hχ).entireCompletion (1 - s) =
      -logDeriv (dirichletData χ⁻¹ hχ.inv).entireCompletion s := by
  have h : logDeriv (fun z ↦ (dirichletData χ hχ).entireCompletion (1 - z)) s =
      -logDeriv (dirichletData χ hχ).entireCompletion (1 - s) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub, neg_div]
  rw [← neg_neg (logDeriv _ (1 - s)), ← h,
    funext (dirichletData_entireCompletion_one_sub χ hχ hne),
    logDeriv_const_mul s _ (DirichletCharacter.rootNumber_ne_zero hχ)]

/-- Conjugation exchanges the logarithmic derivatives of the entire completions of a character
and its inverse. -/
theorem logDeriv_dirichletData_entireCompletion_inv_conj (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (dirichletData χ⁻¹ hχ.inv).entireCompletion (conj s) =
      conj (logDeriv (dirichletData χ hχ).entireCompletion s) := by
  have h : (dirichletData χ⁻¹ hχ.inv).entireCompletion =
      conj ∘ (dirichletData χ hχ).entireCompletion ∘ conj :=
    funext (dirichletData_entireCompletion_inv_conj χ hχ hne)
  rw [h, logDeriv_apply, logDeriv_apply, deriv_conj_conj]
  simp

/-- For a quadratic character, conjugation commutes with the logarithmic derivative of the
entire completion. -/
theorem logDeriv_dirichletData_entireCompletion_conj (hq : χ.IsQuadratic) (hne : χ ≠ 1)
    (s : ℂ) :
    logDeriv (dirichletData χ hχ).entireCompletion (conj s) =
      conj (logDeriv (dirichletData χ hχ).entireCompletion s) := by
  have h := logDeriv_dirichletData_entireCompletion_inv_conj χ hχ hne s
  rwa [dirichletData_inv_of_inv_eq χ hχ hq.inv] at h

/-- For a quadratic character, the logarithmic derivative of the entire completion is real on
the real axis. -/
theorem im_logDeriv_dirichletData_entireCompletion_ofReal (hq : χ.IsQuadratic) (hne : χ ≠ 1)
    (σ : ℝ) : (logDeriv (dirichletData χ hχ).entireCompletion σ).im = 0 := by
  have h := logDeriv_dirichletData_entireCompletion_conj χ hχ hq hne σ
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The logarithmic derivative of the entire completion differs from `½ log N + L'/L` by at most
one constant at every point of a compact subset of the positive half-plane where `L(χ, s) ≠ 0`,
for every nonprincipal primitive character. The constant is chosen before the modulus and the
character. -/
theorem exists_norm_logDeriv_dirichletData_entireCompletion_sub_le (K : Set ℂ)
    (hK : IsCompact K) (hKre : K ⊆ {s : ℂ | 0 < s.re}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive),
      χ ≠ 1 → ∀ s ∈ K, χ.LFunction s ≠ 0 →
        ‖logDeriv (dirichletData χ hχ).entireCompletion s - (Real.log N : ℂ) / 2 -
          logDeriv χ.LFunction s‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := DirichletCharacter.exists_norm_logDeriv_gammaFactor_le K hK hKre
  refine ⟨C, hC0, fun χ hχ hne s hs hL ↦ ?_⟩
  rw [logDeriv_dirichletData_entireCompletion χ hχ hne (hKre hs) hL]
  convert hC χ s hs using 2
  ring

/-- **The gamma term in real-zero estimates.** One absolute constant, chosen before the
modulus, the character and the point, bounds the difference between `Re Λ₀'/Λ₀(σ)` and
`½ log N + Re L'/L(σ, χ)` for `σ ∈ [1, 2]`, for every nonprincipal primitive character
of either parity. -/
theorem exists_abs_re_logDeriv_dirichletData_entireCompletion_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive),
      χ ≠ 1 → ∀ σ ∈ Set.Icc (1 : ℝ) 2,
        |(logDeriv (dirichletData χ hχ).entireCompletion σ).re - Real.log N / 2 -
          (logDeriv χ.LFunction σ).re| ≤ C := by
  have hK : IsCompact ((↑) '' Set.Icc (1 : ℝ) 2 : Set ℂ) :=
    isCompact_Icc.image continuous_ofReal
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_dirichletData_entireCompletion_sub_le _ hK <| by
    rintro _ ⟨σ, hσ, rfl⟩
    simp only [Set.mem_ofPred_eq, ofReal_re]
    linarith [hσ.1]
  refine ⟨C, hC0, fun χ hχ hne σ hσ ↦ ?_⟩
  have hL : χ.LFunction σ ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by simpa using hσ.1)
  refine le_trans (le_of_eq ?_) ((abs_re_le_norm _).trans (hC χ hχ hne σ ⟨σ, hσ, rfl⟩ hL))
  rw [sub_re, sub_re, div_ofNat_re, ofReal_re]

end TauCeti.LFunctions
