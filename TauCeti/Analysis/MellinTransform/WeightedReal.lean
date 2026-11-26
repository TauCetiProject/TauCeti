/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Defs
public import TauCeti.Analysis.LaplaceTransform.Mellin

/-!
# Mellin transforms of weighted real parts

If a family of complex inputs is paired by conjugation, the Mellin transform of a
real-weighted sum of their real parts is the same sum of the pairwise averaged transforms.
The logarithmic variable makes this a one-sided Laplace transform, with absolute convergence
included. The formula applies to families of Riesz remainders paired by character inversion,
as in `Deduction.Gm` and `Deduction.Gchi_conj` in Levent Alpöge's
[formalization](https://github.com/leanprover-community/riemann-hypothesis).
-/

public section

open MeasureTheory Set
open scoped ComplexConjugate

namespace TauCeti

/-- The Laplace transform of the real-weighted family sum in logarithmic coordinates is the
weighted sum of the averaged Mellin transforms of each input and its conjugate partner.
Absolute convergence is needed only on the support, since it passes to the conjugate
partners. The map `j` need not be an involution, and the weights may have either sign. -/
theorem hasLaplace_comp_exp_finsupp_sum_re {ι : Type*} (w : ι →₀ ℝ) {G : ι → ℝ → ℂ}
    {j : ι → ι} {s : ℂ} {z : ι → ℂ}
    (hconj : ∀ i ∈ w.support, ∀ y > 1, G (j i) y = conj (G i y))
    (hM : ∀ i ∈ w.support,
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1)) * G i y) (Ioi 1))
    (hz : ∀ i ∈ (↑w.support : Set ι) ∪ j '' ↑w.support,
      ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (-(s + 1)) * G i y = z i) :
    HasLaplace (fun u ↦ ((w.sum fun i c ↦ c * (G i (Real.exp u)).re : ℝ) : ℂ)) s
      (w.sum fun i c ↦ (c : ℂ) * ((z i + z (j i)) / 2)) := by
  have hL i (hi : i ∈ w.support) : HasLaplace (G i ∘ Real.exp) s (z i) := by
    apply (hasLaplace_comp_exp_iff (G i) s (z i) 0).mpr
    simpa only [Real.exp_zero, smul_eq_mul] using And.intro (hM i hi) (hz i (Or.inl hi))
  have hpair i (hi : i ∈ w.support) :
      HasLaplace (fun u ↦ conj (G i (Real.exp u))) s (z (j i)) := by
    have heq : EqOn (G (j i) ∘ Real.exp) (fun u ↦ conj (G i (Real.exp u))) (Ioi 0) :=
      fun u hu ↦ hconj i hi _ (Real.one_lt_exp_iff.mpr hu)
    -- Conjugating the spectral parameter leaves the real part, and hence convergence, unchanged.
    have h := (hL i hi).integrableOn_of_re_le (s := conj s) (by simp)
    have h' := h.hasLaplace.conj
    rw [Complex.conj_conj] at h'
    have hv := ((hasLaplace_comp_exp_iff (G (j i)) s _ 0).mp
      ((hasLaplace_congr_Ioi heq).mpr h')).2
    simp only [Real.exp_zero, smul_eq_mul, Function.comp_apply] at hv h'
    rwa [← hv, hz (j i) (Or.inr ⟨i, hi, rfl⟩)] at h'
  unfold Finsupp.sum
  push_cast
  apply hasLaplace_sum
  intro i hi
  simpa only [Function.comp_apply, smul_eq_mul] using
    ((hL i hi).ofReal_re_of_conj (hpair i hi)).fun_const_smul (w i : ℂ)

end TauCeti
