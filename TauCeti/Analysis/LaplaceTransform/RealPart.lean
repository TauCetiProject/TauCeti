/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic

/-!
# Laplace transforms of real parts

For a complex-valued function, the Laplace transform of its real part at `s` is the average of
its transform at `s` and the conjugate of its transform at `conj s`. The same formula works for
finitely supported real weights, without any sign condition. This is the averaging used for the
real-valued family remainder in L. Alpöge's `Deduction.Gm`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open MeasureTheory
open scoped ComplexConjugate

namespace TauCeti

/-- The Laplace transform of the real part uses the transform values at both `s` and `conj s`.
The real part is embedded back into `ℂ` so the transform parameter can be complex. -/
theorem HasLaplace.ofReal_re {f : ℝ → ℂ} {s z w : ℂ} {μ : Measure ℝ}
    (hs : HasLaplace f s z μ) (hc : HasLaplace f (conj s) w μ) :
    HasLaplace (fun t ↦ Complex.ofReal (f t).re) s ((z + conj w) / 2) μ := by
  have h := hs.fun_add (by simpa only [Complex.conj_conj] using hc.conj)
  have h' := h.fun_const_smul ((2 : ℂ)⁻¹)
  rw [smul_eq_mul, mul_comm, ← div_eq_mul_inv] at h'
  refine h'.congr_ae (.of_forall fun t ↦ ?_)
  simp only [smul_eq_mul, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Taking a finitely supported real-weighted sum of real parts of functions commutes with
taking the conjugate-paired average of their Laplace transforms. Only indices in the support
need to have convergent transforms. -/
theorem _root_.Finsupp.hasLaplace_sum_ofReal_re {ι : Type*} (w : ι →₀ ℝ) {f : ι → ℝ → ℂ}
    {s : ℂ} {z v : ι → ℂ} {μ : Measure ℝ}
    (hs : ∀ i ∈ w.support, HasLaplace (f i) s (z i) μ)
    (hc : ∀ i ∈ w.support, HasLaplace (f i) (conj s) (v i) μ) :
    HasLaplace (fun t ↦ Complex.ofReal (w.sum fun i c ↦ c * (f i t).re)) s
      (w.sum fun i c ↦ (c : ℂ) * ((z i + conj (v i)) / 2)) μ := by
  simpa only [Finsupp.sum, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul] using
    (hasLaplace_sum (u := w.support) fun i hi ↦ ((hs i hi).ofReal_re (hc i hi)).fun_const_smul
      (w i : ℂ))

end TauCeti
