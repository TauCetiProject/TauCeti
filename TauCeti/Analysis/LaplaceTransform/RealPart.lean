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

/-- Taking a finitely supported real-weighted sum of real parts of functions commutes with
taking the conjugate-paired average of their Laplace transforms. Only indices in the support
need to have convergent transforms. -/
theorem _root_.Finsupp.hasLaplace_sum_ofReal_re {ι : Type*} (w : ι →₀ ℝ) {f : ι → ℝ → ℂ}
    {s : ℂ} {z v : ι → ℂ} {μ : Measure ℝ}
    (hs : ∀ i ∈ w.support, HasLaplace (f i) s (z i) μ)
    (hc : ∀ i ∈ w.support, HasLaplace (f i) (conj s) (v i) μ) :
    HasLaplace (fun t ↦ Complex.ofReal (w.sum fun i c ↦ c * (f i t).re)) s
      (w.sum fun i c ↦ (c : ℂ) * ((z i + conj (v i)) / 2)) μ := by
  have h := hasLaplace_sum (u := w.support) fun i hi ↦
    ((hs i hi).fun_add (by simpa only [Complex.conj_conj] using (hc i hi).conj)).fun_const_smul
      ((w i : ℂ) / 2)
  simpa only [Finsupp.sum, Complex.ofReal_sum, Complex.ofReal_mul, Complex.re_eq_add_conj,
    smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc] using h

end TauCeti
