/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Elliptic regularity of the classical Laplacian on the `L²` Bessel-potential scale

Let `E` be a finite-dimensional real inner product space. If a real `C²` function `f` on `E` and
its classical Laplacian `Δf` both lie in the Bessel-potential space `H^s(E)`, then `f` lies in
`H^(s + 2)(E)` (`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian`).

The classical Laplacian of a `C²` function is its distributional Laplacian, by Green's second
identity against compactly supported test functions
(`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`). So `-Δf = -Δf` holds weakly,
and elliptic regularity for weak solutions of `-Δh + P h = g`, here with `P = 0`
(`TauCeti.mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq`), gives
`f ∈ H^(s + 2)`. No decay of `f` beyond square integrability is needed.

This is the step that turns a classical semilinear equation `Δf = F(f)` into a gain of two
Sobolev orders once `F(f) ∈ H^s` is known.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 6, §6.3.
* M. E. Taylor, *Partial Differential Equations I*, Chapter 4, §1 and §4.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory TauCeti Complex InnerProductSpace Laplacian
open scoped SchwartzMap Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Elliptic regularity of the classical Laplacian.** A real `C²` function `f` with `f` and
`Δf` in `H^s(E)` lies in `H^(s + 2)(E)`. -/
theorem mem_realSobolevFunctions_add_two_of_laplacian {s : ℝ} {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hmem : f ∈ realSobolevFunctions E s 2) (hΔ : Δ f ∈ realSobolevFunctions E s 2) :
    f ∈ realSobolevFunctions E (s + 2) 2 := by
  refine mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq (P := 0) hmem
    (by simp only [Pi.zero_apply, zero_mul]; exact zero_mem _) (neg_mem hΔ) fun φ hφ hφc ↦ ?_
  -- Green's second identity against `φ`, viewed as a test function on `E`.
  let φ' : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) :=
    ⟨φ, hφ, hφc, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
  have hcoe : (φ' : E → ℝ) = φ := TestFunction.coe_mk
  have h := hf.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume) φ'
  simp only [smul_eq_mul, hcoe] at h
  simp only [Pi.zero_apply, zero_mul, add_zero, mul_neg, Pi.neg_apply, neg_mul, integral_neg,
    neg_inj]
  simpa only [mul_comm] using h

end TemperedDistribution
