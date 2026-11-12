/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Elliptic regularity of the classical Laplacian on the `L²` Bessel-potential scale

Let `E` be a finite-dimensional real inner product space. If a real `C²` function `f` on `E` and
its classical Laplacian `Δf` both lie in the Bessel-potential space `H^s(E)`, then `f` lies in
`H^(s + 2)(E)` (`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian`).

The classical Laplacian of a `C²` function is its distributional Laplacian, by Green's second
identity against compactly supported test functions
(`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`). So the tempered distribution
`T` of `f` satisfies `-Δ T + T = f - Δf ∈ H^s`, and the resolvent of the Laplacian
(`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`) gives `T ∈ H^(s + 2)`.
No decay of `f` beyond square integrability is needed: the test functions in Green's identity have
compact support, and they determine a tempered distribution (`TauCeti.ext_real`).

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
  have hf2 : MemLp f 2 volume := memLp_of_mem_realSobolevFunctions hmem
  have hΔ2 : MemLp (Δ f) 2 volume := memLp_of_mem_realSobolevFunctions hΔ
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 (sub_mem hmem hΔ)
  set T : 𝓢'(E, ℂ) := Lp.toTemperedDistribution (ofRealCLM.compLp (hf2.toLp f))
  -- `-Δ T + T` is the distribution of `f - Δf`, tested on real compactly supported functions.
  have hT : -Δ T + (1 : ℝ) • T = Lp.toTemperedDistribution (ofRealCLM.compLp u) := by
    refine ext_real fun φ hφ ↦ ?_
    let φ' : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) :=
      ⟨φ, φ.smooth ⊤, hφ, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
    have hcoe : (φ' : E → ℝ) = φ := TestFunction.coe_mk
    have hgreen : ∫ x, Δ (φ : E → ℝ) x * f x = ∫ x, φ x * Δ f x := by
      have h := hf.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume) φ'
      simpa only [smul_eq_mul, hcoe] using h
    have hφ2 := φ.memLp 2 (μ := volume)
    -- Pairing a real Schwartz function with the distribution of `f`.
    have hpair (ψ : 𝓢(E, ℝ)) : T (ψ.postcompCLM ofRealCLM) = ((∫ x, ψ x * f x : ℝ) : ℂ) := by
      rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
        integral_congr_ae (hf2.coeFn_toLp.mono fun x hx ↦ by rw [hx])]
    have hu' : ∫ x, φ x * u x = (∫ x, φ x * f x) - ∫ x, φ x * Δ f x := by
      rw [integral_congr_ae (huf.mono fun x hx ↦ by rw [hx, Pi.sub_apply, mul_sub])]
      exact integral_sub (f := fun x ↦ φ x * f x) (g := fun x ↦ φ x * Δ f x)
        (hφ2.integrable_mul hf2) (hφ2.integrable_mul hΔ2)
    rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
      hpair, hpair, Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM, one_smul, hu']
    simp only [SchwartzMap.laplacian_apply]
    rw [hgreen]
    push_cast
    ring
  have hT2 : MemSobolev (s + 2) 2 T :=
    (memSobolev_add_two_iff_neg_laplacian_add_smul one_pos).2 (hT ▸ hu)
  exact mem_realSobolevFunctions.2 ⟨hf2.toLp f, hf2.coeFn_toLp, hT2⟩

end TemperedDistribution
