/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
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

The same weak equation, in its distributional form
(`TauCeti.neg_laplacian_add_eq_of_integral_mul_neg_laplacian_add_mul_eq`), identifies the two
Laplacians as tempered distributions when `f` and `Δf` are square integrable
(`TemperedDistribution.laplacian_toTemperedDistribution_ofRealCLM_compLp`). Without assuming
`Δf` square integrable, if `f` is the `L²` function of `u ∈ H^(s+2)(E)`, the `L²` function of the
Laplacian `BesselPotentialSpace.laplacianCLM s u ∈ H^s(E)` is `Δf`
(`BesselPotentialSpace.coeFn_inclusionLp_laplacianCLM_ae_eq`): it is the sum of the second
directional derivatives in an orthonormal basis, each of which is classical
(`BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq`).

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 6, §6.3.
* M. E. Taylor, *Partial Differential Equations I*, Chapter 4, §1 and §4.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory TauCeti Complex InnerProductSpace Laplacian
open scoped SchwartzMap Distributions ContDiff BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A real `C²` function `f` is a weak solution of `-Δh = -Δf`, in the form of the stationary
Schrödinger equation with zero potential: this is Green's second identity. -/
private theorem integral_mul_neg_laplacian_add_zero_mul_eq {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ z, f z * (-Δ φ z + (0 : E → ℝ) z * φ z) = ∫ z, (-Δ f) z * φ z := by
  -- Green's second identity against `φ`, viewed as a test function on `E`.
  let φ' : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) :=
    ⟨φ, hφ, hφc, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
  have hcoe : (φ' : E → ℝ) = φ := TestFunction.coe_mk
  have h := hf.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume) φ'
  simp only [smul_eq_mul, hcoe] at h
  simp only [Pi.zero_apply, zero_mul, add_zero, mul_neg, Pi.neg_apply, neg_mul, integral_neg,
    neg_inj]
  simpa only [mul_comm] using h

/-- **Elliptic regularity of the classical Laplacian.** A real `C²` function `f` with `f` and
`Δf` in `H^s(E)` lies in `H^(s + 2)(E)`. -/
theorem mem_realSobolevFunctions_add_two_of_laplacian {s : ℝ} {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hmem : f ∈ realSobolevFunctions E s 2) (hΔ : Δ f ∈ realSobolevFunctions E s 2) :
    f ∈ realSobolevFunctions E (s + 2) 2 :=
  mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq (P := 0) hmem
    (by simp only [Pi.zero_apply, zero_mul]; exact zero_mem _) (neg_mem hΔ)
    (integral_mul_neg_laplacian_add_zero_mul_eq hf)

/-- **The classical Laplacian is the distributional Laplacian.** If a real `C²` function `f` and
its classical Laplacian `Δf` are square integrable, represented by `u` and `v` in `L²(E)`, then the
distributional Laplacian of `u` is `v`. -/
theorem laplacian_toTemperedDistribution_ofRealCLM_compLp {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {u v : Lp ℝ 2 (volume : Measure E)} (hu : u =ᵐ[volume] f) (hv : v =ᵐ[volume] Δ f) :
    Δ (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u) : 𝓢'(E, ℂ)) =
      Lp.toTemperedDistribution (Complex.ofRealCLM.compLp v) := by
  have hfu : MemLp f 2 volume := (Lp.memLp u).ae_eq hu
  have hfv : MemLp (Δ f) 2 volume := (Lp.memLp v).ae_eq hv
  -- The weak equation `-Δh = -Δf` gives `-Δu + u = u - v` as tempered distributions.
  have h := neg_laplacian_add_eq_of_integral_mul_neg_laplacian_add_mul_eq (P := 0) hfu
    (by simp only [Pi.zero_apply, zero_mul]; exact MemLp.zero')
    hfv.neg (integral_mul_neg_laplacian_add_zero_mul_eq hf) hu (uR := u - v) (by
      filter_upwards [Lp.coeFn_sub u v, hu, hv] with z h₁ h₂ h₃
      simp only [h₁, Pi.sub_apply, h₂, h₃, Pi.add_apply, Pi.neg_apply, Pi.zero_apply, zero_mul,
        sub_zero]
      ring)
  have hsub : Complex.ofRealCLM.compLp (u - v) =
      Complex.ofRealCLM.compLp u - Complex.ofRealCLM.compLp v := by
    simpa only [ContinuousLinearMap.compLpₗ_apply] using
      map_sub (Complex.ofRealCLM.compLpₗ 2 (volume : Measure E)) u v
  rw [hsub, Lp.toTemperedDistribution_sub, one_smul] at h
  rw [← neg_inj, ← add_right_cancel_iff (a := (Lp.toTemperedDistribution
    (Complex.ofRealCLM.compLp u) : 𝓢'(E, ℂ))), h]
  abel

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution MeasureTheory Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The Laplacian of a real element of `H^{s+2}`.** For `s ≥ 0`, if the `L²` function of
`u ∈ H^{s+2}(E)` is almost everywhere a real `C²` function `f`, then the `L²` function of
`Δu ∈ H^s(E)` is almost everywhere the classical Laplacian `Δf`. No integrability of `Δf` is
assumed: the proof applies `BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq` twice in an
orthonormal basis. -/
theorem coeFn_inclusionLp_laplacianCLM_ae_eq {s : ℝ} (hs : 0 ≤ s) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {u : H^{s + 2}(E)}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] fun x ↦ (f x : ℂ)) :
    ⇑(inclusionLp hs (laplacianCLM s u)) =ᵐ[volume] fun x ↦ (Δ f x : ℂ) := by
  set b := stdOrthonormalBasis ℝ E
  set u' : H^{s + 1 + 1}(E) := u.copy (s + 1 + 1) (by ring)
  set D : E → H^{s + 1}(E) →L[ℂ] H^{s}(E) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
  set D' : E → H^{s + 1 + 1}(E) →L[ℂ] H^{s + 1}(E) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
  have hcopy : u'.toDistr = u.toDistr := toDistr_copy u (by ring)
  have hu' : ⇑(inclusionLp (by linarith) u') =ᵐ[volume] fun x ↦ (f x : ℂ) := by
    have h : inclusionLp (by linarith : (0 : ℝ) ≤ s + 1 + 1) u' =
        inclusionLp (by linarith : (0 : ℝ) ≤ s + 2) u := by
      rw [inclusionLp_eq_iff, toTemperedDistribution_inclusionLp]
      exact hcopy.symm
    rwa [h]
  -- Each second derivative `∂_{b i} ∂_{b i} u` is the classical one.
  have hd (i : _) : ⇑(inclusionLp hs (D (b i) (D' (b i) u'))) =ᵐ[volume]
      fun x ↦ (fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) : ℂ) :=
    coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top hs
      ((hf.fderiv_right le_rfl).clm_apply contDiff_const)
      (coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top (by linarith)
        (hf.of_le one_le_two) hu' (b i)) (b i)
  -- `Δu` is the sum of the second derivatives `∂_{b i} ∂_{b i} u`.
  have hsum : laplacianCLM s u = ∑ i, D (b i) (D' (b i) u') := by
    refine ext ?_
    have hmap := map_sum (toDistrCLM E ℂ s 2) (fun i ↦ D (b i) (D' (b i) u')) Finset.univ
    simp only [toDistrCLM_apply] at hmap
    rw [hmap, toDistr_laplacianCLM, TemperedDistribution.laplacian_eq_sum b]
    simp only [D, D', toDistr_lineDerivCLM, hcopy]
  rw [hsum, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun i ↦ inclusionLp hs (D (b i) (D' (b i) u')),
    ae_all_iff.2 hd] with x h₁ h₂
  rw [h₁, TauCeti.laplacian_eq_sum_fderiv_fderiv_apply b
    ((hf.fderiv_right le_rfl).differentiable one_ne_zero x), Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ ↦ h₂ i

end BesselPotentialSpace
