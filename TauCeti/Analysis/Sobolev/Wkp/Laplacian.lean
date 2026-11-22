/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The weak Laplacian on the Sobolev scale

For `u ∈ W^{2,p}(Ω)` on an open set `Ω` of a finite-dimensional real inner product space, the
weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` is an `Lᵖ` field of endomorphisms, and its trace
is the Laplacian of `u` in the sense of distributions: for every test function `φ` on `Ω`,

`∫ Δφ • u = ∫ φ • tr D²u`.

Consequently the two notions of a solution of `Δu = f` coincide in `W^{2,p}(Ω)`: for locally
integrable `f`, the weak formulation `∫ Δφ • u = ∫ φ • f` for all test functions `φ` holds exactly
when `u` is a strong solution, `tr D²u = f` almost everywhere in `Ω`. This is the form in which
`Lᵖ` estimates for the second derivatives, which are stated through the Laplacian, apply to
solutions of Poisson's equation given in either formulation.

On the whole Sobolev scale, the sum of the second directional weak derivatives along an
orthonormal basis is a bounded operator `Δ : W^{k+2,p}(Ω) → W^{k,p}(Ω)`
(`TauCeti.Wkp.laplacianL`). Integrating by parts twice in each direction shows that it is the
distributional Laplacian, `∫ Δφ • u = ∫ φ • Δu` for every test function `φ` on `Ω`, and this
identity determines it; in particular it is the same sum along every orthonormal basis. On
`W^{2,p}(Ω)` it is the trace of the weak Hessian.

No boundedness or boundary regularity of `Ω` is used.

## Main declarations

* `TauCeti.Wkp.integral_laplacian_smul_value_eq`: the distributional Laplacian of a `W^{2,p}`
  function is the trace of its weak Hessian.
* `TauCeti.Wkp.forall_integral_laplacian_smul_value_eq_iff`: weak and strong solutions of
  `Δu = f` agree in `W^{2,p}(Ω)`.
* `TauCeti.Wkp.trace_iteratedGradient_ofTestFunctionₗ_ae_eq`: for a test function `φ`, regarded
  as an element of `W^{2,p}(Ω)`, the trace of the weak Hessian is `Δφ`.
* `TauCeti.Wkp.laplacianL`: the weak Laplacian as a bounded operator
  `W^{k+2,p}(Ω) → W^{k,p}(Ω)`, and `TauCeti.Wkp.laplacianL_eq_sum`: it is the sum of the second
  directional weak derivatives along any orthonormal basis.
* `TauCeti.Wkp.integral_laplacian_smul_value_eq_laplacianL`: it is the distributional Laplacian,
  and `TauCeti.Wkp.laplacianL_eq_of_forall_integral_laplacian_smul_eq`: it is the only element of
  `W^{k,p}(Ω)` that is, since elements of `W^{k,p}(Ω)` are determined by their integrals against
  test functions (`TauCeti.Wkp.ext_of_forall_integral_smul_value_eq`).
* `TauCeti.Wkp.value_laplacianL_zero_ae_eq_trace`: on `W^{2,p}(Ω)` the weak Laplacian is the trace
  of the weak Hessian.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §9.4.
-/

public section

namespace TauCeti.Wkp

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **The distributional Laplacian of a `W^{2,p}` function is the trace of its weak Hessian**:
`∫ Δφ • u = ∫ φ • tr D²u` for every test function `φ` on `Ω`. -/
theorem integral_laplacian_smul_value_eq (u : Wkp mu Omega p 2) (φ : 𝓓(Omega, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • value 2 u x ∂mu =
      ∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (iteratedGradient 1 u x) ∂mu := by
  rw [value_succ]
  exact (hasWeakFDerivOn_value (lowerOrder 1 u)).integral_laplacian_smul_eq_integral_smul_trace
    (hasWeakFDerivOn_iteratedGradient 0 u) φ

/-- **Weak and strong solutions of `Δu = f` agree in `W^{2,p}(Ω)`.** For `u ∈ W^{2,p}(Ω)` and `f`
locally integrable on `Ω`, `∫ Δφ • u = ∫ φ • f` holds for every test function `φ` on `Ω` if and
only if the trace of the weak Hessian of `u` is `f` almost everywhere in `Ω`. -/
theorem forall_integral_laplacian_smul_value_eq_iff (u : Wkp mu Omega p 2) {f : E → ℝ}
    (hf : LocallyIntegrableOn f Omega mu) :
    (∀ φ : 𝓓(Omega, ℝ),
        ∫ x, Δ (φ : E → ℝ) x • value 2 u x ∂mu = ∫ x, (φ : E → ℝ) x • f x ∂mu) ↔
      (fun x => LinearMap.trace ℝ E (iteratedGradient 1 u x)) =ᵐ[mu.restrict Omega] f := by
  -- The trace of the weak Hessian is locally integrable on `Ω`, as the weak Hessian is.
  have htr : LocallyIntegrableOn (fun x => LinearMap.trace ℝ E (iteratedGradient 1 u x))
      Omega mu := fun x hx => by
    obtain ⟨t, ht, hint⟩ := (hasWeakFDerivOn_iteratedGradient 0 u).locallyIntegrableOn_deriv x hx
    exact ⟨t, ht, by simpa only [IntegrableOn, Function.comp_def, traceCLM_apply] using
      (traceCLM ℝ E).integrable_comp hint⟩
  simp_rw [integral_laplacian_smul_value_eq]
  constructor
  · intro h
    have hzero := Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (htr.sub hf)
      fun g hg hgc hgs => by
        set φ : 𝓓(Omega, ℝ) := ⟨g, hg, hgc, hgs⟩
        have hi₁ : Integrable (fun x => g x • LinearMap.trace ℝ E (iteratedGradient 1 u x)) mu := by
          simpa [φ] using φ.integrable_smul htr
        have hi₂ : Integrable (fun x => g x • f x) mu := by
          simpa [φ] using φ.integrable_smul hf
        simp only [Pi.sub_apply, smul_sub]
        rw [integral_sub hi₁ hi₂, sub_eq_zero]
        simpa [φ] using h φ
    rw [Filter.EventuallyEq, ae_restrict_iff' Omega.isOpen.measurableSet]
    filter_upwards [hzero] with x hx hxΩ
    exact sub_eq_zero.1 (hx hxΩ)
  · intro h φ
    rw [← setIntegral_smul_eq_integral_smul, ← setIntegral_smul_eq_integral_smul (w := f)]
    exact integral_congr_ae (h.mono fun x hx => congrArg ((φ : E → ℝ) x • ·) hx)

/-- **The trace of the weak Hessian of a test function is its Laplacian**: for a test function
`φ` on `Ω`, regarded as an element of `W^{2,p}(Ω)`, `tr D²φ = Δφ` almost everywhere in `Ω`. -/
theorem trace_iteratedGradient_ofTestFunctionₗ_ae_eq (φ : 𝓓(Omega, ℝ)) :
    (fun x => LinearMap.trace ℝ E
      (iteratedGradient 1 (ofTestFunctionₗ (mu := mu) (p := p) 2 φ) x : E →L[ℝ] E))
        =ᵐ[mu.restrict Omega] Δ (φ : E → ℝ) := by
  filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) p 1 φ] with x hx
  rw [iteratedGradient_ofTestFunctionₗ 1 φ, hx, iteratedGradientTestFunction_def,
    laplacian_eq_trace_iteratedGradientChain_one]

/-! ### The weak Laplacian on the Sobolev scale -/

/-- **The weak Laplacian** `Δu = ∑ᵢ ∂ᵢ∂ᵢu` as a bounded operator `W^{k+2,p}(Ω) → W^{k,p}(Ω)`, the
sum of the second directional weak derivatives along the standard orthonormal basis of `E`. It is
the distributional Laplacian (`TauCeti.Wkp.integral_laplacian_smul_value_eq_laplacianL`), which
determines it (`TauCeti.Wkp.laplacianL_eq_of_forall_integral_laplacian_smul_eq`), so the choice of
basis does not matter (`TauCeti.Wkp.laplacianL_eq_sum`). -/
noncomputable def laplacianL (k : ℕ) : Wkp mu Omega p (k + 2) →L[ℝ] Wkp mu Omega p k :=
  ∑ i, (lineDerivL (stdOrthonormalBasis ℝ E i) k).comp
    (lineDerivL (stdOrthonormalBasis ℝ E i) (k + 1))

/-- **Second-order integration by parts in one direction on the Sobolev scale**: for
`u ∈ W^{k+2,p}(Ω)` and a test function `φ` on `Ω`, `∫ ∂ᵥ∂ᵥφ • u = ∫ φ • ∂ᵥ∂ᵥu`. -/
theorem integral_fderiv_fderiv_smul_value_eq (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (φ : 𝓓(Omega, ℝ)) (v : E) :
    ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y v) x v • value (k + 2) u x ∂mu =
      ∫ x, (φ : E → ℝ) x • value k (lineDerivL v k (lineDerivL v (k + 1) u)) x ∂mu := by
  have e1 := (hasWeakLineDerivOn_lineDerivL v (k + 1)
    u).integral_lineDeriv_smul_eq_neg_integral_smul (TestFunction.lineDerivCLM ℝ v φ)
  have e2 := (hasWeakLineDerivOn_lineDerivL v k
    (lineDerivL v (k + 1) u)).integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [TestFunction.coe_lineDerivCLM] at e1
  simp_rw [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv, TestFunction.lineDeriv_eq_fderiv]
    at e1 e2
  rw [e1, e2, neg_neg]

/-- The sum of the second directional weak derivatives along an orthonormal basis `b` is the
distributional Laplacian: `∫ Δφ • u = ∫ φ • ∑ᵢ ∂_{bᵢ}∂_{bᵢ}u` for `u ∈ W^{k+2,p}(Ω)`. -/
private theorem integral_laplacian_smul_value_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (k : ℕ) (u : Wkp mu Omega p (k + 2)) (φ : 𝓓(Omega, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • value (k + 2) u x ∂mu =
      ∫ x, (φ : E → ℝ) x •
        value k ((∑ i, (lineDerivL (b i) k).comp (lineDerivL (b i) (k + 1))) u) x ∂mu := by
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ (φ : E → ℝ)) := φ.contDiff.fderiv_right (by simp)
  have hΔφ : ∀ x, Δ (φ : E → ℝ) x =
      ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) := fun x ↦
    laplacian_eq_sum_fderiv_fderiv_apply b (hφ1.differentiable one_ne_zero x)
  have hint₁ : ∀ i, Integrable
      (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) • value (k + 2) u x) mu := by
    intro i
    have := integrable_lineDeriv_smul_of_locallyIntegrableOn
      (hasWeakLineDerivOn_lineDerivL (b i) (k + 1) u).locallyIntegrableOn
      (TestFunction.lineDerivCLM ℝ (b i) φ) (b i)
    rw [TestFunction.coe_lineDerivCLM] at this
    simpa only [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv] using this
  have hint₂ : ∀ i, Integrable (fun x ↦ (φ : E → ℝ) x •
      value k (lineDerivL (b i) k (lineDerivL (b i) (k + 1) u)) x) mu := fun i ↦
    φ.integrable_smul (hasWeakLineDerivOn_lineDerivL (b i) k
      (lineDerivL (b i) (k + 1) u)).locallyIntegrableOn_deriv
  calc ∫ x, Δ (φ : E → ℝ) x • value (k + 2) u x ∂mu
      = ∑ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) •
          value (k + 2) u x ∂mu := by
        simp_rw [hΔφ, Finset.sum_smul]
        exact integral_finsetSum _ fun i _ ↦ hint₁ i
    _ = ∑ i, ∫ x, (φ : E → ℝ) x •
          value k (lineDerivL (b i) k (lineDerivL (b i) (k + 1) u)) x ∂mu :=
        Finset.sum_congr rfl fun i _ ↦ integral_fderiv_fderiv_smul_value_eq k u φ (b i)
    _ = ∫ x, (φ : E → ℝ) x •
          value k ((∑ i, (lineDerivL (b i) k).comp (lineDerivL (b i) (k + 1))) u) x ∂mu := by
        rw [← integral_finsetSum _ fun i _ ↦ hint₂ i]
        refine integral_congr_ae ?_
        -- the value of the sum is the sum of the values, almost everywhere in `Ω`
        have hsum := value_finsetSum_ae k Finset.univ
          fun i ↦ (lineDerivL (b i) k).comp (lineDerivL (b i) (k + 1)) u
        rw [ae_restrict_iff' Omega.isOpen.measurableSet] at hsum
        filter_upwards [hsum] with x hx
        by_cases hxΩ : x ∈ (Omega : Set E)
        · have h := hx hxΩ
          simp only [ContinuousLinearMap.comp_apply] at h
          simp only [sum_apply, ContinuousLinearMap.comp_apply] at h ⊢
          rw [h, Finset.smul_sum]
        · simp [φ.zero_on_compl hxΩ]

/-- **The weak Laplacian along any orthonormal basis**: for every orthonormal basis `b` of `E`,
`Δu = ∑ᵢ ∂_{bᵢ}∂_{bᵢ}u` for `u ∈ W^{k+2,p}(Ω)`. In particular the definition of
`TauCeti.Wkp.laplacianL` does not depend on the choice of basis. -/
theorem laplacianL_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) :
    (laplacianL k : Wkp mu Omega p (k + 2) →L[ℝ] Wkp mu Omega p k) =
      ∑ i, (lineDerivL (b i) k).comp (lineDerivL (b i) (k + 1)) := by
  ext1 u
  refine ext_of_forall_integral_smul_value_eq fun φ ↦ ?_
  rw [← integral_laplacian_smul_value_eq_sum b, laplacianL, ← integral_laplacian_smul_value_eq_sum]

/-- **The weak Laplacian is the distributional Laplacian**: for `u ∈ W^{k+2,p}(Ω)` and a test
function `φ` on `Ω`, `∫ Δφ • u = ∫ φ • Δu`. -/
theorem integral_laplacian_smul_value_eq_laplacianL (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (φ : 𝓓(Omega, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • value (k + 2) u x ∂mu =
      ∫ x, (φ : E → ℝ) x • value k (laplacianL k u) x ∂mu := by
  rw [laplacianL_eq_sum (stdOrthonormalBasis ℝ E)]
  exact integral_laplacian_smul_value_eq_sum _ k u φ

/-- **The weak Laplacian is determined by integration by parts**: an element `d ∈ W^{k,p}(Ω)` with
`∫ Δφ • u = ∫ φ • d` for every test function `φ` on `Ω` is the weak Laplacian of
`u ∈ W^{k+2,p}(Ω)`. -/
theorem laplacianL_eq_of_forall_integral_laplacian_smul_eq {k : ℕ} {u : Wkp mu Omega p (k + 2)}
    {d : Wkp mu Omega p k}
    (h : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x, Δ (φ : E → ℝ) x • value (k + 2) u x ∂mu = ∫ x, (φ : E → ℝ) x • value k d x ∂mu) :
    laplacianL k u = d :=
  ext_of_forall_integral_smul_value_eq fun φ ↦
    (integral_laplacian_smul_value_eq_laplacianL k u φ).symm.trans (h φ)

/-- **The weak Laplacian is the trace of the weak Hessian** on `W^{2,p}(Ω)`:
`Δu = tr D²u` almost everywhere in `Ω`. -/
theorem value_laplacianL_zero_ae_eq_trace (u : Wkp mu Omega p 2) :
    ⇑(value 0 (laplacianL 0 u)) =ᵐ[mu.restrict Omega]
      fun x ↦ LinearMap.trace ℝ E (iteratedGradient 1 u x) :=
  ((forall_integral_laplacian_smul_value_eq_iff u (locallyIntegrableOn_value 0 _)).1
    (integral_laplacian_smul_value_eq_laplacianL 0 u)).symm

end TauCeti.Wkp
