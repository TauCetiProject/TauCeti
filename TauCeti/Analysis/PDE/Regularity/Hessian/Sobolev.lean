/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Normed.Module.Trace
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace
import TauCeti.Analysis.PDE.Regularity.Hessian.Lp
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Laplacian

/-!
# The Calderón–Zygmund estimate for strong solutions in `W^{2,p}(ℝⁿ)`

For `n ≥ 3` and `1 < p < ∞`, this file proves the `W^{2,p}` estimate of the Hessian by the
Laplacian on the whole space: there is a constant `C` such that

`‖D²u‖_{Lᵖ(ℝⁿ)} ≤ C ‖f‖_{Lᵖ(ℝⁿ)}`

for every `u ∈ W^{2,p}(ℝⁿ)` and `f ∈ Lᵖ(ℝⁿ)` with `Δu = f`. Here `D²u` is the highest recorded
weak derivative `TauCeti.Wkp.iteratedGradient 1 u`, the weak Hessian as an `Lᵖ` field of
endomorphisms of `ℝⁿ` with the operator norm. The equation `Δu = f` is taken either strongly, the
trace of the weak Hessian of `u` being `f` in `Lᵖ`
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`), or against test
functions, `∫ Δφ • u = ∫ φ • f` for every `φ ∈ C_c^∞(ℝⁿ)`
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq`); the two agree
by `TauCeti.Wkp.forall_integral_laplacian_smul_value_eq_iff`. The constant depends only on `n`
and `p`.

## The argument

For Schwartz functions this is
`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`, the singular integral
estimate for the Hessian of the Newtonian potential, and test functions are Schwartz functions.
Test functions are dense in `W^{2,p}(ℝⁿ)` for `p < ∞`
(`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`), so choose test functions `φⱼ → u` in the Sobolev
norm. Their Hessians converge to the weak Hessian of `u` in `Lᵖ`. The trace of an endomorphism is
a continuous linear functional, and the trace of the Hessian of `φⱼ` is `Δφⱼ`
(`TauCeti.laplacian_eq_trace_iteratedGradientChain_one`), so `Δφⱼ` converges in `Lᵖ` to the trace
of the weak Hessian of `u`, which is `f`. The estimate for `φⱼ` passes to the limit.

## Main declarations

* `TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`:
  `‖D²u‖_p ≤ C ‖f‖_p` for `u ∈ W^{2,p}(ℝⁿ)` with `tr D²u = f` in `Lᵖ`.
* `TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq`:
  the same estimate for `u ∈ W^{2,p}(ℝⁿ)` with `Δu = f` against test functions.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.4.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Laplacian Distributions SchwartzMap Topology

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Schwartz-space Hessian estimate, for a test function regarded as an element of
`W^{2,p}(ℝⁿ)`. -/
private theorem norm_iteratedGradient_ofTestFunctionₗ_le {C : ℝ≥0}
    (hC : ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))) p volume)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ‖Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)‖ ≤
      C * lpNorm (Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume := by
  have hφ : ContDiff ℝ 2 (φ : EuclideanSpace ℝ (Fin n) → ℝ) := φ.contDiff.of_le (by simp)
  rw [Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 1 _ hφ.contDiffOn
    (by rw [Wkp.value_ofTestFunctionₗ]; exact testFunctionLp_apply_ae p φ), Opens.coe_top,
    Measure.restrict_univ]
  have h := hC (φ.hasCompactSupport.toSchwartzMap φ.contDiff)
  rw [funext (SchwartzMap.laplacian_apply _)] at h
  have hfin : eLpNorm (Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume ≠ ∞ :=
    (hφ.continuous_laplacian.memLp_of_hasCompactSupport
      φ.hasCompactSupport.laplacian).eLpNorm_ne_top
  calc lpNorm (iteratedFDeriv ℝ (1 + 1) (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume
      ≤ ((C : ℝ≥0∞) * eLpNorm (Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h
    _ = C * lpNorm (Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, lpNorm]

/-- **The Calderón–Zygmund estimate for strong solutions in `W^{2,p}(ℝⁿ)`.** Let `n ≥ 3` and
`1 < p < ∞`. There is a constant `C` such that every `u ∈ W^{2,p}(ℝⁿ)` solving `Δu = f` with
`f ∈ Lᵖ(ℝⁿ)` strongly, in the sense that the trace of the weak Hessian of `u` is `f` in `Lᵖ`,
satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝⁿ`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq (hn : 3 ≤ n)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
      (traceCLM ℝ (EuclideanSpace ℝ (Fin n))).compLpL p _ (Wkp.iteratedGradient 1 u) = f →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real hn hp hp_top
  refine ⟨C, fun u f hf' => ?_⟩
  -- The trace of endomorphisms, which is continuous because `ℝⁿ` is finite-dimensional.
  set T := traceCLM ℝ (EuclideanSpace ℝ (Fin n))
  -- Approximate `u` by test functions in the Sobolev norm.
  obtain ⟨v, hv, hlim⟩ :=
    mem_closure_iff_seq_limit.1 (Wkp.denseRange_ofTestFunctionₗ_top hp_top 2 u)
  choose φ hφ using hv
  set H := fun j => Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 (φ j))
  have hH : Tendsto H atTop (𝓝 (Wkp.iteratedGradient 1 u)) := by
    simp only [H, hφ, ← Wkp.iteratedGradientL_apply]
    exact ((Wkp.iteratedGradientL 1).continuous.tendsto u).comp hlim
  -- The trace of the Hessian of a test function is its Laplacian.
  have hTH : ∀ j, ‖T.compLpL p _ (H j)‖ =
      lpNorm (Δ (φ j : EuclideanSpace ℝ (Fin n) → ℝ)) p volume := fun j => by
    have hHj : H j = iteratedGradientTestFunctionLp p 1 (φ j) :=
      Wkp.iteratedGradient_ofTestFunctionₗ 1 (φ j)
    have hae : (T.compLpL p _ (H j) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[(volume : Measure _).restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))]
          Δ (φ j : EuclideanSpace ℝ (Fin n) → ℝ) := by
      filter_upwards [T.coeFn_compLpL (H j),
        iteratedGradientTestFunctionLp_apply_ae (mu := volume) p 1 (φ j)] with x hx hHx
      rw [hx, traceCLM_apply, hHj, hHx, iteratedGradientTestFunction_def,
        laplacian_eq_trace_iteratedGradientChain_one]
    rw [Lp.norm_def, eLpNorm_congr_ae hae, Opens.coe_top, Measure.restrict_univ, lpNorm]
  have hlimT : Tendsto (fun j => (C : ℝ) * ‖T.compLpL p _ (H j)‖) atTop (𝓝 (C * ‖f‖)) := by
    rw [← hf']
    exact ((((T.compLpL p _).continuous.tendsto _).comp hH).norm).const_mul _
  exact le_of_tendsto_of_tendsto' hH.norm hlimT fun j =>
    (norm_iteratedGradient_ofTestFunctionₗ_le hC (φ j)).trans_eq (by rw [hTH j])

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)`, against test functions.** Let `n ≥ 3` and
`1 < p < ∞`. There is a constant `C` such that every `u ∈ W^{2,p}(ℝⁿ)` solving `Δu = f` with
`f ∈ Lᵖ(ℝⁿ)`, in the sense that `∫ Δφ • u = ∫ φ • f` for every test function `φ`, satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝⁿ`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq (hn : 3 ≤ n)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
      (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
        ∫ x, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x • Wkp.value 2 u x = ∫ x, φ x • f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq hn hp hp_top
  refine ⟨C, fun u f hf => hC u f ?_⟩
  -- A solution against test functions is a strong solution: the trace of its weak Hessian is `f`.
  have hloc : LocallyIntegrableOn (f : EuclideanSpace ℝ (Fin n) → ℝ) ⊤ volume :=
    (((Lp.memLp f).locallyIntegrable Fact.out).mono_measure
      (by rw [Opens.coe_top, Measure.restrict_univ])).locallyIntegrableOn _
  refine Lp.ext ?_
  filter_upwards [(traceCLM ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL
      (Wkp.iteratedGradient 1 u),
    (Wkp.forall_integral_laplacian_smul_value_eq_iff u hloc).1 hf] with x hx htr
  rw [hx, traceCLM_apply, htr]

end TauCeti
