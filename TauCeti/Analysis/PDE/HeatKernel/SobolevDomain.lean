/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.PDE.Regularity.Hessian.Poisson
import TauCeti.Analysis.Sobolev.Wkp.Laplacian

/-!
# The domain of the heat generator is the Sobolev space `W^{2,p}`

Let `E` be a finite-dimensional real inner product space and `1 ≤ p < ∞`. The generator `A` of
the heat semigroup `e^{tΔ}` on `Lᵖ(E)` is the Laplacian in the sense of distributions, with domain
`{f ∈ Lᵖ : Δf ∈ Lᵖ}` (`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`). This file identifies
that domain with a Sobolev space for real-valued functions and `1 < p < ∞`:

* `TauCeti.mem_domain_heatSemigroup_of_wkp`: the value of an element of `W^{2,p}(E)` lies in the
  domain of `A`, for every `1 ≤ p < ∞`;
* `TauCeti.mem_domain_heatSemigroup_iff_exists_wkp`: `f` lies in the domain of `A` exactly when it
  is the value of an element of `W^{2,p}(E)`;
* `TauCeti.mem_domain_heatSemigroup_iff_memSobolev`: equivalently, `f` lies in the Bessel
  potential space `H^{2,p}(E)`; for `p = 2` the domain is `H²(E)`;
* `TauCeti.generator_heatSemigroup_ae_eq_trace`: on the domain, `A f` is the trace of the weak
  Hessian of `f`, for every `1 ≤ p < ∞`.

One inclusion holds because the distributional Laplacian of a `W^{2,p}` function is its weak
Laplacian (`TauCeti.Wkp.integral_laplacian_smul_value_eq_laplacianL`), an element of `Lᵖ`. The
other is the `W^{2,p}` regularity of solutions of Poisson's equation on the whole space,
`TauCeti.exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq`, which rests on the
Calderón–Zygmund estimates and therefore needs `1 < p < ∞`. At `p = 1` the domain is strictly
larger than `W^{2,1}` once `dim E ≥ 2`, and no identification is made there.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup and its generator).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TemperedDistribution TopologicalSpace
open scoped ENNReal Laplacian Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`W^{2,p}` lies in the domain of the heat generator.** For `1 ≤ p < ∞`, a real-valued
`f ∈ Lᵖ(E)` that is, almost everywhere, the value of an element of the Sobolev space `W^{2,p}(E)`
lies in the domain of the generator of the heat semigroup on `Lᵖ(E)`. -/
theorem mem_domain_heatSemigroup_of_wkp (hp_top : p ≠ ∞) {f : Lp ℝ p (volume : Measure E)}
    (w : Wkp (volume : Measure E) ⊤ p 2) (hw : (Wkp.value 2 w : E → ℝ) =ᵐ[volume] f) :
    f ∈ (heatSemigroup hp_top).domain := by
  have hΔ := Wkp.memLp_value 0 (Wkp.laplacianL 0 w)
  rw [mem_domain_heatSemigroup_iff hp_top]
  refine ⟨hΔ.toLp _, fun φ ↦ ?_⟩
  calc ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, Δ (φ : E → ℝ) x • Wkp.value 2 w x :=
        integral_congr_ae (hw.mono fun x hx ↦ by simp only [hx])
    _ = ∫ x, (φ : E → ℝ) x • Wkp.value 0 (Wkp.laplacianL 0 w) x :=
        Wkp.integral_laplacian_smul_value_eq_laplacianL 0 w φ
    _ = ∫ x, φ x • (hΔ.toLp _ : Lp ℝ p (volume : Measure E)) x :=
        integral_congr_ae (hΔ.coeFn_toLp.mono fun x hx ↦ by simp only [hx])

/-- **The domain of the heat generator is `W^{2,p}`.** For `1 < p < ∞`, a real-valued
`f ∈ Lᵖ(E)` lies in the domain of the generator of the heat semigroup on `Lᵖ(E)` if and only if it
is, almost everywhere, the value of an element of the Sobolev space `W^{2,p}(E)`. -/
theorem mem_domain_heatSemigroup_iff_exists_wkp (hp : 1 < p) (hp_top : p ≠ ∞)
    {f : Lp ℝ p (volume : Measure E)} :
    f ∈ (heatSemigroup hp_top).domain ↔
      ∃ w : Wkp (volume : Measure E) ⊤ p 2, (Wkp.value 2 w : E → ℝ) =ᵐ[volume] f := by
  refine ⟨fun hf ↦ ?_, fun ⟨w, hw⟩ ↦ mem_domain_heatSemigroup_of_wkp hp_top w hw⟩
  obtain ⟨g, hg⟩ := (mem_domain_heatSemigroup_iff hp_top).1 hf
  obtain ⟨w, hw, -⟩ := exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq hp hp_top
    (Lp.memLp f) (Lp.memLp g) fun φ hφ hc ↦ by
      have h := hg (TestFunction.mk φ hφ hc (by simp only [Opens.coe_top, Set.subset_univ]))
      rw [TestFunction.coe_mk] at h
      simpa only [smul_eq_mul] using h
  exact ⟨w, hw⟩

/-- **The domain of the heat generator is the Bessel potential space `H^{2,p}`.** For
`1 < p < ∞`, a real-valued `f ∈ Lᵖ(E)` lies in the domain of the generator of the heat semigroup on
`Lᵖ(E)` if and only if it lies in `H^{2,p}(E)`. For `p = 2` the domain is `H²(E)`. -/
theorem mem_domain_heatSemigroup_iff_memSobolev (hp : 1 < p) (hp_top : p ≠ ∞)
    {f : Lp ℝ p (volume : Measure E)} :
    f ∈ (heatSemigroup hp_top).domain ↔
      MemSobolev 2 p (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp f)) := by
  rw [mem_domain_heatSemigroup_iff_exists_wkp hp hp_top,
    ← Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top 2 f, Nat.cast_ofNat]

/-- **The heat generator is the trace of the weak Hessian.** If `f` lies in the domain of the
generator `A` of the heat semigroup on `Lᵖ(E)` and is the value of `w ∈ W^{2,p}(E)`, then `A f` is
the trace `tr D²w` of the weak Hessian of `w` almost everywhere. -/
theorem generator_heatSemigroup_ae_eq_trace (hp_top : p ≠ ∞)
    (f : (heatSemigroup (E := E) (F := ℝ) hp_top).generator.domain)
    {w : Wkp (volume : Measure E) ⊤ p 2}
    (hw : (Wkp.value 2 w : E → ℝ) =ᵐ[volume] (f : Lp ℝ p (volume : Measure E))) :
    ((heatSemigroup hp_top).generator f : E → ℝ) =ᵐ[volume]
      fun x ↦ LinearMap.trace ℝ E (Wkp.iteratedGradient 1 w x) := by
  have hgraph : ((f : Lp ℝ p (volume : Measure E)), (heatSemigroup hp_top).generator f) ∈
      (weakLaplacianLp E ℝ p).graph := by
    rw [← generator_heatSemigroup_eq_weakLaplacianLp hp_top]
    exact LinearPMap.mem_graph _ f
  have hloc : LocallyIntegrableOn ((heatSemigroup hp_top).generator f : E → ℝ)
      ((⊤ : Opens E) : Set E) volume :=
    ((Lp.memLp _).locallyIntegrable (Fact.out : 1 ≤ p)).locallyIntegrableOn _
  have h := (Wkp.forall_integral_laplacian_smul_value_eq_iff w hloc).1 fun φ ↦
    (integral_congr_ae (hw.mono fun x hx ↦ by simp only [hx])).trans
      ((mem_graph_weakLaplacianLp_iff.1 hgraph) φ)
  simpa only [Opens.coe_top, Measure.restrict_univ] using h.symm

end TauCeti
