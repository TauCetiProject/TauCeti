/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.Semigroups.Generator.Closed
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Convolution

/-!
# Test functions form a core of the heat generator on `Lᵖ`

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The generator `A` of the heat semigroup `e^{tΔ}` on `Lᵖ(E; F)`
(`TauCeti.heatSemigroup`) is the Laplacian in the sense of distributions on its maximal domain
`{f ∈ Lᵖ : Δf ∈ Lᵖ}` (`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`). This file shows that
the classes of smooth compactly supported functions form a core of `A`
(`TauCeti.generator_heatSemigroup_hasCore_range_ambientToLp`): every element of the graph is a
limit of pairs `(φ, Δφ)` with `φ` a test function.

## The argument

* **Cutoff.** A smooth `u` with `u`, `Du` and `Δu` in `Lᵖ` is approximated by `χ_R u` for
  cutoffs `χ_R` equal to one on the ball of radius `R`, with `‖Dχ_R‖ = O(1/R)` and
  `|Δχ_R| = O(1/R²)`. By the Leibniz rule `Δ(χ_R u) = χ_R Δu + 2 Du(∇χ_R) + Δχ_R u`, so dominated
  convergence gives `(χ_R u, Δ(χ_R u)) → (u, Δu)` in `Lᵖ × Lᵖ`
  (`TauCeti.tendsto_eLpNorm_laplacian_smul_sub`,
  `TauCeti.toLp_laplacian_mem_closure_of_contDiff`). On the test functions `χ_R u` the generator is
  the classical Laplacian (`TauCeti.generator_heatSemigroup`).
* **Mollification.** If `Δf = g` in the sense of distributions, the mollification `ρ ⋆ f` by a
  normalized bump `ρ` is smooth, and `Δ(ρ ⋆ f) = ρ ⋆ g`
  (`TauCeti.laplacian_convolution_eq_convolution_of_integral_laplacian_smul`); the derivatives of
  `ρ ⋆ f` are convolutions of `f` with derivatives of `ρ`, hence in `Lᵖ` by Young's inequality
  (`TauCeti.memLp_fderiv_convolution`). The cutoff step puts `(ρ ⋆ f, ρ ⋆ g)` in the closure of
  the graph on test functions, and as `ρ` concentrates, `(ρ ⋆ f, ρ ⋆ g) → (f, g)` in `Lᵖ`.

## Main declarations

* `TauCeti.generator_heatSemigroup_hasCore_range_ambientToLp`: the smooth compactly supported
  functions form a core of the heat generator on `Lᵖ`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
* L. C. Evans, *Partial Differential Equations*, Appendix C.4 (mollifiers).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory Semigroups Set
  TopologicalSpace Topology
open scoped Convolution Distributions ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E F p) in
/-- The classes in `Lᵖ` of smooth compactly supported functions. -/
private abbrev testFunctionLp : Submodule ℝ (Lp F p (volume : Measure E)) :=
  LinearMap.range (TestFunction.ambientToLp (Ω := (⊤ : Opens E)) (n := ⊤) (F := F) p
    (volume : Measure E)).toLinearMap

/-- The graph of the heat generator restricted to the classes of test functions. -/
private abbrev testGraph (hp : p ≠ ∞) :
    Set (Lp F p (volume : Measure E) × Lp F p (volume : Measure E)) :=
  (((heatSemigroup hp).generator.domRestrict (testFunctionLp E F p)).graph : Set _)

/-- The closure of the graph on test functions lies in the graph of the generator, which is
closed. -/
private theorem closure_testGraph_subset (hp : p ≠ ∞) :
    closure (testGraph (E := E) (F := F) hp) ⊆
      ((heatSemigroup (E := E) (F := F) hp).generator.graph : Set _) :=
  closure_minimal (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le)
    (heatSemigroup (E := E) (F := F) hp).isClosed_generator

/-- The classes of test functions lie in the domain of the heat generator. -/
private theorem testFunctionLp_le_domain (hp : p ≠ ∞) :
    testFunctionLp E F p ≤ (heatSemigroup (E := E) (F := F) hp).generator.domain := by
  rintro _ ⟨φ, rfl⟩
  rw [StronglyContinuousSemigroup.generator_domain]
  exact mem_domain_heatSemigroup hp (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    (TestFunction.coeFn_ambientToLp φ)

/-- A smooth compactly supported `φ` and its Laplacian give a point of the graph on test
functions. -/
private theorem mem_testGraph (hp : p ≠ ∞) {φ : E → F} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (h₀ : MemLp φ p volume) (h₂ : MemLp (Δ φ) p volume) :
    (h₀.toLp φ, h₂.toLp (Δ φ)) ∈ testGraph hp := by
  have hmem : h₀.toLp φ ∈ testFunctionLp E F p :=
    ⟨⟨φ, hφ, hc, subset_univ _⟩, TestFunction.ambientToLp_apply _⟩
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨h₀.toLp φ, Submodule.mem_inf.2
    ⟨hmem, testFunctionLp_le_domain hp hmem⟩⟩, rfl, (LinearPMap.domRestrict_apply rfl).trans
      (generator_heatSemigroup hp (hφ.of_le (by simp)) hc h₀.coeFn_toLp h₂.coeFn_toLp)⟩

/-- If `Δf = g` in the sense of distributions, then `(f, g)` is a limit of pairs `(φ, Δφ)` with
`φ` a test function. -/
private theorem mem_closure_testGraph_of_forall (hp : p ≠ ∞) {f g : Lp F p (volume : Measure E)}
    (hfg : ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, φ x • g x) :
    (f, g) ∈ closure (testGraph hp) := by
  set ψ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos
  have hψ : Tendsto (fun n => (ψ n).rOut) atTop (𝓝 0) := ContDiffBump.tendsto_rOut_shrinking one_pos
  have hf : LocallyIntegrable (f : E → F) volume := (Lp.memLp f).locallyIntegrable Fact.out
  refine isClosed_closure.mem_of_tendsto
    ((tendsto_normedBumpLp hp hψ f).prodMk_nhds (tendsto_normedBumpLp hp hψ g))
    (Eventually.of_forall fun n => ?_)
  set u : E → F := (ψ n).normed volume ⋆[lsmul ℝ ℝ, volume] (f : E → F)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := (ψ n).hasCompactSupport_normed.contDiff_convolution_left _
    (ψ n).contDiff_normed hf
  have hfu : normedBumpLp hp (ψ n) volume f =ᵐ[volume] u := by
    simpa only [Lp.toLp_coeFn] using normedBumpLp_ae_eq_convolution hp (ψ n) (Lp.memLp f)
  have hgu : normedBumpLp hp (ψ n) volume g =ᵐ[volume] Δ u := by
    rw [laplacian_convolution_eq_convolution_of_integral_laplacian_smul (ψ n).contDiff_normed
      (ψ n).hasCompactSupport_normed hf
      fun φ hφ hc => hfg ⟨φ, hφ, hc, subset_univ _⟩]
    simpa only [Lp.toLp_coeFn] using normedBumpLp_ae_eq_convolution hp (ψ n) (Lp.memLp g)
  have hu₀ : MemLp u p volume := (Lp.memLp _).ae_eq hfu
  have hu₂ : MemLp (Δ u) p volume := (Lp.memLp _).ae_eq hgu
  have e₀ : normedBumpLp hp (ψ n) volume f = hu₀.toLp u := Lp.ext (hfu.trans hu₀.coeFn_toLp.symm)
  have e₂ : normedBumpLp hp (ψ n) volume g = hu₂.toLp (Δ u) :=
    Lp.ext (hgu.trans hu₂.coeFn_toLp.symm)
  rw [e₀, e₂]
  exact toLp_laplacian_mem_closure_of_contDiff hp (by simp)
    (fun φ hφ hc h₀ h₂ => mem_testGraph hp hφ hc h₀ h₂) hu hu₀
    (memLp_fderiv_convolution hp (ψ n).contDiff_normed (ψ n).hasCompactSupport_normed
      (Lp.memLp f)) hu₂

/-- **The test functions form a core of the heat generator on `Lᵖ`.** For `1 ≤ p < ∞`, the
classes of smooth compactly supported functions lie in the domain of the generator of the heat
semigroup on `Lᵖ(E; F)`, and the generator is the closure of its restriction to them. -/
theorem generator_heatSemigroup_hasCore_range_ambientToLp (hp : p ≠ ∞) :
    (heatSemigroup (E := E) (F := F) hp).generator.HasCore
      (LinearMap.range (TestFunction.ambientToLp (Ω := (⊤ : Opens E)) (n := ⊤) (F := F) p
        (volume : Measure E)).toLinearMap) := by
  refine ((heatSemigroup hp).isClosed_generator.hasCore_iff_graph_subset_closure
    (testFunctionLp_le_domain hp)).2 fun x hx => ?_
  rw [generator_heatSemigroup_eq_weakLaplacianLp] at hx
  exact mem_closure_testGraph_of_forall hp (mem_graph_weakLaplacianLp_iff.1 (by simpa using hx))

end TauCeti
