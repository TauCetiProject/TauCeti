/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.Analysis.Fourier.LaplacianSymbol
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.HeatKernel.Smoothing
import TauCeti.Analysis.Semigroups.Generator.Closed
import TauCeti.Analysis.Semigroups.Generator.Invariance
import TauCeti.Analysis.Sobolev.SmoothCutoff
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Test functions form a core for the heat generator on `Lᵖ`

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The generator `A` of the heat semigroup `e^{tΔ}` on `Lᵖ(E; F)`
(`TauCeti.heatSemigroup`) is the distributional Laplacian on `{f ∈ Lᵖ : Δf ∈ Lᵖ}`
(`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`). This file shows that the classes of
test functions, the smooth compactly supported functions `C_c^∞(E; F)`, form a core for `A`: the
closure of the Laplacian on test functions is the whole generator. Equivalently, for every `f` in
the domain of `A` there are test functions `φₙ` with `φₙ → f` and `Δφₙ → A f` in `Lᵖ`.

The first step treats smooth functions. Let `u` be smooth, with derivatives through order two in
`Lᵖ`, representing `f` in the domain of `A`. Its Laplacian lies in `Lᵖ` (`‖Δu‖ ≤ dim E ‖D²u‖`), so
`A f = Δu` (`TauCeti.mem_graph_weakLaplacianLp_of_contDiff`). Compactly supported smooth
approximations `φₙ` of `u` (`TauCeti.exists_contDiff_hasCompactSupport_approximation`) are test
functions with `φₙ → u` and `D²φₙ → D²u` in `Lᵖ`, hence `Δφₙ → Δu`. So `(f, A f)` lies in the
closure of the graph of `A` restricted to test functions.

The second step is heat smoothing. For `f` in the domain of `A` and `t > 0`, `e^{tΔ} f` is
represented by a smooth function all of whose derivatives lie in `Lᵖ`
(`TauCeti.exists_contDiff_ae_eq_heatSemigroup`,
`TauCeti.exists_eLpNorm_iteratedFDeriv_le_of_ae_eq_heatSemigroup`), so by the first step
`(e^{tΔ} f, A e^{tΔ} f)` lies in that closure. Since `A e^{tΔ} f = e^{tΔ} A f`, strong continuity
gives `(e^{tΔ} f, A e^{tΔ} f) → (f, A f)` as `t → 0`.

Unlike the semigroup on bounded uniformly continuous functions, where test functions are not
dense and the core is the space of smooth functions with bounded derivatives
(`TauCeti.generator_heatSemigroupBUC_hasCore_smoothBoundedDerivativesSubmodule`), on `Lᵖ` with
`p < ∞` compact support costs nothing.

## Main declarations

* `TauCeti.generator_heatSemigroup_hasCore_range_ambientToLp`: the test functions form a core for
  the generator of the heat semigroup on `Lᵖ`.
* `TauCeti.weakLaplacianLp_hasCore_range_ambientToLp`: equivalently, the distributional Laplacian
  on `Lᵖ` with domain `{f ∈ Lᵖ : Δf ∈ Lᵖ}` is the closure of the Laplacian on test functions.
* `TauCeti.exists_tendsto_toLp_and_tendsto_toLp_laplacian`: on `L²`, in Fourier form, every `ψ`
  with `Δψ ∈ L²` is the limit of Schwartz functions `φₙ` with `Δφₙ → Δψ` in `L²`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup and its generator).
* L. C. Evans, *Partial Differential Equations*, Section 7.4.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Semigroups Set Topology TopologicalSpace
open scoped Distributions ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The classes of test functions lie in the domain of the heat generator. -/
private theorem range_ambientToLp_le_domain_generator_heatSemigroup (hp : p ≠ ∞) :
    LinearMap.range (TestFunction.ambientToLp ℝ p (volume : Measure E) :
      𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap ≤
        (heatSemigroup hp).generator.domain := by
  rintro _ ⟨φ, rfl⟩
  rw [StronglyContinuousSemigroup.generator_domain]
  exact mem_domain_heatSemigroup hp (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    (TestFunction.coeFn_ambientToLp φ)

/-- If an element `f` of the domain of the heat generator is represented by a smooth function `u`
whose derivatives through order two lie in `Lᵖ`, then `(f, A f)` is a limit of points of the graph
of the generator restricted to test functions: compactly supported smooth approximations of `u`
whose derivatives through order two converge in `Lᵖ`. -/
private theorem mem_closure_graph_domRestrict_range_ambientToLp (hp : p ≠ ∞)
    (f : (heatSemigroup (E := E) (F := F) hp).generator.domain) {u : E → F}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hmem : ∀ i ≤ 2, MemLp (iteratedFDeriv ℝ i u) p volume)
    (hf : (f : Lp F p (volume : Measure E)) =ᵐ[volume] u) :
    ((f : Lp F p (volume : Measure E)), (heatSemigroup hp).generator f) ∈
      closure (SetLike.coe ((heatSemigroup hp).generator.domRestrict
        (LinearMap.range (TestFunction.ambientToLp ℝ p (volume : Measure E) :
          𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap)).graph) := by
  have hD := range_ambientToLp_le_domain_generator_heatSemigroup (E := E) (F := F) hp
  obtain ⟨g, hg, -, hlim⟩ :=
    exists_contDiff_hasCompactSupport_approximation hp (m := ⊤) hu 2 (by simp) hmem
  let φ (n : ℕ) : 𝓓((⊤ : Opens E), F) := ⟨g n, (hg n).1, (hg n).2, by simp⟩
  have hφ (n : ℕ) : TestFunction.ambientToLp ℝ p volume (φ n) =ᵐ[volume] g n := by
    simpa [φ] using TestFunction.coeFn_ambientToLp (𝕜 := ℝ) (p := p) (ν := volume) (φ n)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by simp)
  have hg2 (n : ℕ) : ContDiff ℝ 2 (g n) := (hg n).1.of_le (by simp)
  have hΔ : MemLp (Δ u) p volume := (hmem 2 le_rfl).of_le_mul
    hu2.continuous_laplacian.aestronglyMeasurable
    (ae_of_all _ (norm_laplacian_le_norm_iteratedFDeriv_two u))
  -- The generator is the distributional Laplacian, which agrees with `Δ` on `C²` functions.
  have hAf : (heatSemigroup hp).generator f = hΔ.toLp _ := by
    have h := mem_graph_weakLaplacianLp_of_contDiff hu2 hf hΔ.coeFn_toLp
    rw [← generator_heatSemigroup_eq_weakLaplacianLp hp] at h
    exact (heatSemigroup hp).generator.mem_graph_snd_inj
      ((heatSemigroup hp).generator.mem_graph f) h rfl
  have hΔg (n : ℕ) : MemLp (Δ (g n)) p volume :=
    (hg2 n).continuous_laplacian.memLp_of_hasCompactSupport (hg n).2.laplacian
  have hgen (n : ℕ) : (heatSemigroup hp).generator ⟨_, hD ⟨φ n, rfl⟩⟩ = (hΔg n).toLp _ :=
    generator_heatSemigroup hp (hg2 n) (hg n).2 (hφ n) (hΔg n).coeFn_toLp
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => (TestFunction.ambientToLp ℝ p volume
      (φ n), (heatSemigroup hp).generator ⟨_, hD ⟨φ n, rfl⟩⟩)) (Tendsto.prodMk_nhds ?_ ?_)
    (Eventually.of_forall fun n => (LinearPMap.mem_graph_iff' _).mpr
      ⟨⟨_, ⟨φ n, rfl⟩, hD ⟨φ n, rfl⟩⟩, Prod.ext rfl (LinearPMap.domRestrict_apply rfl)⟩)
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (hlim 0 (by norm_num)).congr fun n => eLpNorm_congr_norm_ae
      (((hg n).1.continuous_iteratedFDeriv (by simp)).sub
        (hu.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [hφ n, hf] with x h₁ h₂
    simp only [Pi.sub_apply, h₁, h₂, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
  · simp_rw [hgen, hAf]
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    -- Pointwise `‖Δv‖ ≤ dim E ‖D²v‖` for the difference `v` of the approximation and `u`.
    have hle (n : ℕ) : eLpNorm (Δ (g n) - Δ u) p volume ≤ ENNReal.ofReal (Module.finrank ℝ E) *
        eLpNorm (iteratedFDeriv ℝ 2 (g n) - iteratedFDeriv ℝ 2 u) p volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((hg2 n).continuous_laplacian.sub hu2.continuous_laplacian).aestronglyMeasurable
        (ae_of_all _ fun x => by
          have h := norm_laplacian_le_norm_iteratedFDeriv_two (g n - u) x
          rwa [iteratedFDeriv_sub_apply (hg2 n).contDiffAt hu2.contDiffAt,
            (hg2 n).contDiffAt.laplacian_sub hu2.contDiffAt] at h) p
    have h := ENNReal.Tendsto.const_mul (hlim 2 le_rfl) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (Module.finrank ℝ E))
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hle

/-- **Test functions form a core for the heat generator on `Lᵖ`.** For `1 ≤ p < ∞`, the classes
of the test functions `C_c^∞(E; F)` lie in the domain of the generator of the heat semigroup on
`Lᵖ(E; F)`, and the closure of its restriction to them is the whole generator. -/
theorem generator_heatSemigroup_hasCore_range_ambientToLp (hp : p ≠ ∞) :
    (heatSemigroup (E := E) (F := F) hp).generator.HasCore
      (LinearMap.range (TestFunction.ambientToLp ℝ p (volume : Measure E) :
        𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap) := by
  set S := (heatSemigroup (E := E) (F := F) hp).toStronglyContinuousSemigroup
  refine (S.isClosed_generator.hasCore_iff_graph_subset_closure
    (range_ambientToLp_le_domain_generator_heatSemigroup hp)).2 ?_
  -- Every point of the graph is a limit of heat regularizations `e^{tΔ} f`, which have smooth
  -- representatives with derivatives in `Lᵖ`.
  rintro _ hq
  obtain ⟨f, rfl⟩ := S.generator.mem_graph_iff'.mp hq
  have hf : (f : Lp F p (volume : Measure E)) ∈ S.domain := by
    rw [← S.generator_domain]
    exact f.property
  let g (t : ℝ≥0) : S.generator.domain :=
    ⟨S t f, (SetLike.ext_iff.mp S.generator_domain _).2 (S.map_mem_domain t hf)⟩
  have hg (t : ℝ≥0) : S.generator (g t) = S t (S.generator f) := S.generator_map t ⟨f, hf⟩
  have htend : Tendsto (fun t => ((g t : Lp F p (volume : Measure E)), S.generator (g t)))
      (𝓝[>] 0) (𝓝 ((f : Lp F p (volume : Measure E)), S.generator f)) := by
    simp only [hg]
    exact ((S.continuousAt_zero_tendsto f).prodMk_nhds
      (S.continuousAt_zero_tendsto _)).mono_left nhdsWithin_le_nhds
  rw [← closure_closure]
  refine mem_closure_of_tendsto htend (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => ?_)
  obtain ⟨u, hu, hfu⟩ :=
    exists_contDiff_ae_eq_heatSemigroup hp ht.ne' (f : Lp F p (volume : Measure E))
  refine mem_closure_graph_domRestrict_range_ambientToLp hp (g t) hu (fun i _ => ?_) hfu
  obtain ⟨C, -, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_le_of_ae_eq_heatSemigroup (E := E) (F := F) i
  exact (hC hp ht.ne' f hu.continuous hfu).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top _))

/-- **The distributional Laplacian on `Lᵖ` is the closure of the Laplacian on test functions.**
For `1 ≤ p < ∞`, the test functions form a core for the Laplacian in the sense of distributions
on `Lᵖ`, with domain `{f ∈ Lᵖ : Δf ∈ Lᵖ}`. -/
theorem weakLaplacianLp_hasCore_range_ambientToLp (hp : p ≠ ∞) :
    (weakLaplacianLp E F p).HasCore
      (LinearMap.range (TestFunction.ambientToLp ℝ p (volume : Measure E) :
        𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap) := by
  rw [← generator_heatSemigroup_eq_weakLaplacianLp hp]
  exact generator_heatSemigroup_hasCore_range_ambientToLp hp

/-! ### Schwartz functions are a core for the Laplacian on `L²` -/

section L2

open scoped FourierTransform SchwartzMap

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Schwartz functions are a core for the Laplacian on `L²`.** If `ψ, χ ∈ L²(E, G)` satisfy
`𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ` almost everywhere, that is `χ = Δψ` with `ψ` in the domain of the Laplacian
on `L²`, then there are Schwartz functions `φₙ` with `φₙ → ψ` and `Δφₙ → χ` in `L²`. This is the
case `p = 2` of `TauCeti.weakLaplacianLp_hasCore_range_ambientToLp`, in Fourier form. -/
theorem exists_tendsto_toLp_and_tendsto_toLp_laplacian {ψ χ : Lp G 2 (volume : Measure E)}
    (h : 𝓕 χ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 ψ ξ) :
    ∃ φ : ℕ → 𝓢(E, G), Tendsto (fun n ↦ (φ n).toLp 2) atTop (𝓝 ψ) ∧
      Tendsto (fun n ↦ (Δ (φ n)).toLp 2) atTop (𝓝 χ) := by
  set T : Set (Lp G 2 (volume : Measure E) × Lp G 2 (volume : Measure E)) :=
    range fun φ : 𝓢(E, G) ↦ (φ.toLp 2, (Δ φ).toLp 2)
  -- The graph of the Laplacian on test functions consists of Schwartz pairs `(φ, Δφ)`.
  have hsub : (((weakLaplacianLp E G 2).domRestrict
      (LinearMap.range (TestFunction.ambientToLp ℝ 2 (volume : Measure E) :
        𝓓((⊤ : Opens E), G) →L[ℝ] Lp G 2 (volume : Measure E)).toLinearMap)).graph :
          Set (Lp G 2 (volume : Measure E) × Lp G 2 (volume : Measure E))) ⊆ T := by
    intro q hq
    obtain ⟨⟨x, ⟨φ, hφ⟩, hx⟩, rfl⟩ := (LinearPMap.mem_graph_iff' _).1 hq
    set φ' := TestFunction.toSchwartzMapCLM ℝ φ
    have hφ' : (x : Lp G 2 (volume : Measure E)) =ᵐ[volume] φ' := by
      rw [← hφ, TestFunction.coe_toSchwartzMapCLM]
      exact TestFunction.coeFn_ambientToLp φ
    refine ⟨φ', Prod.ext (Lp.ext (φ'.coeFn_toLp 2 volume |>.trans hφ'.symm)) ?_⟩
    refine (weakLaplacianLp E G 2).mem_graph_snd_inj
      (mem_graph_weakLaplacianLp_of_contDiff (φ'.smooth 2) hφ'
        (((Δ φ').coeFn_toLp 2 volume).trans (ae_of_all _ (SchwartzMap.laplacian_apply φ'))))
      ((weakLaplacianLp E G 2).mem_graph ⟨x, hx⟩) rfl |>.trans ?_
    exact (LinearPMap.domRestrict_apply rfl).symm
  have hmem := (weakLaplacianLp_hasCore_range_ambientToLp (p := 2)
    ENNReal.ofNat_ne_top).graph_subset_of_isClosed isClosed_closure (hsub.trans subset_closure)
    (mem_graph_weakLaplacianLp_of_laplacian_toTemperedDistribution_eq
      ((Lp.laplacian_toTemperedDistribution_eq_iff ψ χ).2 h))
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose φ hφ using hq
  refine ⟨φ, ?_, ?_⟩
  · simpa only [← hφ] using hlim.fst_nhds
  · simpa only [← hφ] using hlim.snd_nhds

end L2

end TauCeti
