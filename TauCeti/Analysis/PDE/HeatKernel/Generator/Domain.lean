/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.Analysis.PDE.HeatKernel.Generator.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.PDE.HeatKernel.Smoothing
import TauCeti.Analysis.Semigroups.Generator.Closed
import TauCeti.Analysis.Semigroups.Generator.Invariance
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Integral.BoundedSmul

/-!
# The domain of the heat generator on `Lᵖ`

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The generator `A` of the heat semigroup `e^{tΔ}` on `Lᵖ(E; F)`
(`TauCeti.heatSemigroup`) is the Laplacian with its maximal distributional domain:

`D(A) = {f ∈ Lᵖ : Δf ∈ Lᵖ}`, and `A f = Δf`,

where `Δf = g` means `∫ Δφ • f = ∫ φ • g` for every smooth compactly supported test function
`φ : E → ℝ`. In graph form, `(f, g)` lies on the graph of `A` exactly when `Δf = g` in this
sense (`TauCeti.mem_graph_generator_heatSemigroup_iff`). Moreover the classes of smooth
compactly supported functions form a core of `A`
(`TauCeti.generator_heatSemigroup_hasCore_range_ambientToLp`): every element of the graph is a
limit of pairs `(φ, Δφ)` with `φ` a test function. No Sobolev space appears: for `p = 1` and
`dim E ≥ 2` the domain is strictly larger than `W^{2,1}`, and the distributional description is
the one that holds for every `p`.

## The argument

* **Cutoff.** A smooth `u` with `u`, `Du` and `Δu` in `Lᵖ` is approximated by `χ_R u` for
  cutoffs `χ_R` equal to one on the ball of radius `R`, with `‖Dχ_R‖ = O(1/R)` and
  `|Δχ_R| = O(1/R²)`. By the Leibniz rule `Δ(χ_R u) = χ_R Δu + 2 Du(∇χ_R) + Δχ_R u`, so dominated
  convergence gives `(χ_R u, Δ(χ_R u)) → (u, Δu)` in `Lᵖ × Lᵖ`
  (`TauCeti.tendsto_eLpNorm_laplacian_smul_sub`). On the test functions `χ_R u` the generator is
  the classical Laplacian (`TauCeti.generator_heatSemigroup`).
* **Distributional Laplacian to the graph.** If `Δf = g` in the sense of distributions, the
  mollification `ρ ⋆ f` by a normalized bump `ρ` is smooth, and its Laplacian falls on the
  kernel, `Δ(ρ ⋆ f)(x) = ∫ Δρ(x - y) f(y) dy`. Testing `Δf = g` against `y ↦ ρ(x - y)` gives
  `Δ(ρ ⋆ f) = ρ ⋆ g` (`TauCeti.laplacian_convolution_eq_convolution_of_integral_laplacian_smul`),
  and the derivatives of `ρ ⋆ f` are convolutions of `f` with derivatives of `ρ`, hence in `Lᵖ` by
  Young's inequality (`TauCeti.memLp_fderiv_convolution`). The cutoff step puts `(ρ ⋆ f, ρ ⋆ g)`
  in the closure of the graph on test functions, and as `ρ` concentrates,
  `(ρ ⋆ f, ρ ⋆ g) → (f, g)` in `Lᵖ`. Since the generator is closed
  (`TauCeti.Semigroups.StronglyContinuousSemigroup.isClosed_generator`), `(f, g)` lies on its
  graph. By Green's identity this applies to `(u, Δu)` for every `C²` function `u` with `u` and
  `Δu` in `Lᵖ`, so `A u = Δu`.
* **The graph to the distributional Laplacian.** If `A f = g`, then for `t > 0` the class
  `e^{tΔ} f` has a smooth representative `w` (`TauCeti.exists_contDiff_ae_eq_heatSemigroup`)
  whose Laplacian lies in `Lᵖ` (`TauCeti.exists_eLpNorm_laplacian_le_of_ae_eq_heatSemigroup`), so
  `A e^{tΔ} f = Δw` by the previous step, while `A e^{tΔ} f = e^{tΔ} g` since the generator
  commutes with the semigroup. Green's identity `∫ Δφ • w = ∫ φ • Δw` and the limit `t → 0` give
  `∫ Δφ • f = ∫ φ • g`.

## Main declarations

* `TauCeti.mem_graph_generator_heatSemigroup_of_contDiff`: a `C²` function `u` with `u` and `Δu`
  in `Lᵖ` lies in the domain of the generator, which sends it to `Δu`.
* `TauCeti.mem_graph_generator_heatSemigroup_iff`: `A f = g` exactly when `Δf = g` in the sense of
  distributions.
* `TauCeti.mem_domain_heatSemigroup_iff`: `f` lies in the domain exactly when its distributional
  Laplacian is an `Lᵖ` function.
* `TauCeti.generator_heatSemigroup_hasCore_range_ambientToLp`: the smooth compactly supported
  functions form a core.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
* L. C. Evans, *Partial Differential Equations*, Appendix C.4 (mollifiers) and Section 7.4
  (semigroup theory).
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

/-- A smooth compactly supported `φ` and its Laplacian give a point of the graph on test
functions. -/
private theorem mem_testGraph (hp : p ≠ ∞) {φ : E → F} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (h₀ : MemLp φ p volume) (h₂ : MemLp (Δ φ) p volume) :
    (h₀.toLp φ, h₂.toLp (Δ φ)) ∈ testGraph hp := by
  obtain ⟨y, hy, hgy⟩ := (LinearPMap.mem_graph_iff _).1 <|
    mem_graph_generator_heatSemigroup hp (hφ.of_le (by simp)) hc h₀.coeFn_toLp h₂.coeFn_toLp
  refine (LinearPMap.mem_graph_iff _).2
    ⟨⟨y, Submodule.mem_inf.2 ⟨?_, y.2⟩⟩, hy, (LinearPMap.domRestrict_apply rfl).trans hgy⟩
  rw [hy]
  exact ⟨⟨φ, hφ, hc, subset_univ _⟩, TestFunction.ambientToLp_apply _⟩

omit [CompleteSpace F] in
/-- **The cutoff step.** Let `G` be a set of pairs of `Lᵖ` classes containing `(φ, Δφ)` for every
compactly supported `φ` of class `Cⁿ`, `n ≥ 2`. Then the closure of `G` contains `(u, Δu)` for
every `u` of class `Cⁿ` with `u`, `Du` and `Δu` in `Lᵖ`: the truncations `χ_R u` converge to `u`
together with their Laplacians. -/
private theorem mem_closure_of_contDiff (hp : p ≠ ∞) {n : ℕ∞} (hn : 2 ≤ n)
    {G : Set (Lp F p (volume : Measure E) × Lp F p (volume : Measure E))}
    (hG : ∀ φ : E → F, ContDiff ℝ n φ → HasCompactSupport φ → ∀ (h₀ : MemLp φ p volume)
      (h₂ : MemLp (Δ φ) p volume), (h₀.toLp φ, h₂.toLp (Δ φ)) ∈ G)
    {u : E → F} (hu : ContDiff ℝ n u) (hu₀ : MemLp u p volume)
    (hu₁ : MemLp (fderiv ℝ u) p volume) (hu₂ : MemLp (Δ u) p volume) :
    (hu₀.toLp u, hu₂.toLp (Δ u)) ∈ closure G := by
  obtain ⟨C, hC⟩ := exists_forall_contDiff_cutoff_ball_norm_laplacian_le (E := E)
  choose χ hχs hχc hχ1 _ hχd hχΔ hχI using fun n : ℕ => hC (n + 1) (by positivity)
  have hR : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hn' : (2 : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
  have hu2 : ContDiff ℝ 2 u := hu.of_le hn'
  have hφ (m : ℕ) : ContDiff ℝ n fun x => χ m x • u x :=
    ((hχs m).of_le (WithTop.coe_le_coe.2 le_top)).smul hu
  have hφ2 (m : ℕ) : ContDiff ℝ 2 fun x => χ m x • u x := (hφ m).of_le hn'
  refine mem_closure_of_tendsto (b := atTop) (Tendsto.prodMk_nhds ?_ ?_)
    (Eventually.of_forall fun m => hG _ (hφ m) (hχc m).smul_right
      ((hφ2 m).continuous.memLp_of_hasCompactSupport (hχc m).smul_right)
      ((hφ2 m).continuous_laplacian.memLp_of_hasCompactSupport (hχc m).smul_right.laplacian))
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ hu₀]
    exact tendsto_eLpNorm_smul_sub hp hR (fun m => (hχs m).continuous.aestronglyMeasurable) hχ1 hχI
      hu₀
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ hu₂]
    exact tendsto_eLpNorm_laplacian_smul_sub hp hR (fun m => (hχs m).of_le (by simp)) hχ1 hχd
      hχΔ hχI hu2 hu₀ hu₁ hu₂

/-- **The distributional Laplacian to the graph.** If `Δf = g` in the sense of distributions,
then `(f, g)` is a limit of pairs `(φ, Δφ)` with `φ` a test function. -/
private theorem mem_closure_testGraph_of_forall (hp : p ≠ ∞) {f g : Lp F p (volume : Measure E)}
    (hfg : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, Δ φ x • f x = ∫ x, φ x • g x) :
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
      (ψ n).hasCompactSupport_normed hf hfg]
    simpa only [Lp.toLp_coeFn] using normedBumpLp_ae_eq_convolution hp (ψ n) (Lp.memLp g)
  have hu₀ : MemLp u p volume := (Lp.memLp _).ae_eq hfu
  have hu₂ : MemLp (Δ u) p volume := (Lp.memLp _).ae_eq hgu
  have e₀ : normedBumpLp hp (ψ n) volume f = hu₀.toLp u := Lp.ext (hfu.trans hu₀.coeFn_toLp.symm)
  have e₂ : normedBumpLp hp (ψ n) volume g = hu₂.toLp (Δ u) :=
    Lp.ext (hgu.trans hu₂.coeFn_toLp.symm)
  rw [e₀, e₂]
  exact mem_closure_of_contDiff hp (by simp) (fun φ hφ hc h₀ h₂ => mem_testGraph hp hφ hc h₀ h₂) hu
    hu₀ (memLp_fderiv_convolution hp (ψ n).contDiff_normed (ψ n).hasCompactSupport_normed
      (Lp.memLp f)) hu₂

omit [CompleteSpace F] [Fact (1 ≤ p)] in
/-- **Green's identity in `Lᵖ`.** For a `C²` function `u` with `u` and `Δu` in `Lᵖ`, the
distributional Laplacian of the class of `u` is the class of `Δu`: `∫ Δφ • u = ∫ φ • Δu` for every
smooth compactly supported `φ`. -/
private theorem integral_laplacian_smul_toLp_eq {u : E → F} (hu : ContDiff ℝ 2 u)
    (hu₀ : MemLp u p volume) (hu₂ : MemLp (Δ u) p volume) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∫ x, Δ φ x • hu₀.toLp u x = ∫ x, φ x • hu₂.toLp (Δ u) x :=
  calc ∫ x, Δ φ x • hu₀.toLp u x = ∫ x, Δ φ x • u x :=
        integral_congr_ae (hu₀.coeFn_toLp.mono fun x hx => congrArg (Δ φ x • ·) hx)
    _ = ∫ x, φ x • Δ u x :=
        hu.contDiffOn (s := ((⊤ : Opens E) : Set E))
          |>.integral_laplacian_smul_eq_integral_smul_laplacian
            (⟨φ, hφ, hc, subset_univ _⟩ : 𝓓((⊤ : Opens E), ℝ))
    _ = _ := integral_congr_ae (hu₂.coeFn_toLp.mono fun x hx => congrArg (φ x • ·) hx.symm)

/-- **A `C²` function with `u` and `Δu` in `Lᵖ` lies in the domain of the heat generator**, which
sends it to its classical Laplacian `Δu`. -/
theorem mem_graph_generator_heatSemigroup_of_contDiff (hp : p ≠ ∞) {u : E → F}
    (hu : ContDiff ℝ 2 u) (hu₀ : MemLp u p volume) (hu₂ : MemLp (Δ u) p volume) :
    (hu₀.toLp u, hu₂.toLp (Δ u)) ∈ (heatSemigroup hp).generator.graph :=
  closure_testGraph_subset hp <| mem_closure_testGraph_of_forall hp fun _ hφ hc =>
    integral_laplacian_smul_toLp_eq hu hu₀ hu₂ hφ hc

/-- If the heat generator sends `f` to `g`, then `Δ(e^{tΔ} f) = e^{tΔ} g` in the sense of
distributions at every time `t > 0`. -/
private theorem integral_laplacian_smul_heatSemigroup_eq (hp : p ≠ ∞)
    {f g : Lp F p (volume : Measure E)} (h : (f, g) ∈ (heatSemigroup hp).generator.graph)
    {t : ℝ≥0} (ht : t ≠ 0) {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∫ x, Δ φ x • heatSemigroup hp t f x = ∫ x, φ x • heatSemigroup hp t g x := by
  set S := (heatSemigroup (E := E) (F := F) hp).toStronglyContinuousSemigroup
  -- The smooth representative `w` of `e^{tΔ} f` and its Laplacian lie in `Lᵖ`.
  obtain ⟨w, hw, hfw⟩ := exists_contDiff_ae_eq_heatSemigroup hp ht f
  obtain ⟨C₂, -, hC₂⟩ := exists_eLpNorm_laplacian_le_of_ae_eq_heatSemigroup (E := E) (F := F)
  have hw₀ : MemLp w p volume := (Lp.memLp _).ae_eq hfw
  have hw₂ : MemLp (Δ w) p volume := (hC₂ hp ht f hw.continuous hfw).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).eLpNorm_lt_top)
  -- The generator sends `e^{tΔ} f` both to `Δw` and to `e^{tΔ} g`.
  obtain ⟨⟨f', hf'⟩, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).1 h
  have hf'S : f' ∈ S.domain := by rwa [← StronglyContinuousSemigroup.generator_domain]
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by simp)
  have h₁ := mem_graph_generator_heatSemigroup_of_contDiff hp hw2 hw₀ hw₂
  have h₂ : (S t f', S t (S.generator ⟨f', hf'⟩)) ∈ S.generator.graph :=
    (LinearPMap.mem_graph_iff _).2 ⟨⟨S t f', by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact S.map_mem_domain _ hf'S⟩, rfl, S.generator_map _ ⟨f', hf'S⟩⟩
  have e₁ : hw₀.toLp w = S t f' := Lp.ext (hw₀.coeFn_toLp.trans hfw.symm)
  have e₂ := S.generator.mem_graph_snd_inj h₁ h₂ e₁
  -- Green's identity for the smooth representative.
  have h := integral_laplacian_smul_toLp_eq hw2 hw₀ hw₂ hφ hc
  rw [e₁, e₂] at h
  exact h

/-- **The graph to the distributional Laplacian.** If the heat generator sends `f` to `g`, then
`Δf = g` in the sense of distributions: let `t → 0` in the same identity for `e^{tΔ} f` and
`e^{tΔ} g`. -/
private theorem integral_laplacian_smul_eq_of_mem_graph (hp : p ≠ ∞)
    {f g : Lp F p (volume : Measure E)} (h : (f, g) ∈ (heatSemigroup hp).generator.graph)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∫ x, Δ φ x • f x = ∫ x, φ x • g x := by
  set S := (heatSemigroup (E := E) (F := F) hp).toStronglyContinuousSemigroup
  set t : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := by
    have hcoe : (fun n => (t n : ℝ)) = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      funext n
      simp [t]
    rw [← NNReal.tendsto_coe, NNReal.coe_zero, hcoe]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim₁ := (((hφ.of_le (by simp) : ContDiff ℝ 2 φ).continuous_laplacian
    |>.continuous_integral_smul_Lp_of_hasCompactSupport hc.laplacian).tendsto f).comp
    ((S.continuousAt_zero_tendsto f).comp ht)
  have hlim₂ := ((hφ.continuous.continuous_integral_smul_Lp_of_hasCompactSupport hc).tendsto
    g).comp ((S.continuousAt_zero_tendsto g).comp ht)
  exact tendsto_nhds_unique (hlim₁.congr fun n =>
    integral_laplacian_smul_heatSemigroup_eq hp h (inv_ne_zero (by positivity)) hφ hc) hlim₂

/-- **The heat generator on `Lᵖ` is the distributional Laplacian.** For `1 ≤ p < ∞`, the
generator of the heat semigroup on `Lᵖ(E; F)` sends `f` to `g` exactly when `Δf = g` in the sense
of distributions: `∫ Δφ • f = ∫ φ • g` for every smooth compactly supported `φ : E → ℝ`. -/
theorem mem_graph_generator_heatSemigroup_iff (hp : p ≠ ∞) {f g : Lp F p (volume : Measure E)} :
    (f, g) ∈ (heatSemigroup hp).generator.graph ↔
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, Δ φ x • f x = ∫ x, φ x • g x :=
  ⟨fun h _ hφ hc => integral_laplacian_smul_eq_of_mem_graph hp h hφ hc,
    fun h => closure_testGraph_subset hp (mem_closure_testGraph_of_forall hp h)⟩

/-- **The domain of the heat generator on `Lᵖ`.** For `1 ≤ p < ∞`, `f ∈ Lᵖ(E; F)` lies in the
domain of the generator of the heat semigroup exactly when its distributional Laplacian is an
`Lᵖ` function: `D(A) = {f ∈ Lᵖ : Δf ∈ Lᵖ}`. -/
theorem mem_domain_heatSemigroup_iff (hp : p ≠ ∞) {f : Lp F p (volume : Measure E)} :
    f ∈ (heatSemigroup hp).domain ↔
      ∃ g : Lp F p (volume : Measure E), ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, Δ φ x • f x = ∫ x, φ x • g x := by
  rw [← StronglyContinuousSemigroup.generator_domain, LinearPMap.mem_domain_iff]
  exact exists_congr fun g => mem_graph_generator_heatSemigroup_iff hp

/-- **The test functions form a core of the heat generator on `Lᵖ`.** For `1 ≤ p < ∞`, the
classes of smooth compactly supported functions lie in the domain of the generator of the heat
semigroup on `Lᵖ(E; F)`, and the generator is the closure of its restriction to them. -/
theorem generator_heatSemigroup_hasCore_range_ambientToLp (hp : p ≠ ∞) :
    (heatSemigroup (E := E) (F := F) hp).generator.HasCore
      (LinearMap.range (TestFunction.ambientToLp (Ω := (⊤ : Opens E)) (n := ⊤) (F := F) p
        (volume : Measure E)).toLinearMap) := by
  have hle : testFunctionLp E F p ≤ (heatSemigroup (E := E) (F := F) hp).generator.domain := by
    rintro _ ⟨φ, rfl⟩
    rw [StronglyContinuousSemigroup.generator_domain]
    exact mem_domain_heatSemigroup hp (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
      (TestFunction.coeFn_ambientToLp φ)
  refine ((heatSemigroup hp).isClosed_generator.hasCore_iff_graph_subset_closure hle).2
    fun x hx => ?_
  exact mem_closure_testGraph_of_forall hp
    ((mem_graph_generator_heatSemigroup_iff hp).1 (by simpa using hx))

end TauCeti
