/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import Mathlib.Topology.Algebra.Module.LinearPMap
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

The first step removes the compact support. A function `u` of class `C²` whose derivatives
through order two lie in `Lᵖ` is in the domain of `A`, and `A u = Δu`: its expanding cutoffs
`χ (x / R) • u x` are `C²` with compact support, so the generator sends them to their
Laplacians, and as `R → ∞` they converge to `u` and their Laplacians to `Δu` in `Lᵖ`
(`TauCeti.tendsto_eLpNorm_iteratedFDeriv_cutoff_sub`, using `‖Δv‖ ≤ dim E ‖D²v‖`); since the
generator is closed, the limit lies in its graph. For smooth `u` the cutoffs are test functions,
so `(u, Δu)` lies in the closure of the graph of `A` restricted to test functions.

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

* `TauCeti.mem_domain_heatSemigroup_of_memLp_iteratedFDeriv` and
  `TauCeti.generator_heatSemigroup_of_memLp_iteratedFDeriv`: a `C²` function in `Lᵖ` whose
  first and second derivatives lie in `Lᵖ` is in the domain of the generator, which sends it to
  its Laplacian.
* `TauCeti.generator_heatSemigroup_hasCore_range_ambientToLp`: the test functions form a core for
  the generator of the heat semigroup on `Lᵖ`.
* `TauCeti.weakLaplacianLp_hasCore_range_ambientToLp`: equivalently, the distributional Laplacian
  on `Lᵖ` with domain `{f ∈ Lᵖ : Δf ∈ Lᵖ}` is the closure of the Laplacian on test functions.

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

omit [CompleteSpace F] [Fact (1 ≤ p)] in
/-- **Expanding cutoffs of a `C²` function converge with their Laplacians.** If `u` is `C²` and
its derivatives through order two lie in `Lᵖ`, then for a bump function `χ` the cutoffs
`χ ((n + 1)⁻¹ • x) • u x` converge to `u` in `Lᵖ`, and their Laplacians converge to `Δ u`. -/
private theorem tendsto_eLpNorm_cutoff_sub (hp : p ≠ ∞) (χ : ContDiffBump (0 : E)) {u : E → F}
    (hu : ContDiff ℝ 2 u) (hmem : ∀ i ≤ 2, MemLp (iteratedFDeriv ℝ i u) p volume) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => χ (((n : ℝ) + 1)⁻¹ • x) • u x - u x) p volume)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        eLpNorm (fun x => Δ (fun y => χ (((n : ℝ) + 1)⁻¹ • y) • u y) x - Δ u x) p volume)
        atTop (𝓝 0) := by
  choose B hB using fun i : ℕ =>
    (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (χ.hasCompactSupport.iteratedFDeriv i)
  have hr : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h0 := tendsto_eLpNorm_iteratedFDeriv_cutoff_sub hp hr (k := 0) χ.contDiff
    χ.eventuallyEq_one (fun i _ x => hB i x) (hu.of_le (by norm_num))
    (fun i hi => hmem i (hi.trans (by norm_num)))
  have h2 := tendsto_eLpNorm_iteratedFDeriv_cutoff_sub hp hr (k := 2) χ.contDiff
    χ.eventuallyEq_one (fun i _ x => hB i x) hu hmem
  have hcut (n : ℕ) : ContDiff ℝ 2 fun y => χ (((n : ℝ) + 1)⁻¹ • y) • u y :=
    (χ.contDiff.comp (contDiff_const_smul _)).smul hu
  refine ⟨h0.congr fun n => eLpNorm_congr_norm_ae
      (((hcut n).continuous_iteratedFDeriv (by norm_num)).sub
        (hu.continuous_iteratedFDeriv (by norm_num))).aestronglyMeasurable
      ((hcut n).continuous.sub hu.continuous).aestronglyMeasurable
      (ae_of_all _ fun x => ?_), ?_⟩
  · simp only [Pi.sub_apply, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
  · -- Pointwise `‖Δv‖ ≤ dim E ‖D²v‖` for the difference `v` of the cutoff and `u`.
    have hle (n : ℕ) :
        eLpNorm (fun x => Δ (fun y => χ (((n : ℝ) + 1)⁻¹ • y) • u y) x - Δ u x) p volume ≤
          ENNReal.ofReal (Module.finrank ℝ E) * eLpNorm (iteratedFDeriv ℝ 2
            (fun x => χ (((n : ℝ) + 1)⁻¹ • x) • u x) - iteratedFDeriv ℝ 2 u) p volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((hcut n).continuous_laplacian.sub hu.continuous_laplacian).aestronglyMeasurable
        (ae_of_all _ fun x => by
          have hc : ContDiff ℝ (2 : ℕ) fun y => χ (((n : ℝ) + 1)⁻¹ • y) • u y := hcut n
          have hu' : ContDiff ℝ (2 : ℕ) u := hu
          have h := norm_laplacian_le ((fun y => χ (((n : ℝ) + 1)⁻¹ • y) • u y) - u) x
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
            iteratedFDeriv_sub_apply hc.contDiffAt hu'.contDiffAt,
            (hcut n).contDiffAt.laplacian_sub hu.contDiffAt] at h
          simpa only [Pi.sub_apply] using h) p
    have h := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (Module.finrank ℝ E))
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hle

/-- An `Lᵖ` class represented by a `C²` function whose first and second derivatives lie in `Lᵖ`
lies in the domain of the heat generator, which sends it to the Laplacian: the limit of the
expanding cutoffs, whose Laplacians converge, lies in the graph of the closed generator. -/
private theorem exists_generator_heatSemigroup_ae_eq_laplacian (hp : p ≠ ∞) {u : E → F}
    (hu : ContDiff ℝ 2 u) (h₁ : MemLp (iteratedFDeriv ℝ 1 u) p volume)
    (h₂ : MemLp (iteratedFDeriv ℝ 2 u) p volume) {f : Lp F p (volume : Measure E)}
    (hf : f =ᵐ[volume] u) :
    ∃ h : f ∈ (heatSemigroup hp).generator.domain,
      ((heatSemigroup hp).generator ⟨f, h⟩ : E → F) =ᵐ[volume] Δ u := by
  set S := (heatSemigroup (E := E) (F := F) hp).toStronglyContinuousSemigroup
  have hmem : ∀ i ≤ 2, MemLp (iteratedFDeriv ℝ i u) p volume := by
    intro i hi
    interval_cases i
    · exact ((Lp.memLp f).ae_eq hf).of_le_mul (c := 1)
        (hu.continuous_iteratedFDeriv (by norm_num)).aestronglyMeasurable
        (ae_of_all _ fun x => by simp [norm_iteratedFDeriv_zero])
    · exact h₁
    · exact h₂
  -- `‖Δu‖ ≤ dim E ‖D²u‖`, so `Δu ∈ Lᵖ`.
  have hΔ : MemLp (Δ u) p volume := h₂.of_le_mul
    hu.continuous_laplacian.aestronglyMeasurable (ae_of_all _ fun x => by
      have h := norm_laplacian_le u x
      rwa [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at h)
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  set v : ℕ → E → F := fun n x => χ (((n : ℝ) + 1)⁻¹ • x) • u x
  have hv (n : ℕ) : ContDiff ℝ 2 (v n) := (χ.contDiff.comp (contDiff_const_smul _)).smul hu
  have hvc (n : ℕ) : HasCompactSupport (v n) :=
    (χ.hasCompactSupport.comp_smul (by positivity)).smul_right
  have hmemv (n : ℕ) : MemLp (v n) p volume :=
    (hv n).continuous.memLp_of_hasCompactSupport (hvc n)
  have hmemΔ (n : ℕ) : MemLp (Δ (v n)) p volume :=
    (hv n).continuous_laplacian.memLp_of_hasCompactSupport (hvc n).laplacian
  have hdom (n : ℕ) : (hmemv n).toLp _ ∈ S.generator.domain := by
    rw [S.generator_domain]
    exact mem_domain_heatSemigroup hp (hv n) (hvc n) (hmemv n).coeFn_toLp
  have hgen (n : ℕ) : S.generator ⟨_, hdom n⟩ = (hmemΔ n).toLp _ :=
    generator_heatSemigroup hp (hv n) (hvc n) (hmemv n).coeFn_toLp (hmemΔ n).coeFn_toLp
  obtain ⟨h0, h2⟩ := tendsto_eLpNorm_cutoff_sub hp χ hu hmem
  have hlim : Tendsto (fun n => (hmemv n).toLp _) atTop (𝓝 f) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine h0.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hmemv n).coeFn_toLp, hf] with x h₁ h₂
    rw [Pi.sub_apply, h₁, h₂]
  have hlimΔ : Tendsto (fun n => S.generator ⟨_, hdom n⟩) atTop (𝓝 (hΔ.toLp _)) := by
    simp_rw [hgen]
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine h2.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hmemΔ n).coeFn_toLp, hΔ.coeFn_toLp] with x h₁ h₂
    rw [Pi.sub_apply, h₁, h₂]
  obtain ⟨h, hAf⟩ := S.isClosed_generator.mem_domain_of_tendsto hdom hlim hlimΔ
  exact ⟨h, hAf ▸ hΔ.coeFn_toLp⟩

/-- **`C²` functions with derivatives in `Lᵖ` lie in the domain of the heat generator.** If `u` is
of class `C²` and represents an element `f` of `Lᵖ`, and its first and second derivatives lie in
`Lᵖ`, then `f` lies in the domain of the generator of the heat semigroup on `Lᵖ`. No compact
support is needed. -/
theorem mem_domain_heatSemigroup_of_memLp_iteratedFDeriv (hp : p ≠ ∞) {u : E → F}
    (hu : ContDiff ℝ 2 u) (h₁ : MemLp (iteratedFDeriv ℝ 1 u) p volume)
    (h₂ : MemLp (iteratedFDeriv ℝ 2 u) p volume) {f : Lp F p (volume : Measure E)}
    (hf : f =ᵐ[volume] u) :
    f ∈ (heatSemigroup hp).domain := by
  obtain ⟨h, -⟩ := exists_generator_heatSemigroup_ae_eq_laplacian hp hu h₁ h₂ hf
  rwa [StronglyContinuousSemigroup.generator_domain] at h

/-- **The heat generator on `C²` functions with derivatives in `Lᵖ`.** If `u` is of class `C²`,
its first and second derivatives lie in `Lᵖ`, and `f, g ∈ Lᵖ` are the classes of `u` and `Δ u`,
then the generator of the heat semigroup sends `f` to `g`. -/
theorem generator_heatSemigroup_of_memLp_iteratedFDeriv (hp : p ≠ ∞) {u : E → F}
    (hu : ContDiff ℝ 2 u) (h₁ : MemLp (iteratedFDeriv ℝ 1 u) p volume)
    (h₂ : MemLp (iteratedFDeriv ℝ 2 u) p volume) {f g : Lp F p (volume : Measure E)}
    (hf : f =ᵐ[volume] u) (hg : g =ᵐ[volume] Δ u) :
    (heatSemigroup hp).generator ⟨f, by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact mem_domain_heatSemigroup_of_memLp_iteratedFDeriv hp hu h₁ h₂ hf⟩ = g :=
  Lp.ext ((exists_generator_heatSemigroup_ae_eq_laplacian hp hu h₁ h₂ hf).2.trans hg.symm)

/-- The classes of test functions lie in the domain of the heat generator. -/
private theorem range_ambientToLp_le_domain_generator_heatSemigroup (hp : p ≠ ∞) :
    LinearMap.range (TestFunction.ambientToLp p (volume : Measure E) :
      𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap ≤
        (heatSemigroup hp).generator.domain := by
  rintro _ ⟨φ, rfl⟩
  rw [StronglyContinuousSemigroup.generator_domain]
  exact mem_domain_heatSemigroup hp (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    (TestFunction.coeFn_ambientToLp φ)

/-- If an element `f` of the domain of the heat generator is represented by a smooth function `u`
whose derivatives through order two lie in `Lᵖ`, then `(f, A f)` is a limit of points of the graph
of the generator restricted to test functions: the expanding cutoffs of `u`. -/
private theorem mem_closure_graph_domRestrict_range_ambientToLp (hp : p ≠ ∞)
    (f : (heatSemigroup (E := E) (F := F) hp).generator.domain) {u : E → F}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hmem : ∀ i ≤ 2, MemLp (iteratedFDeriv ℝ i u) p volume)
    (hf : (f : Lp F p (volume : Measure E)) =ᵐ[volume] u) :
    ((f : Lp F p (volume : Measure E)), (heatSemigroup hp).generator f) ∈
      closure (SetLike.coe ((heatSemigroup hp).generator.domRestrict
        (LinearMap.range (TestFunction.ambientToLp p (volume : Measure E) :
          𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap)).graph) := by
  have hD := range_ambientToLp_le_domain_generator_heatSemigroup (E := E) (F := F) hp
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ (n : ℕ) : 𝓓((⊤ : Opens E), F) :=
    ⟨fun x => χ (((n : ℝ) + 1)⁻¹ • x) • u x, (χ.contDiff.comp (contDiff_const_smul _)).smul hu,
      (χ.hasCompactSupport.comp_smul (by positivity)).smul_right, by simp⟩
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by simp)
  have hAf : ((heatSemigroup hp).generator f : E → F) =ᵐ[volume] Δ u :=
    (exists_generator_heatSemigroup_ae_eq_laplacian hp hu2 (hmem 1 (by norm_num))
      (hmem 2 le_rfl) hf).2
  have hφ (n : ℕ) : ContDiff ℝ 2 (φ n) := (φ n).contDiff.of_le (by simp)
  have hΔφ (n : ℕ) : MemLp (Δ (φ n : E → F)) p volume :=
    (hφ n).continuous_laplacian.memLp_of_hasCompactSupport (φ n).hasCompactSupport.laplacian
  have hgen (n : ℕ) : (heatSemigroup hp).generator ⟨_, hD ⟨φ n, rfl⟩⟩ = (hΔφ n).toLp _ :=
    generator_heatSemigroup hp (hφ n) (φ n).hasCompactSupport
      (TestFunction.coeFn_ambientToLp (φ n)) (hΔφ n).coeFn_toLp
  obtain ⟨h0, h2⟩ := tendsto_eLpNorm_cutoff_sub hp χ hu2 hmem
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => (TestFunction.ambientToLp p volume
      (φ n), (heatSemigroup hp).generator ⟨_, hD ⟨φ n, rfl⟩⟩)) (Tendsto.prodMk_nhds ?_ ?_)
    (Eventually.of_forall fun n => (LinearPMap.mem_graph_iff' _).mpr
      ⟨⟨_, ⟨φ n, rfl⟩, hD ⟨φ n, rfl⟩⟩, Prod.ext rfl (LinearPMap.domRestrict_apply rfl)⟩)
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine h0.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [TestFunction.coeFn_ambientToLp (p := p) (ν := volume) (φ n), hf]
      with x h₁ h₂
    rw [Pi.sub_apply, h₁, h₂]
    rfl
  · simp_rw [hgen]
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine h2.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hΔφ n).coeFn_toLp, hAf] with x h₁ h₂
    rw [Pi.sub_apply, h₁, h₂]
    rfl

/-- **Test functions form a core for the heat generator on `Lᵖ`.** For `1 ≤ p < ∞`, the classes
of the test functions `C_c^∞(E; F)` lie in the domain of the generator of the heat semigroup on
`Lᵖ(E; F)`, and the closure of its restriction to them is the whole generator. -/
theorem generator_heatSemigroup_hasCore_range_ambientToLp (hp : p ≠ ∞) :
    (heatSemigroup (E := E) (F := F) hp).generator.HasCore
      (LinearMap.range (TestFunction.ambientToLp p (volume : Measure E) :
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
    exact f.2
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
      (LinearMap.range (TestFunction.ambientToLp p (volume : Measure E) :
        𝓓((⊤ : Opens E), F) →L[ℝ] Lp F p (volume : Measure E)).toLinearMap) := by
  rw [← generator_heatSemigroup_eq_weakLaplacianLp hp]
  exact generator_heatSemigroup_hasCore_range_ambientToLp hp

end TauCeti
