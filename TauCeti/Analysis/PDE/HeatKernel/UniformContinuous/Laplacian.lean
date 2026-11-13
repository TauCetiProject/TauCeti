/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous.Core
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.Semigroups.Resolvent.Identity
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Integral.BoundedContinuousFunction
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# The heat generator on bounded uniformly continuous functions is the distributional Laplacian

Let `E` be a finite-dimensional real inner product space and `F` a real Banach space. The heat
semigroup `e^{tΔ}` acts on the Banach space `BUC(E; F)` of bounded uniformly continuous functions
(`TauCeti.heatSemigroupBUC`). This file determines the domain of its generator `A`: a function
`f ∈ BUC` lies in the domain exactly when its Laplacian in the sense of distributions is again a
function `g ∈ BUC`, that is

`∫ Δφ • f = ∫ φ • g` for every test function `φ ∈ C_c^∞(E)`,

and then `A f = g` (`TauCeti.mem_graph_generator_heatSemigroupBUC_iff`). So `A` is the maximal
realization of the Laplacian in `BUC`. Together with the smooth core of
`TauCeti.generator_heatSemigroupBUC_hasCore_smoothBoundedDerivativesSubmodule` this identifies the
generator completely.

## The argument

* **`A` is a restriction of the distributional Laplacian.** On the smooth functions with bounded
  derivatives of every order, which form a core, `A` is the classical Laplacian, and Green's
  identity `∫ Δφ • f = ∫ φ • Δf` holds. The pairs `(f, g)` satisfying `∫ Δφ • f = ∫ φ • g` for all
  `φ` form a closed subset of `BUC × BUC`, so the closure of the graph of the core, which is the
  graph of `A`, lies in it.
* **The distributional Laplacian has no eigenvalue `c > 0` in `BUC`.** If `Δw = c w` in the sense
  of distributions for a bounded continuous `w`, then each mollification `ρ ⋆ w` is smooth with
  bounded derivatives and satisfies `Δ(ρ ⋆ w) = c (ρ ⋆ w)` classically, so it lies in the domain of
  `A` with `A (ρ ⋆ w) = c (ρ ⋆ w)`. Since `c` is in the resolvent set of the generator of a
  contraction semigroup, `ρ ⋆ w = 0`, and letting `ρ` shrink to a point gives `w = 0`
  (`TauCeti.eq_zero_of_forall_integral_laplacian_smul_eq_smul`).
* **Equality.** If `∫ Δφ • f = ∫ φ • g`, let `h = (1 - A)⁻¹ (f - g)`. Then `w = f - h` satisfies
  `Δw = w` in the sense of distributions, so `w = 0`: `f = h` lies in the domain of `A` and
  `A f = g`.

## Main declarations

* `TauCeti.integral_laplacian_smul_eq_of_mem_graph_generator_heatSemigroupBUC`: the generator
  satisfies `∫ Δφ • f = ∫ φ • A f`.
* `TauCeti.eq_zero_of_forall_integral_laplacian_smul_eq_smul`: a bounded continuous solution of
  `Δw = c w`, `c > 0`, in the sense of distributions vanishes.
* `TauCeti.mem_graph_generator_heatSemigroupBUC_iff`: the graph of the generator is the graph of
  the distributional Laplacian in `BUC`.
* `TauCeti.mem_domain_heatSemigroupBUC_iff`: the domain of the generator.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup on `BUC`).
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Section 3.1.
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory
  Metric Semigroups Set TopologicalSpace Topology
open scoped ContDiff Convolution Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The pairs `(f, g)` of bounded uniformly continuous functions with `Δ f = g` in the sense of
distributions form a closed set. -/
private theorem isClosed_setOf_forall_integral_laplacian_smul_eq :
    IsClosed {p : uniformContinuousSubmodule ℝ E F × uniformContinuousSubmodule ℝ E F |
      ∀ φ : 𝓓(⊤, ℝ), ∫ x, Δ (φ : E → ℝ) x • p.1.val x = ∫ x, (φ : E → ℝ) x • p.2.val x} := by
  have H : LocallyIntegrableOn (fun _ : E ↦ (1 : ℝ)) (⊤ : Opens E) :=
    (locallyIntegrable_const 1).locallyIntegrableOn _
  simp only [ofPred_forall]
  exact isClosed_iInter fun φ ↦ isClosed_eq
    ((continuous_integral_smul_boundedContinuousFunction (φ.integrable_laplacian H)).comp
      (continuous_subtype_val.comp continuous_fst))
    ((continuous_integral_smul_boundedContinuousFunction (φ.integrable H)).comp
      (continuous_subtype_val.comp continuous_snd))

/-- **The heat generator is a restriction of the distributional Laplacian.** If `f` lies in the
domain of the generator `A` of the heat semigroup on `BUC` and `g = A f`, then
`∫ Δφ • f = ∫ φ • g` for every test function `φ`. -/
theorem integral_laplacian_smul_eq_of_mem_graph_generator_heatSemigroupBUC
    {f g : uniformContinuousSubmodule ℝ E F}
    (h : (f, g) ∈ (heatSemigroupBUC (E := E) (F := F)).generator.graph) (φ : 𝓓(⊤, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • f.val x = ∫ x, (φ : E → ℝ) x • g.val x := by
  refine LinearPMap.HasCore.graph_subset_of_isClosed
    generator_heatSemigroupBUC_hasCore_smoothBoundedDerivativesSubmodule
    isClosed_setOf_forall_integral_laplacian_smul_eq (fun ⟨a, b⟩ hp ψ ↦ ?_) h φ
  -- On the core the generator is the classical Laplacian, and Green's identity applies.
  obtain ⟨u, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp hp
  have hS : (u : uniformContinuousSubmodule ℝ E F) ∈ smoothBoundedDerivativesSubmodule ℝ E F :=
    u.property.1
  obtain ⟨hdom, hA⟩ := exists_generator_heatSemigroupBUC_eq_laplacian hS
  have hu : ((heatSemigroupBUC (E := E) (F := F)).generator.domRestrict
      (smoothBoundedDerivativesSubmodule ℝ E F) u) =
      (heatSemigroupBUC (E := E) (F := F)).generator ⟨u, by
        rw [StronglyContinuousSemigroup.generator_domain]; exact hdom⟩ :=
    LinearPMap.domRestrict_apply rfl
  dsimp only
  rw [hu, hA]
  exact ((mem_smoothBoundedDerivativesSubmodule ℝ E F _).mp hS).1.of_le (by simp)
    |>.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian ψ

/-- The test function `y ↦ ρ (x - y)` built from a smooth compactly supported `ρ`. -/
private def reflectTestFunction {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (x : E) : 𝓓((⊤ : Opens E), ℝ) :=
  ⟨fun y ↦ ρ (x - y), hρ.comp (contDiff_const.sub contDiff_id : ContDiff ℝ ∞ fun y : E ↦ x - y),
    hρc.comp_homeomorph (Homeomorph.subLeft x), by simp⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem coe_reflectTestFunction {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (x : E) :
    (reflectTestFunction hρ hρc x : E → ℝ) = fun y ↦ ρ (x - y) :=
  rfl

/-- **The distributional Laplacian has no positive eigenvalue on bounded continuous functions.**
If a bounded continuous `w` satisfies `Δw = c w` in the sense of distributions for some `c > 0`,
then `w = 0`. -/
theorem eq_zero_of_forall_integral_laplacian_smul_eq_smul {w : E →ᵇ F} {c : ℝ} (hc : 0 < c)
    (hw : ∀ φ : 𝓓(⊤, ℝ), ∫ x, Δ (φ : E → ℝ) x • w x = c • ∫ x, (φ : E → ℝ) x • w x) :
    w = 0 := by
  have hwl : LocallyIntegrable (w : E → F) volume :=
    w.continuous.locallyIntegrable
  -- Every mollification `ρ ⋆ w` vanishes.
  have hmoll : ∀ ρ : E → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      ρ ⋆[lsmul ℝ ℝ, volume] (w : E → F) = 0 := by
    intro ρ hρ hρc
    set v := ρ ⋆[lsmul ℝ ℝ, volume] (w : E → F) with hv_def
    have hvs : ContDiff ℝ ∞ v := hρc.contDiff_convolution_left (lsmul ℝ ℝ) hρ hwl
    have hvb : ∀ m : ℕ, ∀ x, ‖iteratedFDeriv ℝ m v x‖ ≤
        ‖w‖ * ∫ y, ‖iteratedFDeriv ℝ m ρ y‖ := fun m x ↦
      hρc.norm_iteratedFDeriv_convolution_left_le (hρ.of_le (by simp)) hwl w.norm_coe_le_norm x
    have hvu : UniformContinuous v :=
      (hρc.lipschitzWith_convolution_left (hρ.of_le (by simp)) hwl
        w.norm_coe_le_norm).uniformContinuous
    let vB : E →ᵇ F := .ofNormedAddCommGroup v hvs.continuous _ fun x ↦ by
      simpa only [norm_iteratedFDeriv_zero] using hvb 0 x
    let vU : uniformContinuousSubmodule ℝ E F := ⟨vB, (mem_uniformContinuousSubmodule vB).2 hvu⟩
    have hvU : vU ∈ smoothBoundedDerivativesSubmodule ℝ E F :=
      (mem_smoothBoundedDerivativesSubmodule ℝ E F vU).2 ⟨hvs, fun m ↦ ⟨_, hvb m⟩⟩
    -- Classically `Δ (ρ ⋆ w) = c (ρ ⋆ w)`: the Laplacian falls on `ρ`, and the distributional
    -- equation is tested against `y ↦ ρ (x - y)`.
    have hΔ : Δ v = c • v := by
      rw [hv_def, ← convolution_flip,
        hρc.laplacian_convolution_right _ hwl (hρ.of_le (by simp))]
      funext x
      have h := hw (reflectTestFunction hρ hρc x)
      have hΔρ : Δ (fun y ↦ ρ (x - y)) = fun y ↦ Δ ρ (x - y) :=
        laplacian_comp_affineIsometryEquiv_right (AffineIsometryEquiv.constVSub ℝ x) ρ
      simp only [coe_reflectTestFunction, hΔρ] at h
      simp only [convolution_def, flip_apply, lsmul_apply, Pi.smul_apply]
      exact h
    obtain ⟨hdom, hA⟩ := exists_generator_heatSemigroupBUC_eq_laplacian hvU
    have hAv : (heatSemigroupBUC (E := E) (F := F)).generator ⟨vU, by
        rw [StronglyContinuousSemigroup.generator_domain]; exact hdom⟩ = c • vU := by
      apply Subtype.ext
      apply BoundedContinuousFunction.ext
      intro x
      exact congrFun (hA.trans hΔ) x
    have h0 := LinearPMap.eq_zero_of_apply_eq_smul
      (heatSemigroupBUC.mem_resolventSet_generator hc) _ hAv
    funext x
    exact congrArg (fun u : uniformContinuousSubmodule ℝ E F ↦ u.val x)
      (congrArg Subtype.val h0)
  -- Shrinking the mollifier recovers `w`.
  ext x
  let φ : ℕ → ContDiffBump (0 : E) := fun n ↦
    ⟨1 / (n + 2), 1 / (n + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ w.continuous x
  simp only [hmoll _ (φ _).contDiff_normed (φ _).hasCompactSupport_normed, Pi.zero_apply] at hlim
  simpa using tendsto_nhds_unique hlim tendsto_const_nhds

/-- **The heat generator on `BUC` is the distributional Laplacian.** For bounded uniformly
continuous `f` and `g`, `f` lies in the domain of the generator `A` of the heat semigroup with
`A f = g` if and only if `Δ f = g` in the sense of distributions:
`∫ Δφ • f = ∫ φ • g` for every test function `φ`. -/
theorem mem_graph_generator_heatSemigroupBUC_iff {f g : uniformContinuousSubmodule ℝ E F} :
    (f, g) ∈ (heatSemigroupBUC (E := E) (F := F)).generator.graph ↔
      ∀ φ : 𝓓(⊤, ℝ), ∫ x, Δ (φ : E → ℝ) x • f.val x = ∫ x, (φ : E → ℝ) x • g.val x := by
  refine ⟨integral_laplacian_smul_eq_of_mem_graph_generator_heatSemigroupBUC, fun hfg ↦ ?_⟩
  set A := (heatSemigroupBUC (E := E) (F := F)).generator
  have h1 : (1 : ℝ) ∈ A.resolventSet := heatSemigroupBUC.mem_resolventSet_generator one_pos
  set h := A.resolvent 1 (f - g)
  have hh : h ∈ A.domain := LinearPMap.resolvent_mem_domain h1 _
  have hAh : A ⟨h, hh⟩ = h - (f - g) := by
    rw [LinearPMap.apply_resolvent h1, one_smul]
  have hh' := integral_laplacian_smul_eq_of_mem_graph_generator_heatSemigroupBUC
    (A.mem_graph ⟨h, hh⟩)
  -- Pairing with an integrable `ψ` is additive in the bounded continuous function.
  have integral_smul_sub {ψ : E → ℝ} (hψ : Integrable ψ) (u v : E →ᵇ F) :
      ∫ x, ψ x • (u - v) x = (∫ x, ψ x • u x) - ∫ x, ψ x • v x := by
    simp only [sub_apply, smul_sub]
    exact integral_sub (hψ.smul_boundedContinuousFunction u) (hψ.smul_boundedContinuousFunction v)
  -- `w = f - h` satisfies `Δw = w` in the sense of distributions.
  have hw : (f - h).val = 0 := by
    refine eq_zero_of_forall_integral_laplacian_smul_eq_smul one_pos fun φ ↦ ?_
    have H : LocallyIntegrableOn (fun _ : E ↦ (1 : ℝ)) (⊤ : Opens E) :=
      (locallyIntegrable_const 1).locallyIntegrableOn _
    have hφ : Integrable (φ : E → ℝ) := φ.integrable H
    rw [one_smul, Submodule.coe_sub, integral_smul_sub (φ.integrable_laplacian H),
      integral_smul_sub hφ, hfg φ, hh' φ, hAh, Submodule.coe_sub, Submodule.coe_sub,
      integral_smul_sub hφ, integral_smul_sub hφ]
    abel
  have hfh : f = h := sub_eq_zero.1 (Subtype.ext hw)
  refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨h, hh⟩, hfh.symm, ?_⟩
  rw [hAh, ← hfh, sub_sub_cancel]

/-- **The domain of the heat generator on `BUC`.** A bounded uniformly continuous `f` lies in the
domain of the generator of the heat semigroup if and only if its Laplacian in the sense of
distributions is a bounded uniformly continuous function. -/
theorem mem_domain_heatSemigroupBUC_iff {f : uniformContinuousSubmodule ℝ E F} :
    f ∈ (heatSemigroupBUC (E := E) (F := F)).domain ↔
      ∃ g : uniformContinuousSubmodule ℝ E F,
        ∀ φ : 𝓓(⊤, ℝ), ∫ x, Δ (φ : E → ℝ) x • f.val x = ∫ x, (φ : E → ℝ) x • g.val x := by
  rw [← StronglyContinuousSemigroup.generator_domain]
  refine ⟨fun hf ↦ ⟨_, mem_graph_generator_heatSemigroupBUC_iff.mp
    ((heatSemigroupBUC (E := E) (F := F)).generator.mem_graph ⟨f, hf⟩)⟩, fun ⟨g, hg⟩ ↦ ?_⟩
  exact LinearPMap.mem_domain_of_mem_graph (mem_graph_generator_heatSemigroupBUC_iff.mpr hg)

end TauCeti
