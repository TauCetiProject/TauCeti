/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.SmoothDensity
public import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Analysis.Sobolev.SmoothCutoff

/-!
# Test functions are dense in whole-space higher-order Sobolev spaces

For `1 ≤ p < ∞`, test functions are dense in `W^{k,p}(E)` for every natural order `k`,
where `E` is a finite-dimensional real inner product space equipped with an additive Haar
measure. Thus `W^{k,p}_0(E) = W^{k,p}(E)` in the full iterated graph norm.

Smooth Sobolev representatives are already dense by mollification. Expanding smooth cutoffs
approximate each such representative simultaneously in every classical derivative through
order `k`. Identification with the recorded weak derivatives then upgrades this convergence to
the bundled Sobolev norm. No boundary regularity or boundedness assumption is needed because
this is a whole-space result; it does not assert test-function density on proper open domains.

The argument follows Evans, *Partial Differential Equations*, §5.3.1, using
`TauCeti.exists_contDiff_hasCompactSupport_approximation` and
`TauCeti.Wkp.dense_contDiff_representatives`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Simultaneous `Lᵖ` convergence of the classical derivatives of test functions through
order `k` implies convergence in the full `W^{k,p}` norm to a Sobolev representative that is
`C^k` on the domain. This implication works on any open domain, not only on the whole space. -/
theorem Wkp.tendsto_ofTestFunctionₗ_of_contDiffOn {I : Type*} {l : Filter I}
    (k : ℕ) (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) (phi : I → 𝓓(Omega, ℝ))
    (hphi : ∀ i ≤ k, Tendsto (fun j => eLpNorm
      (iteratedFDeriv ℝ i (phi j : E → ℝ) - iteratedFDeriv ℝ i f)
      p (mu.restrict Omega)) l (𝓝 0)) :
    Tendsto (fun j => ofTestFunctionₗ (mu := mu) (p := p) k (phi j)) l (𝓝 u) := by
  induction k with
  | zero =>
      -- At order zero the Sobolev space is `Lp`, so its convergence criterion applies directly.
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      convert hphi 0 le_rfl using 1
      funext j
      have hval : (ofTestFunctionₗ (mu := mu) (p := p) 0 (phi j) : E → ℝ)
          =ᵐ[mu.restrict Omega] (phi j : E → ℝ) := by
        have he := (value_zero (ofTestFunctionₗ (mu := mu) (p := p) 0 (phi j))).symm.trans
          (value_ofTestFunctionₗ (mu := mu) (p := p) 0 (phi j))
        rw [he]
        exact testFunctionLp_apply_ae (mu := mu) p (phi j)
      apply eLpNorm_congr_norm_ae
        ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
        (((phi j).contDiff.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable.sub
          ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen
            (by simp)).aestronglyMeasurable Omega.isOpen.measurableSet))
      filter_upwards [hval, hu, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hy hxO
      simp only [value_zero] at hy
      rw [Pi.sub_apply, hx, hy]
      exact (norm_iteratedFDeriv_zero (f := (phi j : E → ℝ) - f) (x := x)).symm.trans
        (congrArg norm (fun_iteratedFDeriv_sub_apply
          ((phi j).contDiff.of_le (by simp)).contDiffAt
          ((hf.of_le (by simp)).contDiffAt (Omega.isOpen.mem_nhds hxO))))
  | succ k ih =>
      -- The graph topology separates the preceding Sobolev order from the highest derivative.
      rw [tendsto_iff_lowerOrder_iteratedGradient]
      constructor
      · convert ih (lowerOrder k u) (hf.of_le (by simp)) (by simpa only [value_succ] using hu)
          (fun i hi => hphi i (hi.trans (Nat.le_succ k))) using 1
        funext j
        exact lowerOrder_ofTestFunctionₗ k (phi j)
      · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
        convert hphi (k + 1) le_rfl using 1
        funext j
        have hgrad : (iteratedGradient k u : E → IteratedGradient E k)
            =ᵐ[mu.restrict Omega] iteratedGradientChain f k :=
          iteratedGradient_ae_eq_of_contDiffOn k u hf hu
        have htest : (iteratedGradient k
            (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) (phi j)) :
              E → IteratedGradient E k) =ᵐ[mu.restrict Omega]
                iteratedGradientChain (phi j : E → ℝ) k := by
          rw [iteratedGradient_ofTestFunctionₗ]
          filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) p k (phi j)]
            with x hx
          exact hx.trans (congrFun (iteratedGradientTestFunction_def (phi j) k) x)
        apply eLpNorm_congr_norm_ae
          ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
          (((phi j).contDiff.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable.sub
            ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen
              (by simp)).aestronglyMeasurable Omega.isOpen.measurableSet))
        filter_upwards [htest, hgrad, ae_restrict_mem Omega.isOpen.measurableSet]
          with x hx hy hxO
        simp only [Pi.sub_apply, hx, hy]
        exact norm_iteratedGradientChain_sub k ((phi j).contDiff.of_le (by simp)).contDiffAt
          (hf.contDiffAt (Omega.isOpen.mem_nhds hxO))

/-- Every whole-space higher-order Sobolev function with a smooth representative belongs to
the closure of test functions in the full Sobolev norm, for finite `p`. -/
private theorem Wkp.mem_wkp0Submodule_top_of_contDiff (hp : p ≠ ⊤)
    (k : ℕ) (u : Wkp mu ⊤ p k) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict (⊤ : Opens E)] f) :
    u ∈ wkp0Submodule mu ⊤ p k := by
  obtain ⟨g, hg, _, hlim⟩ := exists_contDiff_hasCompactSupport_approximation
    (zero_lt_one.trans_le Fact.out).ne' hp hf k
      (memLp_iteratedFDeriv_of_contDiffOn k u (hf.of_le (by simp)).contDiffOn hu)
  let phi : ℕ → 𝓓((⊤ : Opens E), ℝ) := fun j =>
    ⟨g j, (hg j).1, (hg j).2, subset_univ _⟩
  have hconv : Tendsto (fun j => ofTestFunctionₗ (mu := mu) (p := p) k (phi j))
      atTop (𝓝 u) :=
    tendsto_ofTestFunctionₗ_of_contDiffOn k u (hf.of_le (by simp)).contDiffOn hu phi hlim
  exact (wkp0Submodule mu ⊤ p k).isClosed.mem_of_tendsto hconv
    (.of_forall fun j => ofTestFunctionₗ_mem_wkp0Submodule k (phi j))

/-- **`W^{k,p}_0(E) = W^{k,p}(E)`**, as an equality of closed subspaces of the whole-space
Sobolev space, for every natural order and `1 ≤ p < ∞`. -/
theorem wkp0Submodule_top_eq_top (hp : p ≠ ⊤) (k : ℕ) :
    wkp0Submodule mu ⊤ p k = ⊤ := by
  apply eq_top_iff.2
  intro u _
  have hsubset : {v : Wkp mu ⊤ p k | ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      (Wkp.value k v : E → ℝ) =ᵐ[mu.restrict (⊤ : Opens E)] f} ⊆
        (wkp0Submodule mu ⊤ p k : Set (Wkp mu ⊤ p k)) := by
    rintro v ⟨f, hf, hae⟩
    exact Wkp.mem_wkp0Submodule_top_of_contDiff hp k v hf hae
  have hclosure := closure_minimal hsubset (wkp0Submodule mu ⊤ p k).isClosed
  rw [(Wkp.dense_contDiff_representatives (mu := mu) hp k).closure_eq] at hclosure
  exact hclosure (mem_univ u)

/-- Test functions are dense in the full whole-space `W^{k,p}` norm for `1 ≤ p < ∞`. -/
theorem Wkp.denseRange_ofTestFunctionₗ_top (hp : p ≠ ⊤) (k : ℕ) :
    DenseRange (ofTestFunctionₗ (mu := mu) (Omega := ⊤) (p := p) k) := by
  intro u
  rw [← coe_wkp0Submodule, wkp0Submodule_top_eq_top hp]
  trivial

end TauCeti
