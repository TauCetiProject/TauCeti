/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.Entropy
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Finite

/-!
# Entropically regularized finite Gromov–Wasserstein problems

Let `μ` and `ν` be probability vectors on finite types `ι` and `κ`, with kernels
`ωX : ι × ι → Z` and `ωY : κ × κ → Z` valued in a pseudometric space. A real transport plan is a
nonnegative array `f : ι × κ → ℝ` with row sums `μ` and column sums `ν`
(`TauCeti.RealPlans μ ν`). The finite Gromov–Wasserstein objective
`TauCeti.gromovWassersteinObjective p ωX ωY f` is the four-index sum

`∑ q, ∑ q', d(ωX (q.1, q'.1), ωY (q.2, q'.2)) ^ p * f q * f q'`,

and for `ε : ℝ` the entropically regularized objective adds `ε` times the relative entropy of `f`
against the product of the marginals:

`∑ q, ∑ q', d(ωX (q.1, q'.1), ωY (q.2, q'.2)) ^ p * f q * f q' + ε * KL(f ‖ μ ⊗ ν)`.

For `0 < p < ∞`, the objective of the real plan of a transport matrix is the `p`-th power of the
distortion of its coupling (`TauCeti.TransportMatrix.gromovWassersteinObjective_toRealFun`). So it
is the `p`-th power of the distortion that is regularized, and not the distortion itself. The
Gromov–Wasserstein distance is the infimum of these distortions over all admissible plans, not the
distortion of any single plan. At `p = 2` this is the quadratic objective of entropic
Gromov–Wasserstein. The relative entropy is written with `Matrix.relEntropy`; on real plans it is
the Kullback–Leibler divergence of the plan from `μ ⊗ ν`, and it equals `H(μ) + H(ν) - H(f)`, where
`H` is the Shannon entropy (`TauCeti.relEntropy_vecMulVec_eq_of_mem_realPlans`). So the
regularization `-ε H(f)` used by many sources differs from this one by the constant
`ε (H(μ) + H(ν))` on real plans, and has the same minimizers.

The regularized objective is continuous, so it attains its minimum on the compact set of real
plans. The relative entropy of a real plan lies between `0` and `H(μ) + H(ν)`, and this gives the
zero-temperature limit: as `ε → 0⁺`, the regularized optimal values converge to the unregularized
optimal value, and every cluster point of regularized minimizers minimizes the unregularized
objective. By `TauCeti.isMinOn_gromovWassersteinObjective_iff`, for `0 < p < ∞` those are exactly
the optimal couplings of the Gromov–Wasserstein problem `TauCeti.gromovWassersteinEDist`. The
objective is not convex in `f`, and nothing here concerns an algorithm for computing a minimizer.

## Main definitions

* `TauCeti.entropicGromovWassersteinObjective p ε μ ωX ν ωY f`: the entropically regularized
  finite Gromov–Wasserstein objective.

## Main results

* `TauCeti.entropicGromovWassersteinObjective_eq_of_mem_realPlans`: the comparison with the
  regularization `-ε H(f)`.
* `TauCeti.exists_isMinOn_entropicGromovWassersteinObjective`: existence of a global minimizer.
* `TauCeti.entropicGromovWassersteinObjective_le_of_isMinOn`: the regularized optimal value is at
  most the objective of any real plan plus `ε (H(μ) + H(ν))`.
* `TauCeti.tendsto_entropicGromovWassersteinObjective_of_isMinOn`: convergence of the optimal
  values as `ε → 0⁺`.
* `TauCeti.isMinOn_gromovWassersteinObjective_of_mapClusterPt` and
  `TauCeti.exists_isMinOn_gromovWassersteinObjective_tendsto_subseq`: cluster points of
  regularized minimizers are unregularized minimizers, and along a sequence of temperatures some
  subsequence converges to one.

## References

* G. Peyré, M. Cuturi and J. Solomon, *Gromov–Wasserstein averaging of kernel and distance
  matrices*, ICML 2016.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11
  (2019), §10.6.
-/

public section

noncomputable section

open Filter Topology MeasureTheory Real
open scoped ENNReal BigOperators

namespace TauCeti

variable {ι κ Z : Type*} [Fintype ι] [Fintype κ] [PseudoMetricSpace Z]
  {μ : PMF ι} {ν : PMF κ} {ωX : ι × ι → Z} {ωY : κ × κ → Z} {f g : ι × κ → ℝ} {p ε : ℝ}

/-! ### The objectives -/

/-- The entropically regularized finite Gromov–Wasserstein objective: the finite objective
`TauCeti.gromovWassersteinObjective p ωX ωY f` plus `ε` times the relative entropy of `f` against
the product `μ ⊗ ν` of the marginals. -/
def entropicGromovWassersteinObjective (p ε : ℝ) (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ)
    (ωY : κ × κ → Z) (f : ι × κ → ℝ) : ℝ :=
  gromovWassersteinObjective p ωX ωY f +
    ε * Matrix.relEntropy (Matrix.of fun i j ↦ f (i, j))
      (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal)

theorem entropicGromovWassersteinObjective_def (p ε : ℝ) (μ : PMF ι) (ωX : ι × ι → Z)
    (ν : PMF κ) (ωY : κ × κ → Z) (f : ι × κ → ℝ) :
    entropicGromovWassersteinObjective p ε μ ωX ν ωY f =
      gromovWassersteinObjective p ωX ωY f +
        ε * Matrix.relEntropy (Matrix.of fun i j ↦ f (i, j))
          (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal) :=
  (rfl)

/-- At `ε = 0` the regularized objective is the unregularized one. -/
@[simp]
theorem entropicGromovWassersteinObjective_zero (p : ℝ) (μ : PMF ι) (ωX : ι × ι → Z) (ν : PMF κ)
    (ωY : κ × κ → Z) :
    entropicGromovWassersteinObjective p 0 μ ωX ν ωY = gromovWassersteinObjective p ωX ωY := by
  ext f
  simp [entropicGromovWassersteinObjective_def]

theorem continuous_entropicGromovWassersteinObjective (p ε : ℝ) (μ : PMF ι) (ωX : ι × ι → Z)
    (ν : PMF κ) (ωY : κ × κ → Z) :
    Continuous (entropicGromovWassersteinObjective p ε μ ωX ν ωY) := by
  simp_rw [funext (entropicGromovWassersteinObjective_def p ε μ ωX ν ωY)]
  exact (continuous_gromovWassersteinObjective p ωX ωY).add (continuous_const.mul
    ((Matrix.continuous_relEntropy _).comp (by fun_prop)))

/-- On a real plan, the regularized objective is the unregularized one minus `ε` times the
Shannon entropy of the plan, up to the constant `ε (H(μ) + H(ν))`. This compares the convention
used here with the regularization `-ε H(f)`; the two have the same minimizers. -/
theorem entropicGromovWassersteinObjective_eq_of_mem_realPlans (hf : f ∈ RealPlans μ ν) :
    entropicGromovWassersteinObjective p ε μ ωX ν ωY f =
      gromovWassersteinObjective p ωX ωY f - ε * ∑ q, negMulLog (f q) +
        ε * (∑ i, negMulLog (μ i).toReal + ∑ j, negMulLog (ν j).toReal) := by
  rw [entropicGromovWassersteinObjective_def, relEntropy_vecMulVec_eq_of_mem_realPlans hf]
  ring

/-! ### Existence of minimizers -/

/-- The entropically regularized finite Gromov–Wasserstein objective has a global minimizer among
the real plans, for every `ε`. -/
theorem exists_isMinOn_entropicGromovWassersteinObjective (p ε : ℝ) (μ : PMF ι)
    (ωX : ι × ι → Z) (ν : PMF κ) (ωY : κ × κ → Z) :
    ∃ f ∈ RealPlans μ ν,
      IsMinOn (entropicGromovWassersteinObjective p ε μ ωX ν ωY) (RealPlans μ ν) f :=
  isCompact_realPlans.exists_isMinOn (realPlans_nonempty μ ν)
    (continuous_entropicGromovWassersteinObjective p ε μ ωX ν ωY).continuousOn

/-! ### The zero-temperature limit -/

/-- For `ε ≥ 0`, the regularized objective dominates the unregularized one on real plans. -/
theorem gromovWassersteinObjective_le_entropicGromovWassersteinObjective (hε : 0 ≤ ε)
    (hf : f ∈ RealPlans μ ν) :
    gromovWassersteinObjective p ωX ωY f ≤ entropicGromovWassersteinObjective p ε μ ωX ν ωY f :=
  le_add_of_nonneg_right (mul_nonneg hε (relEntropy_vecMulVec_nonneg_of_mem_realPlans hf))

/-- For `ε ≥ 0`, the regularized objective exceeds the unregularized one by at most
`ε (H(μ) + H(ν))` on real plans. -/
theorem entropicGromovWassersteinObjective_le_add (hε : 0 ≤ ε) (hf : f ∈ RealPlans μ ν) :
    entropicGromovWassersteinObjective p ε μ ωX ν ωY f ≤
      gromovWassersteinObjective p ωX ωY f +
        ε * (∑ i, negMulLog (μ i).toReal + ∑ j, negMulLog (ν j).toReal) :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (relEntropy_vecMulVec_le_of_mem_realPlans hf) hε)

/-- The regularized optimal value exceeds the objective of any real plan `g` by at most
`ε (H(μ) + H(ν))`. Taking for `g` an unregularized minimizer bounds the regularized optimal value
by the unregularized one plus `ε (H(μ) + H(ν))`. -/
theorem entropicGromovWassersteinObjective_le_of_isMinOn (hε : 0 ≤ ε)
    (hf : IsMinOn (entropicGromovWassersteinObjective p ε μ ωX ν ωY) (RealPlans μ ν) f)
    (hg : g ∈ RealPlans μ ν) :
    entropicGromovWassersteinObjective p ε μ ωX ν ωY f ≤
      gromovWassersteinObjective p ωX ωY g +
        ε * (∑ i, negMulLog (μ i).toReal + ∑ j, negMulLog (ν j).toReal) :=
  (isMinOn_iff.1 hf g hg).trans (entropicGromovWassersteinObjective_le_add hε hg)

variable {α : Type*} {l : Filter α} {e : α → ℝ} {F : α → ι × κ → ℝ}

/-- **Convergence of the optimal values** as `ε → 0⁺`. Let `F a` minimize the objective regularized
at `e a ≥ 0`, with `e a → 0`, and let `g` minimize the unregularized objective. Then both the
regularized optimal values and the unregularized objectives of the `F a` converge to the
unregularized optimal value. -/
theorem tendsto_entropicGromovWassersteinObjective_of_isMinOn (he0 : ∀ a, 0 ≤ e a)
    (he : Tendsto e l (𝓝 0)) (hF : ∀ a, F a ∈ RealPlans μ ν)
    (hFmin : ∀ a,
      IsMinOn (entropicGromovWassersteinObjective p (e a) μ ωX ν ωY) (RealPlans μ ν) (F a))
    (hg : g ∈ RealPlans μ ν)
    (hgmin : IsMinOn (gromovWassersteinObjective p ωX ωY) (RealPlans μ ν) g) :
    Tendsto (fun a ↦ entropicGromovWassersteinObjective p (e a) μ ωX ν ωY (F a)) l
        (𝓝 (gromovWassersteinObjective p ωX ωY g)) ∧
      Tendsto (fun a ↦ gromovWassersteinObjective p ωX ωY (F a)) l
        (𝓝 (gromovWassersteinObjective p ωX ωY g)) := by
  set M := ∑ i, negMulLog (μ i).toReal + ∑ j, negMulLog (ν j).toReal
  have hlow : ∀ a,
      gromovWassersteinObjective p ωX ωY g ≤ gromovWassersteinObjective p ωX ωY (F a) :=
    fun a ↦ isMinOn_iff.1 hgmin _ (hF a)
  have hmid : ∀ a, gromovWassersteinObjective p ωX ωY (F a) ≤
      entropicGromovWassersteinObjective p (e a) μ ωX ν ωY (F a) :=
    fun a ↦ gromovWassersteinObjective_le_entropicGromovWassersteinObjective (he0 a) (hF a)
  have hup : ∀ a, entropicGromovWassersteinObjective p (e a) μ ωX ν ωY (F a) ≤
      gromovWassersteinObjective p ωX ωY g + e a * M :=
    fun a ↦ entropicGromovWassersteinObjective_le_of_isMinOn (he0 a) (hFmin a) hg
  have hlim : Tendsto (fun a ↦ gromovWassersteinObjective p ωX ωY g + e a * M) l
      (𝓝 (gromovWassersteinObjective p ωX ωY g)) := by
    simpa using tendsto_const_nhds.add (he.mul_const M)
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun a ↦ (hlow a).trans (hmid a)) hup,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlow
      fun a ↦ (hmid a).trans (hup a)⟩

/-- **Cluster points of regularized minimizers** are unregularized minimizers. Let `F a` minimize
the objective regularized at `e a ≥ 0`, with `e a → 0`. Every cluster point `h` of `F` is a real
plan minimizing the unregularized objective. -/
theorem isMinOn_gromovWassersteinObjective_of_mapClusterPt (he0 : ∀ a, 0 ≤ e a)
    (he : Tendsto e l (𝓝 0)) (hF : ∀ a, F a ∈ RealPlans μ ν)
    (hFmin : ∀ a,
      IsMinOn (entropicGromovWassersteinObjective p (e a) μ ωX ν ωY) (RealPlans μ ν) (F a))
    {h : ι × κ → ℝ} (hh : MapClusterPt h l F) :
    h ∈ RealPlans μ ν ∧ IsMinOn (gromovWassersteinObjective p ωX ωY) (RealPlans μ ν) h := by
  have hmem : h ∈ RealPlans μ ν :=
    isCompact_realPlans.isClosed.mem_of_mapClusterPt hh (Eventually.of_forall hF)
  obtain ⟨g, hg, hgmin⟩ := exists_isMinOn_gromovWassersteinObjective p μ ωX ν ωY
  have hlim := (tendsto_entropicGromovWassersteinObjective_of_isMinOn he0 he hF hFmin hg hgmin).2
  -- The objective at `h` is a cluster value of a family converging to the optimal value.
  have hc : ClusterPt (gromovWassersteinObjective p ωX ωY h)
      (𝓝 (gromovWassersteinObjective p ωX ωY g)) :=
    (hh.continuousAt_comp
      (continuous_gromovWassersteinObjective p ωX ωY).continuousAt).clusterPt.mono hlim
  have heq : gromovWassersteinObjective p ωX ωY h = gromovWassersteinObjective p ωX ωY g := by
    by_contra hne
    exact hc.ne (disjoint_nhds_nhds.2 hne).eq_bot
  exact ⟨hmem, isMinOn_iff.2 fun x hx ↦ heq ▸ isMinOn_iff.1 hgmin x hx⟩

/-- Along a sequence of temperatures `e n → 0` with `e n ≥ 0`, every sequence of regularized
minimizers has a subsequence converging to a minimizer of the unregularized objective. -/
theorem exists_isMinOn_gromovWassersteinObjective_tendsto_subseq {e : ℕ → ℝ}
    {F : ℕ → ι × κ → ℝ} (he0 : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (hF : ∀ n, F n ∈ RealPlans μ ν)
    (hFmin : ∀ n,
      IsMinOn (entropicGromovWassersteinObjective p (e n) μ ωX ν ωY) (RealPlans μ ν) (F n)) :
    ∃ h ∈ RealPlans μ ν, IsMinOn (gromovWassersteinObjective p ωX ωY) (RealPlans μ ν) h ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 h) := by
  obtain ⟨h, hmem, φ, hφ, hlim⟩ := isCompact_realPlans.tendsto_subseq hF
  refine ⟨h, hmem, ?_, φ, hφ, hlim⟩
  exact (isMinOn_gromovWassersteinObjective_of_mapClusterPt (fun n ↦ he0 (φ n))
    (he.comp hφ.tendsto_atTop) (fun n ↦ hF (φ n)) (fun n ↦ hFmin (φ n)) hlim.mapClusterPt).2

end TauCeti
