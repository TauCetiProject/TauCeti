/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Topology.ContinuousMap.Ascoli
public import TauCeti.Analysis.Calculus.Equicontinuity

/-!
# Smooth subsequences from local derivative bounds

For a sequence of smooth maps between finite-dimensional real normed spaces, eventual
bounds on every derivative on every compact subset of an open domain give one strictly
increasing subsequence converging there in all derivatives. The limit is smooth, and its
canonical iterated derivatives are the limits. The bounds and their eventual thresholds
may depend on the compact set and derivative order.

This is the local analytic extraction used for coordinate metrics in pointed smooth
compactness. No geometric atlas, curvature estimate or geometric limit is constructed here.

## Main results

* `TauCeti.exists_strictMono_tendstoUniformlyOn_iteratedFDeriv`: simultaneous convergence
  of every derivative to those of one smooth limit on every compact subset.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 5.6 and
  Proposition 5.14.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter Set Metric
open scoped ContDiff Topology

namespace TauCeti

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [FiniteDimensional ℝ X] in
/-- Smoothness bounds the finitely many terms preceding an eventual uniform
bound, giving an all-index bound on every compact subset. -/
private theorem norm_iteratedFDeriv_le_on_compact
    {Ω : Set X}
    (hΩ : IsOpen Ω) (f : ℕ → X → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B)
    {K : Set X} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K →
      ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B := by
  classical
  have hc (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ m (f j)) K := by
    intro x hx
    exact ((hf j x (hKΩ hx)).contDiffAt (hΩ.mem_nhds (hKΩ hx))).continuousAt_iteratedFDeriv
      (by simp) |>.continuousWithinAt
  choose b hb using fun j ↦ hK.exists_bound_of_continuousOn (hc j)
  obtain ⟨B, hB⟩ := hbound K hK hKΩ m
  obtain ⟨N, hN⟩ := eventually_atTop.1 hB
  let C := ∑ j ∈ Finset.range N, max (b j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ ↦ le_max_right _ _
  refine ⟨max B 0 + C, add_nonneg (le_max_right _ _) hC, ?_⟩
  intro j x hx
  by_cases hj : N ≤ j
  · exact (hN j hj x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right hC))
  · have hbj : max (b j) 0 ≤ C :=
      Finset.single_le_sum (fun i _ ↦ le_max_right (b i) 0)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hj))
    exact (hb j x hx).trans ((le_max_left _ _).trans
      (hbj.trans (le_add_of_nonneg_left (le_max_right _ _))))

private theorem equicontinuous_iteratedFDeriv
    {Ω : Set X} (hΩ : IsOpen Ω) (f : ℕ → X → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B) (m : ℕ) :
    Equicontinuous (fun j (x : Ω) ↦ iteratedFDeriv ℝ m (f j) x) := by
  apply (equicontinuous_restrict_iff (fun j ↦ iteratedFDeriv ℝ m (f j))).mpr
  apply equicontinuousOn_of_forall_isCompact_norm_fderiv_le hΩ
  · intro j x hx
    exact ((hf j x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
      |>.differentiableWithinAt
  · intro K hK hKΩ
    obtain ⟨B, _, hB⟩ := norm_iteratedFDeriv_le_on_compact hΩ f hf hbound hK hKΩ (m + 1)
    exact ⟨B, fun j x hx ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hB j x hx⟩

private theorem exists_locallyUniform_jet_limits
    [FiniteDimensional ℝ E]
    {Ω : Set X}
    (hΩ : IsOpen Ω) (f : ℕ → X → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : (m : ℕ) → X → X [×m]→L[ℝ] E,
        ∀ m, TendstoLocallyUniformlyOn
          (fun j ↦ iteratedFDeriv ℝ m (f (σ j))) (g m) atTop Ω := by
  classical
  let J := fun m : ℕ ↦ X [×m]→L[ℝ] E
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have : ∀ m, FiniteDimensional ℝ (J m) := by
    intro m
    induction m with
    | zero => exact (continuousMultilinearCurryFin0 ℝ X E).symm.toLinearEquiv.finiteDimensional
    | succ m ih => exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) ↦ X) E).symm.toLinearEquiv.finiteDimensional
  let u : ∀ m, ℕ → C(Ω, J m) := fun m j ↦
    ⟨fun x ↦ iteratedFDeriv ℝ m (f j) x,
      (equicontinuous_iteratedFDeriv hΩ f hf hbound m).continuous j⟩
  have hc (m : ℕ) : IsCompact (closure (range (u m))) := by
    apply ArzelaAscoli.isCompact_closure_range_of_equicontinuous
      (equicontinuous_iteratedFDeriv hΩ f hf hbound m)
    intro x
    obtain ⟨B, _, hboundB⟩ := norm_iteratedFDeriv_le_on_compact hΩ f hf hbound
      (isCompact_singleton (x := (x : X))) (singleton_subset_iff.mpr x.property) m
    refine ⟨closedBall (0 : J m) B, isCompact_closedBall _ _, fun j ↦ ?_⟩
    simpa only [mem_closedBall, dist_zero_right, u, ContinuousMap.coe_mk] using
      hboundB j x (mem_singleton _)
  have : SigmaCompactSpace Ω := inferInstance
  have : ∀ m, FirstCountableTopology C(Ω, J m) := fun m ↦ by
    have : Filter.IsCountablyGenerated (uniformity C(Ω, J m)) := inferInstance
    exact UniformSpace.firstCountableTopology C(Ω, J m)
  obtain ⟨a, _, σ, hσ, hlim⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (fun j m ↦ subset_closure (mem_range_self j))
  have hlim' := tendsto_pi_nhds.mp hlim
  let g : ∀ m, X → J m := fun m x ↦ if hx : x ∈ Ω then a m ⟨x, hx⟩ else 0
  refine ⟨σ, hσ, g, fun m ↦ ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have hg : g m ∘ Subtype.val = (a m : Ω → J m) := by
    funext x
    simp only [g, Function.comp_apply, dite_eq_left x.property]
  rw [hg]
  simpa only [u, Function.comp_apply, ContinuousMap.coe_mk] using
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hlim' m))

/-- Eventual compact bounds for all derivatives of a sequence of smooth maps give a single
strictly increasing subsequence converging to one smooth map in all derivatives on compact sets.
Both the domain and target may be arbitrary finite-dimensional real normed spaces. -/
theorem exists_strictMono_tendstoUniformlyOn_iteratedFDeriv [FiniteDimensional ℝ E]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : ℕ → X → E}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : X → E, ContDiffOn ℝ ∞ g Ω ∧
      ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun j ↦ iteratedFDeriv ℝ m (f (σ j))) (iteratedFDeriv ℝ m g) atTop K := by
  obtain ⟨σ, hσ, jets, hjets⟩ := exists_locallyUniform_jet_limits hΩ f hf hbound
  obtain ⟨g, hg, heq⟩ := exists_smooth_of_locallyUniform_jet_limits hΩ
    (fun j ↦ f (σ j)) (fun j ↦ hf (σ j)) jets hjets
  refine ⟨σ, hσ, g, hg, fun m K hK hKΩ ↦ ?_⟩
  have hconv := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp (hjets m) K hKΩ hK
  exact hconv.congr_right (fun x hx ↦ (heq m (hKΩ hx)).symm)

end TauCeti
