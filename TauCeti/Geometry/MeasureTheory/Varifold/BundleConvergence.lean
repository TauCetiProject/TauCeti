/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.Convergence
public import TauCeti.Geometry.MeasureTheory.Varifold.Restrict
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Varifold convergence on the Grassmann bundle

Let `E → B` be a real vector bundle of finite rank with continuous fibre norm, over a Hausdorff,
second-countable, locally compact base, for instance the tangent bundle of a Riemannian manifold,
and let `G_k(E) = TauCeti.grassmannBundle F E k` be its Grassmann bundle. Varifolds `V_j → V`
converge when `∫ f dV_j → ∫ f dV` for every compactly supported continuous `f` on `G_k(E)`
(`TauCeti.VarifoldTendsto`). This file specializes the theory of `TauCeti.VarifoldTendsto` on a
locally compact space to `G_k(E)`, through the proper projection `π : G_k(E) → B`.

## Main results

* `TauCeti.grassmannBundle.VarifoldTendsto.weight`: `V_j → V` implies `‖V_j‖ → ‖V‖` against
  compactly supported continuous functions on `B`.
* `TauCeti.grassmannBundle.VarifoldTendsto.limsup_weight_le`,
  `TauCeti.grassmannBundle.VarifoldTendsto.weight_le_liminf`: for compact `C` and open `O` in
  `B`, `lim sup ‖V_j‖(C) ≤ ‖V‖(C)` and `‖V‖(O) ≤ lim inf ‖V_j‖(O)`.
* `TauCeti.grassmannBundle.VarifoldTendsto.iSup_weight_ne_top`: a convergent sequence of varifolds
  has locally bounded mass, `sup_j ‖V_j‖(K) < ∞` for every compact `K ⊆ B`.
* `TauCeti.grassmannBundle.exists_subseq_varifoldTendsto`: **compactness**, every sequence of
  varifolds with `sup_j ‖V_j‖(K) < ∞` for each compact `K ⊆ B` has a subsequence converging to a
  varifold.
* `TauCeti.grassmannBundle.VarifoldTendsto.restrictOpens`: convergence commutes with restriction
  to an open `W ⊆ B`, and `TauCeti.grassmannBundle.varifoldTendsto_iff_forall_restrictOpens`:
  convergence is local, it holds exactly when it holds on every set of an open cover of `B`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Theorem 4.4 and §38.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Bundle Filter
open scoped ENNReal

namespace TauCeti.grassmannBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : ℕ}
  [FiniteDimensional ℝ F] [ContinuousFiberNorm F E]
  [T2Space B] [SecondCountableTopology B] [LocallyCompactSpace B] [MeasurableSpace B]
  [BorelSpace B]
  {V : ℕ → Measure (grassmannBundle F E k)} {V' : Measure (grassmannBundle F E k)}

omit [SecondCountableTopology B] in
/-- **Weights converge**: if varifolds `V_j → V`, then `‖V_j‖ → ‖V‖` against compactly supported
continuous functions on the base. -/
theorem VarifoldTendsto.weight (h : VarifoldTendsto V V') :
    VarifoldTendsto (fun n ↦ grassmannBundle.weight (V n)) (grassmannBundle.weight V') := by
  have hπ := (isProperMap_iff_tendsto_cocompact.1 (isProperMap_proj F E k)).2
  simpa [weight_def] using h.map ⟨⟨proj, continuous_proj⟩, hπ⟩

omit [SecondCountableTopology B] in
/-- **Locally bounded mass**: along a convergent sequence of varifolds, the weights of each compact
subset of the base are bounded uniformly in `n`. -/
theorem VarifoldTendsto.iSup_weight_ne_top [∀ n, IsFiniteMeasureOnCompacts (V n)]
    (h : VarifoldTendsto V V') {K : Set B} (hK : IsCompact K) :
    ⨆ n, grassmannBundle.weight (V n) K ≠ ∞ := by
  have : LocallyCompactSpace (grassmannBundle F E k) := inferInstance
  simp only [weight_apply hK.measurableSet]
  exact VarifoldTendsto.iSup_measure_ne_top h ((isProperMap_proj F E k).isCompact_preimage hK)

/-- **Upper semicontinuity of the weights on compact sets**: along a convergent sequence of
varifolds, `lim sup ‖V_j‖(C) ≤ ‖V‖(C)` for compact `C ⊆ B`. -/
theorem VarifoldTendsto.limsup_weight_le [∀ n, IsFiniteMeasureOnCompacts (V n)]
    [IsFiniteMeasureOnCompacts V'] (h : VarifoldTendsto V V') {C : Set B} (hC : IsCompact C) :
    limsup (fun n ↦ grassmannBundle.weight (V n) C) atTop ≤ grassmannBundle.weight V' C := by
  have : LocallyCompactSpace (grassmannBundle F E k) := inferInstance
  have : PseudoMetrizableSpace (grassmannBundle F E k) := inferInstance
  simp only [weight_apply hC.measurableSet]
  exact VarifoldTendsto.limsup_measure_le h ((isProperMap_proj F E k).isCompact_preimage hC)

/-- **Lower semicontinuity of the weights on open sets**: along a convergent sequence of
varifolds with limit a varifold, `‖V‖(O) ≤ lim inf ‖V_j‖(O)` for open `O ⊆ B`. -/
theorem VarifoldTendsto.weight_le_liminf [IsFiniteMeasureOnCompacts V']
    (h : VarifoldTendsto V V') {O : Set B} (hO : IsOpen O) :
    grassmannBundle.weight V' O ≤ liminf (fun n ↦ grassmannBundle.weight (V n) O) atTop := by
  have : LocallyCompactSpace (grassmannBundle F E k) := inferInstance
  have : PseudoMetrizableSpace (grassmannBundle F E k) := inferInstance
  simp only [weight_apply hO.measurableSet]
  exact VarifoldTendsto.le_liminf_measure h (hO.preimage (continuous_proj))

/-- **Compactness of varifolds.** A sequence of varifolds on `G_k(E)` whose weights are bounded on
each compact subset of the base, uniformly in `n`, has a subsequence converging to a varifold. -/
theorem exists_subseq_varifoldTendsto (V : ℕ → Measure (grassmannBundle F E k))
    (hV : ∀ K : Set B, IsCompact K → ⨆ n, grassmannBundle.weight (V n) K ≠ ∞) :
    ∃ (V' : Measure (grassmannBundle F E k)) (φ : ℕ → ℕ), IsFiniteMeasureOnCompacts V' ∧
      StrictMono φ ∧ VarifoldTendsto (V ∘ φ) V' := by
  have : LocallyCompactSpace (grassmannBundle F E k) := inferInstance
  have hS : ∀ C : Set (grassmannBundle F E k), IsCompact C → ⨆ ρ ∈ range V, ρ C ≠ ∞ := by
    intro C hC
    have hK := hC.image (continuous_proj)
    refine ne_top_of_le_ne_top (hV _ hK) ?_
    rw [iSup_range]
    refine iSup_mono fun n ↦ ?_
    rw [weight_apply hK.measurableSet]
    exact measure_mono (subset_preimage_image _ _)
  obtain ⟨V', φ, hV', hφ, -, hlim⟩ :=
    TauCeti.exists_subseq_varifoldTendsto V hS (.of_forall fun n ↦ mem_range_self n)
  exact ⟨V', φ, hV', hφ, hlim⟩

omit [SecondCountableTopology B] [LocallyCompactSpace B] [MeasurableSpace B]
  [BorelSpace B] in
/-- **Convergence commutes with restriction to open sets**: if varifolds `V_j → V` on `B`, then
their restrictions to an open `W ⊆ B` converge to the restriction of `V`. -/
theorem VarifoldTendsto.restrictOpens (h : VarifoldTendsto V V') {W : Set B} (hW : IsOpen W) :
    VarifoldTendsto (fun n ↦ grassmannBundle.restrictOpens W (V n))
      (grassmannBundle.restrictOpens W V') := by
  simpa only [restrictOpens_def] using
    TauCeti.VarifoldTendsto.comap h (isOpenEmbedding_inclusion W hW)

omit [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] in
/-- **Locality of convergence**: for an open cover `U` of the base, varifolds `V_j → V` on `B`
exactly when their restrictions converge on every `U i`. -/
theorem varifoldTendsto_iff_forall_restrictOpens [∀ n, IsFiniteMeasureOnCompacts (V n)]
    [IsFiniteMeasureOnCompacts V'] {ι : Type*} {U : ι → Set B} (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = univ) :
    VarifoldTendsto V V' ↔ ∀ i, VarifoldTendsto
      (fun n ↦ grassmannBundle.restrictOpens (U i) (V n))
      (grassmannBundle.restrictOpens (U i) V') := by
  have : LocallyCompactSpace (grassmannBundle F E k) := inferInstance
  simp only [restrictOpens_def]
  refine TauCeti.varifoldTendsto_iff_forall_comap (fun i ↦ isOpenEmbedding_inclusion (U i) (hU i))
    ?_
  simp only [range_inclusion, ← preimage_iUnion, hcover, preimage_univ]

end TauCeti.grassmannBundle
