/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Right invariant Haar measures

On a second countable locally compact group whose left Haar measure `μ` is also right invariant,
every s-finite right invariant measure is a multiple of `μ`
(`MeasureTheory.Measure.exists_eq_smul_of_isMulRightInvariant`), and `μ` is invariant under
inversion (`MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant`). Mathlib's uniqueness
theorem for Haar measures on second countable groups (`MeasureTheory.Measure.haarMeasure_unique`)
asks for a σ-finite left invariant measure; the first statement weakens σ-finiteness to
s-finiteness and is about right invariant measures.

## References

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/Basic.lean`
(`New.exists_eq_smul_haar`, and the instance for `IsInvInvariant` of a right invariant Haar
measure).
-/

public section

open Set

open scoped ENNReal Pointwise

namespace MeasureTheory.Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- On a group with a right invariant left Haar measure `μ`, every s-finite right invariant measure
is `d • μ` for some `d ∈ [0, ∞]`. -/
theorem exists_eq_smul_of_isMulRightInvariant [SecondCountableTopology G] [μ.IsMulRightInvariant]
    {ν : Measure G} [SFinite ν] [ν.IsMulRightInvariant] : ∃ d : ℝ≥0∞, ν = d • μ := by
  -- Compare `ν.inv` with `(μ V)⁻¹ • μ` for a set `V` of finite positive measure, by
  -- `measure_mul_lintegral_eq`; right invariance of `μ` makes the weight there one.
  obtain ⟨V, hV_meas, -, hV_pos, hV_fin⟩ :
      ∃ V : Set G, MeasurableSet V ∧ V ⊆ univ ∧ 0 < μ V ∧ μ V < ∞ :=
    μ.exists_subset_measure_lt_top .univ (NeZero.pos _)
  refine ⟨ν.inv V * (μ V)⁻¹, Eq.symm (ext_of_lintegral _ fun f hf ↦ ?_)⟩
  have h_compare : ν.inv V * ∫⁻ y, f y ∂(μ V)⁻¹ • μ =
      ∫⁻ x, ((μ V)⁻¹ • μ) ((· * x) ⁻¹' V) * f x⁻¹ ∂ν.inv :=
    measure_mul_lintegral_eq ν.inv ((μ V)⁻¹ • μ) hV_meas f hf
  have h_weight (x : G) : ((μ V)⁻¹ • μ) ((· * x) ⁻¹' V) = 1 := by
    simp [measure_preimage_mul_right, ENNReal.inv_mul_cancel hV_pos.ne' hV_fin.ne]
  simpa [h_weight, mul_assoc, measurableEmbedding_inv.lintegral_map, inv_def] using h_compare

/-- A right invariant Haar measure is invariant under inversion. -/
theorem isInvInvariant_of_isMulRightInvariant [SecondCountableTopology G]
    [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  -- `μ.inv` and `μ` are left invariant, so both are multiples of the Haar measure normalised on
  -- `K = K₀ ∪ K₀⁻¹`; the factors agree because `K` is symmetric.
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  let K : TopologicalSpace.PositiveCompacts G := K₀ ⊔ K₀.map _ continuous_inv (isOpenMap_inv G)
  have h_mass : μ.inv K = μ K := by
    simp only [K, Measure.inv_apply]
    simp [inv_inv, union_comm]
  constructor
  calc μ.inv = μ.inv K • haarMeasure K := haarMeasure_unique _ K
    _ = μ K • haarMeasure K := by rw [h_mass]
    _ = μ := (haarMeasure_unique μ K).symm

end MeasureTheory.Measure
