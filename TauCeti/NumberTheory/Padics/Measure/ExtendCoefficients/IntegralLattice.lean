/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Integral lattices of measures

Extending coefficients from the closed unit ball of a field gives a weakly closed set of measures.
For `ℚ_p`-valued measures on a profinite space, a single power of `p` carries any measure into
this integral lattice.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Remark 3.28(1).
-/

public section

open scoped AbstractMeasure

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Extension from coefficients in the closed unit ball of a field has weakly closed range. -/
theorem isClosed_range_extendCoefficients_weak [T2Space X] [TotallyDisconnectedSpace X]
    {O K : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) :
    @IsClosed D(X, K) WeakTopology (extendCoefficients (X := X) j hj).range := by
  have hball : ((extendCoefficients (X := X) j hj).range : Set D(X, K)) =
      toCLMEquiv ⁻¹' Metric.closedBall 0 1 :=
    Set.ext fun _ ↦ (mem_range_extendCoefficients_iff hj hje hjr).trans
      mem_closedBall_zero_iff.symm
  rw [hball]
  apply isClosed_induced_iff'.2
  intro μ hμ
  apply ContinuousLinearMap.is_weak_closed_closedBall 0 1
  have hcoe (ν : D(X, K)) : ⇑(toCLMEquiv ν) = (fun f ↦ ν f) :=
    funext (coe_toCLMEquiv ν)
  rw [hcoe]
  refine closure_mono ?_ hμ
  rintro _ ⟨ν, hν, rfl⟩
  exact ⟨toCLMEquiv ν, hν, hcoe ν⟩

variable {p : ℕ} [Fact p.Prime] [T2Space X] [TotallyDisconnectedSpace X]

/-- Every bounded rational p-adic measure is an integral measure divided by a single power of
`p`. This power works simultaneously on all continuous test functions. -/
theorem exists_inv_pow_smul_extendCoefficients_eq (ν : D(X, ℚ_[p])) :
    ∃ (n : ℕ) (μ : D(X, ℤ_[p])),
      ((p : ℚ_[p]) ^ n)⁻¹ •
        extendCoefficients PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one μ = ν := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr
    (show 0 < 1 + ‖toCLMEquiv ν‖ by positivity)) (Padic.norm_p_lt_one (p := p))
  have hnν : ‖(p : ℚ_[p])‖ ^ n * ‖toCLMEquiv ν‖ ≤ 1 := by
    calc
      _ ≤ (1 + ‖toCLMEquiv ν‖)⁻¹ * (1 + ‖toCLMEquiv ν‖) :=
        mul_le_mul hn.le (le_add_of_nonneg_left zero_le_one) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hν : ‖toCLMEquiv ((p : ℚ_[p]) ^ n • ν)‖ ≤ 1 := by
    simpa only [map_smul, norm_smul, norm_pow] using hnν
  obtain ⟨μ, hμ⟩ := (mem_range_extendCoefficients_iff PadicInt.norm_coe_ringHom_le_one
    PadicInt.isEmbedding_coe_ringHom PadicInt.closedBall_subset_range_coe_ringHom).2 hν
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ⟨n, μ, by rw [hμ, inv_smul_smul₀ (pow_ne_zero n hp)]⟩

end AbstractMeasure
