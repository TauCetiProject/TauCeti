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

Let `X` be a profinite space and let `j : O →+* K` be a topological embedding onto the closed
unit ball of a complete ultrametric normed field. Extending coefficients along `j` gives a weakly
closed set of `K`-valued measures. For `ℚ_p`-valued measures, a single power of `p` carries the
whole measure into this integral lattice. After scaling, its values on all continuous
`ℤ_p`-valued test functions are integral.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Remark 3.28(1).
-/

public section

open scoped AbstractMeasure

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- On a profinite space, extension along a topological embedding onto the closed unit ball of a
complete ultrametric normed field has weakly closed range. -/
theorem isClosed_range_extendCoefficients_weak [T2Space X] [TotallyDisconnectedSpace X]
    {O K : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) :
    @IsClosed D(X, K) WeakTopology (extendCoefficients (X := X) j hj).range := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with hK | ⟨_, rfl⟩
  · let := hK
    have hsurj : Function.Surjective j := fun k ↦ hjr (by simp)
    rw [AddMonoidHom.coe_range,
      Set.range_eq_univ.mpr (extendCoefficients_surjective j hj hje hsurj)]
    exact @isClosed_univ _ WeakTopology
  · have hball : ((extendCoefficients (X := X) j hj).range : Set D(X, K)) =
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

/-- A single power of `p` puts the whole bounded rational p-adic measure in the image of
extension of coefficients from `ℤ_p`. After scaling, its values on all continuous `ℤ_p`-valued
test functions are integral. -/
theorem exists_inv_pow_smul_extendCoefficients_eq (ν : D(X, ℚ_[p])) :
    ∃ (n : ℕ) (μ : D(X, ℤ_[p])),
      ((p : ℚ_[p]) ^ n)⁻¹ •
        extendCoefficients PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one μ = ν := by
  have hpos : 0 < 1 + ‖toCLMEquiv ν‖ := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) (Padic.norm_p_lt_one (p := p))
  have hnν : ‖(p : ℚ_[p])‖ ^ n * ‖toCLMEquiv ν‖ ≤ 1 := by
    calc
      _ ≤ (1 + ‖toCLMEquiv ν‖)⁻¹ * (1 + ‖toCLMEquiv ν‖) :=
        mul_le_mul hn.le (le_add_of_nonneg_left zero_le_one) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hν : ‖toCLMEquiv ((p : ℚ_[p]) ^ n • ν)‖ ≤ 1 := by
    simpa only [map_smul, norm_smul, norm_pow] using hnν
  obtain ⟨μ, hμ⟩ := (mem_range_extendCoefficients_iff PadicInt.norm_coe_ringHom_le_one
    PadicInt.isEmbedding_coe_ringHom PadicInt.closedBall_subset_range_coe_ringHom).2 hν
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ⟨n, μ, by rw [hμ, inv_smul_smul₀ (pow_ne_zero n hp)]⟩

end AbstractMeasure
