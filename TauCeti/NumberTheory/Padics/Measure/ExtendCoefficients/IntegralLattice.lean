/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic

/-!
# Integral lattices of measures

Let `X` be a profinite space and let `j : O →+* K` be a bounded topological embedding with closed
image in a complete ultrametric normed commutative ring. Extending coefficients along `j` gives a
weakly closed set of `K`-valued measures. For `ℚ_p`-valued measures, a single power of `p` carries
the whole measure into this integral lattice. After scaling, its values on all continuous
`ℤ_p`-valued test functions are integral.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Remark 3.28(1).
-/

public section

open scoped AbstractMeasure

namespace RingHom

open AbstractMeasure

/-- On a profinite space, extension along a bounded coefficient embedding with closed image has
weakly closed range. -/
theorem isClosed_range_extendCoefficients_weak
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {O K : Type*}
    [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K]
    (j : O →+* K) {B : ℝ} (hj : ∀ a, ‖j a‖ ≤ B) (hje : Topology.IsEmbedding j)
    (hjr : IsClosed (Set.range j)) :
    @IsClosed D(X, K) WeakTopology (extendCoefficients (X := X) j hj).range := by
  have hrange : ((extendCoefficients (X := X) j hj).range : Set D(X, K)) =
      ⋂ f : C(X, O), {ν | ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) ∈ Set.range j} := by
    ext ν
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨μ, rfl⟩ f
      exact ⟨μ f, (extendCoefficients_apply_comp j μ hj hje.continuous f).symm⟩
    · intro hν
      obtain ⟨μ, hμ⟩ := j.exists_apply_comp_eq_of_mem_range hje ν hν
      exact ⟨μ, (eq_extendCoefficients_of_apply_comp j μ hj hje.continuous hμ).symm⟩
  rw [hrange]
  let : TopologicalSpace D(X, K) := WeakTopology
  have heval : Continuous (fun μ : D(X, K) ↦ fun f : C(X, K) ↦ μ f) :=
    continuous_induced_dom
  exact isClosed_iInter fun f ↦ hjr.preimage
    ((continuous_apply ((⟨j, hje.continuous⟩ : C(O, K)).comp f)).comp heval)

end RingHom

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

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
