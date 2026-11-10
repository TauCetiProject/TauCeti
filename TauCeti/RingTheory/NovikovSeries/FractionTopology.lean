/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import TauCeti.RingTheory.NovikovSeries.Valuation

/-!
# The period topology on fraction fields of Novikov rings

Equip a fraction field of a domain Novikov ring with the extended period valuation,
using Mathlib's `WithVal` carrier. The group-ring domain hypothesis allows tied leading
coefficients and does not require an injective or discrete period map.

The coefficient-preserving inclusion of Novikov series is a uniform embedding for
its existing period topology. Since the series ring is complete, its image in the
valued fraction field is closed. This does not assert completeness of the fraction
field. The zero period map is included: both induced topologies are discrete.

The neighbourhood comparison supplies the topology in which high-period changes of
denominators, and later of based torsion minors, become small. Ring operations and
inversion away from zero on the fraction field use the native valued-field API.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*,
  Forum Math. 14 (2002), Definition 2.6 and Lemma 2.8.
-/

public section

noncomputable section

open Filter Topology Uniformity
open MonoidWithZeroHom.ValueGroup₀

namespace TauCeti.NovikovSeries

variable {R H : Type*} [CommRing R] [Nontrivial R] [AddCommGroup H]
  [NoZeroDivisors (AddMonoidAlgebra R H)] (N : H →+ ℝ)

section Ring

variable (F : Type*) [CommRing F] [Algebra (NovikovSeries R H N) F]
  [IsFractionRing (NovikovSeries R H N) F]

/-- The valued-ring inclusion retains the intrinsic period valuation of each series. -/
@[simp]
theorem valued_algebraMap_fractionValuation (a : NovikovSeries R H N) :
    Valued.v (algebraMap (NovikovSeries R H N) (WithVal (fractionValuation R N F)) a) =
      periodValuation N a := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal, fractionValuation_algebraMap]

/-- Closed balls for the fraction valuation pull back to the original period filtration. -/
theorem valued_algebraMap_fractionValuation_le_iff (a : NovikovSeries R H N) (C : ℝ) :
    Valued.v (algebraMap (NovikovSeries R H N) (WithVal (fractionValuation R N F)) a) ≤
      ↑(Multiplicative.ofAdd (-C)) ↔ a ∈ periodFiltration R N C := by
  rw [valued_algebraMap_fractionValuation, periodValuation_le_iff]

/-- The fraction-field valuation topology induces exactly the period uniformity on series. -/
theorem isUniformEmbedding_algebraMap_fractionValuation :
    IsUniformEmbedding (algebraMap (NovikovSeries R H N)
      (WithVal (fractionValuation R N F))) := by
  let v := (Valued.v : Valuation (WithVal (fractionValuation R N F))
    (WithZero (Multiplicative ℝ)))
  apply IsUniformInducing.isUniformEmbedding
  apply (hasBasis_uniformity.isUniformInducing_iff
    (Valued.hasBasis_uniformity (WithVal (fractionValuation R N F)) _)).2
  constructor
  -- Each value-group radius contains a closed period ball with a slightly larger cutoff.
  · intro γ _
    have hγ : embedding (γ : v.ValueGroup₀) ≠ 0 := by simp
    obtain ⟨r, hr⟩ := WithZero.ne_zero_iff_exists.1 hγ
    refine ⟨-Multiplicative.toAdd r + 1, trivial, fun a b hab => ?_⟩
    rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, ← map_sub,
      valued_algebraMap_fractionValuation, ← hr]
    apply ((periodValuation_le_iff N _ _).2 hab).trans_lt
    rw [WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt]
    simp only [toAdd_ofAdd]
    linarith
  · intro C _
    -- For the zero period map, the open unit ball pulls back to zero.
    by_cases hN : N = 0
    · refine ⟨1, trivial, fun a b hab => ?_⟩
      have hlt : periodValuation N (b - a) < 1 := by
        simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_one_iff,
          ← map_sub, valued_algebraMap_fractionValuation] using hab
      have hz : b - a = 0 := by
        by_contra hn
        obtain ⟨h, _, hh⟩ := (isLeast_order hn).1
        have ho : (b - a).order = 0 := by simpa [hN] using hh.symm
        simp [periodValuation_apply_of_ne_zero N hn, ho] at hlt
      exact (periodValuation_le_iff N (b - a) C).1 (by simp [hz])
    -- Otherwise powers of a positive-period monomial give arbitrarily small radii.
    · obtain ⟨g, hg⟩ : ∃ g, 0 < N g := by
        obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hN
        simp only [AddMonoidHom.zero_apply] at hg
        rcases hg.lt_or_gt with hg | hg
        · exact ⟨-g, by simpa using hg⟩
        · exact ⟨g, hg⟩
      obtain ⟨n, hn⟩ := exists_lt_nsmul hg C
      let s := algebraMap (NovikovSeries R H N) (WithVal (fractionValuation R N F))
        (single (n • g) 1)
      have hs : v.restrict s ≠ 0 := by
        simp [v, s, one_ne_zero]
      refine ⟨Units.mk0 (v.restrict s) hs, trivial, fun a b hab => ?_⟩
      have hlt : periodValuation N (b - a) <
          ↑(Multiplicative.ofAdd (-N (n • g))) := by
        simpa [v, s, ← map_sub, periodValuation_single, one_ne_zero] using hab
      apply (periodValuation_le_iff N _ C).1
      apply hlt.le.trans
      rw [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
      exact neg_le_neg (by simpa only [map_nsmul] using hn.le)

end Ring

variable (F : Type*) [Field F] [Algebra (NovikovSeries R H N) F]
  [IsFractionRing (NovikovSeries R H N) F]

/-- The Novikov ring is a closed subspace of its valued fraction field, not necessarily a
dense subspace. No completeness assertion about the fraction field is required. -/
theorem isClosedEmbedding_algebraMap_fractionValuation :
    IsClosedEmbedding (algebraMap (NovikovSeries R H N)
      (WithVal (fractionValuation R N F))) :=
  (isUniformEmbedding_algebraMap_fractionValuation N F).isClosedEmbedding

end TauCeti.NovikovSeries
