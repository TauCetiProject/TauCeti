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

section Monoid

variable {R H : Type*} [CommRing R] [Nontrivial R] [AddCommMonoid H]
  [NoZeroDivisors (AddMonoidAlgebra R H)] (N : H →+ ℝ)

variable (F : Type*) [CommRing F] [Algebra (NovikovSeries R H N) F]
  [IsFractionRing (NovikovSeries R H N) F]

/-- The valued-ring inclusion retains the intrinsic period valuation of each series. -/
@[simp]
theorem valued_algebraMap_fractionValuation (a : NovikovSeries R H N) :
    Valued.v (algebraMap (NovikovSeries R H N) (WithVal (fractionValuation R N F)) a) =
      periodValuation N a := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal, fractionValuation_algebraMap]

end Monoid

variable {R H : Type*} [CommRing R] [Nontrivial R] [AddCommGroup H]
  [NoZeroDivisors (AddMonoidAlgebra R H)] (N : H →+ ℝ)

section Ring

variable (F : Type*) [CommRing F] [Algebra (NovikovSeries R H N) F]
  [IsFractionRing (NovikovSeries R H N) F]

/-- The fraction-field valuation topology induces exactly the period uniformity on series. -/
theorem isUniformEmbedding_algebraMap_fractionValuation :
    IsUniformEmbedding (algebraMap (NovikovSeries R H N)
      (WithVal (fractionValuation R N F))) := by
  let v := (Valued.v : Valuation (WithVal (fractionValuation R N F))
    (WithZero (Multiplicative ℝ)))
  have hrestrict (a b : NovikovSeries R H N) (γ : v.ValueGroup₀) :
      v.restrict (algebraMap _ (WithVal (fractionValuation R N F)) b -
        algebraMap _ (WithVal (fractionValuation R N F)) a) < γ ↔
        periodValuation N (b - a) < embedding γ := by
    rw [Valuation.restrict_lt_iff_lt_embedding, ← map_sub,
      valued_algebraMap_fractionValuation]
  apply IsUniformInducing.isUniformEmbedding
  apply (hasBasis_uniformity.isUniformInducing_iff
    (Valued.hasBasis_uniformity (WithVal (fractionValuation R N F)) _)).2
  constructor
  -- Each value-group radius contains a closed period ball with a slightly larger cutoff.
  · intro γ _
    have hγ : embedding (γ : v.ValueGroup₀) ≠ 0 := by simp
    obtain ⟨r, hr⟩ := WithZero.ne_zero_iff_exists.1 hγ
    refine ⟨-Multiplicative.toAdd r + 1, trivial, fun a b hab => ?_⟩
    rw [Set.mem_ofPred_eq, hrestrict, ← hr]
    apply ((periodValuation_le_iff N _ _).2 hab).trans_lt
    rw [WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt]
    simp only [toAdd_ofAdd]
    linarith
  · intro C _
    -- For the zero period map, the open unit ball pulls back to zero.
    by_cases hN : N = 0
    · refine ⟨1, trivial, fun a b hab => ?_⟩
      have hlt : periodValuation N (b - a) < 1 := by
        rw [Set.mem_ofPred_eq, hrestrict, Units.val_one, map_one] at hab
        exact hab
      have hz : b - a = 0 := by
        rcases (periodValuation_lt_iff N (b - a) 0).1 (by simpa using hlt) with hz | ho
        · exact hz
        · ext h
          simpa using coeff_eq_zero_of_lt_order (a := b - a) (h := h)
            (by simpa [hN] using ho)
      exact (periodValuation_le_iff N (b - a) C).1 (by simp [hz])
    -- Otherwise powers of a positive-period monomial give arbitrarily small radii.
    · obtain ⟨g, hg⟩ := N.exists_pos_of_ne_zero hN
      obtain ⟨n, hn⟩ := exists_lt_nsmul hg C
      let s := algebraMap (NovikovSeries R H N) (WithVal (fractionValuation R N F))
        (single (n • g) 1)
      have hvs : v s = ↑(Multiplicative.ofAdd (-N (n • g))) :=
        (valued_algebraMap_fractionValuation N F _).trans
          (periodValuation_single N _ one_ne_zero)
      have hs : v.restrict s ≠ 0 := by
        rw [Ne, Valuation.restrict_eq_zero_iff, hvs]
        exact WithZero.coe_ne_zero
      refine ⟨Units.mk0 (v.restrict s) hs, trivial, fun a b hab => ?_⟩
      rw [Set.mem_ofPred_eq, hrestrict, Units.val_mk0,
        Valuation.embedding_restrict, hvs] at hab
      apply (periodValuation_le_iff N _ C).1
      apply hab.le.trans
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
