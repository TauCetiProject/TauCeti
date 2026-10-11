/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Finrank

/-!
# Additivity of the Euler characteristic along open covers

If a space `X` is covered by two open subsets `U` and `V`, and `X`, `U`, `V` and `U ∩ V` all have
finite CW type, then

```text
χ(X) + χ(U ∩ V) = χ(U) + χ(V).
```

The proof reads the Mayer--Vietoris long exact sequence
`⋯ ⟶ Hₙ(U ∩ V) ⟶ Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X) ⟶ Hₙ₋₁(U ∩ V) ⟶ ⋯ ⟶ H₀(X) ⟶ 0`
with rational coefficients, whose terms are finite-dimensional and vanish in large degrees, and
uses that the alternating sum of the dimensions along such a sequence vanishes
(`TauCeti.finsum_finrank_singularHomology_mayerVietoris`).  The Euler characteristics are then the
alternating sums of the dimensions of rational homology
(`TauCeti.eulerChar_eq_finsum_finrank_singularHomology`).

## Main results

* `TauCeti.eulerChar_add_eulerChar_inter_of_union_eq_univ`: additivity for a cover of `X` by two
  open subsets.
* `TauCeti.eulerChar_union_add_eulerChar_inter`: the same for two open subsets `U` and `V` of a
  space, read as `χ(U ∪ V) + χ(U ∩ V) = χ(U) + χ(V)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Mayer--Vietoris sequences and Theorem 2.44.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology AlgebraicTopology Set

universe w

namespace TauCeti

/-- **Additivity of the Euler characteristic along an open cover.**  If `X` is covered by two
open subsets `U` and `V`, and `X`, `U`, `V` and `U ∩ V` have finite CW type, then
`χ(X) + χ(U ∩ V) = χ(U) + χ(V)`. -/
theorem eulerChar_add_eulerChar_inter_of_union_eq_univ {X : Type w} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) [FiniteCWType X]
    [FiniteCWType U] [FiniteCWType V] [FiniteCWType ↥(U ∩ V)] :
    eulerChar X + eulerChar ↥(U ∩ V) = eulerChar U + eulerChar V := by
  let k := ULift.{w} ℚ
  have (Y : Type w) [TopologicalSpace Y] [FiniteCWType Y] (n : ℕ) :=
    finite_singularHomology_of_finiteCWType Y (ModuleCat.of k k) n
  -- All four homologies vanish beyond some common degree `N`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((((eventually_isZero_singularHomology_of_finiteCWType X (ModuleCat.of k k)).and
      (eventually_isZero_singularHomology_of_finiteCWType U (ModuleCat.of k k))).and
      (eventually_isZero_singularHomology_of_finiteCWType V (ModuleCat.of k k))).and
      (eventually_isZero_singularHomology_of_finiteCWType ↥(U ∩ V) (ModuleCat.of k k)))
  have key := finsum_finrank_singularHomology_mayerVietoris (X := TopCat.of X) hU hV hUV k
    ((finite_Iio N).subset fun n hn ↦ not_le.1 fun h ↦
      hn (ModuleCat.finrank_eq_zero_of_isZero (hN n h).2))
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N) _ fun n hn ↦ by
    rw [Finset.coe_range, mem_Iio]
    by_contra h
    obtain ⟨⟨⟨hX, hU⟩, hV⟩, hI⟩ := hN n (not_lt.1 h)
    exact hn (by simp [ModuleCat.finrank_eq_zero_of_isZero hX,
      ModuleCat.finrank_eq_zero_of_isZero hU, ModuleCat.finrank_eq_zero_of_isZero hV,
      ModuleCat.finrank_eq_zero_of_isZero hI])] at key
  rw [eulerChar_eq_finsum_finrank_singularHomology X k,
    eulerChar_eq_finsum_finrank_singularHomology ↥(U ∩ V) k,
    eulerChar_eq_finsum_finrank_singularHomology U k,
    eulerChar_eq_finsum_finrank_singularHomology V k,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range fun n hn ↦ (hN n hn).1.1.1,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range fun n hn ↦ (hN n hn).2,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range fun n hn ↦ (hN n hn).1.1.2,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range fun n hn ↦ (hN n hn).1.2]
  simp only [Nat.cast_add, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    at key
  linarith

/-- **Additivity of the Euler characteristic for open subsets.**  If `U` and `V` are open subsets
of a space, and `U ∪ V`, `U`, `V` and `U ∩ V` have finite CW type, then
`χ(U ∪ V) + χ(U ∩ V) = χ(U) + χ(V)`. -/
theorem eulerChar_union_add_eulerChar_inter {X : Type w} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) [FiniteCWType ↥(U ∪ V)] [FiniteCWType U] [FiniteCWType V]
    [FiniteCWType ↥(U ∩ V)] :
    eulerChar ↥(U ∪ V) + eulerChar ↥(U ∩ V) = eulerChar U + eulerChar V := by
  -- Inside `U ∪ V`, the traces of `U`, `V` and `U ∩ V` are homeomorphic to these sets.
  have hrange {s : Set X} (hs : s ⊆ U ∪ V) : s ⊆ range (Subtype.val : ↥(U ∪ V) → X) := by
    rwa [Subtype.range_coe]
  let eU := IsEmbedding.subtypeVal.homeomorphOfSubsetRange (hrange subset_union_left)
  let eV := IsEmbedding.subtypeVal.homeomorphOfSubsetRange (hrange subset_union_right)
  let eI := (Homeomorph.setCongr (preimage_inter (f := Subtype.val) (s := U) (t := V))).symm.trans
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (hrange (inter_subset_left.trans subset_union_left)))
  have := eU.finiteCWType
  have := eV.finiteCWType
  have := eI.finiteCWType
  rw [← eU.eulerChar_eq, ← eV.eulerChar_eq, ← eI.eulerChar_eq]
  exact eulerChar_add_eulerChar_inter_of_union_eq_univ (hU.preimage continuous_subtype_val)
    (hV.preimage continuous_subtype_val) (by rw [← preimage_union, Subtype.coe_preimage_self])

end TauCeti
