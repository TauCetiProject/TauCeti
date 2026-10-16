/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic

/-!
# Local degrees of the filled cover over the three punctures

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over `1/2` is numbered by
`ν : p ⁻¹' {1/2} ≃ Fin n`, with monodromy triple `(σ0, σ1, σinf)`. The points that
`TauCeti.FilledCover p` adds over a puncture `q ∈ {0, 1, ∞}` are the connected components of
`p ⁻¹' D_q*`, and each has a local degree `TauCeti.FilledCover.degree`, the exponent `e` for which
`p` is `w ↦ w ^ e` near it. This file proves that over each puncture the multiset of these local
degrees is the full cycle type of the corresponding permutation, a partition of `n`, so the local
degrees over each puncture sum to `n`. Once `p` is extended to a branched cover of the Riemann
sphere, these local degrees are its ramification indices over `0`, `1` and `∞`, and the three
multisets are its ramification partitions.

Summing over all added points gives the combinatorial form of the Riemann–Hurwitz formula: the
total ramification `∑ (e - 1)` is `2 n - χ`, where `χ` is the Euler characteristic of the monodromy
triple, so for a connected cover of genus `g` it is `2 n + 2 g - 2`.

## Main results

* `TauCeti.FilledCover.map_degree_overZero`, `TauCeti.FilledCover.map_degree_overOne`,
  `TauCeti.FilledCover.map_degree_overInf`: the local degrees over `0`, `1` and `∞` are the full
  cycle types of `σ0`, `σ1` and `σinf`.
* `TauCeti.FilledCover.sum_degree_overZero`, `TauCeti.FilledCover.sum_degree_overOne`,
  `TauCeti.FilledCover.sum_degree_overInf`: over each puncture the local degrees sum to `n`.
* `TauCeti.FilledCover.sum_degree`: the local degrees of all added points sum to `3 n`.
* `TauCeti.FilledCover.sum_degree_sub_one`: the total ramification is `2 n - χ`.
* `TauCeti.FilledCover.two_mul_genus_sub_two`: the Riemann–Hurwitz formula
  `2 g - 2 = -2 n + ∑ (e - 1)` for a connected cover.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 and §4.2 (the cycle lengths of the monodromy are the ramification indices).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §17, Theorem 17.14 (the Riemann–Hurwitz formula).
-/

public section

namespace TauCeti

open Equiv.Perm FilledPoint ThricePuncturedSphere

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere} (hp : IsCoveringMap p)
  {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n)
include hp ν

namespace FilledCover

/-- **The ramification partition over `0`.** The local degrees of the points added over `0` are
the cycle lengths of `σ0`, fixed points included. -/
theorem map_degree_overZero [Fintype (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero))] :
    Finset.univ.val.map (fun c ↦ degree p (overZero p c)) =
      fullCycleType (hp.monodromyTriple ν).σ0 :=
  (fullCycleType_eq_map_univ _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν) (by simp)).symm

/-- **The ramification partition over `1`.** The local degrees of the points added over `1` are
the cycle lengths of `σ1`, fixed points included. -/
theorem map_degree_overOne [Fintype (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne))] :
    Finset.univ.val.map (fun c ↦ degree p (overOne p c)) =
      fullCycleType (hp.monodromyTriple ν).σ1 :=
  (fullCycleType_eq_map_univ _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν) (by simp)).symm

/-- **The ramification partition over `∞`.** The local degrees of the points added over `∞` are
the cycle lengths of `σinf`, fixed points included. -/
theorem map_degree_overInf [Fintype (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf))] :
    Finset.univ.val.map (fun c ↦ degree p (overInf p c)) =
      fullCycleType (hp.monodromyTriple ν).σinf :=
  (fullCycleType_eq_map_univ _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν) (by simp)).symm

/-- The local degrees of the points added over `0` sum to the degree of the cover. -/
theorem sum_degree_overZero [Fintype (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero))] :
    ∑ c, degree p (overZero p c) = n := by
  rw [Finset.sum_eq_multiset_sum, map_degree_overZero hp ν, sum_fullCycleType, Fintype.card_fin]

/-- The local degrees of the points added over `1` sum to the degree of the cover. -/
theorem sum_degree_overOne [Fintype (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne))] :
    ∑ c, degree p (overOne p c) = n := by
  rw [Finset.sum_eq_multiset_sum, map_degree_overOne hp ν, sum_fullCycleType, Fintype.card_fin]

/-- The local degrees of the points added over `∞` sum to the degree of the cover. -/
theorem sum_degree_overInf [Fintype (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf))] :
    ∑ c, degree p (overInf p c) = n := by
  rw [Finset.sum_eq_multiset_sum, map_degree_overInf hp ν, sum_fullCycleType, Fintype.card_fin]

/-- The local degrees of all the added points sum to three times the degree of the cover, `n` over
each of the three punctures. -/
theorem sum_degree [Fintype (FilledPoint p)] : ∑ i, degree p i = 3 * n := by
  have := Fintype.ofInjective _ (overZero_injective p)
  have := Fintype.ofInjective _ (overOne_injective p)
  have := Fintype.ofInjective _ (overInf_injective p)
  rw [← (equivSum p).symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [← equivSum_overZero, ← equivSum_overOne, ← equivSum_overInf, Equiv.symm_apply_apply]
  rw [sum_degree_overZero hp ν, sum_degree_overOne hp ν, sum_degree_overInf hp ν]
  ring

/-- **The total ramification.** Summed over all the added points, `e - 1` adds up to `2 n - χ`,
where `e` is the local degree and `χ` is the Euler characteristic of the monodromy triple. -/
theorem sum_degree_sub_one [Fintype (FilledPoint p)] :
    ∑ i, ((degree p i : ℤ) - 1) = 2 * n - (hp.monodromyTriple ν).eulerChar := by
  have hcard := FilledPoint.natCard_eq_cycleCounts p hp ν
  rw [Nat.card_eq_fintype_card] at hcard
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_degree hp ν, Finset.sum_const,
    Finset.card_univ, hcard, PermutationTriple.eulerChar_eq_cycleCounts]
  push_cast
  ring

/-- **The Riemann–Hurwitz formula for a filled cover.** For a connected cover of degree `n`, whose
monodromy triple has genus `g`, the total ramification `∑ (e - 1)` over the added points satisfies
`2 g - 2 = -2 n + ∑ (e - 1)`. This is the shape of the Riemann–Hurwitz formula for a degree-`n`
branched cover of the Riemann sphere, which has genus `0`. -/
theorem two_mul_genus_sub_two [PathConnectedSpace E] [Fintype (FilledPoint p)] :
    2 * ((hp.monodromyTriple ν).genus : ℤ) - 2 = -2 * n + ∑ i, ((degree p i : ℤ) - 1) := by
  rw [sum_degree_sub_one hp ν, ← (hp.isConnected_monodromyTriple ν).two_sub_two_mul_genus]
  ring

end FilledCover

end TauCeti
