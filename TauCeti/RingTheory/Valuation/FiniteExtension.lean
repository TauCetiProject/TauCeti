/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Tail
import TauCeti.RingTheory.Valuation.Center
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Extensions of a valuation ring to a finite field extension

Let `L / K` be a finite field extension and `O` a valuation subring of `K`. A valuation subring
`O'` of `L` *lies over* `O` when `O' ∩ K = O`, that is `O'.comap (algebraMap K L) = O`. This file
proves that there are at most `[L : K]` of them; equivalently, a valuation of `K` has at most
`[L : K]` inequivalent extensions to `L`.

The proof runs through the integral closure `C` of `O` in `L`, which every `O'` over `O` contains.
The centre `𝔫(O') = {c ∈ C | c ∈ 𝔪(O')}` is a maximal ideal of `C`, because it lies over the
maximal ideal of `O` and `C` is integral over `O`. Two valuation subrings over `O` with the same
centre coincide: for `x ∈ O'`, scaling a polynomial relation of `x` over `K` so that its
coefficients lie in `O` and taking the tail of the relation after its last unit coefficient
(`Polynomial.isIntegral_mul_aeval_iterate_divX`) produces `u ∈ C ∖ 𝔫(O')` with `x u ∈ C`, so
`O' ⊆ C_𝔫(O')`. Prime avoidance among the distinct maximal ideals `𝔫(O'_i)` then gives elements
`e_i ∈ C` that are units in `O'_i` and lie in the maximal ideal of every other `O'_j`, and such a
family is linearly independent over `K`: in a relation normalised so that its coefficients lie
in `O` with one coefficient equal to `1`, the valuation of `O'_i` at that index sees only the
term `e_i`.

This is the field-level input for bounding the fibres of the map from the adic spectrum of a
finite algebra to that of its base: a point lying over a given point is an extension of its
valuation to a residue field extension.

## Main results

* `ValuationSubring.finite_setOf_comap_eq`: only finitely many valuation subrings of `L` lie over
  `O`.
* `ValuationSubring.ncard_setOf_comap_eq_le_finrank`: there are at most `[L : K]` of them.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Chapter 3.
-/

public section

open Polynomial Module

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  {O' : ValuationSubring L}

/-- **Normalising a relation.** A family `g` of elements of `K` that vanishes outside `s` and is
not identically zero has an index `i₀` with `g i₀ ≠ 0` such that every `g i / g i₀` lies in `O`. -/
private theorem exists_valuation_div_le_one {ι : Type*} (s : Finset ι) {g : ι → K}
    (hs : ∀ i ∉ s, g i = 0) {i : ι} (hi : g i ≠ 0) :
    ∃ i₀, g i₀ ≠ 0 ∧ ∀ i, O.valuation (g i / g i₀) ≤ 1 := by
  have hne : s.Nonempty := ⟨i, by_contra fun h ↦ hi (hs i h)⟩
  obtain ⟨i₀, -, hmax⟩ := s.exists_max_image (fun i ↦ O.valuation (g i)) hne
  have hi₀ : g i₀ ≠ 0 := fun h ↦ hi <| by
    by_cases his : i ∈ s
    · simpa [h] using hmax i his
    · exact hs i his
  refine ⟨i₀, hi₀, fun j ↦ ?_⟩
  rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).mpr hi₀)]
  by_cases hj : j ∈ s
  · exact hmax j hj
  · simp [hs j hj]

/-- **The key step.** If `O'` lies over `O` and `x ∈ O'` is algebraic over `K`, there is `u` in
the integral closure `C` of `O` with `x u ∈ C` and `u` a unit of `O'`. -/
private theorem exists_mul_mem_integralClosure (hO' : O'.comap (algebraMap K L) = O) {x : L}
    (hx : IsAlgebraic K x) (hxO' : x ∈ O') :
    ∃ u ∈ integralClosure O L, x * u ∈ integralClosure O L ∧ O'.valuation u = 1 := by
  classical
  obtain ⟨p, hp0, hpx⟩ := hx
  -- scale `p` so that its coefficients lie in `O`, one of them being `1`
  obtain ⟨n₀, hn₀⟩ := nonempty_support_iff.mpr hp0
  obtain ⟨i₀, hc₀, hmax⟩ := exists_valuation_div_le_one (O := O) p.support
    (fun n ↦ notMem_support_iff.mp) (mem_support_iff.mp hn₀)
  have hlift : C (p.coeff i₀)⁻¹ * p ∈ lifts (algebraMap O K) := by
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦
      ⟨⟨(C (p.coeff i₀)⁻¹ * p).coeff n, ?_⟩, algebraMap_apply _ _⟩
    rw [coeff_C_mul, ← valuation_le_one_iff, ← div_eq_inv_mul]
    exact hmax n
  obtain ⟨q, hq⟩ := hlift
  rw [coe_mapRingHom] at hq
  have hqx : aeval x q = 0 := by
    rw [← aeval_map_algebraMap K, hq, map_mul, aeval_C, hpx, mul_zero]
  have hq₀ : IsUnit (q.coeff i₀) := by
    have h := congrArg (·.coeff i₀) hq
    simp only [coeff_map, coeff_C_mul, inv_mul_cancel₀ hc₀] at h
    exact (IsFractionRing.injective O K (h.trans (map_one _).symm)) ▸ isUnit_one
  -- `j` is the last index whose coefficient is a unit of `O`
  set U := q.support.filter fun i ↦ IsUnit (q.coeff i)
  have hU : U.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨mem_support_iff.mpr hq₀.ne_zero, hq₀⟩⟩
  set j := U.max' hU
  have hj : IsUnit (q.coeff j) := (Finset.mem_filter.mp (U.max'_mem hU)).2
  have hgt (n : ℕ) : ¬IsUnit (q.coeff (n + j + 1)) := fun h ↦ by
    have := U.le_max' (n + j + 1) (Finset.mem_filter.mpr ⟨mem_support_iff.mpr h.ne_zero, h⟩)
    omega
  -- the value of the tail after `j` has valuation below `1`
  have htail : O'.valuation (x * aeval x (divX^[j + 1] q)) < 1 := by
    rw [map_mul, aeval_eq_sum_range]
    refine (mul_le_of_le_one_left' ((valuation_le_one_iff _ _).mpr hxO')).trans_lt
      (Valuation.map_sum_lt _ one_ne_zero fun n _ ↦ ?_)
    rw [Algebra.smul_def, map_mul, map_pow, coeff_iterate_divX, ← add_assoc,
      IsScalarTower.algebraMap_apply O K L]
    exact (mul_le_of_le_one_right' (pow_le_one' ((valuation_le_one_iff _ _).mpr hxO') n)).trans_lt
      (valuation_apply_lt_one_of_comap_eq hO' (hgt n))
  refine ⟨aeval x (divX^[j] q), ?_, isIntegral_mul_aeval_iterate_divX hqx j, ?_⟩ <;>
    rw [aeval_iterate_divX]
  · exact (isIntegral_mul_aeval_iterate_divX hqx (j + 1)).add isIntegral_algebraMap
  · have hu : O'.valuation (algebraMap O L (q.coeff j)) = 1 := by
      rw [IsScalarTower.algebraMap_apply O K L]
      exact valuation_apply_eq_one_of_comap_eq hO' hj
    rw [Valuation.map_add_eq_of_lt_right _ (htail.trans_eq hu.symm), hu]

/-- The centre of `O'` on the integral closure `C` of `O`: the elements of `C` in the maximal
ideal of `O'`. -/
private noncomputable def centre (hO' : O'.comap (algebraMap K L) = O) :
    Ideal (integralClosure O L) :=
  Valuation.centerIdeal (integralClosure O L) O'.valuation fun c ↦ by
    rw [Subalgebra.algebraMap_apply]
    exact (valuation_le_one_iff _ _).mpr (integralClosure_le_of_comap_eq hO' c.2)

private theorem mem_centre (hO' : O'.comap (algebraMap K L) = O) {c : integralClosure O L} :
    c ∈ centre hO' ↔ O'.valuation c < 1 := by
  rw [centre, Valuation.mem_centerIdeal, Subalgebra.algebraMap_apply]

/-- An element of the integral closure outside the centre of `O'` is a unit of `O'`. -/
private theorem valuation_eq_one_of_notMem_centre (hO' : O'.comap (algebraMap K L) = O)
    {c : integralClosure O L} (hc : c ∉ centre hO') : O'.valuation c = 1 :=
  ((valuation_le_one_iff _ _).mpr (integralClosure_le_of_comap_eq hO' c.2)).antisymm <|
    not_lt.mp (mt (mem_centre hO').mpr hc)

private theorem isPrime_centre (hO' : O'.comap (algebraMap K L) = O) : (centre hO').IsPrime :=
  Valuation.isPrime_centerIdeal _

/-- The centre of `O'` lies over the maximal ideal of `O`, so it is maximal in the integral
closure of `O`. -/
private theorem isMaximal_centre (hO' : O'.comap (algebraMap K L) = O) :
    (centre hO').IsMaximal := by
  have := isPrime_centre hO'
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap O (integralClosure O L))
    (fun c ↦ Algebra.IsIntegral.isIntegral c) _ ?_
  convert IsLocalRing.maximalIdeal.isMaximal O
  ext a
  rw [Ideal.mem_comap, mem_centre, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff,
    Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply O K L]
  exact ⟨fun h hu ↦ h.ne (valuation_apply_eq_one_of_comap_eq hO' hu),
    valuation_apply_lt_one_of_comap_eq hO'⟩

/-- A valuation subring over `O` is contained in every valuation subring over `O` whose centre
lies inside its own. -/
private theorem le_of_centre_le [Algebra.IsAlgebraic K L] {O₁ O₂ : ValuationSubring L}
    (h₁ : O₁.comap (algebraMap K L) = O) (h₂ : O₂.comap (algebraMap K L) = O)
    (h : centre h₂ ≤ centre h₁) : O₁ ≤ O₂ := by
  intro x hx
  obtain ⟨u, hu, hxu, hu₁⟩ :=
    exists_mul_mem_integralClosure h₁ (Algebra.IsAlgebraic.isAlgebraic x) hx
  have hu₂ : O₂.valuation u = 1 :=
    valuation_eq_one_of_notMem_centre h₂ (c := ⟨u, hu⟩) fun h' ↦
      (mem_centre h₁).mp (h h') |>.ne hu₁
  have := (valuation_le_one_iff _ _).mpr (integralClosure_le_of_comap_eq h₂ hxu)
  rw [map_mul, hu₂, mul_one] at this
  exact (valuation_le_one_iff _ _).mp this

/-- **Separating elements.** Among finitely many valuation subrings of `L` over `O`, each one has
an element of the integral closure of `O` that is a unit in it and lies in the maximal ideal of
every other one. -/
private theorem exists_separating [Algebra.IsAlgebraic K L] (s : Finset (ValuationSubring L))
    (hs : ∀ O' ∈ s, O'.comap (algebraMap K L) = O) {O₀ : ValuationSubring L} (h₀ : O₀ ∈ s) :
    ∃ e ∈ integralClosure O L, O₀.valuation e = 1 ∧
      ∀ O' ∈ s, O' ≠ O₀ → O'.valuation e < 1 := by
  classical
  let N (O' : ValuationSubring L) : Ideal (integralClosure O L) :=
    if h : O'.comap (algebraMap K L) = O then centre h else ⊤
  have hN {O'} (h : O' ∈ s) : N O' = centre (hs O' h) := by simp [N, hs O' h]
  have hP := isPrime_centre (hs O₀ h₀)
  -- prime avoidance: the other centres are not inside the centre of `O₀`
  have : ¬(s.erase O₀).inf N ≤ centre (hs O₀ h₀) := by
    rw [hP.inf_le']
    rintro ⟨O₁, hO₁, hle⟩
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hO₁
    rw [hN hmem] at hle
    have heq := (isMaximal_centre (hs O₁ hmem)).eq_of_le hP.ne_top hle
    exact hne (le_antisymm (le_of_centre_le _ _ heq.ge) (le_of_centre_le _ _ heq.le))
  obtain ⟨e, he, heP⟩ := Set.not_subset.mp this
  refine ⟨e, e.2, valuation_eq_one_of_notMem_centre _ heP, fun O' hO' hne ↦ ?_⟩
  have := Finset.inf_le (f := N) (Finset.mem_erase.mpr ⟨hne, hO'⟩) he
  rwa [hN hO', mem_centre] at this

/-- **At most `[L : K]` valuation subrings over `O`.** A finite set of valuation subrings of `L`
over `O` has at most `[L : K]` members: separating elements for them are linearly independent
over `K`. -/
private theorem card_le_finrank [FiniteDimensional K L] (s : Finset (ValuationSubring L))
    (hs : ∀ O' ∈ s, O'.comap (algebraMap K L) = O) : s.card ≤ finrank K L := by
  classical
  have hsep (O₀ : s) := exists_separating s hs O₀.2
  choose e he₁ he₂ he₃ using hsep
  suffices LinearIndependent K e by simpa using this.fintype_card_le_finrank
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hgi
  -- normalise the relation by a coefficient of largest valuation
  obtain ⟨i₀, hg₀, hi₀⟩ :=
    exists_valuation_div_le_one (O := O) Finset.univ (fun j hj ↦ absurd (Finset.mem_univ j) hj) hgi
  have hsum : ∑ i, (g i / g i₀) • e i = 0 := by
    simp_rw [div_eq_inv_mul, mul_smul, ← Finset.smul_sum, hg, smul_zero]
  -- the valuation of the `i₀`-th subring sees only the `i₀`-th term
  have hlt : (i₀ : ValuationSubring L).valuation
      (∑ i ∈ Finset.univ.erase i₀, (g i / g i₀) • e i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi ↦ ?_
    rw [Algebra.smul_def, map_mul]
    refine mul_le_of_le_one_left' ?_ |>.trans_lt <|
      he₃ i i₀ i₀.2 (Subtype.coe_injective.ne (Finset.ne_of_mem_erase hi).symm)
    exact (valuation_apply_le_one_iff_of_comap_eq (hs _ i₀.2) _).mpr (hi₀ i)
  have := congrArg (i₀ : ValuationSubring L).valuation hsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), div_self hg₀, one_smul,
    Valuation.map_add_eq_of_lt_left _ (hlt.trans_eq (he₂ i₀).symm), he₂, map_zero] at this
  exact one_ne_zero this

variable [FiniteDimensional K L]

variable (L) in
/-- **Finitely many extensions.** Only finitely many valuation subrings of a finite extension
`L` of `K` lie over a given valuation subring of `K`. -/
theorem finite_setOf_comap_eq (O : ValuationSubring K) :
    {O' : ValuationSubring L | O'.comap (algebraMap K L) = O}.Finite := by
  by_contra h
  obtain ⟨t, hts, hcard⟩ := Set.Infinite.exists_subset_card_eq h (finrank K L + 1)
  have := card_le_finrank t fun O' hO' ↦ hts hO'
  omega

variable (L) in
/-- **At most `[L : K]` extensions.** At most `[L : K]` valuation subrings of a finite extension
`L` of `K` lie over a given valuation subring of `K`; equivalently, a valuation of `K` has at most
`[L : K]` pairwise inequivalent extensions to `L`. -/
theorem ncard_setOf_comap_eq_le_finrank (O : ValuationSubring K) :
    {O' : ValuationSubring L | O'.comap (algebraMap K L) = O}.ncard ≤ finrank K L := by
  rw [Set.ncard_eq_toFinset_card _ (finite_setOf_comap_eq L O)]
  exact card_le_finrank _ fun O' hO' ↦ (Set.Finite.mem_toFinset _).mp hO'

end ValuationSubring
