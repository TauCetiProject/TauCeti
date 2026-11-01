/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Extensions of a valuation subring to an algebraic extension

Let `L / K` be an algebraic field extension and `O` a valuation subring of `K`. The valuation
subrings `A` of `L` lying over `O`, in the sense that `A ∩ K = O`, are pairwise incomparable, and
any finitely many of them can be told apart by elements of `L` that lie in all of them: for each
`A` there is an element that is a unit of `A` and a nonunit of every other one.

The engine is a single polynomial manipulation. Let `x ∈ A ∖ B` and put `t = x⁻¹`, a nonunit of
`B`. Scale a nonzero polynomial relation `∑ aᵢ tⁱ = 0` over `K` so that every `aᵢ` lies in `O`
and some `aᵢ` is a unit of `O`, and let `j` be the least such index. Then
`u = ∑_{i ≥ j} aᵢ t^{i - j}` is congruent to the unit `aⱼ` modulo the nonunits of `B`, while
`u = -∑_{i < j} aᵢ x^{j - i}` is a nonunit of `A`. Every valuation subring of `L` containing `O`
contains `x` or `t`, so it contains `u` by one of the two expressions; that is, `u` is integral
over `O`.

Separating elements turn into a bound on the number of such extensions through linear
independence. If `v i` are valuations on an algebra over `K`, all at most `1` on `O`, and `e i` is
strictly the largest member of a family `e` for `v i`, then `e` is linearly independent over `K`:
in a relation, divide by a coefficient dividing all the others in `O`, and the summand `e k`
dominates for `v k`. Together these bound the number of points of a valuation spectrum lying over
a given point along a finite ring map by the dimension of the fibre.

## Main results

* `ValuationSubring.eq_of_le_of_comap_eq`: two comparable valuation subrings of an algebraic
  extension with the same restriction to the base are equal.
* `ValuationSubring.exists_mem_nonunits_valuation_eq_one`: two distinct valuation subrings with
  the same restriction `O` are separated by an element lying in every valuation subring over `O`.
* `ValuationSubring.exists_valuation_eq_one_and_lt_one`: finitely many distinct valuation subrings
  over `O` admit a family of elements, each a unit for its own subring and a nonunit for the others.
* `Valuation.linearIndependent_of_map_lt`: a family in which each member strictly dominates the
  others for its own valuation, the valuations being bounded on a common valuation subring of the
  scalars, is linearly independent. It complements `Valuation.linearIndependent_of_map_smul_ne`,
  which uses a single valuation.

## References

* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005, §3.2,
  for the extensions of a valuation to an algebraic extension, their incomparability and the
  bound on their number by the degree.
-/

public section

open Polynomial

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Units of `O` are sent to units of every valuation subring of `L` whose restriction contains
`O`. -/
private theorem valuation_algebraMap_eq_one {O : ValuationSubring K} {W : ValuationSubring L}
    (hW : O ≤ W.comap (algebraMap K L)) {a : K} (ha : O.valuation a = 1) :
    W.valuation (algebraMap K L a) = 1 := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have h₁ : W.valuation (algebraMap K L a) ≤ 1 :=
    (W.valuation_le_one_iff _).mpr (hW ((O.valuation_le_one_iff a).mp ha.le))
  have h₂ : W.valuation (algebraMap K L a⁻¹) ≤ 1 :=
    (W.valuation_le_one_iff _).mpr
      (hW ((O.valuation_le_one_iff _).mp (by rw [map_inv₀, ha, inv_one])))
  have hmul : W.valuation (algebraMap K L a) * W.valuation (algebraMap K L a⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
  by_contra hne
  exact (mul_lt_one_of_lt_of_le (lt_of_le_of_ne h₁ hne) h₂).ne hmul

/-- **The separating element.** If `A` and `B` are valuation subrings of `L` with
`A ∩ K ⊆ O ⊆ B ∩ K`, an algebraic element `x ∈ A ∖ B` produces a nonunit `u` of `A` that is a
unit of `B` and lies in every valuation subring of `L` whose restriction to `K` contains `O`. -/
private theorem exists_of_mem_of_notMem {O : ValuationSubring K} {A B : ValuationSubring L}
    (hA : A.comap (algebraMap K L) ≤ O) (hB : O ≤ B.comap (algebraMap K L)) {x : L}
    (hx : IsAlgebraic K x) (hxA : x ∈ A) (hxB : x ∉ B) :
    ∃ u : L, u ∈ A.nonunits ∧ B.valuation u = 1 ∧
      ∀ W : ValuationSubring L, O ≤ W.comap (algebraMap K L) → u ∈ W := by
  classical
  have hx0 : x ≠ 0 := by rintro rfl; exact hxB B.zero_mem
  set t := x⁻¹ with ht_def
  have htx : t * x = 1 := inv_mul_cancel₀ hx0
  have ht0 : t ≠ 0 := inv_ne_zero hx0
  -- `t` is a nonunit of `B`, and nonunits of `O` are nonunits of `A`
  have htB : B.valuation t < 1 := by
    rw [← mem_nonunits_iff, mem_nonunits_iff_or, ht_def, inv_inv]
    exact Or.inr hxB
  have hnon {a : K} (ha : O.valuation a < 1) : A.valuation (algebraMap K L a) < 1 := by
    rw [← mem_nonunits_iff, ← mem_nonunits_comap]
    exact nonunits_le_nonunits.mpr hA ((O.mem_nonunits_iff).mpr ha)
  -- a relation `∑ aᵢ tⁱ = 0` with all `aᵢ ∈ O` and some `aᵢ` a unit of `O`
  obtain ⟨p, hp0, hpt⟩ := hx.inv
  set n := p.natDegree
  obtain ⟨k, hk, hkmax⟩ := (Finset.range (n + 1)).exists_max_image (fun i ↦ O.valuation (p.coeff i))
    ⟨n, Finset.self_mem_range_succ n⟩
  have hck : p.coeff k ≠ 0 := by
    intro h
    refine hp0 (leadingCoeff_eq_zero.mp ?_)
    have := hkmax n (Finset.self_mem_range_succ n)
    rwa [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
  set a : ℕ → K := fun i ↦ p.coeff i / p.coeff k with ha_def
  have haO (i : ℕ) : O.valuation (a i) ≤ 1 := by
    by_cases hi : i ∈ Finset.range (n + 1)
    · rw [ha_def, map_div₀]
      exact div_le_one_of_le₀ (hkmax i hi) zero_le
    · rw [Finset.mem_range, not_lt] at hi
      simp [ha_def, coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hi)]
  have haO' (i : ℕ) : a i ∈ O := (O.valuation_le_one_iff _).mp (haO i)
  have hak : O.valuation (a k) = 1 := by simp [ha_def, hck]
  have hrel : ∑ i ∈ Finset.range (n + 1), algebraMap K L (a i) * t ^ i = 0 := by
    have h := hpt
    rw [aeval_eq_sum_range] at h
    have hsum : ∑ i ∈ Finset.range (n + 1), algebraMap K L (a i) * t ^ i =
        (algebraMap K L (p.coeff k))⁻¹ * ∑ i ∈ Finset.range (n + 1), p.coeff i • t ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [ha_def, Algebra.smul_def, div_eq_mul_inv, map_mul, map_inv₀]
      ring
    rw [hsum, ht_def, h, mul_zero]
  -- `j` is the least index with `aⱼ` a unit of `O`
  have hex : ∃ i, O.valuation (a i) = 1 := ⟨k, hak⟩
  set j := Nat.find hex
  have hj : O.valuation (a j) = 1 := Nat.find_spec hex
  have hjn : j ≤ n := (Nat.find_min' hex hak).trans (Finset.mem_range_succ_iff.mp hk)
  have hlt {i : ℕ} (hi : i < j) : O.valuation (a i) < 1 :=
    lt_of_le_of_ne (haO i) (Nat.find_min hex hi)
  set u := ∑ i ∈ Finset.Ico j (n + 1), algebraMap K L (a i) * t ^ (i - j) with hu_def
  set s := ∑ i ∈ Finset.range j, algebraMap K L (a i) * x ^ (j - i) with hs_def
  -- the two expressions for `u`
  have hus : u = -s := by
    refine eq_neg_of_add_eq_zero_left (mul_left_cancel₀ (pow_ne_zero j ht0) ?_)
    rw [mul_zero, ← hrel, ← Finset.sum_range_add_sum_Ico _ (hjn.trans n.le_succ), mul_add,
      add_comm, hu_def, hs_def, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hij := (Finset.mem_range.mp hi).le
      have htj : t ^ j = t ^ i * t ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
      rw [mul_left_comm, htj, mul_assoc, ← mul_pow, htx, one_pow, mul_one]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.mp hi).1]
  refine ⟨u, ?_, ?_, fun W hW ↦ ?_⟩
  · -- `u = -s` is a nonunit of `A`
    rw [mem_nonunits_iff, hus, Valuation.map_neg]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi ↦ ?_
    rw [map_mul, map_pow]
    exact mul_lt_one_of_lt_of_le (hnon (hlt (Finset.mem_range.mp hi)))
      (pow_le_one' ((A.valuation_le_one_iff x).mpr hxA) _)
  · -- `u ≡ aⱼ` modulo the nonunits of `B`
    rw [hu_def, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero,
      mul_one, Valuation.map_add_eq_of_lt_left, valuation_algebraMap_eq_one hB hj]
    rw [valuation_algebraMap_eq_one hB hj]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi ↦ ?_
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [map_mul, map_pow]
    rw [mul_comm]
    exact mul_lt_one_of_lt_of_le (pow_lt_one₀ zero_le htB (by omega))
      ((B.valuation_le_one_iff _).mpr (hB (haO' i)))
  · -- every valuation subring over `O` contains `x` or `t`, hence `u`
    rcases W.mem_or_inv_mem x with hxW | htW
    · rw [hus]
      exact W.neg_mem _ (W.sum_mem fun i _ ↦ W.mul_mem _ _ (hW (haO' i)) (W.pow_mem hxW _))
    · exact W.sum_mem fun i _ ↦ W.mul_mem _ _ (hW (haO' i)) (W.pow_mem htW _)

variable [Algebra.IsAlgebraic K L]

/-- **Extensions of a valuation subring to an algebraic extension are incomparable.** If `A ≤ B`
are valuation subrings of `L` with the same restriction to `K`, then `A = B`. -/
theorem eq_of_le_of_comap_eq {A B : ValuationSubring L} (hAB : A ≤ B)
    (h : A.comap (algebraMap K L) = B.comap (algebraMap K L)) : A = B := by
  by_contra hne
  obtain ⟨x, hxB, hxA⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hAB hne)
  obtain ⟨u, hu, hu1, -⟩ := exists_of_mem_of_notMem (O := B.comap (algebraMap K L)) le_rfl
    h.ge (Algebra.IsAlgebraic.isAlgebraic x) hxB hxA
  exact ((A.mem_nonunits_iff).mp (nonunits_le_nonunits.mpr hAB hu)).ne hu1

/-- **Separating two extensions of a valuation subring.** Let `A ≠ B` be valuation subrings of an
algebraic extension `L` of `K` with the same restriction `O` to `K`. Some `u ∈ L` is a nonunit
of `A` and a unit of `B`, and lies in every valuation subring of `L` whose restriction to `K`
contains `O` (equivalently, `u` is integral over `O`). -/
theorem exists_mem_nonunits_valuation_eq_one {A B : ValuationSubring L} (hAB : A ≠ B)
    (h : A.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    ∃ u : L, u ∈ A.nonunits ∧ B.valuation u = 1 ∧
      ∀ W : ValuationSubring L, A.comap (algebraMap K L) ≤ W.comap (algebraMap K L) → u ∈ W := by
  obtain ⟨x, hxA, hxB⟩ :=
    IsConcreteLE.not_le_iff_exists.mp fun hle ↦ hAB (eq_of_le_of_comap_eq hle h)
  exact exists_of_mem_of_notMem le_rfl h.le (Algebra.IsAlgebraic.isAlgebraic x) hxA hxB

/-- **Separating finitely many extensions of a valuation subring.** For a finite set `S` of
valuation subrings of an algebraic extension `L` of `K`, all restricting to `O`, there is a family
`e` of elements of `L` such that `e A` is a unit of `A` and a nonunit of every other member of
`S`. -/
theorem exists_valuation_eq_one_and_lt_one (O : ValuationSubring K)
    (S : Finset (ValuationSubring L)) (hS : ∀ A ∈ S, A.comap (algebraMap K L) = O) :
    ∃ e : ValuationSubring L → L,
      ∀ A ∈ S, A.valuation (e A) = 1 ∧ ∀ B ∈ S, B ≠ A → B.valuation (e A) < 1 := by
  classical
  have hsep : ∀ A B : ValuationSubring L, ∃ u : L, A ∈ S → B ∈ S → B ≠ A →
      u ∈ B.nonunits ∧ A.valuation u = 1 ∧
        ∀ W : ValuationSubring L, O ≤ W.comap (algebraMap K L) → u ∈ W := by
    intro A B
    by_cases hAB : A ∈ S ∧ B ∈ S ∧ B ≠ A
    · obtain ⟨hA, hB, hne⟩ := hAB
      obtain ⟨u, hu⟩ := exists_mem_nonunits_valuation_eq_one hne ((hS B hB).trans (hS A hA).symm)
      exact ⟨u, fun _ _ _ ↦ by simpa only [hS B hB] using hu⟩
    · exact ⟨0, fun hA hB hne ↦ (hAB ⟨hA, hB, hne⟩).elim⟩
  choose u hu using hsep
  refine ⟨fun A ↦ ∏ B ∈ S.erase A, u A B, fun A hA ↦ ⟨?_, fun B hB hBA ↦ ?_⟩⟩
  · dsimp only
    rw [map_prod]
    exact Finset.prod_eq_one fun B hB ↦
      (hu A B hA (Finset.mem_of_mem_erase hB) (Finset.ne_of_mem_erase hB)).2.1
  · dsimp only
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hBA, hB⟩), map_mul]
    refine mul_lt_one_of_lt_of_le ((B.mem_nonunits_iff).mp (hu A B hA hB hBA).1) ?_
    rw [map_prod]
    refine Finset.prod_le_one fun C hC ↦ (B.valuation_le_one_iff _).mpr ?_
    have hC' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    exact (hu A C hA hC' (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hC))).2.2 B (hS B hB).ge

end ValuationSubring

namespace Valuation

/-- **Elements each dominating for its own valuation are linearly independent.** Let `v i` be
valuations on an algebra `C` over a field `K` with `v i ≤ 1` on a valuation subring `O` of `K`. If
`v i (e i) ≠ 0` and `v i (e j) < v i (e i)` for `j ≠ i`, then `e` is linearly independent over
`K`. -/
theorem linearIndependent_of_map_lt {K C : Type*} [Field K] [Ring C] [Algebra K C]
    {O : ValuationSubring K} {ι : Type*} [Finite ι] {Γ : ι → Type*}
    [∀ i, LinearOrderedCommMonoidWithZero (Γ i)] (v : ∀ i, Valuation C (Γ i))
    (hO : ∀ i, ∀ a ∈ O, v i (algebraMap K C a) ≤ 1) {e : ι → C} (he : ∀ i, v i (e i) ≠ 0)
    (hlt : ∀ i j, j ≠ i → v i (e j) < v i (e i)) : LinearIndependent K e := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra! hne
  obtain ⟨i₀, hi₀⟩ := hne
  -- a coefficient `g k` dividing all the others in `O`
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨k, hk⟩ := Finite.exists_max fun i ↦ O.valuation (g i)
  have hgk : g k ≠ 0 := by
    intro h
    have := hk i₀
    rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₀ this
  have hO' (i : ι) : g i / g k ∈ O := by
    rw [← O.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hk i) zero_le
  -- after dividing by `g k`, the summand `e k` dominates for `v k`
  have hsum : e k + ∑ i ∈ Finset.univ.erase k, (g i / g k) • e i = 0 := by
    have h := congrArg ((g k)⁻¹ • ·) hg
    simp only [smul_zero, Finset.smul_sum, smul_smul] at h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), inv_mul_cancel₀ hgk, one_smul] at h
    simpa only [div_eq_inv_mul] using h
  have hlt' : v k (∑ i ∈ Finset.univ.erase k, (g i / g k) • e i) < v k (e k) := by
    refine Valuation.map_sum_lt _ (he k) fun i hi ↦ ?_
    rw [Algebra.smul_def, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hO k _ (hO' i)))
      (hlt k i (Finset.ne_of_mem_erase hi))
  have := (v k).map_add_eq_of_lt_left hlt'
  rw [hsum, map_zero] at this
  exact he k this.symm

end Valuation
