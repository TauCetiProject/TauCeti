/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver
import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic

/-!
# Completeness of the cyclotomic Dixon solver

Every finite group admits an exact cyclotomic character-table certificate. Its finitely many
central coefficients have a common bound, and there are arbitrarily large good Dixon primes.
At a prime beyond twice that bound, the existing reconstruction theorem finds the table.
The assembled prime search therefore succeeds after a finite number of steps, and its answer
stays the same for every larger search budget.

The coefficient bound here is existential: it proves termination without a quantitative
estimate for the running time or a prescribed prime.
-/

public section

namespace TauCeti.ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  (d : ClassData G) (e : ℕ) (he : e = Monoid.exponent G)

include he

/-- Every finite group has ordinary and central tables over the exact cyclotomic integers at
its exponent which satisfy the executable certificate. -/
theorem exists_isCyclotomicCharacterTableSpec :
    ∃ (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
      (degree : Fin d.numClasses → ℕ),
      d.IsCyclotomicCharacterTableSpec e omega table degree := by
  classical
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  let τ := finCongr d.numClasses_eq_card_conjClasses
  choose omega homega using fun i k ↦ centralCharacterTable_mem_range_complexEmbedding
    e he (τ i) (d.classOf k)
  choose table htable using fun i k ↦ characterTable_mem_range_complexEmbedding
    e he (τ i) (d.classOf k)
  refine ⟨omega, table, fun i ↦ characterDegree ℂ (τ i), ?_⟩
  -- Reflect the exact identities through the injective complex embedding.
  refine
    { central_one := fun i ↦ Cyclotomic.complexEmbedding_injective ?_
      central_eigen := fun i ↦ ?_
      degree_pos := fun i ↦ characterDegree_pos ℂ (τ i)
      degree_dvd := fun i ↦ ?_
      sum_degree_sq := ?_
      degree_mul_central := fun i k ↦ Cyclotomic.complexEmbedding_injective ?_
      row_orthogonal := fun i j ↦ Cyclotomic.complexEmbedding_injective ?_ }
  · simp only [homega, d.classOf_index, centralCharacterTable_mk_one, map_one]
  · have hrow : d.IsModularEigenrow
        (fun k ↦ centralCharacterTable ℂ G (τ i) (d.classOf k)) := by
      apply (d.isModularEigenrow_iff_isClassEigenrow _).mpr
      have hindex : d.reindexModularRow
          (fun k ↦ centralCharacterTable ℂ G (τ i) (d.classOf k)) =
          centralCharacterTable ℂ G (τ i) := by
        funext C
        obtain ⟨k, rfl⟩ := d.equivConjClasses.surjective C
        rw [d.equivConjClasses_apply, d.reindexModularRow_classOf]
      rw [hindex]
      exact isClassEigenrow_centralCharacterTable (τ i)
    apply (d.isModularEigenrow_iff _).mpr
    intro a b
    apply Cyclotomic.complexEmbedding_injective
    simpa only [map_sum, map_mul, map_natCast, homega] using
      (d.isModularEigenrow_iff _).mp hrow a b
  · simpa only [Nat.card_eq_fintype_card] using characterDegree_dvd_card ℂ (τ i)
  · exact (Equiv.sum_comp τ fun i ↦ characterDegree ℂ (G := G) i ^ 2).trans
      (by simpa only [Nat.card_eq_fintype_card] using sum_characterDegree_sq_eq_card ℂ (G := G))
  · simpa only [map_mul, map_natCast, homega, htable, d.card_classFinset, mul_comm] using
      centralCharacterTable_mul_characterDegree (k := ℂ) (τ i) (d.classOf k)
  · have horth := card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj (τ i) (τ j)
    have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hsum := (inv_mul_eq_iff_eq_mul₀ hG).mp horth
    have hindex := Equiv.sum_comp d.equivConjClasses fun C ↦
      (Nat.card C.carrier : ℂ) * characterTable ℂ G (τ i) C *
        star (characterTable ℂ G (τ j) C)
    simp only [starRingEnd_apply] at hsum
    rw [← hindex] at hsum
    simpa only [map_sum, map_mul, map_natCast, Cyclotomic.complexEmbedding_star,
      htable, apply_ite, map_zero, d.card_classFinset, ← d.equivConjClasses_apply,
      τ.injective.eq_iff, Nat.card_eq_fintype_card, mul_ite, mul_one, mul_zero] using hsum

/-- The assembled cyclotomic Dixon solver returns an exact certified table after finitely many
prime-search steps, and returns the same table for every larger budget. -/
theorem exists_characterTableDixon?_eq_some :
    ∃ (fuel : ℕ) (output : d.CyclotomicCharacterTableData e),
      ∀ fuel' ≥ fuel, d.characterTableDixon? e he fuel' = some output := by
  classical
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨omega, table, degree, hspec⟩ := d.exists_isCyclotomicCharacterTableSpec e he
  -- A bound on the finite family of actual coefficients suffices; no sharp estimate is needed.
  obtain ⟨B, hB⟩ := Finite.exists_le fun x :
      Fin d.numClasses × Fin d.numClasses × Fin e.totient ↦
      2 * ((omega x.1 x.2.1).coeff x.2.2).natAbs
  obtain ⟨p, hprime, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one
    (k := e) (max B (max (Nat.card G) (2 * Nat.sqrt (Nat.card G)))) (NeZero.ne e)
  have hgood : IsGoodDixonPrime G p :=
    { prime := hprime
      not_dvd_natCard := fun hdvd ↦ (not_le_of_gt
        (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hgt))
          (Nat.le_of_dvd Nat.card_pos hdvd)
      exponent_dvd := he ▸ (Nat.modEq_iff_dvd' hprime.one_lt.le).mp hmod.symm
      two_mul_sqrt_lt := lt_of_le_of_lt
        (le_trans (le_max_right _ _) (le_max_right _ _)) hgt }
  have hfuel : p ≤ e * p + 1 := by nlinarith [NeZero.pos e]
  obtain ⟨q, hq, hqp⟩ := DixonPrimeData.exists_mem_candidates
    (he := he) (hn := Nat.card_eq_fintype_card.symm) hgood hfuel
  have hsolve := d.isSome_dixonCyclotomicCharacterTable_of_spec e he q omega table degree hspec
    (fun i k l ↦ by
      rw [hqp]
      exact lt_of_le_of_lt (hB (i, k, l)) (lt_of_le_of_lt (le_max_left _ _) hgt))
  have hsome : (d.characterTableDixon? e he p).isSome :=
    (d.isSome_characterTableDixon?_iff e he p).mpr ⟨q, hq, hsolve⟩
  obtain ⟨output, houtput⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨p, output, fun _ hle ↦ d.characterTableDixon?_eq_some_of_le e he hle houtput⟩

end TauCeti.ClassData
