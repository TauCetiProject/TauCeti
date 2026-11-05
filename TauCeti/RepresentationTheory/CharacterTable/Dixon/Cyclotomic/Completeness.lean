/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Bounds
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver

/-!
# Completeness of the cyclotomic Dixon solver

Every finite group admits an exact cyclotomic character-table certificate whose complex image is
the labeled character table and whose central coefficients are bounded by
`TauCeti.centralCoefficientBound G e`. At every strong Dixon prime, one beyond twice that bound,
the existing reconstruction theorem finds the table. Such primes exist, so the assembled prime
search succeeds after a finite number of steps, and its answer stays the same for every larger
search budget.

Consequently the search with the least successful budget is a total, executable algorithm,
`TauCeti.ClassData.characterTableDixon`. Embedded in `ℂ`, its table is the character table of
`G` up to a permutation of the rows.

## Main definitions

* `TauCeti.ClassData.characterTableDixon`: the total Burnside--Dixon--Schneider algorithm.

## Main results

* `TauCeti.ClassData.exists_bounded_exact_character_table`: the bounded exact certificate.
* `TauCeti.ClassData.isSome_dixonCyclotomicCharacterTable_of_centralCoefficientBound`: the solver
  succeeds at every strong Dixon prime.
* `TauCeti.ClassData.isSome_characterTableDixon?_of_centralCoefficientBound`: the budgeted search
  succeeds as soon as it reaches a strong Dixon prime.
* `TauCeti.ClassData.exists_characterTableDixon?_eq_some`: the budgeted search succeeds.
* `TauCeti.ClassData.characterTableDixon_eq_of_characterTableDixon?_eq_some`: every successful
  budgeted search returns the table of the total algorithm.
* `TauCeti.ClassData.isCharacterTableSpec_characterTableDixon`: the computed table satisfies the
  character-table specification, so it is the character table up to a permutation of the rows.
-/

public section

namespace TauCeti.ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  (d : ClassData G) (e : ℕ) (he : e = Monoid.exponent G)

include he

omit he in
/-- Exact tables whose complex images are the labeled central and ordinary character tables pass
the executable certificate, with the character degrees as the degree vector. -/
theorem isCyclotomicCharacterTableSpec_of_complexEmbedding_eq [NeZero e]
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
    (homega : ∀ i k, Cyclotomic.complexEmbedding (omega i k) = centralCharacterTable ℂ G
      (finCongr d.numClasses_eq_card_conjClasses i) (d.classOf k))
    (htable : ∀ i k, Cyclotomic.complexEmbedding (table i k) = characterTable ℂ G
      (finCongr d.numClasses_eq_card_conjClasses i) (d.classOf k)) :
    d.IsCyclotomicCharacterTableSpec e omega table
      fun i ↦ characterDegree ℂ (finCongr d.numClasses_eq_card_conjClasses i) := by
  classical
  let τ := finCongr d.numClasses_eq_card_conjClasses
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

/-- **The bounded exact certificate.** Every finite group has ordinary and central tables over
the exact cyclotomic integers at its exponent which satisfy the executable certificate, whose
ordinary table embeds in `ℂ` as the labeled character table, and whose central coefficients are
bounded by `TauCeti.centralCoefficientBound G e`. -/
theorem exists_bounded_exact_character_table :
    haveI : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
    ∃ out : d.CyclotomicCharacterTableData e,
      d.IsCyclotomicCharacterTableSpec e out.omega out.table out.degree ∧
      d.complexTableOfCyclotomic e out.table = characterTable ℂ G ∧
      ∀ i k j, ((out.omega i k).coeff j).natAbs ≤ centralCoefficientBound G e := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  let τ := finCongr d.numClasses_eq_card_conjClasses
  choose table omega htable homega _ _ hbound using
    exists_exact_character_and_central_values (G := G) e he
  refine ⟨⟨fun i k ↦ omega (τ i) (d.classOf k), fun i k ↦ table (τ i) (d.classOf k),
    fun i ↦ characterDegree ℂ (τ i)⟩,
    d.isCyclotomicCharacterTableSpec_of_complexEmbedding_eq e (fun _ _ ↦ homega _ _)
      (fun _ _ ↦ htable _ _), ?_, fun _ _ _ ↦ hbound _ _ _⟩
  ext i C
  obtain ⟨i, rfl⟩ := τ.surjective i
  obtain ⟨k, rfl⟩ := d.equivConjClasses.surjective C
  rw [d.equivConjClasses_apply]
  exact (d.complexTableOfCyclotomic_apply_classOf e _ i k).trans (htable _ _)

/-- **The solver is complete at every strong Dixon prime.** The cyclotomic Dixon solver returns a
table at all Dixon prime data beyond twice the central coefficient bound, whatever the primitive
root chosen. The threshold is computable from the group order and exponent. -/
theorem isSome_dixonCyclotomicCharacterTable_of_centralCoefficientBound (q : DixonPrimeData G)
    (hq : 2 * centralCoefficientBound G e < q.p) :
    (d.dixonCyclotomicCharacterTable? e q).isSome = true := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨out, hspec, -, hbound⟩ := d.exists_bounded_exact_character_table e he
  apply d.isSome_dixonCyclotomicCharacterTable_of_spec e he q out.omega out.table out.degree hspec
  exact fun i k j ↦ (Nat.mul_le_mul_left 2 (hbound i k j)).trans_lt hq

/-- The prime search returns a table as soon as it reaches a strong Dixon prime, a good Dixon prime
beyond twice the central coefficient bound. -/
theorem isSome_characterTableDixon?_of_centralCoefficientBound {p fuel : ℕ}
    (hp : IsGoodDixonPrime G p) (hlt : 2 * centralCoefficientBound G e < p)
    (hfuel : p ≤ e * fuel + 1) : (d.characterTableDixon? e he fuel).isSome := by
  obtain ⟨q, hq, rfl⟩ := DixonPrimeData.exists_mem_candidates (he := he)
    (hn := Nat.card_eq_fintype_card.symm) hp hfuel
  exact (d.isSome_characterTableDixon?_iff e he fuel).mpr
    ⟨q, hq, d.isSome_dixonCyclotomicCharacterTable_of_centralCoefficientBound e he q hlt⟩

/-- The assembled cyclotomic Dixon solver returns an exact certified table after finitely many
prime-search steps, and returns the same table for every larger budget. -/
theorem exists_characterTableDixon?_eq_some :
    ∃ (fuel : ℕ) (output : d.CyclotomicCharacterTableData e),
      ∀ fuel' ≥ fuel, d.characterTableDixon? e he fuel' = some output := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨q, hq⟩ := exists_strongDixonPrime he
  have hfuel : q.p ≤ e * q.p + 1 := by nlinarith [NeZero.pos e]
  obtain ⟨output, houtput⟩ := Option.isSome_iff_exists.mp
    (d.isSome_characterTableDixon?_of_centralCoefficientBound e he q.isGoodDixonPrime hq hfuel)
  exact ⟨q.p, output, fun _ hle ↦ d.characterTableDixon?_eq_some_of_le e he hle houtput⟩

/-! ### The total algorithm

Completeness turns the budgeted search into a total function: the algorithm runs
`TauCeti.ClassData.characterTableDixon?` with budgets `0, 1, 2, …` and stops at the first one
at which it succeeds. -/

/-- **The Burnside--Dixon--Schneider algorithm.** It runs the prime search
`TauCeti.ClassData.characterTableDixon?` with the least budget at which it returns a table,
and returns that table. The search terminates by
`TauCeti.ClassData.exists_characterTableDixon?_eq_some`, so the result is total; it remains
executable, because finding the least budget only evaluates the search at increasing budgets. -/
def characterTableDixon : d.CyclotomicCharacterTableData e :=
  have h : ∃ fuel, (d.characterTableDixon? e he fuel).isSome :=
    (d.exists_characterTableDixon?_eq_some e he).imp fun fuel ⟨output, h⟩ ↦
      Option.isSome_iff_exists.mpr ⟨output, h fuel le_rfl⟩
  (d.characterTableDixon? e he (Nat.find h)).get (Nat.find_spec h)

/-- Whenever the budgeted search succeeds, it returns the table of the total algorithm. -/
theorem characterTableDixon?_eq_some_characterTableDixon {fuel : ℕ}
    (h : (d.characterTableDixon? e he fuel).isSome) :
    d.characterTableDixon? e he fuel = some (d.characterTableDixon e he) := by
  have hex : ∃ fuel, (d.characterTableDixon? e he fuel).isSome := ⟨fuel, h⟩
  exact d.characterTableDixon?_eq_some_of_le e he (Nat.find_min' hex h)
    (Option.some_get (Nat.find_spec hex)).symm

/-- A table returned by the budgeted search is the table of the total algorithm. -/
theorem characterTableDixon_eq_of_characterTableDixon?_eq_some {fuel : ℕ}
    {output : d.CyclotomicCharacterTableData e}
    (h : d.characterTableDixon? e he fuel = some output) :
    d.characterTableDixon e he = output :=
  Option.some_injective _ <| (d.characterTableDixon?_eq_some_characterTableDixon e he
    (Option.isSome_iff_exists.mpr ⟨output, h⟩)).symm.trans h

/-- The table of the Burnside--Dixon--Schneider algorithm passes the exact cyclotomic
certificate. -/
theorem isCyclotomicCharacterTableSpec_characterTableDixon :
    d.IsCyclotomicCharacterTableSpec e (d.characterTableDixon e he).omega
      (d.characterTableDixon e he).table (d.characterTableDixon e he).degree := by
  obtain ⟨fuel, output, h⟩ := d.exists_characterTableDixon?_eq_some e he
  rw [d.characterTableDixon_eq_of_characterTableDixon?_eq_some e he (h fuel le_rfl)]
  exact d.isCyclotomicCharacterTableSpec_of_characterTableDixon?_eq_some e he (h fuel le_rfl)

/-- **Correctness of the Burnside--Dixon--Schneider algorithm.** The table it computes, embedded
in `ℂ` and reindexed by the conjugacy classes, satisfies the complex character-table
specification; by `TauCeti.characterTable_unique_rows` it is therefore the character table of `G`
up to a permutation of the rows. -/
theorem isCharacterTableSpec_characterTableDixon :
    haveI : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
    IsCharacterTableSpec G (d.complexTableOfCyclotomic e (d.characterTableDixon e he).table) :=
  haveI : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  (d.isCyclotomicCharacterTableSpec_characterTableDixon e he).isCharacterTableSpec

end TauCeti.ClassData
