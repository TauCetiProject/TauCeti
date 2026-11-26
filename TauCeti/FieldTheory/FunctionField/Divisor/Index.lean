/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# The index of a function field

The *index* of an algebraic function field `F / k` is the least positive degree of a divisor.
The degrees of divisors form a subgroup of `ℤ`, and for a function field this subgroup is
nonzero (every place has positive degree), so the index is its positive generator: a degree
occurs exactly when the index divides it. A rational place, or an algebraically closed constant
field, gives index one; in genus at least two, index one need not produce a rational place.

## Main definitions

* `TauCeti.index`: the least positive degree of a divisor of `F / k`.

## Main results

* `TauCeti.Divisor.range_degree`: the degrees of divisors are the multiples of the index.
* `TauCeti.index_dvd_iff_exists_degree_eq`, `TauCeti.index_dvd_degree`: an integer is the degree
  of a divisor exactly when the index divides it.
* `TauCeti.index_eq_one_iff`: index one means a divisor of degree one;
  `TauCeti.Place.index_eq_one_of_degree_eq_one` and `TauCeti.index_eq_one_of_isAlgClosed` are the
  two standard sources.

## References

* B. Poonen, *Gonality of modular curves in characteristic `p`*, Math. Res. Lett. 14 (2007),
  Appendix A.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Remark 1.6.4.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The **index** of `F / k`: the least positive degree of a divisor.

For an algebraic function field the degrees of divisors are exactly the multiples of the index
(`TauCeti.Divisor.range_degree`), so the index is the positive generator of the image of the
degree map. It is one when a rational place exists. Outside the function-field setting the set
of positive degrees can be empty, and the index is then the junk value zero. -/
noncomputable def index (k F : Type*) [Field k] [Field F] [Algebra k F] : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n}

/-- **The index is at most every positive divisor degree.** -/
theorem index_le_of_degree_eq {D : Divisor k F} {n : ℕ} (hn : 0 < n)
    (hD : Divisor.degree D = n) : index k F ≤ n :=
  Nat.sInf_le ⟨hn, D, hD⟩

/-- A divisor of positive degree makes the index positive and attained. -/
private theorem index_mem_of_degree_pos {D : Divisor k F} (hD : 0 < Divisor.degree D) :
    0 < index k F ∧ ∃ D : Divisor k F, Divisor.degree D = index k F :=
  Nat.sInf_mem (s := {n : ℕ | 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n})
    ⟨(Divisor.degree D).toNat, by omega, D, by omega⟩

/-- A function field has a divisor of positive degree: the divisor of any place. -/
private theorem exists_degree_pos (hF : IsFunctionField k F) :
    ∃ D : Divisor k F, 0 < Divisor.degree D := by
  obtain ⟨P⟩ := Place.nonempty hF
  refine ⟨WeilDivisor.ofPoint P, ?_⟩
  have := P.one_le_degree_of_isFunctionField hF
  rw [Divisor.degree_ofPoint]
  omega

/-- **The index of a function field is positive.** -/
theorem index_pos (hF : IsFunctionField k F) : 0 < index k F :=
  (index_mem_of_degree_pos (exists_degree_pos hF).choose_spec).1

/-- **The index of a function field is attained** by the degree of some divisor. -/
theorem exists_degree_eq_index (hF : IsFunctionField k F) :
    ∃ D : Divisor k F, Divisor.degree D = index k F :=
  (index_mem_of_degree_pos (exists_degree_pos hF).choose_spec).2

/-- **The index generates the degrees**: the image of the degree map on divisors of a function
field is the subgroup of multiples of the index. -/
theorem Divisor.range_degree (hF : IsFunctionField k F) :
    (Divisor.degree (k := k) (F := F)).range = AddSubgroup.zmultiples (index k F : ℤ) := by
  -- The index is the least positive element of the range, hence generates it.
  obtain ⟨D₀, hD₀⟩ := exists_degree_eq_index hF
  have hpos := index_pos hF
  refine (AddSubgroup.zmultiples_eq_of_isLeast_mem_and_pos (H := Divisor.degree.range)
    ⟨⟨⟨D₀, hD₀⟩, by omega⟩, fun g ⟨⟨D, hD⟩, hg⟩ ↦ ?_⟩).symm
  have := index_le_of_degree_eq (n := g.toNat) (by omega) (by rw [hD]; omega)
  omega

/-- **The degrees of divisors are the multiples of the index**: an integer is the degree of a
divisor of a function field exactly when the index divides it. -/
theorem index_dvd_iff_exists_degree_eq (hF : IsFunctionField k F) {d : ℤ} :
    (index k F : ℤ) ∣ d ↔ ∃ D : Divisor k F, Divisor.degree D = d := by
  rw [← Int.mem_zmultiples_iff, ← Divisor.range_degree hF, AddMonoidHom.mem_range]

/-- **The index divides the degree of every divisor** of a function field. -/
theorem index_dvd_degree (hF : IsFunctionField k F) (D : Divisor k F) :
    (index k F : ℤ) ∣ Divisor.degree D :=
  (index_dvd_iff_exists_degree_eq hF).mpr ⟨D, rfl⟩

/-- The index of a function field divides the degree of every place. -/
theorem Place.index_dvd_degree (hF : IsFunctionField k F) (P : Place k F) :
    index k F ∣ P.degree := by
  have := TauCeti.index_dvd_degree hF (WeilDivisor.ofPoint P)
  rw [Divisor.degree_ofPoint] at this
  exact_mod_cast this

/-- **Index one means a divisor of degree one.** No function-field hypothesis is needed. -/
theorem index_eq_one_iff : index k F = 1 ↔ ∃ D : Divisor k F, Divisor.degree D = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨D, hD⟩ ↦ ?_⟩
  · have hne : {n : ℕ | 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n}.Nonempty :=
      Nat.nonempty_of_pos_sInf (h ▸ Nat.one_pos : 0 < index k F)
    obtain ⟨-, D, hD⟩ : index k F ∈ _ := Nat.sInf_mem hne
    exact ⟨D, by rw [hD, h, Nat.cast_one]⟩
  · have := (index_mem_of_degree_pos (D := D) (by omega)).1
    have := index_le_of_degree_eq Nat.one_pos (by rw [hD, Nat.cast_one])
    omega

/-- **A rational place gives index one.** The converse can fail in genus at least two. -/
theorem Place.index_eq_one_of_degree_eq_one {P : Place k F} (hP : P.degree = 1) :
    index k F = 1 :=
  index_eq_one_iff.mpr ⟨WeilDivisor.ofPoint P, by rw [Divisor.degree_ofPoint, hP, Nat.cast_one]⟩

/-- **Over an algebraically closed constant field the index is one**, since every place is
rational. -/
theorem index_eq_one_of_isAlgClosed [IsAlgClosed k] (hF : IsFunctionField k F) :
    index k F = 1 := by
  obtain ⟨P⟩ := Place.nonempty hF
  exact Place.index_eq_one_of_degree_eq_one
    (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF)

end TauCeti
