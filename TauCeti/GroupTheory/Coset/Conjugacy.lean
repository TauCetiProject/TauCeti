/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Table
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugacy tests from certified coset tables

A certified coset table whose subgroup words commute with `x` covers the cosets of the
actual centralizer of `x`. Consequently every conjugate of `x` is obtained by conjugating
by one of the table's representative words. Testing those words decides whether `x` and `y`
are conjugate, including a sound negative answer.

The subgroup words need only centralize `x`: they need not generate its full centralizer,
and the table may repeat cosets. Neither finiteness of the ambient group nor its order is
required. All word equalities and comparisons concern the actual group. A failed search
among the representatives without certified coverage does not establish nonconjugacy.

This complements centralizer recognition and class-size exhaustion: representative pairs can
be certified nonconjugate before their centralizer indices are used in the class equation.
The table's deduction certificate avoids checking each generator transition as a separate
ambient-group equality.

## References

* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*,
  Chapman & Hall/CRC, 2005, Chapter 5 (coset enumeration).
-/

public section

namespace TauCeti.CosetTable

variable {m k : ℕ} (T : CosetTable m k) {G : Type*} [Group G] (g : Fin m → G)

/-- Test whether some representative word of the table conjugates `x` to `y`.
Without a coverage certificate, a negative answer need not imply nonconjugacy.
The body is exposed so that importing modules can compute the finite test. -/
@[expose]
def checkConjugacy [DecidableEq G] (x y : G) : Bool :=
  decide (∃ i : Fin k, ((T.word i).map g).prod * x * (((T.word i).map g).prod)⁻¹ = y)

/-- Acceptance gives an actual conjugating representative word, without any table hypotheses. -/
@[simp]
theorem checkConjugacy_eq_true [DecidableEq G] (x y : G) :
    T.checkConjugacy g x y = true ↔
      ∃ i : Fin k, ((T.word i).map g).prod * x * (((T.word i).map g).prod)⁻¹ = y := by
  simp [checkConjugacy]

variable {T g} {rels stab : List (List (Fin m))}
  {cert : List (Fin k × List (Fin m))}

/-- A certified table with subgroup words centralizing `x` contains a conjugator for every
conjugate of `x`. The subgroup words need not generate the entire centralizer. -/
theorem isConj_iff_exists_of_check (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    {x y : G} (hstab : ∀ r ∈ stab, (r.map g).prod * x = x * (r.map g).prod) :
    IsConj x y ↔
      ∃ i : Fin k, ((T.word i).map g).prod * x * (((T.word i).map g).prod)⁻¹ = y := by
  constructor
  · intro hxy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    obtain ⟨i, hmem⟩ := T.exists_inv_word_mul_mem hg hT hrels
      (H := Subgroup.centralizer {x})
      (fun r hr ↦ Subgroup.mem_centralizer_singleton_iff.mpr (hstab r hr)) c
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hmem
    have heq := congrArg (fun z ↦ ((T.word i).map g).prod * z * c⁻¹) hcomm
    refine ⟨i, ?_⟩
    simpa [mul_assoc, hc] using heq.symm
  · rintro ⟨i, hi⟩
    exact isConj_iff.mpr ⟨_, hi⟩

/-- With a certified centralizing coset cover, the finite conjugacy test is exact. -/
theorem checkConjugacy_eq_true_iff_of_check [DecidableEq G]
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    {x y : G} (hstab : ∀ r ∈ stab, (r.map g).prod * x = x * (r.map g).prod) :
    T.checkConjugacy g x y = true ↔ IsConj x y :=
  (T.checkConjugacy_eq_true g x y).trans
    (isConj_iff_exists_of_check hg hT hrels hstab).symm

/-- A rejected conjugacy test proves nonconjugacy when the table's centralizing cover
has been certified. No decidability of conjugacy in the ambient group is assumed. -/
theorem checkConjugacy_eq_false_iff_of_check [DecidableEq G]
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    {x y : G} (hstab : ∀ r ∈ stab, (r.map g).prod * x = x * (r.map g).prod) :
    T.checkConjugacy g x y = false ↔ ¬ IsConj x y := by
  rw [Bool.eq_false_iff]
  exact not_congr (checkConjugacy_eq_true_iff_of_check hg hT hrels hstab)

end TauCeti.CosetTable
