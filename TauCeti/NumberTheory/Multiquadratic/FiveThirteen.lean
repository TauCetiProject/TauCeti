/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.GroupTheory.Exponent
import Mathlib.Tactic.FinCases
import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Radicands
import TauCeti.NumberTheory.Multiquadratic.Subfield.Classification

/-!
# Galois structure and quadratic subfields of `ℚ(√5, √13)`

Let `L` be a field of characteristic zero generated over `ℚ` by `s` and `t` with `s² = 5` and
`t² = 13`. Because `5` and `13` are distinct primes, their nonempty subset products are nonsquares
in `ℚ`, so the multiquadratic structure theory gives:

* `L/ℚ` is abelian Galois (`isAbelianGalois_five_thirteen`),
* `Gal(L/ℚ)` has exponent dividing `2` (`aut_exponent_dvd_two_five_thirteen`),
* the quadratic intermediate fields of `L/ℚ` are precisely `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯`
  (`finrank_eq_two_iff_five_thirteen`), and
* these three quadratic subfields are pairwise distinct (`adjoin_five_thirteen_ne`).

These are purely field-theoretic facts independent of class field theory; they are consumed by the
biquadratic Artin-tower worked example in
`TauCeti.NumberTheory.ClassFieldTheory.Global.Tower.Examples`.

## Main results

* `TauCeti.Multiquadratic.isAbelianGalois_five_thirteen`: `ℚ(√5, √13)/ℚ` is abelian Galois.
* `TauCeti.Multiquadratic.aut_exponent_dvd_two_five_thirteen`: `Monoid.exponent (L ≃ₐ[ℚ] L) ∣ 2`.
* `TauCeti.Multiquadratic.finrank_eq_two_iff_five_thirteen`: classification of the three quadratic
  subfields `ℚ⟮s⟯`, `ℚ⟮t⟯`, and `ℚ⟮s * t⟯`.
* `TauCeti.Multiquadratic.adjoin_five_thirteen_ne`: pairwise distinctness of `ℚ⟮s⟯`, `ℚ⟮t⟯`, and
  `ℚ⟮s * t⟯`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {L : Type*} [Field L] [CharZero L] {s t : L}

/-- The pair `![s, t]` satisfies the rational radicand equations for `![5, 13]`. -/
private lemma sq_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) :
    ∀ i, (![s, t] : Fin 2 → L) i ^ 2 = algebraMap ℚ L ((![5, 13] : Fin 2 → ℕ) i : ℚ) := by
  intro i
  fin_cases i <;> simp [hs, ht]

/-- Square-class independence of the prime radicands `![5, 13]`. -/
private lemma indep_five_thirteen :
    ∀ S : Finset (Fin 2), S.Nonempty → ¬ IsSquare (∏ i ∈ S, ((![5, 13] : Fin 2 → ℕ) i : ℚ)) :=
  not_isSquare_prod_primes_of_injective ![5, 13] (by decide) (by decide)

/-- A field generated over `ℚ` by square roots of `5` and `13` is abelian Galois over `ℚ`. -/
theorem isAbelianGalois_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤) :
    IsAbelianGalois ℚ L :=
  have hadj : IntermediateField.adjoin ℚ (Set.range (![s, t] : Fin 2 → L)) = ⊤ :=
    Matrix.range_cons_cons_empty s t ![] ▸ hst
  have := isGalois_of_adjoin_eq_top (sq_five_thirteen hs ht) hadj
  have := isMulCommutative_of_adjoin_eq_top (sq_five_thirteen hs ht) hadj
  {}

/-- In `L = ℚ(√5, √13)`, the Galois group `Gal(L/ℚ)` has exponent dividing `2`. -/
theorem aut_exponent_dvd_two_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤) :
    Monoid.exponent (L ≃ₐ[ℚ] L) ∣ 2 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one
    (aut_pow_two_eq_one_of_adjoin_eq_top
      (sq_five_thirteen hs ht) (Matrix.range_cons_cons_empty s t ![] ▸ hst))

/-- **Classification of the quadratic subfields of `ℚ(√5, √13)`.** If `L` is generated over `ℚ` by
square roots `s` of `5` and `t` of `13`, then an intermediate field `E` of `L/ℚ` has degree `2` over
`ℚ` if and only if `E = ℚ⟮s⟯`, `E = ℚ⟮t⟯`, or `E = ℚ⟮s * t⟯`. -/
theorem finrank_eq_two_iff_five_thirteen (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) (hst : ℚ⟮s, t⟯ = ⊤)
    (E : IntermediateField ℚ L) :
    Module.finrank ℚ E = 2 ↔ E = ℚ⟮s⟯ ∨ E = ℚ⟮t⟯ ∨ E = ℚ⟮s * t⟯ := by
  have hroot := sq_five_thirteen hs ht
  constructor
  · intro hE
    obtain ⟨S, hS, rfl⟩ := exists_finset_of_finrank_two_of_adjoin_eq_top
      hroot indep_five_thirteen (Matrix.range_cons_cons_empty s t ![] ▸ hst) E hE
    rcases (by decide : ∀ S : Finset (Fin 2), S.Nonempty →
        S = {0} ∨ S = {1} ∨ S = {0, 1}) S hS with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by simp))
  · have hfin {r : L} (S : Finset (Fin 2)) (hS : S.Nonempty)
        (hr : ∏ i ∈ S, (![s, t] : Fin 2 → L) i = r) :
        Module.finrank ℚ ℚ⟮r⟯ = 2 :=
      hr ▸ IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare
        (prod_root_sq hroot S) (indep_five_thirteen S hS)
    rintro (rfl | rfl | rfl)
    · exact hfin {0} (Finset.singleton_nonempty 0) (by simp)
    · exact hfin {1} (Finset.singleton_nonempty 1) (by simp)
    · exact hfin {0, 1} ⟨0, by simp⟩ (by simp)

/-- **Distinctness of the three quadratic subfields of `ℚ(√5, √13)`.** The subfields `ℚ⟮s⟯`, `ℚ⟮t⟯`,
and `ℚ⟮s * t⟯` are pairwise distinct. -/
theorem adjoin_five_thirteen_ne (hs : s ^ 2 = 5) (ht : t ^ 2 = 13) :
    ℚ⟮s⟯ ≠ ℚ⟮t⟯ ∧ ℚ⟮s⟯ ≠ ℚ⟮s * t⟯ ∧ ℚ⟮t⟯ ≠ ℚ⟮s * t⟯ := by
  have hinj := adjoin_prod_root_injective (sq_five_thirteen hs ht) indep_five_thirteen
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (by decide : ({0} : Finset (Fin 2)) ≠ {1}) (hinj (by simpa using h))
  · exact (by decide : ({0} : Finset (Fin 2)) ≠ {0, 1}) (hinj (by simpa using h))
  · exact (by decide : ({1} : Finset (Fin 2)) ≠ {0, 1}) (hinj (by simpa using h))

end TauCeti.Multiquadratic
