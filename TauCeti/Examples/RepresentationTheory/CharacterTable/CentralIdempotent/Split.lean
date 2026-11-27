/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RepresentationTheory.CharacterTable.CentralIdempotent.Split
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# Examples: central idempotents of characters over a splitting field

* The trivial character of `S₃` gives `(1/6) ∑_g g`.
* `C₂ = ℤˣ` over `ℚ₂`: the characters `1` and `t ↦ -1` give `e_± = (1 ± t)/2`, which are
  orthogonal idempotents with sum `1` (both characters stay irreducible over an algebraic closure
  of `ℚ₂`), and neither lies in the image of `ℤ₂[C₂]`.
-/

public section

open scoped MonoidAlgebra

open TauCeti.Representation

namespace TauCeti.Examples.SplitCentralIdempotent

-- The trivial character of `S₃` over `ℚ` gives `(1/6) ∑_g g`.
example (g : Equiv.Perm (Fin 3)) :
    (primitiveCentralIdempotent (Representation.trivial ℚ (Equiv.Perm (Fin 3)) ℚ)).coeff g =
      1 / 6 := by
  simp [Representation.char_trivial, Fintype.card_perm, Nat.factorial]

/-- The sign character `t ↦ -1` of `C₂ = ℤˣ` over `ℚ₂`. -/
noncomputable abbrev signCharacter : ℤˣ →* ℚ_[2]ˣ := Units.map (Int.castRingHom ℚ_[2])

noncomputable instance invertibleNatCardUnitsInt : Invertible (Nat.card ℤˣ : ℚ_[2]) :=
  invertibleOfNonzero (by simp [Nat.card_eq_fintype_card, Fintype.card_units_int])

/-- `e₊ = (1 + t)/2`, from the trivial character of `C₂ = ℤˣ` over `ℚ₂`. -/
noncomputable abbrev ePlus : MonoidAlgebra ℚ_[2] ℤˣ :=
  primitiveCentralIdempotent (Representation.ofLinearCharacter (1 : ℤˣ →* ℚ_[2]ˣ))

/-- `e₋ = (1 - t)/2`, from the sign character of `C₂ = ℤˣ` over `ℚ₂`. -/
noncomputable abbrev eMinus : MonoidAlgebra ℚ_[2] ℤˣ :=
  primitiveCentralIdempotent (Representation.ofLinearCharacter signCharacter)

-- The coefficients of `e₊` and `e₋` at `t = -1` are `1/2` and `-1/2`, at `1` both are `1/2`.
example : ePlus.coeff (-1) = 1 / 2 ∧ eMinus.coeff (-1) = -1 / 2 ∧
    ePlus.coeff 1 = 1 / 2 ∧ eMinus.coeff 1 = 1 / 2 := by
  simp only [primitiveCentralIdempotent_coeff, Representation.char_ofLinearCharacter, signCharacter,
    Nat.card_eq_fintype_card, Fintype.card_units_int]
  norm_num

instance (χ : ℤˣ →* ℚ_[2]ˣ) :
    ((Representation.ofLinearCharacter χ).baseChange (AlgebraicClosure ℚ_[2])).IsIrreducible :=
  Representation.isIrreducible_of_finrank_eq_one _ (by simp)

/-- The base changes of the trivial and sign characters to `ℚ₂^alg` are not isomorphic: their
characters differ at `t = -1`. -/
theorem isEmpty_equiv_baseChange :
    IsEmpty (((Representation.ofLinearCharacter (1 : ℤˣ →* ℚ_[2]ˣ)).baseChange
        (AlgebraicClosure ℚ_[2])).Equiv
      ((Representation.ofLinearCharacter signCharacter).baseChange (AlgebraicClosure ℚ_[2]))) := by
  refine ⟨fun φ ↦ ?_⟩
  have h := congrFun (Representation.char_iso φ) (-1)
  simp only [Representation.character_baseChange, Representation.char_ofLinearCharacter,
    signCharacter] at h
  norm_num at h

-- `e₊` and `e₋` are orthogonal.
example : ePlus * eMinus = 0 :=
  primitiveCentralIdempotent_mul_primitiveCentralIdempotent_of_baseChange _
    (AlgebraicClosure ℚ_[2]) _ isEmpty_equiv_baseChange

-- `e₊` is idempotent.
example : IsIdempotentElem ePlus :=
  isIdempotentElem_primitiveCentralIdempotent_of_baseChange _ (AlgebraicClosure ℚ_[2])

-- `e₊ + e₋ = 1`: the two characters are a complete list for `C₂`, which has two classes.
example : ePlus + eMinus = 1 := by
  have hcard : Nat.card (ConjClasses ℤˣ) = 2 := by
    rw [Nat.card_congr (Equiv.ofBijective ConjClasses.mk ⟨fun a b h ↦
      isConj_iff_eq.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h), ConjClasses.mk_surjective⟩).symm]
    simp [Fintype.card_units_int]
  have (i : Fin 2) : ((![Representation.ofLinearCharacter 1,
      Representation.ofLinearCharacter signCharacter] i : Representation ℚ_[2] ℤˣ ℚ_[2]).baseChange
        (AlgebraicClosure ℚ_[2])).IsIrreducible :=
    Representation.isIrreducible_of_finrank_eq_one _ (by simp)
  have h := sum_primitiveCentralIdempotent_of_baseChange (AlgebraicClosure ℚ_[2])
    (![Representation.ofLinearCharacter 1, Representation.ofLinearCharacter signCharacter] :
      Fin 2 → Representation ℚ_[2] ℤˣ ℚ_[2])
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact isEmpty_equiv_baseChange
      · exact ⟨fun φ ↦ isEmpty_equiv_baseChange.false φ.symm⟩
      · exact absurd rfl hij)
    (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

-- Neither `e₊` nor `e₋` lies in the image of `ℤ₂[C₂]`: their coefficient `± 1/2` at `1` has norm
-- `2 > 1`.
example : ePlus ∉ Set.range (MonoidAlgebra.mapRingHom ℤˣ (algebraMap ℤ_[2] ℚ_[2])) ∧
    eMinus ∉ Set.range (MonoidAlgebra.mapRingHom ℤˣ (algebraMap ℤ_[2] ℚ_[2])) := by
  have key (e : MonoidAlgebra ℚ_[2] ℤˣ) (he : e.coeff 1 = 1 / 2) :
      e ∉ Set.range (MonoidAlgebra.mapRingHom ℤˣ (algebraMap ℤ_[2] ℚ_[2])) := by
    rintro ⟨x, rfl⟩
    rw [MonoidAlgebra.coeff_mapRingHom] at he
    have h1 : ‖algebraMap ℤ_[2] ℚ_[2] (x.coeff 1)‖ ≤ 1 := (x.coeff 1).norm_le_one
    rw [he, one_div, norm_inv, show ((2 : ℚ_[2])) = ((2 : ℕ) : ℚ_[2]) by norm_num,
      Padic.norm_p] at h1
    norm_num at h1
  refine ⟨key _ ?_, key _ ?_⟩ <;>
    simp only [primitiveCentralIdempotent_coeff, Representation.char_ofLinearCharacter,
      signCharacter, Nat.card_eq_fintype_card, Fintype.card_units_int] <;>
    norm_num

end TauCeti.Examples.SplitCentralIdempotent
