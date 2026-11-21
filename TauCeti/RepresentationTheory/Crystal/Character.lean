/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.StringReflection
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic

/-!
# Formal characters of finite normal crystals

The formal character counts elements of each weight in the integral group algebra of the
actual weight lattice. Reversal of simple-root strings identifies reflected weight fibres,
so the character is Weyl-invariant for a finite reduced root datum, and each Demazure operator
`Dᵢ` fixes it over any root datum. This uses no classification of normal crystals and does not
identify the character with that of a highest-weight module.

The character `∑_{x ∈ s} e^{wt x}` of a finite set of crystal elements
(`TauCeti.NormalCrystal.character`) extends the formal character to subsets of a possibly
infinite crystal.

Strict crystal isomorphisms preserve this character, providing the interface for comparing
finite combinatorial models with one another.

## References

* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*,
  World Scientific (2017), Ch. 2.
-/

public section

namespace TauCeti.NormalCrystal

variable {ι X Y B B' : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}
  (c : NormalCrystal P b B)

/-- The **character** `∑_{x ∈ s} e^{wt x}` of a finite set of crystal elements, in the integral
group algebra of the weight lattice. -/
noncomputable def character (s : Finset B) : AddMonoidAlgebra ℤ X :=
  ∑ x ∈ s, AddMonoidAlgebra.single (c.wt x) 1

theorem character_def (s : Finset B) :
    c.character s = ∑ x ∈ s, AddMonoidAlgebra.single (c.wt x) 1 := (rfl)

@[simp]
theorem character_empty : c.character ∅ = 0 := by
  simp [character_def]

@[simp]
theorem character_singleton (x : B) : c.character {x} = AddMonoidAlgebra.single (c.wt x) 1 := by
  simp [character_def]

theorem character_union [DecidableEq B] {s t : Finset B} (h : Disjoint s t) :
    c.character (s ∪ t) = c.character s + c.character t :=
  Finset.sum_union h

variable [Fintype B]

/-- The formal character of a finite crystal, counting every element with its weight,
including multiplicities. -/
noncomputable def formalCharacter : AddMonoidAlgebra ℤ X :=
  ∑ x : B, AddMonoidAlgebra.single (c.wt x) 1

/-- The defining sum for the character. -/
theorem formalCharacter_def :
    c.formalCharacter = ∑ x : B, AddMonoidAlgebra.single (c.wt x) 1 := (rfl)

/-- The formal character of a finite crystal is the character of the whole crystal. -/
theorem formalCharacter_eq_character_univ :
    c.formalCharacter = c.character Finset.univ := by
  rw [formalCharacter_def, character_def]

/-- The coefficient at a weight is the cardinality of that weight fibre. -/
@[simp]
theorem coeff_formalCharacter (μ : X) :
    c.formalCharacter.coeff μ = (Nat.card {x : B // c.wt x = μ} : ℤ) := by
  classical
  simp [formalCharacter_def, AddMonoidAlgebra.coeff_sum,
    Finsupp.single_apply, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Each coefficient of the formal character is unchanged when its weight is reflected by a
simple reflection. -/
theorem coeff_formalCharacter_reflection (i : b.support) (μ : X) :
    c.formalCharacter.coeff (P.reflection i μ) = c.formalCharacter.coeff μ := by
  simp only [coeff_formalCharacter, c.card_weightFiber_reflection i μ]

/-- **`Dᵢ` fixes the character of a finite normal crystal**, over any root datum. -/
@[simp]
theorem demazureOperator_formalCharacter (i : b.support) :
    P.demazureOperator i c.formalCharacter = c.formalCharacter :=
  (P.demazureOperator_eq_self_iff i).mpr
    (AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ by simp [← LinearEquiv.coe_inv]))

/-- The formal character of a finite normal crystal is invariant under the Weyl group of a
finite reduced root datum. -/
theorem isWeylInvariant_formalCharacter [Finite ι] [P.IsReduced] :
    IsWeylInvariant P c.formalCharacter := by
  apply isWeylInvariant_of_forall_coeff_reflection P b
  intro i hi μ
  exact c.coeff_formalCharacter_reflection ⟨i, hi⟩ μ

/-- A strict crystal isomorphism preserves the finite formal character. -/
theorem StrictIso.formalCharacter_eq {c : NormalCrystal P b B}
    {d : NormalCrystal P b B'} [Fintype B'] (ψ : StrictIso c d) :
    d.formalCharacter = c.formalCharacter := by
  classical
  rw [formalCharacter_def, formalCharacter_def, ← ψ.toEquiv.sum_comp]
  simp only [StrictIso.coe_toEquiv, ψ.wt_apply]

end TauCeti.NormalCrystal
