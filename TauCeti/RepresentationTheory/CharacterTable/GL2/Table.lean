/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.irreducibleCharacters_GL2_eq_union`, the four families and their disjointness.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Classification
-- `TauCeti.IsCharacterTableSpec` and its stability under row permutations.
public import TauCeti.RepresentationTheory.CharacterTable.Specification
-- Non-public: `FDRep.nonempty_iso_of_character_eq` recovers an isomorphism from a character
-- identity.
import TauCeti.RepresentationTheory.CharacterTable.Determined
-- Non-public: `TauCeti.primitiveChar_to_Complex_ne_one`, the canonical additive character is
-- nontrivial.
import TauCeti.NumberTheory.LegendreSymbol.Complex
-- Non-public: the `q`-power map is an involution on the units of the quadratic extension.
import TauCeti.FieldTheory.Finite.FrobeniusFixed
-- Non-public: `TauCeti.card_conjClasses_GL2` counts the conjugacy classes of `GL₂(𝔽_q)`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses

/-!
# The character table of `GL₂(𝔽_q)`

Let `F` be a finite field with `q` elements and `E/F` a degree-`2` extension. The irreducible
complex characters of `GL₂(F)` come in four families
(`TauCeti.irreducibleCharacters_GL2_eq_union`), and this file assembles them into a square
character table whose rows are labelled by the classical parameters rather than by an arbitrary
enumeration.

The row labels form the type `TauCeti.GL2CharacterParam F E`, with one constructor per family:

* `linear α`, for a character `α` of `Fˣ`: the linear character `α ∘ det`, of degree `1`;
* `steinbergTwist α`: the Steinberg twist `(α ∘ det) ⊗ St`, of degree `q`;
* `principalSeries {α, β}`, for an unordered pair of distinct characters of `Fˣ`: the principal
  series `Ind_B^{GL₂}(α ⊗ β)`, of degree `q + 1`;
* `cuspidal {θ, θ^q}`, for an orbit of the `q`-power map on the characters `θ` of `Eˣ` with
  `θ^q ≠ θ`: the cuspidal character attached to `θ`, of degree `q - 1`.

The orbit relation on cuspidal parameters is `TauCeti.gl2CuspidalSetoid`; it is an equivalence
relation because the `q`-power map is an involution on `Eˣ`. The two quotients (unordered pairs
and orbits) are exactly the within-family identifications, so the parametrisation is a bijection
onto the irreducible characters (`TauCeti.GL2CharacterParam.equivIrreducibleCharacters`), and
there are `q² - 1` parameters, as many as conjugacy classes.

The table `TauCeti.GL2CharacterTable F E` has these rows and the conjugacy classes of `GL₂(F)` as
columns. It is the character table of `GL₂(F)` with its rows relabelled
(`TauCeti.GL2CharacterTable_eq_submatrix_characterTable`); consequently its rows are orthonormal
for the character pairing, its identity column lists the degrees `1`, `q`, `q + 1` and `q - 1` of
the four families, and every enumeration of its rows satisfies the specification of a character
table. The entries on the four families of conjugacy classes are the value formulas of the four
families, reached through `TauCeti.GL2CharacterTable_apply` and the `coe_classFunction_*` lemmas.

No lower bound on `q` is assumed: for `q = 2` the principal-series family is simply empty.

## Main definitions

* `TauCeti.GL2CharacterParam`: the classical parameters of the irreducible characters.
* `TauCeti.GL2CharacterParam.classFunction`: the irreducible character with a given parameter.
* `TauCeti.GL2CharacterTable`: the character table with rows labelled by parameters.

## Main results

* `TauCeti.GL2CharacterParam.equivIrreducibleCharacters`: the parameters are in bijection with
  the irreducible characters.
* `TauCeti.natCard_GL2CharacterParam`: there are `q² - 1` of them.
* `TauCeti.GL2CharacterTable_eq_submatrix_characterTable`: the table is the character table up to
  relabelling its rows.
* `TauCeti.GL2CharacterParam.characterPairing_classFunction`: its rows are orthonormal.
* `TauCeti.GL2CharacterTable_mk_one`: its identity column lists the four degrees.
* `TauCeti.isCharacterTableSpec_GL2CharacterTable_submatrix`: it satisfies the specification of a
  character table.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §§4–5.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

section Param

variable (F : Type) [Field F] [Fintype F] (E : Type*) [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- **The orbit relation on cuspidal parameters.** Two characters `θ, θ'` of `Eˣ` in general
position (`θ^q ≠ θ`) are related when `θ'` lies in the orbit `{θ, θ^q}` of the `q`-power map. This
is an equivalence relation because the `q`-power map is an involution on `Eˣ`, and its classes are
exactly the fibres of `θ ↦ χ_θ` (`TauCeti.GL2CuspidalVirtualCharacter_eq_iff`). -/
def gl2CuspidalSetoid :
    Setoid {θ : Eˣ →* ℂˣ // θ.comp (powMonoidHom (Fintype.card F)) ≠ θ} where
  r θ θ' := θ'.1 = θ.1 ∨ θ'.1 = θ.1.comp (powMonoidHom (Fintype.card F))
  iseqv := by
    -- the `q`-power map is an involution on `Eˣ`, hence so is precomposition with it
    have h (θ : Eˣ →* ℂˣ) :
        (θ.comp (powMonoidHom (Fintype.card F))).comp (powMonoidHom (Fintype.card F)) = θ := by
      rw [MonoidHom.comp_assoc, ← Nat.card_eq_fintype_card,
        FiniteField.units_powMonoidHom_comp_powMonoidHom (K := F), MonoidHom.comp_id]
    refine ⟨fun θ => Or.inl rfl, ?_, ?_⟩
    · rintro θ θ' (hθ | hθ)
      · exact Or.inl hθ.symm
      · exact Or.inr (by rw [hθ, h])
    · rintro θ θ' θ'' (hθ | hθ) (hθ' | hθ')
      · exact Or.inl (hθ'.trans hθ)
      · exact Or.inr (by rw [hθ', hθ])
      · exact Or.inr (hθ'.trans hθ)
      · exact Or.inl (by rw [hθ', hθ, h])

variable {F E} in
/-- Two cuspidal parameters are related by `TauCeti.gl2CuspidalSetoid` exactly when the second
lies in the orbit `{θ, θ^q}` of the first. -/
@[simp]
theorem gl2CuspidalSetoid_apply
    {θ θ' : {θ : Eˣ →* ℂˣ // θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}} :
    (gl2CuspidalSetoid F E) θ θ' ↔
      θ'.1 = θ.1 ∨ θ'.1 = θ.1.comp (powMonoidHom (Fintype.card F)) :=
  Iff.rfl

/-- **The classical parameters of the irreducible characters of `GL₂(𝔽_q)`**, one constructor
for each of the four families: a character `α` of `Fˣ` for the linear characters `α ∘ det` and
for the Steinberg twists `(α ∘ det) ⊗ St`, an unordered pair `{α, β}` of distinct characters of
`Fˣ` for the principal series `Ind_B^{GL₂}(α ⊗ β)`, and an orbit `{θ, θ^q}` of characters of `Eˣ`
with `θ^q ≠ θ` for the cuspidal characters. -/
inductive GL2CharacterParam where
  /-- The parameter of the linear character `α ∘ det`. -/
  | linear (α : Fˣ →* ℂˣ)
  /-- The parameter of the Steinberg twist `(α ∘ det) ⊗ St`. -/
  | steinbergTwist (α : Fˣ →* ℂˣ)
  /-- The parameter of the principal series `Ind_B^{GL₂}(α ⊗ β)`, for `s = {α, β}` with
  `α ≠ β`. -/
  | principalSeries (s : Sym2 (Fˣ →* ℂˣ)) (hs : ¬ s.IsDiag)
  /-- The parameter of the cuspidal character attached to the orbit `{θ, θ^q}`. -/
  | cuspidal (o : Quotient (gl2CuspidalSetoid F E))

variable {F E}

namespace GL2CharacterParam

/-- The principal-series character does not depend on the order of its two inducing characters,
so it descends to unordered pairs. -/
private theorem ofFDRep_GL2PrincipalSeries_comm (α β : Fˣ →* ℂˣ) :
    ClassFunction.ofFDRep (GL2PrincipalSeries F α β) =
      ClassFunction.ofFDRep (GL2PrincipalSeries F β α) :=
  Subtype.ext (funext fun g => by
    rw [ClassFunction.ofFDRep_apply, ClassFunction.ofFDRep_apply,
      FDRep.char_iso (nonempty_iso_GL2PrincipalSeries_swap F α β).some])

/-- The cuspidal virtual character, built from Mathlib's canonical additive character of `F`, is
constant on the orbits `{θ, θ^q}`, so it descends to cuspidal parameters. -/
private theorem GL2CuspidalVirtualCharacter_eq_of_rel
    {θ θ' : {θ : Eˣ →* ℂˣ // θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}}
    (h : (gl2CuspidalSetoid F E) θ θ') :
    GL2CuspidalVirtualCharacter F E θ.1 (AddChar.FiniteField.primitiveChar_to_Complex F) =
      GL2CuspidalVirtualCharacter F E θ'.1 (AddChar.FiniteField.primitiveChar_to_Complex F) := by
  rcases h with h | h <;> rw [h]
  rw [GL2CuspidalVirtualCharacter_comp_powMonoidHom]

/-- **The irreducible character of `GL₂(𝔽_q)` with a given parameter**, as a class function: the
character of `α ∘ det`, of `(α ∘ det) ⊗ St`, of `Ind_B^{GL₂}(α ⊗ β)`, or of the cuspidal
representation attached to `θ`, according to the family of the parameter. -/
noncomputable def classFunction : GL2CharacterParam F E → ClassFunction ℂ (GL (Fin 2) F)
  | linear α => ClassFunction.ofFDRep (GL2Linear F α)
  | steinbergTwist α => ClassFunction.ofFDRep (GL2SteinbergTwist F α)
  | principalSeries s _ => Sym2.lift
      ⟨fun α β => ClassFunction.ofFDRep (GL2PrincipalSeries F α β),
        ofFDRep_GL2PrincipalSeries_comm⟩ s
  | cuspidal o => Quotient.lift
      (fun θ =>
        GL2CuspidalVirtualCharacter F E θ.1 (AddChar.FiniteField.primitiveChar_to_Complex F))
      (fun _ _ h => GL2CuspidalVirtualCharacter_eq_of_rel h) o

/-- The row of a linear parameter, as a function, is the character of `α ∘ det`. -/
@[simp]
theorem coe_classFunction_linear (α : Fˣ →* ℂˣ) :
    ((linear (E := E) α).classFunction : GL (Fin 2) F → ℂ) = (GL2Linear F α).character :=
  funext (ClassFunction.ofFDRep_apply _)

/-- The row of a Steinberg parameter, as a function, is the character of `(α ∘ det) ⊗ St`. -/
@[simp]
theorem coe_classFunction_steinbergTwist (α : Fˣ →* ℂˣ) :
    ((steinbergTwist (E := E) α).classFunction : GL (Fin 2) F → ℂ) =
      (GL2SteinbergTwist F α).character :=
  funext (ClassFunction.ofFDRep_apply _)

/-- The row of a principal-series parameter `{α, β}`, as a function, is the character of
`Ind_B^{GL₂}(α ⊗ β)`. -/
@[simp]
theorem coe_classFunction_principalSeries_mk (α β : Fˣ →* ℂˣ) (h : ¬ s(α, β).IsDiag) :
    ((principalSeries (E := E) s(α, β) h).classFunction : GL (Fin 2) F → ℂ) =
      (GL2PrincipalSeries F α β).character :=
  funext (ClassFunction.ofFDRep_apply _)

/-- The row of a cuspidal parameter `{θ, θ^q}`, as a function, is the character of the cuspidal
representation attached to `θ`. -/
@[simp]
theorem coe_classFunction_cuspidal_mk
    (θ : {θ : Eˣ →* ℂˣ // θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}) :
    ((cuspidal ⟦θ⟧).classFunction : GL (Fin 2) F → ℂ) = (GL2Cuspidal θ.1 θ.2).character :=
  (character_GL2Cuspidal θ.1 θ.2).symm

/-- The row of a parameter is an irreducible character of `GL₂(F)`. -/
theorem classFunction_mem_irreducibleCharacters (i : GL2CharacterParam F E) :
    (i.classFunction : GL (Fin 2) F → ℂ) ∈ irreducibleCharacters ℂ (GL (Fin 2) F) := by
  rcases i with α | α | ⟨s, hs⟩ | o
  · rw [coe_classFunction_linear]
    exact character_GL2Linear_mem_irreducibleCharacters α
  · rw [coe_classFunction_steinbergTwist]
    exact character_GL2SteinbergTwist_mem_irreducibleCharacters F α
  · induction s using Sym2.ind with
    | _ α β =>
      rw [coe_classFunction_principalSeries_mk]
      exact character_GL2PrincipalSeries_mem_irreducibleCharacters F
        (Sym2.mk_isDiag_iff.not.mp hs)
  · induction o using Quotient.ind with
    | _ θ =>
      have := simple_GL2Cuspidal θ.1 θ.2
      rw [coe_classFunction_cuspidal_mk]
      exact (GL2Cuspidal θ.1 θ.2).character_mem_irreducibleCharacters

/-- **Distinct parameters have distinct characters.** Across families this is the disjointness of
the four families; within a family it is the identification of the parameters: a character of
`Fˣ` for the linear characters and the Steinberg twists, the unordered pair for the principal
series (`TauCeti.nonempty_iso_GL2PrincipalSeries_iff`) and the orbit `{θ, θ^q}` for the cuspidal
characters (`TauCeti.GL2CuspidalVirtualCharacter_eq_iff`). -/
theorem coe_classFunction_injective :
    Function.Injective fun i : GL2CharacterParam F E => (i.classFunction : GL (Fin 2) F → ℂ) := by
  have hψ := primitiveChar_to_Complex_ne_one F
  intro i j hij
  simp only at hij
  rcases i with α | α | ⟨s, hs⟩ | o <;> rcases j with β | β | ⟨t, ht⟩ | o'
  all_goals
    try induction s using Sym2.ind
    try induction t using Sym2.ind
    try induction o using Quotient.ind
    try induction o' using Quotient.ind
    simp only [coe_classFunction_linear, coe_classFunction_steinbergTwist,
      coe_classFunction_principalSeries_mk, coe_classFunction_cuspidal_mk,
      character_GL2Cuspidal] at hij
  · exact congrArg linear (GL2Linear_character_injective hij)
  · exact absurd hij (character_GL2Linear_ne_character_GL2SteinbergTwist α β)
  · exact absurd hij (character_GL2Linear_ne_character_GL2PrincipalSeries α _ _)
  · exact absurd hij (character_GL2Linear_ne_GL2CuspidalVirtualCharacter α _ hψ)
  · exact absurd hij.symm (character_GL2Linear_ne_character_GL2SteinbergTwist β α)
  · exact congrArg steinbergTwist (GL2SteinbergTwist_character_injective hij)
  · exact absurd hij (character_GL2SteinbergTwist_ne_character_GL2PrincipalSeries α _ _)
  · exact absurd hij (character_GL2SteinbergTwist_ne_GL2CuspidalVirtualCharacter α _ hψ)
  · exact absurd hij.symm (character_GL2Linear_ne_character_GL2PrincipalSeries β _ _)
  · exact absurd hij.symm (character_GL2SteinbergTwist_ne_character_GL2PrincipalSeries β _ _)
  · obtain ⟨e⟩ := FDRep.nonempty_iso_of_character_eq _ _ hij
    simp only [principalSeries.injEq]
    exact Sym2.eq_iff.mpr ((nonempty_iso_GL2PrincipalSeries_iff F).mp ⟨e⟩)
  · exact absurd hij (character_GL2PrincipalSeries_ne_GL2CuspidalVirtualCharacter _ _ _ _)
  · exact absurd hij.symm (character_GL2Linear_ne_GL2CuspidalVirtualCharacter β _ hψ)
  · exact absurd hij.symm (character_GL2SteinbergTwist_ne_GL2CuspidalVirtualCharacter β _ hψ)
  · exact absurd hij.symm (character_GL2PrincipalSeries_ne_GL2CuspidalVirtualCharacter _ _ _ _)
  · simp only [cuspidal.injEq]
    exact Quotient.sound
      ((GL2CuspidalVirtualCharacter_eq_iff _ _ hψ hψ).mp (Subtype.ext hij))

/-- **Every irreducible character of `GL₂(F)` has a parameter.** This is the classification
`TauCeti.irreducibleCharacters_GL2_eq_union`, read through the parametrisation. -/
theorem exists_coe_classFunction_eq {f : GL (Fin 2) F → ℂ}
    (hf : f ∈ irreducibleCharacters ℂ (GL (Fin 2) F)) :
    ∃ i : GL2CharacterParam F E, (i.classFunction : GL (Fin 2) F → ℂ) = f := by
  rw [irreducibleCharacters_GL2_eq_union F E (primitiveChar_to_Complex_ne_one F)] at hf
  rcases hf with (((⟨α, rfl⟩ | ⟨α, rfl⟩) | ⟨⟨α, β⟩, hαβ, rfl⟩) | ⟨θ, hθ, rfl⟩)
  · exact ⟨linear α, coe_classFunction_linear α⟩
  · exact ⟨steinbergTwist α, coe_classFunction_steinbergTwist α⟩
  · exact ⟨principalSeries s(α, β) (Sym2.mk_isDiag_iff.not.mpr hαβ),
      coe_classFunction_principalSeries_mk α β _⟩
  · exact ⟨cuspidal ⟦⟨θ, hθ⟩⟧, rfl⟩

variable (F E) in
/-- **The parameters are in bijection with the irreducible characters of `GL₂(F)`**, a parameter
going to the character of its family. -/
noncomputable def equivIrreducibleCharacters :
    GL2CharacterParam F E ≃ irreducibleCharacters ℂ (GL (Fin 2) F) :=
  Equiv.ofBijective (fun i => ⟨i.classFunction, i.classFunction_mem_irreducibleCharacters⟩)
    ⟨fun _ _ h => coe_classFunction_injective (by simpa using congrArg Subtype.val h),
      fun f => (exists_coe_classFunction_eq f.2).imp fun _ h => Subtype.ext h⟩

/-- The irreducible character a parameter is sent to is its row. -/
@[simp]
theorem coe_equivIrreducibleCharacters_apply (i : GL2CharacterParam F E) :
    (equivIrreducibleCharacters F E i : GL (Fin 2) F → ℂ) = i.classFunction :=
  (rfl)

/-- There are finitely many parameters, being in bijection with the irreducible characters. -/
instance : Finite (GL2CharacterParam F E) :=
  let _ : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr (equivIrreducibleCharacters F E), card_irreducibleCharacters]
    exact Nat.card_pos.ne')

/-- The degree of the irreducible character with a given parameter: `1` for the linear
characters, `q` for the Steinberg twists, `q + 1` for the principal series and `q - 1` for the
cuspidal characters. -/
def degree : GL2CharacterParam F E → ℕ
  | linear _ => 1
  | steinbergTwist _ => Fintype.card F
  | principalSeries _ _ => Fintype.card F + 1
  | cuspidal _ => Fintype.card F - 1

/-- The linear characters have degree `1`. -/
@[simp] theorem degree_linear (α : Fˣ →* ℂˣ) : (linear (E := E) α).degree = 1 := (rfl)

/-- The Steinberg twists have degree `q`. -/
@[simp] theorem degree_steinbergTwist (α : Fˣ →* ℂˣ) :
    (steinbergTwist (E := E) α).degree = Fintype.card F := (rfl)

/-- The principal series have degree `q + 1`. -/
@[simp] theorem degree_principalSeries (s : Sym2 (Fˣ →* ℂˣ)) (hs : ¬ s.IsDiag) :
    (principalSeries (E := E) s hs).degree = Fintype.card F + 1 := (rfl)

/-- The cuspidal characters have degree `q - 1`. -/
@[simp] theorem degree_cuspidal (o : Quotient (gl2CuspidalSetoid F E)) :
    (cuspidal o).degree = Fintype.card F - 1 := (rfl)

/-- The irreducible character with a given parameter takes the value `degree` at the identity. -/
@[simp]
theorem classFunction_apply_one (i : GL2CharacterParam F E) :
    (i.classFunction : GL (Fin 2) F → ℂ) 1 = i.degree := by
  rcases i with α | α | ⟨s, hs⟩ | o
  · simp [finrank_GL2Linear]
  · simp [finrank_GL2SteinbergTwist]
  · induction s using Sym2.ind with
    | _ α β => simp
  · induction o using Quotient.ind with
    | _ θ => simp [FDRep.char_one, finrank_GL2Cuspidal]

end GL2CharacterParam

variable (F E) in
/-- **There are `q² - 1` parameters**, as many as conjugacy classes of `GL₂(F)`. -/
theorem natCard_GL2CharacterParam :
    Nat.card (GL2CharacterParam F E) = Fintype.card F ^ 2 - 1 := by
  let _ : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [Nat.card_congr (GL2CharacterParam.equivIrreducibleCharacters F E),
    card_irreducibleCharacters, card_conjClasses_GL2, Nat.card_eq_fintype_card]

end Param

section Table

variable (F : Type) [Field F] [Fintype F] (E : Type*) [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- **The character table of `GL₂(𝔽_q)`**, with rows labelled by the classical parameters
`TauCeti.GL2CharacterParam F E` and columns by the conjugacy classes: the entry in row `i` and
column `C` is the value of the irreducible character with parameter `i` on `C`. -/
noncomputable def GL2CharacterTable :
    Matrix (GL2CharacterParam F E) (ConjClasses (GL (Fin 2) F)) ℂ := fun i =>
  ClassFunction.toConjClasses i.classFunction

variable {F E}

/-- The entry of the table in row `i` and the column of `g` is the value at `g` of the irreducible
character with parameter `i`. -/
@[simp]
theorem GL2CharacterTable_apply (i : GL2CharacterParam F E) (g : GL (Fin 2) F) :
    GL2CharacterTable F E i (ConjClasses.mk g) = (i.classFunction : GL (Fin 2) F → ℂ) g :=
  ClassFunction.toConjClasses_mk _ g

/-- **The identity column lists the degrees** `1`, `q`, `q + 1` and `q - 1` of the four
families. -/
theorem GL2CharacterTable_mk_one (i : GL2CharacterParam F E) :
    GL2CharacterTable F E i (ConjClasses.mk 1) = i.degree := by
  rw [GL2CharacterTable_apply, GL2CharacterParam.classFunction_apply_one]

variable (F E) in
/-- **The table is the character table of `GL₂(F)` with its rows relabelled**: row `i` is the row
of `TauCeti.characterTable` enumerating the irreducible character with parameter `i`. -/
theorem GL2CharacterTable_eq_submatrix_characterTable :
    GL2CharacterTable F E = (characterTable ℂ (GL (Fin 2) F)).submatrix
      ((GL2CharacterParam.equivIrreducibleCharacters F E).trans
        (finEquivIrreducibleCharacters ℂ (GL (Fin 2) F)).symm) id := by
  ext i C
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
  rw [submatrix_apply, id_eq, characterTable_apply, GL2CharacterTable_apply, Equiv.trans_apply,
    ← coe_finEquivIrreducibleCharacters_apply, Equiv.apply_symm_apply,
    GL2CharacterParam.coe_equivIrreducibleCharacters_apply]

open Classical in
/-- **The rows of the table are orthonormal** for the character pairing: the irreducible
characters with parameters `i` and `j` pair to `1` when `i = j` and to `0` otherwise. -/
theorem GL2CharacterParam.characterPairing_classFunction
    (i j : GL2CharacterParam F E) :
    ClassFunction.characterPairing i.classFunction j.classFunction = if i = j then 1 else 0 := by
  set τ := (GL2CharacterParam.equivIrreducibleCharacters F E).trans
    (finEquivIrreducibleCharacters ℂ (GL (Fin 2) F)).symm
  have h : ∀ i : GL2CharacterParam F E, i.classFunction =
      ClassFunction.ofCharacter (irreducibleRepresentation ℂ (τ i)) := fun i =>
    Subtype.ext (funext fun g => by
      rw [ClassFunction.ofCharacter_apply, character_irreducibleRepresentation, Equiv.trans_apply,
        ← coe_finEquivIrreducibleCharacters_apply, Equiv.apply_symm_apply,
        GL2CharacterParam.coe_equivIrreducibleCharacters_apply])
  rw [h, h, characterPairing_ofCharacter_irreducibleRepresentation_orthonormal]
  simp only [τ.apply_eq_iff_eq]

/-- **The table satisfies the specification of a character table**, under any enumeration of its
rows by `Fin (q² - 1)`: its identity column lists positive divisors of `|GL₂(F)|` whose squares sum
to `|GL₂(F)|`, its rows are orthonormal for the class-size weighted Hermitian pairing, and its
normalized rows are common eigenrows of the class-multiplication matrices. -/
theorem isCharacterTableSpec_GL2CharacterTable_submatrix [Fintype (GL (Fin 2) F)]
    [DecidableEq (GL (Fin 2) F)]
    (e : Fin (Nat.card (ConjClasses (GL (Fin 2) F))) ≃ GL2CharacterParam F E) :
    IsCharacterTableSpec (GL (Fin 2) F) ((GL2CharacterTable F E).submatrix e id) := by
  rw [GL2CharacterTable_eq_submatrix_characterTable, submatrix_submatrix, Function.id_comp]
  exact (isCharacterTableSpec_characterTable _).submatrix
    (e.trans ((GL2CharacterParam.equivIrreducibleCharacters F E).trans
      (finEquivIrreducibleCharacters ℂ (GL (Fin 2) F)).symm))

end Table

end TauCeti
