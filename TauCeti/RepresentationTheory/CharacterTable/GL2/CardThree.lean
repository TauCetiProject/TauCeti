/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The four families, their parameter counts and the classification they satisfy.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Classification
-- Non-public: `TauCeti.card_conjClasses_GL2` counts the conjugacy classes of `GL₂(𝔽_q)`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: `Matrix.card_GL_field` counts the elements of `GL₂(𝔽_q)`.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: `AddChar.exists_apply_ne_zero` supplies the nontrivial additive character of `F`.
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
-- Non-public: `FiniteField.Extension` supplies the quadratic extension of `F`.
import Mathlib.FieldTheory.Finite.Extension

/-!
# The irreducible characters of `GL₂(𝔽₃)`

`TauCeti/RepresentationTheory/CharacterTable/GL2/Classification.lean` sorts the irreducible
complex characters of `GL₂(F)`, for a finite field `F` with `q` elements, into four families: the
`q - 1` **linear** characters `α ∘ det`, of degree `1`; the `q - 1` **Steinberg twists**, of degree
`q`; the `½ (q - 1)(q - 2)` **principal-series** characters, of degree `q + 1`; and the
`½ q (q - 1)` **cuspidal** characters, of degree `q - 1`. This file reads that classification at
`q = 3` and assembles the resulting table of degrees.

`GL₂(𝔽₃)` has `48` elements and `q² - 1 = 8` conjugacy classes, so it has `8` irreducible complex
characters. The four families supply

```text
2 linear (degree 1) + 2 Steinberg twists (degree 3) + 1 principal series (degree 4)
  + 3 cuspidal (degree 2) = 8,
```

so the eight degrees are `1, 1, 2, 2, 2, 3, 3, 4`, and

`2 · 1² + 2 · 3² + 1 · 4² + 3 · 2² = 2 + 18 + 16 + 12 = 48`

is the order of the group, as the degree equation demands. Three is the smallest `q` for which all
four families are nonempty: at `q = 2` the principal series is empty, `½ (q - 1)(q - 2)` being
zero, which is why `GL₂(𝔽₂)` is a separate, degenerate instance.

Everything is stated for an arbitrary finite field `F` with three elements rather than for a chosen
model of `𝔽₃`. The statements about the cuspidal family carry the auxiliary data the general
classification carries — a degree-`2` extension `E/F`, which is what the cuspidal characters are
parameterised by, and a nontrivial additive character `ψ` of `F` — while the statements that
mention neither, the two counts, the order and the degree set, ask for neither: the last obtains
its own `E` and `ψ`, as `F` admits both.

The multiplicities above are read off the four families. Identifying the families intrinsically,
as the fibres of the degree map, is a separate statement about a general `q` and is not used here.

## Main results

* `TauCeti.natCard_GL2_of_card_eq_three`: `GL₂(𝔽₃)` has `48` elements, and
  `TauCeti.card_conjClasses_GL2_of_card_eq_three` and
  `TauCeti.card_irreducibleCharacters_GL2_of_card_eq_three`: it has `8` conjugacy classes and so
  `8` irreducible complex characters.
* `TauCeti.ncard_range_character_GL2Linear_of_card_eq_three` and its three companions: the four
  families have `2`, `2`, `1` and `3` members.
* `TauCeti.finrank_GL2SteinbergTwist_of_card_eq_three` and
  `TauCeti.finrank_GL2PrincipalSeries_of_card_eq_three`: the degrees `3` and `4` of the Steinberg
  twists and of the principal series, and
  `TauCeti.GL2CuspidalVirtualCharacter_apply_one_of_card_eq_three`: the value `2` of
  `GL2CuspidalVirtualCharacter` at the identity, which is the cuspidal degree `q - 1` at `q = 3`.
* `TauCeti.ncard_families_GL2_of_card_eq_three` and `TauCeti.sum_sq_degree_GL2_of_card_eq_three`:
  **the tally** — the four family sizes add up to the number of irreducible characters, and the
  sum of the squares of their degrees is the order of the group.
* `TauCeti.image_apply_one_irreducibleCharacters_GL2_of_card_eq_three`: the degrees of `GL₂(𝔽₃)`
  are exactly `1`, `2`, `3` and `4`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

variable (F : Type) [Field F] [Fintype F]

/-- **`GL₂(𝔽₃)` has `48` elements**, `(3² - 1)(3² - 3)`. -/
theorem natCard_GL2_of_card_eq_three (hF : Fintype.card F = 3) :
    Nat.card (GL (Fin 2) F) = 48 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, hF]

/-- **`GL₂(𝔽₃)` has `8` conjugacy classes**, the `q² - 1` of the general count at `q = 3`. -/
theorem card_conjClasses_GL2_of_card_eq_three (hF : Fintype.card F = 3) :
    Nat.card (ConjClasses (GL (Fin 2) F)) = 8 := by
  rw [card_conjClasses_GL2, Nat.card_eq_fintype_card, hF]
  rfl

/-- **`GL₂(𝔽₃)` has `8` irreducible complex characters.** -/
theorem card_irreducibleCharacters_GL2_of_card_eq_three (hF : Fintype.card F = 3) :
    Nat.card (irreducibleCharacters ℂ (GL (Fin 2) F)) = 8 := by
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [card_irreducibleCharacters, card_conjClasses_GL2_of_card_eq_three F hF]

/-! ### The four families at `q = 3` -/

variable (E : Type*) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- **`GL₂(𝔽₃)` has two linear characters**, `α ∘ det` for the two characters `α` of `𝔽₃ˣ`. -/
theorem ncard_range_character_GL2Linear_of_card_eq_three (hF : Fintype.card F = 3) :
    (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character).ncard = 2 := by
  rw [ncard_range_character_GL2Linear, hF]

/-- **`GL₂(𝔽₃)` has two Steinberg twists.** -/
theorem ncard_range_character_GL2SteinbergTwist_of_card_eq_three (hF : Fintype.card F = 3) :
    (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character).ncard = 2 := by
  rw [ncard_range_character_GL2SteinbergTwist, hF]

/-- **`GL₂(𝔽₃)` has a single principal-series character**, `½ (q - 1)(q - 2)` being `1` at
`q = 3`: there are only two characters of `𝔽₃ˣ`, so only one unordered pair of distinct ones. -/
theorem ncard_image_character_GL2PrincipalSeries_of_card_eq_three (hF : Fintype.card F = 3) :
    ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
      {p | p.1 ≠ p.2}).ncard = 1 := by
  rw [ncard_image_character_GL2PrincipalSeries, hF]

/-- **`GL₂(𝔽₃)` has three cuspidal characters**, `½ q (q - 1)` being `3` at `q = 3`. -/
theorem ncard_image_GL2CuspidalVirtualCharacter_of_card_eq_three {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (hF : Fintype.card F = 3) :
    ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
      {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard = 3 := by
  rw [ncard_image_GL2CuspidalVirtualCharacter F E hψ, hF]

/-! ### The four degrees at `q = 3` -/

/-- A Steinberg twist of `GL₂(𝔽₃)` has degree `3`. -/
theorem finrank_GL2SteinbergTwist_of_card_eq_three (hF : Fintype.card F = 3) (α : Fˣ →* ℂˣ) :
    Module.finrank ℂ (GL2SteinbergTwist F α) = 3 := by
  rw [finrank_GL2SteinbergTwist, hF]

/-- The principal-series character of `GL₂(𝔽₃)` has degree `4`. -/
theorem finrank_GL2PrincipalSeries_of_card_eq_three (hF : Fintype.card F = 3)
    (α β : Fˣ →* ℂˣ) : Module.finrank ℂ (GL2PrincipalSeries F α β) = 4 := by
  rw [finrank_GL2PrincipalSeries, hF]

/-- **`GL2CuspidalVirtualCharacter` takes the value `2` at the identity** over a field with three
elements, that being the cuspidal degree `q - 1` at `q = 3`. -/
theorem GL2CuspidalVirtualCharacter_apply_one_of_card_eq_three (hF : Fintype.card F = 3)
    (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    (GL2CuspidalVirtualCharacter F E θ ψ).1 1 = 2 := by
  rw [GL2CuspidalVirtualCharacter_apply_one, hF]
  norm_num

/-! ### The tally -/

/-- **The family sizes of `GL₂(𝔽₃)` tally**: the two linear characters, the two Steinberg twists,
the one principal-series character and the three cuspidal ones are `8` in all, the number of
irreducible characters. -/
theorem ncard_families_GL2_of_card_eq_three {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (hF : Fintype.card F = 3) :
    (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character).ncard
      + (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character).ncard
      + ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
          {p | p.1 ≠ p.2}).ncard
      + ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
          {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard
      = Nat.card (irreducibleCharacters ℂ (GL (Fin 2) F)) := by
  rw [ncard_range_character_GL2Linear_of_card_eq_three F hF,
    ncard_range_character_GL2SteinbergTwist_of_card_eq_three F hF,
    ncard_image_character_GL2PrincipalSeries_of_card_eq_three F hF,
    ncard_image_GL2CuspidalVirtualCharacter_of_card_eq_three F E hψ hF,
    card_irreducibleCharacters_GL2_of_card_eq_three F hF]

/-- **The degree tally of `GL₂(𝔽₃)`**: the two linear characters of degree `1`, the two Steinberg
twists of degree `3`, the principal-series character of degree `4` and the three cuspidal
characters of degree `2` have `2 · 1² + 2 · 3² + 1 · 4² + 3 · 2² = 48` for the sum of the squares
of their degrees, the order of the group. -/
theorem sum_sq_degree_GL2_of_card_eq_three {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (hF : Fintype.card F = 3) :
    (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character).ncard * 1 ^ 2
      + (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character).ncard * 3 ^ 2
      + ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
          {p | p.1 ≠ p.2}).ncard * 4 ^ 2
      + ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
          {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard * 2 ^ 2
      = Nat.card (GL (Fin 2) F) := by
  rw [ncard_range_character_GL2Linear_of_card_eq_three F hF,
    ncard_range_character_GL2SteinbergTwist_of_card_eq_three F hF,
    ncard_image_character_GL2PrincipalSeries_of_card_eq_three F hF,
    ncard_image_GL2CuspidalVirtualCharacter_of_card_eq_three F E hψ hF,
    natCard_GL2_of_card_eq_three F hF]
  rfl

include E in
/-- The degree set of `GL₂(𝔽₃)`, read off a given quadratic extension `E/F` and a given
nontrivial additive character `ψ`. Neither occurs in the conclusion, and
`image_apply_one_irreducibleCharacters_GL2_of_card_eq_three` supplies both. -/
private theorem image_apply_one_irreducibleCharacters_GL2_of_card_eq_three_aux
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (hF : Fintype.card F = 3) :
    (fun χ : GL (Fin 2) F → ℂ => χ 1) '' irreducibleCharacters ℂ (GL (Fin 2) F)
      = {1, 3, 4, 2} := by
  have hlin : (fun χ : GL (Fin 2) F → ℂ => χ 1) ''
      (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) = {1} := by
    rw [← Set.range_comp]
    have hval : ((fun χ : GL (Fin 2) F → ℂ => χ 1) ∘
        fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) = fun _ => (1 : ℂ) := by
      funext α
      simp [FDRep.char_one, finrank_GL2Linear]
    rw [hval, Set.range_const]
  have hst : (fun χ : GL (Fin 2) F → ℂ => χ 1) ''
      (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) = {3} := by
    rw [← Set.range_comp]
    have hval : ((fun χ : GL (Fin 2) F → ℂ => χ 1) ∘
        fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) = fun _ => (3 : ℂ) := by
      funext α
      simp [FDRep.char_one, finrank_GL2SteinbergTwist_of_card_eq_three F hF]
    rw [hval, Set.range_const]
  have hps : (fun χ : GL (Fin 2) F → ℂ => χ 1) ''
      ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
        {p | p.1 ≠ p.2}) = {4} := by
    have hne : ({p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) | p.1 ≠ p.2}).Nonempty := by
      refine Set.Nonempty.of_image
        (f := fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character)
        (Set.nonempty_of_ncard_ne_zero ?_)
      rw [ncard_image_character_GL2PrincipalSeries_of_card_eq_three F hF]
      exact one_ne_zero
    rw [← Set.image_comp]
    have hval : ((fun χ : GL (Fin 2) F → ℂ => χ 1) ∘
        fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character)
        = fun _ => (4 : ℂ) := by
      funext p
      simp [FDRep.char_one, finrank_GL2PrincipalSeries_of_card_eq_three F hF]
    rw [hval, hne.image_const]
  have hcusp : (fun χ : GL (Fin 2) F → ℂ => χ 1) ''
      ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
        {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}) = {2} := by
    have hne : ({θ : Eˣ →* ℂˣ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).Nonempty := by
      refine Set.Nonempty.of_image
        (f := fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1)
        (Set.nonempty_of_ncard_ne_zero ?_)
      rw [ncard_image_GL2CuspidalVirtualCharacter_of_card_eq_three F E hψ hF]
      exact three_ne_zero
    rw [← Set.image_comp]
    have hval : ((fun χ : GL (Fin 2) F → ℂ => χ 1) ∘
        fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) = fun _ => (2 : ℂ) := by
      funext θ
      simp [GL2CuspidalVirtualCharacter_apply_one_of_card_eq_three F E hF]
    rw [hval, hne.image_const]
  rw [irreducibleCharacters_GL2_eq_union F E hψ, Set.image_union, Set.image_union,
    Set.image_union, hlin, hst, hps, hcusp]
  ext x
  simp
  tauto

/-- **The degrees of `GL₂(𝔽₃)` are `1`, `2`, `3` and `4`.** With the counts above, the eight
irreducible characters have degrees `1, 1, 2, 2, 2, 3, 3, 4`. -/
theorem image_apply_one_irreducibleCharacters_GL2_of_card_eq_three (hF : Fintype.card F = 3) :
    (fun χ : GL (Fin 2) F → ℂ => χ 1) '' irreducibleCharacters ℂ (GL (Fin 2) F)
      = {1, 3, 4, 2} := by
  -- A nontrivial additive character of `F`, from the duality of a finite abelian group.
  obtain ⟨ψ, hψ1⟩ := (AddChar.exists_apply_ne_zero (α := F) (a := 1)).2 one_ne_zero
  have hψ : ψ ≠ 1 := AddChar.ne_one_iff.2 ⟨1, hψ1⟩
  -- A quadratic extension of `F`, Mathlib's chosen degree-`2` extension of a finite field.
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : Algebra.IsQuadraticExtension F (FiniteField.Extension F p 2) :=
    ⟨FiniteField.finrank_extension F p 2⟩
  exact image_apply_one_irreducibleCharacters_GL2_of_card_eq_three_aux F
    (FiniteField.Extension F p 2) hψ hF

end TauCeti
