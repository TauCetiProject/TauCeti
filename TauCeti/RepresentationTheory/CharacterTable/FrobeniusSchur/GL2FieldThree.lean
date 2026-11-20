/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.RealCount
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Field.Three
-- Non-public: transporting the count of square roots of `1` along `GL₂(𝔽₃) ≃* GL₂(ZMod 3)`.
import TauCeti.Algebra.Group.SquareRoot

/-!
# The Frobenius-Schur indicators of `GL₂(𝔽₃)`

The explicit character table `TauCeti.gl2FieldThreeCharacterTable` of `GL₂(𝔽₃)` has eight rows:
the two linear characters, three cuspidal characters of degree `2`, the Steinberg character and its
twist, both of degree `3`, and one principal series character of degree `4`. This file computes
the Frobenius-Schur indicator `ν₂(χ) = |G|⁻¹ ∑_g χ(g²)` of every row: it is `0` on the two complex
conjugate cuspidal rows `3` and `4`, and `1` on the six others. In particular, of the three cuspidal
representations of degree `2`, one is orthogonal and two are of complex type, and `GL₂(𝔽₃)` has no
irreducible representation of quaternionic type.

The values are forced by three facts.

* A row has indicator `0` exactly when it is not real-valued
  (`TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff` together with `TauCeti.conj_characterTable`).
  Rows `3` and `4` take the values `∓i√2`, and every other row is integral. So rows `3` and `4`
  have indicator `0` and the others have indicator `1` or `-1`.
* The involution count `#{g : g² = 1} = ∑_χ ν₂(χ) χ(1)`
  (`TauCeti.card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree`).
* There are exactly `14` elements of `GL₂(𝔽₃)` whose square is `1`
  (`TauCeti.card_squareRoot_one_GL_fin_two_of_card_eq_three`): the two central elements `±1` and
  the twelve elements of the split class with characteristic polynomial `X² - 1`.

The degrees of the six real rows are `1, 1, 2, 3, 3, 4`, with sum `14`. A signed sum
`±1 ± 1 ± 2 ± 3 ± 3 ± 4` equals `14` only when every sign is `+`, so every real row has
indicator `1`.

The rows of `TauCeti.characterTable ℂ (GL (Fin 2) F)` are an abstract enumeration of the
irreducible characters. They are matched with the rows of the explicit matrix by any bijection
`σ` that carries one table to the other
(`TauCeti.exists_equiv_submatrix_characterTable_eq_gl2FieldThreeCharacterTable`), and the
indicators are stated along every such `σ`.

## Main statements

* `TauCeti.card_squareRoot_one_GL_fin_two_of_card_eq_three`: `GL₂(𝔽₃)` has fourteen solutions of
  `g² = 1`.
* **The Frobenius-Schur indicators of the rows of the table are `1, 1, 1, 0, 0, 1, 1, 1`**:
  `TauCeti.frobeniusSchurIndicatorRow_eq_of_submatrix_eq_gl2FieldThreeCharacterTable`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F]

/-- **`GL₂(𝔽₃)` has fourteen solutions of `g² = 1`**: the two central elements `1` and `-1`, and
the twelve elements of the split semisimple class with characteristic polynomial `X² - 1`. -/
theorem card_squareRoot_one_GL_fin_two_of_card_eq_three (hF : Fintype.card F = 3) :
    Nat.card {g : GL (Fin 2) F // g * g = 1} = 14 := by
  let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hF
  let φ : GL (Fin 2) (ZMod 3) ≃* GL (Fin 2) F := Units.mapEquiv e.mapMatrix.toMulEquiv
  -- An invertible matrix squaring to `1` is determined by its underlying matrix, and every matrix
  -- squaring to `1` is invertible, being its own inverse.
  let ψ : {g : GL (Fin 2) (ZMod 3) // g * g = 1} ≃
      {M : Matrix (Fin 2) (Fin 2) (ZMod 3) // M * M = 1} :=
    { toFun := fun g => ⟨g.1, by rw [← Units.val_mul, g.2, Units.val_one]⟩
      invFun := fun M => ⟨⟨M.1, M.1, M.2, M.2⟩, Units.ext M.2⟩
      left_inv := fun g => Subtype.ext (Units.ext rfl)
      right_inv := fun M => rfl }
  rw [← Nat.card_congr ((φ.squareRootMap 1).trans (Equiv.subtypeEquivRight fun _ => by
    rw [map_one])), Nat.card_congr ψ, Nat.card_eq_fintype_card]
  decide

/-- **The Frobenius-Schur indicators of `GL₂(𝔽₃)`**: along any enumeration `σ` of the rows of the
character table of `GL₂(F)`, for a field `F` with three elements, that turns it into the explicit
matrix `TauCeti.gl2FieldThreeCharacterTable`, the rows have indicators `1, 1, 1, 0, 0, 1, 1, 1`.

So the linear characters, the Steinberg character and its twist, the principal series character
and the cuspidal character of row `2` are orthogonal, the two complex conjugate cuspidal characters
of rows `3` and `4` are of complex type, and no row is quaternionic. Such an enumeration exists by
`TauCeti.exists_equiv_submatrix_characterTable_eq_gl2FieldThreeCharacterTable`. -/
theorem frobeniusSchurIndicatorRow_eq_of_submatrix_eq_gl2FieldThreeCharacterTable
    [Fintype (GL (Fin 2) F)] (hF : Fintype.card F = 3)
    (σ : Fin 8 ≃ Fin (Nat.card (ConjClasses (GL (Fin 2) F))))
    (hσ : (characterTable ℂ (GL (Fin 2) F)).submatrix σ
        (conjClassesGLFinTwoEquiv ∘ gl2FieldThreeClassIndex F) = gl2FieldThreeCharacterTable)
    (i : Fin 8) :
    frobeniusSchurIndicatorRow ℂ (σ i) = ![1, 1, 1, 0, 0, 1, 1, 1] i := by
  set c := conjClassesGLFinTwoEquiv ∘ gl2FieldThreeClassIndex F
  have hc : Function.Bijective c :=
    (conjClassesGLFinTwoEquiv (F := F)).bijective.comp (bijective_gl2FieldThreeClassIndex hF)
  have hval (i j : Fin 8) :
      characterTable ℂ (GL (Fin 2) F) (σ i) (c j) = gl2FieldThreeCharacterTable i j := by
    rw [← hσ, submatrix_apply]
  -- Rows `3` and `4` are not real-valued, so their indicators vanish.
  have hcomplex (j : Fin 8) (hj : j = 3 ∨ j = 4) : frobeniusSchurIndicatorRow ℂ (σ j) = 0 := by
    rw [frobeniusSchurIndicatorRow_eq_zero_iff]
    intro hinv
    have h := hinv (c 3)
    rw [← conj_characterTable, hval] at h
    have hsqrt : 0 < √2 := by positivity
    rcases hj with rfl | rfl <;> simp [Complex.ext_iff] at h <;> linarith
  -- The other six rows are integral, hence real-valued, so their indicators are `1` or `-1`.
  have hreal (j : Fin 8) (hj : j ≠ 3 ∧ j ≠ 4) :
      frobeniusSchurIndicatorRow ℂ (σ j) = 1 ∨ frobeniusSchurIndicatorRow ℂ (σ j) = -1 := by
    have hne : frobeniusSchurIndicatorRow ℂ (σ j) ≠ 0 := by
      rw [frobeniusSchurIndicatorRow_ne_zero_iff]
      intro C
      obtain ⟨k, rfl⟩ := hc.2 C
      rw [← conj_characterTable, hval]
      fin_cases j <;> fin_cases k <;> simp_all [map_ofNat]
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one ℂ (σ j) with h | h | h
    exacts [Or.inl h, absurd h hne, Or.inr h]
  -- The involution count `14 = ∑ⱼ ν₂(χⱼ) χⱼ(1)`, read along `σ`; the column `0` is the identity.
  have hone : c 0 = ConjClasses.mk 1 := by
    simp [c]
  have hcount := card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree ℂ
    (GL (Fin 2) F)
  rw [card_squareRoot_one_GL_fin_two_of_card_eq_three hF, ← σ.sum_comp] at hcount
  simp only [← characterTable_one, ← hone, hval, Fin.sum_univ_eight] at hcount
  simp only [hcomplex 3 (Or.inl rfl), hcomplex 4 (Or.inr rfl)] at hcount
  norm_num [gl2FieldThreeCharacterTable_apply] at hcount
  -- A signed sum `±1 ± 1 ± 2 ± 3 ± 3 ± 4` is `14` only when every sign is `+`.
  rcases hreal 0 (by decide) with h0 | h0 <;> rcases hreal 1 (by decide) with h1 | h1 <;>
    rcases hreal 2 (by decide) with h2 | h2 <;> rcases hreal 5 (by decide) with h5 | h5 <;>
    rcases hreal 6 (by decide) with h6 | h6 <;> rcases hreal 7 (by decide) with h7 | h7 <;>
    rw [h0, h1, h2, h5, h6, h7] at hcount <;> norm_num at hcount
  fin_cases i <;> simp [h0, h1, h2, h5, h6, h7, hcomplex]

end TauCeti
