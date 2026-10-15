/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GL2.Table
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NormalForm
import TauCeti.FieldTheory.Quadratic
import TauCeti.NumberTheory.LegendreSymbol.Complex

/-!
# The character table of `GL₂(𝔽₂)`

Over a field with two elements the principal-series family is empty, and the cuspidal
character has degree one. This file computes the full table, not just the degrees, from
`TauCeti.GL2CharacterTable` and the existing character-value formulas. Its columns are the
identity, the nonidentity unipotent class, and the elliptic class, labelled respectively by
`1`, `(X - 1)²`, and `X² + X + 1` through `TauCeti.conjClassesGLFinTwoEquiv`.
The rows are the trivial, cuspidal, and Steinberg characters, with degrees `1, 1, 2`.
Thus the matrix is the familiar table of `S₃`, with columns of sizes `1, 3, 2`.

## Main results

* `TauCeti.bijective_gl2FieldTwoClassIndex`: the three columns exhaust the conjugacy classes.
* `TauCeti.exists_equiv_submatrix_GL2CharacterTable_eq_gl2FieldTwoCharacterTable`: the
  parametrized table is the explicit `3 × 3` matrix after enumerating its rows.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

/-- The three class labels of `GL₂(𝔽₂)`: the identity, the nonidentity unipotent class,
and the elliptic class with characteristic polynomial `X² + X + 1`. -/
def gl2FieldTwoClassIndex (F : Type*) [Field F] : Fin 3 → Fˣ ⊕ F × Fˣ :=
  ![.inl 1, .inr (0, 1), .inr (1, 1)]

/-- The column labels, entry by entry. -/
@[simp]
theorem gl2FieldTwoClassIndex_apply (F : Type*) [Field F] (j : Fin 3) :
    gl2FieldTwoClassIndex F j = ![.inl 1, .inr (0, 1), .inr (1, 1)] j :=
  (rfl)

/-- The character table of `GL₂(𝔽₂)`, with rows trivial, cuspidal, and Steinberg,
and columns identity, nonidentity unipotent, and elliptic. -/
noncomputable def gl2FieldTwoCharacterTable : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; 1, -1, 1; 2, 0, -1]

/-- The entries of the character table of `GL₂(𝔽₂)`. -/
@[simp]
theorem gl2FieldTwoCharacterTable_apply (i j : Fin 3) :
    gl2FieldTwoCharacterTable i j = !![1, 1, 1; 1, -1, 1; 2, 0, -1] i j :=
  (rfl)

section Columns

variable {F : Type*} [Field F] [Fintype F]

/-- The column labels list every conjugacy class of `GL₂(𝔽₂)` exactly once. -/
theorem bijective_gl2FieldTwoClassIndex (hF : Fintype.card F = 2) :
    Function.Bijective (gl2FieldTwoClassIndex F) := by
  refine Function.Injective.bijective_of_nat_card_le (fun i j h => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp_all
  · simp [Nat.card_units, hF]

/-- The field identities needed for the three column calculations. -/
private theorem fieldTwo_facts (hF : Fintype.card F = 2) :
    (2 : F) = 0 ∧ (∀ a : F, a * a ≠ a + 1) := by
  let e := ZMod.ringEquivOfPrime F Nat.prime_two hF
  refine ⟨?_, fun a => ?_⟩
  · have hz : (2 : ZMod 2) = 0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg e hz
  · obtain ⟨b, rfl⟩ := e.surjective a
    have hb : ∀ b : ZMod 2, b * b ≠ b + 1 := by decide
    simpa using e.injective.ne (hb b)

variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- The quadratic extension contains a root of `X² + X + 1`, outside the base field. -/
private theorem exists_fieldTwo_root (hF : Fintype.card F = 2) :
    ∃ u : Eˣ, (u : E) * u = u + 1 ∧ (u : E) ∉ Set.range (algebraMap F E) := by
  obtain ⟨-, hroot⟩ := fieldTwo_facts hF
  obtain ⟨x, hx⟩ := exists_mul_self_eq_of_finite E (t := (1 : F)) (d := -1)
    (fun a => by simpa using hroot a)
  have hx' : x * x = x + 1 := by simpa using hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx'
  refine ⟨Units.mk0 x hx0, hx', ?_⟩
  rintro ⟨a, ha⟩
  exact hroot a ((algebraMap F E).injective (by simp [ha, hx']))

/-- The three normal forms at which the character formulas are evaluated. -/
private noncomputable def fieldTwoNormalForm (u : Eˣ) : Fin 3 → GL (Fin 2) F :=
  ![Matrix.GeneralLinearGroup.scalar (Fin 2) 1, jordanGL 1 1, GL2NonSplitTorusHom F E u]

/-- A column representative is conjugate to its normal form. -/
private theorem isConj_fieldTwoNormalForm (hF : Fintype.card F = 2) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (hout : (u : E) ∉ Set.range (algebraMap F E)) (j : Fin 3) :
    IsConj (conjRepGLFinTwo (gl2FieldTwoClassIndex F j)) (fieldTwoNormalForm (F := F) u j) := by
  obtain ⟨h2, -⟩ := fieldTwo_facts hF
  have hE2 : (2 : E) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap F E) h2
  fin_cases j <;> simp only [gl2FieldTwoClassIndex_apply, fieldTwoNormalForm,
    Fin.reduceFinMk, Matrix.cons_val, conjRepGLFinTwo_inl, conjRepGLFinTwo_inr]
  · exact IsConj.refl _
  · refine isConj_jordanGL_one_of_trace_of_det (companionGL_notMem_range_scalar _ _) ?_ ?_
    · simp [trace_companionFinTwo, h2]
    · simp [det_companionFinTwo]
  · refine isConj_gl2NonSplitTorusHom_of_trace_of_det hout (t := 1) (d := 1) ?_ ?_ ?_
    · simp only [map_one, one_mul]
      linear_combination hu + hE2
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]

/-- Characters agree on a representative and its normal form. -/
private theorem character_fieldTwoNormalForm (hF : Fintype.card F = 2) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (hout : (u : E) ∉ Set.range (algebraMap F E))
    (V : FDRep ℂ (GL (Fin 2) F)) (j : Fin 3) :
    V.character (conjRepGLFinTwo (gl2FieldTwoClassIndex F j)) =
      V.character (fieldTwoNormalForm (F := F) u j) := by
  simpa only [ClassFunction.ofFDRep_apply] using
    ClassFunction.eq_of_isConj (ClassFunction.ofFDRep V)
      (isConj_fieldTwoNormalForm hF hu hout j)

/-- A general-position character of the extension takes primitive cube-root values at `u`. -/
private theorem fieldTwo_cuspidal_value (hF : Fintype.card F = 2) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (hout : (u : E) ∉ Set.range (algebraMap F E))
    (θ : Eˣ →* ℂˣ) (hθ : θ.comp (powMonoidHom (Fintype.card F)) ≠ θ) :
    (θ u : ℂ) + (θ u : ℂ) ^ 2 = -1 := by
  obtain ⟨h2, -⟩ := fieldTwo_facts hF
  have hE2 : (2 : E) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap F E) h2
  have hu3 : u ^ 3 = 1 := Units.ext (by
    push_cast
    linear_combination ((u : E) + 1) * hu + (u : E) * hE2)
  have : Finite E := Module.finite_of_finite F
  have hcard : Nat.card Eˣ = 3 := by
    rw [Nat.card_units, Module.natCard_eq_pow_finrank (K := F),
      Algebra.IsQuadraticExtension.finrank_eq_two F E, Nat.card_eq_fintype_card, hF]
    norm_num
  have hgen : Subgroup.zpowers u = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3 (by rintro rfl; exact hout ⟨1, by simp⟩), hcard])
  have hne : (θ u : ℂ) ≠ 1 := by
    intro h
    have hθu : θ u = 1 := Units.ext h
    apply hθ
    ext v
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen ▸ Subgroup.mem_top v)
    simp [hθu]
  have hζ3 : (θ u : ℂ) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hu3, map_one, Units.val_one]
  have hprim := isPrimitiveRoot_of_mem_nthRootsFinset Nat.prime_three
    ((Polynomial.mem_nthRootsFinset (by norm_num) (1 : ℂ)).mpr hζ3) hne
  have hz := hprim.geom_sum_eq_zero (by norm_num)
  norm_num [Finset.sum_range_succ] at hz
  linear_combination hz

end Columns

variable {F : Type} [Field F] [Fintype F] {E : Type*} [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- Each parameter gives one of the three explicit rows. -/
private theorem exists_fieldTwo_row (hF : Fintype.card F = 2) (i : GL2CharacterParam F E) :
    ∃ k, ∀ j,
      GL2CharacterTable F E i (conjClassesGLFinTwoEquiv (gl2FieldTwoClassIndex F j)) =
        gl2FieldTwoCharacterTable k j := by
  have hunit : Subsingleton Fˣ := by
    rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units, Nat.card_eq_fintype_card, hF]
  obtain ⟨u, hu, hout⟩ := exists_fieldTwo_root (E := E) hF
  simp only [conjClassesGLFinTwoEquiv_apply, GL2CharacterTable_apply]
  rcases i with α | α | ⟨s, hs⟩ | o
  · refine ⟨0, fun j => ?_⟩
    rw [GL2CharacterParam.coe_classFunction_linear, character_GL2Linear,
      Subsingleton.elim (Matrix.GeneralLinearGroup.det _) 1]
    fin_cases j <;> simp
  · refine ⟨2, fun j => ?_⟩
    rw [GL2CharacterParam.coe_classFunction_steinbergTwist, character_GL2SteinbergTwist,
      Subsingleton.elim (Matrix.GeneralLinearGroup.det _) 1, map_one, Units.val_one, one_mul,
      character_fieldTwoNormalForm hF hu hout]
    fin_cases j <;> simp only [fieldTwoNormalForm, Fin.reduceFinMk, Matrix.cons_val,
      gl2FieldTwoCharacterTable_apply, Matrix.of_apply]
    · rw [character_GL2Steinberg_scalar, hF]
      norm_num
    · exact character_GL2Steinberg_jordanGL 1 one_ne_zero
    · exact character_GL2Steinberg_gl2NonSplitTorusHom hout
  · induction s using Sym2.ind with
    | _ α β => exact (Sym2.mk_isDiag_iff.not.mp hs (Subsingleton.elim α β)).elim
  · induction o using Quotient.ind with
    | _ θ =>
    refine ⟨1, fun j => ?_⟩
    rw [GL2CharacterParam.coe_classFunction_cuspidal_mk,
      character_fieldTwoNormalForm hF hu hout, character_GL2Cuspidal]
    have hψ := primitiveChar_to_Complex_ne_one F
    fin_cases j <;> simp only [fieldTwoNormalForm, Fin.reduceFinMk, Matrix.cons_val,
      gl2FieldTwoCharacterTable_apply, Matrix.of_apply]
    · rw [GL2CuspidalVirtualCharacter_apply_scalar]
      norm_num [hF]
    · rw [GL2CuspidalVirtualCharacter_apply_jordanGL _ hψ 1 one_ne_zero,
        map_one, map_one, Units.val_one]
    · rw [GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ hout]
      simp only [hF, map_pow, Units.val_pow_eq_pow_val,
        fieldTwo_cuspidal_value hF hu hout θ.1 θ.2]
      norm_num

/-- The full character table of `GL₂(𝔽₂)`: for any quadratic extension, an enumeration of
its irreducible parameters gives the explicit matrix, with the columns labelled by
`TauCeti.gl2FieldTwoClassIndex`. -/
theorem exists_equiv_submatrix_GL2CharacterTable_eq_gl2FieldTwoCharacterTable
    (hF : Fintype.card F = 2) :
    ∃ e : Fin 3 ≃ GL2CharacterParam F E,
      (GL2CharacterTable F E).submatrix e (conjClassesGLFinTwoEquiv ∘ gl2FieldTwoClassIndex F) =
        gl2FieldTwoCharacterTable := by
  apply exists_equiv_submatrix_GL2CharacterTable_eq
    (conjClassesGLFinTwoEquiv ∘ gl2FieldTwoClassIndex F)
    ((conjClassesGLFinTwoEquiv (F := F)).bijective.comp (bijective_gl2FieldTwoClassIndex hF))
    gl2FieldTwoCharacterTable (exists_fieldTwo_row hF)
  rw [natCard_GL2CharacterParam, hF, Nat.card_fin]
  norm_num

end TauCeti
