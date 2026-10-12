/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2CharacterTable`, `TauCeti.GL2CharacterParam` and their API.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Table
-- `TauCeti.conjClassesGLFinTwoEquiv` labels the columns of the table below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: conjugating the column representatives into the normal forms at which the four
-- families of characters are evaluated.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NormalForm
-- Non-public: a root of `X² - X - 1` in the quadratic extension.
import TauCeti.FieldTheory.Quadratic
-- Non-public: the canonical additive character is nontrivial.
import TauCeti.NumberTheory.LegendreSymbol.Complex

/-!
# The character table of `GL₂(𝔽₃)`

`GL₂(𝔽₃)` is the smallest general linear group `GL₂(𝔽_q)` in which all four families of
irreducible characters occur. This file specializes the parametrized character table
`TauCeti.GL2CharacterTable` to a field `F` with three elements and writes it out as an explicit
`8 × 8` matrix of complex numbers, `TauCeti.gl2FieldThreeCharacterTable`.

The columns are the eight conjugacy classes of `GL₂(F)`, labelled through
`TauCeti.conjClassesGLFinTwoEquiv` by the two central elements `1` and `-1` and by the six
characteristic polynomials of the non-central classes, in the order below; the sizes are the class
sizes computed in `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ClassSize.lean`.

| column | class | polynomial | size |
|---|---|---|---|
| 0 | `1` | | 1 |
| 1 | `-1` | | 1 |
| 2 | elliptic, order 4 | `X² + 1` | 6 |
| 3 | elliptic, order 8 | `X² - X - 1` | 6 |
| 4 | elliptic, order 8 | `X² + X - 1` | 6 |
| 5 | unipotent | `(X - 1)²` | 8 |
| 6 | `-1` times unipotent | `(X + 1)²` | 8 |
| 7 | split semisimple | `X² - 1` | 12 |

(`TauCeti.gl2FieldThreeClassIndex`). The rows are the eight irreducible characters, ordered by
degree:

| row | character | degree |
|---|---|---|
| 0 | trivial | 1 |
| 1 | `sgn ∘ det` | 1 |
| 2, 3, 4 | cuspidal | 2 |
| 5 | Steinberg | 3 |
| 6 | Steinberg twisted by `sgn ∘ det` | 3 |
| 7 | principal series `Ind_B^{GL₂}(1 ⊗ sgn)` | 4 |

Here `sgn` is the nontrivial character of `Fˣ = {±1}`. The family of a row can be read off its
degree in column `0`, since for `q = 3` the four families have the four distinct degrees `1`, `2`,
`3` and `4`. The two cuspidal characters of rows 3 and 4 are complex conjugates, taking the values
`∓i√2` and `±i√2` on the two classes of elements of order `8`; every other entry is an integer.

The main result, `TauCeti.exists_equiv_submatrix_GL2CharacterTable_eq_gl2FieldThreeCharacterTable`,
says that for every quadratic extension `E/F` some enumeration of the parameters
`TauCeti.GL2CharacterParam F E` turns `TauCeti.GL2CharacterTable F E`, read in the columns above,
into this matrix. The rows can only be matched up to such an enumeration, because the parameters
are characters of `Fˣ` and of `Eˣ`, which carry no preferred order. Since the parametrized table is
the character table of `GL₂(F)` with relabelled rows
(`TauCeti.GL2CharacterTable_eq_submatrix_characterTable`), the matrix is the character table of
`GL₂(𝔽₃)`.

Each entry comes from the value formulas of the four families. A non-central column is first
conjugated into the normal form those formulas are stated at: a Jordan block, a diagonal matrix,
or the image `TauCeti.GL2NonSplitTorusHom F E v` of an element `v ∈ E ∖ F`. For the three elliptic
columns, `v` runs over `u ^ 2`, `u` and `-u = u ^ 5` for a fixed root `u ∈ E` of `X² - X - 1`.
That root generates the cyclic group `Eˣ` of order `8`, so the value `ζ = θ(u)` of a character
`θ` of `Eˣ` determines its cuspidal row. That row is row 2 when `ζ⁴ = 1`, and otherwise row 3 or
row 4 according to the sign in `ζ + ζ³ = ±i√2`.

## Main definitions

* `TauCeti.gl2FieldThreeClassIndex`: the labels of the eight columns.
* `TauCeti.gl2FieldThreeCharacterTable`: the character table of `GL₂(𝔽₃)`, as a matrix.

## Main results

* `TauCeti.bijective_gl2FieldThreeClassIndex`: the column labels list every conjugacy class of
  `GL₂(F)` exactly once.
* `TauCeti.exists_equiv_submatrix_GL2CharacterTable_eq_gl2FieldThreeCharacterTable`: the
  parametrized character table of `GL₂(F)` is `TauCeti.gl2FieldThreeCharacterTable` up to an
  enumeration of its rows.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

/-- **The labels of the eight conjugacy classes of `GL₂(𝔽₃)`**, as inputs to
`TauCeti.conjClassesGLFinTwoEquiv`: the central units `1` and `-1`, then the pairs `(t, d)` of the
characteristic polynomials `X² - t X + d` of the elliptic classes `X² + 1`, `X² - X - 1` and
`X² + X - 1`, of the non-semisimple classes `(X - 1)²` and `(X + 1)²`, and of the split semisimple
class `X² - 1`. Over a field with three elements these are all the classes
(`TauCeti.bijective_gl2FieldThreeClassIndex`). -/
def gl2FieldThreeClassIndex (F : Type*) [Field F] : Fin 8 → Fˣ ⊕ F × Fˣ :=
  ![.inl 1, .inl (-1), .inr (0, 1), .inr (1, -1), .inr (-1, -1), .inr (2, 1), .inr (-2, 1),
    .inr (0, -1)]

/-- The column labels, entry by entry. -/
@[simp]
theorem gl2FieldThreeClassIndex_apply (F : Type*) [Field F] (j : Fin 8) :
    gl2FieldThreeClassIndex F j =
      ![.inl 1, .inl (-1), .inr (0, 1), .inr (1, -1), .inr (-1, -1), .inr (2, 1), .inr (-2, 1),
        .inr (0, -1)] j :=
  (rfl)

/-- **The character table of `GL₂(𝔽₃)`.** The columns are the conjugacy classes labelled by
`TauCeti.gl2FieldThreeClassIndex`, of sizes `1, 1, 6, 6, 6, 8, 8, 12`. The rows are the trivial
character, the character `sgn ∘ det`, the three cuspidal characters, the Steinberg character and
its twist by `sgn ∘ det`, and the principal series character of degree `4`. -/
noncomputable def gl2FieldThreeCharacterTable : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, 1, -1, -1, 1, 1, -1;
     2, 2, 2, 0, 0, -1, -1, 0;
     2, -2, 0, -(Complex.I * √2), Complex.I * √2, -1, 1, 0;
     2, -2, 0, Complex.I * √2, -(Complex.I * √2), -1, 1, 0;
     3, 3, -1, -1, -1, 0, 0, 1;
     3, 3, -1, 1, 1, 0, 0, -1;
     4, -4, 0, 0, 0, 1, -1, 0]

/-- The entries of the character table of `GL₂(𝔽₃)`. -/
@[simp]
theorem gl2FieldThreeCharacterTable_apply (i j : Fin 8) :
    gl2FieldThreeCharacterTable i j =
      !![1, 1, 1, 1, 1, 1, 1, 1;
         1, 1, 1, -1, -1, 1, 1, -1;
         2, 2, 2, 0, 0, -1, -1, 0;
         2, -2, 0, -(Complex.I * √2), Complex.I * √2, -1, 1, 0;
         2, -2, 0, Complex.I * √2, -(Complex.I * √2), -1, 1, 0;
         3, 3, -1, -1, -1, 0, 0, 1;
         3, 3, -1, 1, 1, 0, 0, -1;
         4, -4, 0, 0, 0, 1, -1, 0] i j :=
  (rfl)

section Columns

variable {F : Type*} [Field F] [Fintype F]

/-- Over a field with three elements, the identities in `F` that the computations below need:
`3 = 0`, `1 ≠ -1`, every unit is `1` or `-1`, and `X² - X - 1` has no root. Each is read off
`ZMod 3` through the isomorphism `ZMod 3 ≃+* F`. -/
private theorem fieldThree_facts (hF : Fintype.card F = 3) :
    (3 : F) = 0 ∧ (1 : F) ≠ -1 ∧ (∀ x : Fˣ, x = 1 ∨ x = -1) ∧ ∀ a : F, a * a ≠ a + 1 := by
  let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hF
  refine ⟨by simpa only [map_ofNat, map_zero] using congrArg e (show (3 : ZMod 3) = 0 by decide),
    by simpa using e.injective.ne (show (1 : ZMod 3) ≠ -1 by decide), fun x => ?_, fun a => ?_⟩
  · obtain ⟨y, hy⟩ := e.surjective x
    have hx : (x : F) ≠ 0 := x.ne_zero
    have : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = -1 := by decide
    rcases this y with rfl | rfl | rfl
    · exact absurd (by simpa using hy.symm) hx
    · exact Or.inl (Units.ext (by simpa using hy.symm))
    · exact Or.inr (Units.ext (by simpa using hy.symm))
  · obtain ⟨y, rfl⟩ := e.surjective a
    have : ∀ y : ZMod 3, y * y ≠ y + 1 := by decide
    simpa using e.injective.ne (this y)

/-- **The labels list every conjugacy class of `GL₂(𝔽₃)` exactly once**: over a field with three
elements, `TauCeti.gl2FieldThreeClassIndex` is a bijection onto the labels of
`TauCeti.conjClassesGLFinTwoEquiv`. -/
theorem bijective_gl2FieldThreeClassIndex (hF : Fintype.card F = 3) :
    Function.Bijective (gl2FieldThreeClassIndex F) := by
  obtain ⟨h3, h1, -, -⟩ := fieldThree_facts hF
  have h2 : (2 : F) = -1 := by linear_combination h3
  refine Function.Injective.bijective_of_nat_card_le (fun i j h => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp_all [Units.ext_iff]
  · simp [Nat.card_units, hF]

variable {E : Type*} [Field E] [Algebra F E]

/-- The facts about a root `u ∈ E` of `X² - X - 1` that place the three elliptic columns: `u`,
`u ^ 2` and `-u` lie outside `F`, `u ^ 4 = -1`, and `-u = u ^ 5`. -/
private theorem units_facts (hF : Fintype.card F = 3) {u : Eˣ} (hu : (u : E) * u = u + 1) :
    (u : E) ∉ Set.range (algebraMap F E) ∧ ((u ^ 2 : Eˣ) : E) ∉ Set.range (algebraMap F E) ∧
      ((-u : Eˣ) : E) ∉ Set.range (algebraMap F E) ∧ u ^ 4 = -1 ∧ -u = u ^ 5 := by
  obtain ⟨h3, -, -, hroot⟩ := fieldThree_facts hF
  have hE3 : (3 : E) = 0 := by
    have := congrArg (algebraMap F E) h3
    rwa [map_ofNat, map_zero] at this
  have hu4 : (u : E) ^ 4 = -1 := by linear_combination ((u : E) ^ 2 + u + 2) * hu + (u + 1) * hE3
  have hnot : (u : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    exact hroot a ((algebraMap F E).injective (by simp [ha, hu]))
  refine ⟨hnot, ?_, ?_, Units.ext (by simpa using hu4), Units.ext ?_⟩
  · rintro ⟨a, ha⟩
    refine hnot ⟨a - 1, ?_⟩
    rw [Units.val_pow_eq_pow_val, pow_two, hu] at ha
    rw [map_sub, ha, map_one, add_sub_cancel_right]
  · rintro ⟨a, ha⟩
    exact hnot ⟨-a, by rw [map_neg, ha, Units.val_neg, neg_neg]⟩
  · push_cast
    linear_combination (-(u : E)) * hu4

end Columns

variable {F : Type} [Field F] [Fintype F] {E : Type*} [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- A quadratic extension of a field with three elements contains a root of `X² - X - 1`. -/
private theorem exists_units_mul_self_eq_add_one (hF : Fintype.card F = 3) :
    ∃ u : Eˣ, (u : E) * u = u + 1 := by
  obtain ⟨-, -, -, hroot⟩ := fieldThree_facts hF
  obtain ⟨x, hx⟩ := exists_mul_self_eq_of_finite E (t := (1 : F)) (d := -1)
    (fun a => by simpa using hroot a)
  have hx' : x * x = x + 1 := by simpa using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx'
  exact ⟨Units.mk0 x hx0, hx'⟩

/-- The normal forms of the eight columns of the table, for a root `u ∈ E` of `X² - X - 1`: the
two central elements, the elliptic elements attached to `u ^ 2`, `u` and `-u`, the two Jordan
blocks, and the diagonal matrix `diag(1, -1)`. -/
private noncomputable def gl2FieldThreeNormalForm (u : Eˣ) : Fin 8 → GL (Fin 2) F :=
  ![Matrix.GeneralLinearGroup.scalar (Fin 2) 1, Matrix.GeneralLinearGroup.scalar (Fin 2) (-1),
    GL2NonSplitTorusHom F E (u ^ 2), GL2NonSplitTorusHom F E u, GL2NonSplitTorusHom F E (-u),
    jordanGL 1 1, jordanGL (-1) 1, diagGL ![1, -1]]

/-- Each column representative is conjugate to its normal form. -/
private theorem isConj_gl2FieldThreeNormalForm (hF : Fintype.card F = 3) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (j : Fin 8) :
    IsConj (conjRepGLFinTwo (gl2FieldThreeClassIndex F j))
      (gl2FieldThreeNormalForm (F := F) u j) := by
  obtain ⟨-, h1, -, -⟩ := fieldThree_facts hF
  obtain ⟨hu1, hu2, hu3, hu4, -⟩ := units_facts hF hu
  have hu4' : (u : E) ^ 4 = -1 := by simpa using congrArg Units.val hu4
  fin_cases j <;>
    simp only [gl2FieldThreeClassIndex_apply, gl2FieldThreeNormalForm, Fin.reduceFinMk,
      Matrix.cons_val, conjRepGLFinTwo_inl, conjRepGLFinTwo_inr]
  · exact IsConj.refl _
  · exact IsConj.refl _
  · refine isConj_gl2NonSplitTorusHom_of_trace_of_det hu2 (t := 0) (d := 1) ?_ ?_ ?_
    · simp only [Units.val_pow_eq_pow_val, map_zero, map_one, zero_mul, zero_sub]
      linear_combination hu4'
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]
  · refine isConj_gl2NonSplitTorusHom_of_trace_of_det hu1 (t := 1) (d := -1) ?_ ?_ ?_
    · simpa using hu
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]
  · refine isConj_gl2NonSplitTorusHom_of_trace_of_det hu3 (t := -1) (d := -1) ?_ ?_ ?_
    · simpa using hu
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]
  · refine isConj_jordanGL_one_of_trace_of_det (companionGL_notMem_range_scalar _ _) ?_ ?_
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]
  · refine isConj_jordanGL_one_of_trace_of_det (companionGL_notMem_range_scalar _ _) ?_ ?_
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]
  · refine isConj_diagGL_of_trace_of_det (fun h => h1 (by simpa using congrArg Units.val h)) ?_ ?_
    · simp [trace_companionFinTwo]
    · simp [det_companionFinTwo]

/-- A character takes the same value at a column representative and at its normal form. -/
private theorem character_conjRepGLFinTwo_gl2FieldThreeClassIndex (hF : Fintype.card F = 3)
    {u : Eˣ} (hu : (u : E) * u = u + 1) (V : FDRep ℂ (GL (Fin 2) F)) (j : Fin 8) :
    V.character (conjRepGLFinTwo (gl2FieldThreeClassIndex F j)) =
      V.character (gl2FieldThreeNormalForm (F := F) u j) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_gl2FieldThreeNormalForm hF hu j)
  rw [← hc, FDRep.char_conj]

/-- The Steinberg character at the eight normal forms. -/
private theorem character_GL2Steinberg_gl2FieldThreeNormalForm (hF : Fintype.card F = 3)
    {u : Eˣ} (hu : (u : E) * u = u + 1) (j : Fin 8) :
    (GL2Steinberg F).character (gl2FieldThreeNormalForm (F := F) u j) =
      ![3, 3, -1, -1, -1, 0, 0, 1] j := by
  obtain ⟨-, h1, -, -⟩ := fieldThree_facts hF
  obtain ⟨hu1, hu2, hu3, -, -⟩ := units_facts hF hu
  fin_cases j <;> simp only [gl2FieldThreeNormalForm, Fin.reduceFinMk, Matrix.cons_val]
  · rw [character_GL2Steinberg_scalar, hF]
    norm_num
  · rw [character_GL2Steinberg_scalar, hF]
    norm_num
  · exact character_GL2Steinberg_gl2NonSplitTorusHom hu2
  · exact character_GL2Steinberg_gl2NonSplitTorusHom hu1
  · exact character_GL2Steinberg_gl2NonSplitTorusHom hu3
  · exact character_GL2Steinberg_jordanGL 1 one_ne_zero
  · exact character_GL2Steinberg_jordanGL (-1) one_ne_zero
  · exact character_GL2Steinberg_diagGL fun h => h1 (by simpa using congrArg Units.val h)

/-- The row of a linear character `α ∘ det` is row `0` or row `1` of the table. -/
private theorem exists_linear_row (α : Fˣ →* ℂˣ) :
    ∃ k, ∀ j, ((GL2CharacterParam.linear (E := E) α).classFunction : GL (Fin 2) F → ℂ)
      (conjRepGLFinTwo (gl2FieldThreeClassIndex F j)) = gl2FieldThreeCharacterTable k j := by
  simp only [GL2CharacterParam.coe_classFunction_linear, character_GL2Linear]
  rcases val_apply_neg_one_eq_one_or_eq_neg_one (α := α) with hα | hα
  · refine ⟨0, fun j => ?_⟩
    fin_cases j <;> simp [det_companionGL, hα]
  · refine ⟨1, fun j => ?_⟩
    fin_cases j <;> simp [det_companionGL, hα]

/-- The row of a Steinberg twist `(α ∘ det) ⊗ St` is row `5` or row `6` of the table. -/
private theorem exists_steinbergTwist_row (hF : Fintype.card F = 3) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (α : Fˣ →* ℂˣ) :
    ∃ k, ∀ j, ((GL2CharacterParam.steinbergTwist (E := E) α).classFunction : GL (Fin 2) F → ℂ)
      (conjRepGLFinTwo (gl2FieldThreeClassIndex F j)) = gl2FieldThreeCharacterTable k j := by
  simp only [GL2CharacterParam.coe_classFunction_steinbergTwist, character_GL2SteinbergTwist]
  simp only [character_conjRepGLFinTwo_gl2FieldThreeClassIndex hF hu (GL2Steinberg F),
    character_GL2Steinberg_gl2FieldThreeNormalForm hF hu]
  rcases val_apply_neg_one_eq_one_or_eq_neg_one (α := α) with hα | hα
  · refine ⟨5, fun j => ?_⟩
    fin_cases j <;> simp [det_companionGL, hα]
  · refine ⟨6, fun j => ?_⟩
    fin_cases j <;> simp [det_companionGL, hα]

/-- The row of a principal series `Ind_B^{GL₂}(α ⊗ β)` is row `7` of the table: there is a single
unordered pair `{α, β} = {1, sgn}` of distinct characters of `Fˣ = {±1}`. -/
private theorem exists_principalSeries_row (hF : Fintype.card F = 3) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (s : Sym2 (Fˣ →* ℂˣ)) (hs : ¬ s.IsDiag) :
    ∃ k, ∀ j, ((GL2CharacterParam.principalSeries (E := E) s hs).classFunction :
      GL (Fin 2) F → ℂ) (conjRepGLFinTwo (gl2FieldThreeClassIndex F j)) =
        gl2FieldThreeCharacterTable k j := by
  obtain ⟨-, h1, hunits, -⟩ := fieldThree_facts hF
  obtain ⟨hu1, hu2, hu3, -, -⟩ := units_facts hF hu
  induction s using Sym2.ind with
  | _ α β =>
  -- two characters of `Fˣ = {±1}` are distinguished by their values at `-1`
  have hne : (α (-1) : ℂ) ≠ β (-1) := fun h => Sym2.mk_isDiag_iff.not.mp hs <|
    MonoidHom.ext fun x => by
      rcases hunits x with rfl | rfl
      · simp
      · exact Units.ext h
  have hprod : (α (-1) : ℂ) * β (-1) = -1 ∧ (β (-1) : ℂ) + α (-1) = 0 := by
    rcases val_apply_neg_one_eq_one_or_eq_neg_one (α := α) with ha | ha <;>
      rcases val_apply_neg_one_eq_one_or_eq_neg_one (α := β) with hb | hb <;>
      simp_all
  have hab : (1 : Fˣ) ≠ -1 := fun h => h1 (by simpa using congrArg Units.val h)
  refine ⟨7, fun j => ?_⟩
  rw [GL2CharacterParam.coe_classFunction_principalSeries_mk,
    character_conjRepGLFinTwo_gl2FieldThreeClassIndex hF hu]
  fin_cases j <;>
    simp only [gl2FieldThreeNormalForm, gl2FieldThreeCharacterTable_apply, Fin.reduceFinMk,
      Matrix.cons_val, Matrix.of_apply]
  · rw [character_GL2PrincipalSeries_scalar, hF]
    norm_num
  · rw [character_GL2PrincipalSeries_scalar, hF, hprod.1]
    norm_num
  · exact character_GL2PrincipalSeries_gl2NonSplitTorusHom α β hu2
  · exact character_GL2PrincipalSeries_gl2NonSplitTorusHom α β hu1
  · exact character_GL2PrincipalSeries_gl2NonSplitTorusHom α β hu3
  · rw [character_GL2PrincipalSeries_jordanGL α β 1 one_ne_zero]
    simp
  · rw [character_GL2PrincipalSeries_jordanGL α β (-1) one_ne_zero, hprod.1]
  · rw [character_GL2PrincipalSeries_diagGL α β hab]
    simpa using hprod.2

/-- The cuspidal character attached to `θ` at the eight normal forms, in terms of `ζ = θ(u)`. -/
private theorem cuspidal_apply_gl2FieldThreeNormalForm (hF : Fintype.card F = 3) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (θ : Eˣ →* ℂˣ) (j : Fin 8) :
    (GL2CuspidalVirtualCharacter F E θ (AddChar.FiniteField.primitiveChar_to_Complex F)).1
        (gl2FieldThreeNormalForm u j) =
      ![2, 2 * (θ u : ℂ) ^ 4, -((θ u : ℂ) ^ 2 + (θ u : ℂ) ^ 6), -((θ u : ℂ) + (θ u : ℂ) ^ 3),
        -((θ u : ℂ) ^ 5 + (θ u : ℂ) ^ 15), -1, -(θ u : ℂ) ^ 4, 0] j := by
  obtain ⟨-, h1, -, -⟩ := fieldThree_facts hF
  obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := units_facts hF hu
  have hψ := primitiveChar_to_Complex_ne_one F
  -- the scalar `-1` of `F`, as a unit of `E`, is `u ^ 4`
  have hneg : Units.map (algebraMap F E : F →* E) (-1) = u ^ 4 := by
    rw [hu4]
    ext
    simp
  fin_cases j <;>
    simp only [gl2FieldThreeNormalForm, Fin.reduceFinMk, Matrix.cons_val]
  · rw [GL2CuspidalVirtualCharacter_apply_scalar, hF, map_one, map_one]
    norm_num
  · rw [GL2CuspidalVirtualCharacter_apply_scalar, hF, hneg, map_pow, Units.val_pow_eq_pow_val]
    norm_num
  · rw [GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ hu2]
    simp [hF, ← pow_mul]
  · rw [GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ hu1, hF, map_pow,
      Units.val_pow_eq_pow_val]
  · rw [GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ hu3]
    simp [hF, hu5, ← pow_mul]
  · rw [GL2CuspidalVirtualCharacter_apply_jordanGL _ hψ 1 one_ne_zero, map_one, map_one,
      Units.val_one]
  · rw [GL2CuspidalVirtualCharacter_apply_jordanGL _ hψ (-1) one_ne_zero, hneg, map_pow,
      Units.val_pow_eq_pow_val]
  · exact GL2CuspidalVirtualCharacter_apply_diagGL _ _
      (fun h => h1 (by simpa using congrArg Units.val h))

/-- A root `u ∈ E` of `X² - X - 1` generates `Eˣ`: it has order `8`, as many as there are units
of the field with nine elements. -/
private theorem exists_zpow_eq (hF : Fintype.card F = 3) {u : Eˣ} (hu : (u : E) * u = u + 1)
    (v : Eˣ) : ∃ n : ℤ, u ^ n = v := by
  obtain ⟨-, h1, -, -⟩ := fieldThree_facts hF
  obtain ⟨-, -, -, hu4, -⟩ := units_facts hF hu
  have : Finite E := Module.finite_of_finite F
  have hcard : Nat.card Eˣ = 2 ^ 3 := by
    rw [Nat.card_units, Module.natCard_eq_pow_finrank (K := F) (V := E),
      Algebra.IsQuadraticExtension.finrank_eq_two F E, Nat.card_eq_fintype_card, hF]
    norm_num
  have hord : orderOf u = 2 ^ 3 := by
    refine orderOf_eq_prime_pow (fun h => h1 ((algebraMap F E).injective ?_)) ?_
    · have := congrArg Units.val (hu4.symm.trans h)
      simpa using this.symm
    · rw [pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, hu4]
      simp
  rw [← Subgroup.mem_zpowers_iff,
    Subgroup.eq_top_of_card_eq (Subgroup.zpowers u) (by rw [Nat.card_zpowers, hord, hcard])]
  trivial

/-- The row of a cuspidal character is row `2`, `3` or `4` of the table. With `ζ = θ(u)` a
primitive `4`th or `8`th root of unity, it is row `2` when `ζ⁴ = 1`, and otherwise row `3` or `4`
according as `ζ + ζ³` is `i√2` or `-i√2`. -/
private theorem exists_cuspidal_row (hF : Fintype.card F = 3) {u : Eˣ}
    (hu : (u : E) * u = u + 1) (o : Quotient (gl2CuspidalSetoid F E)) :
    ∃ k, ∀ j, ((GL2CharacterParam.cuspidal o).classFunction : GL (Fin 2) F → ℂ)
      (conjRepGLFinTwo (gl2FieldThreeClassIndex F j)) = gl2FieldThreeCharacterTable k j := by
  induction o using Quotient.ind with
  | _ θ =>
  obtain ⟨θ, hθ⟩ := θ
  obtain ⟨-, -, -, hu4, -⟩ := units_facts hF hu
  simp only [GL2CharacterParam.coe_classFunction_cuspidal_mk,
    character_conjRepGLFinTwo_gl2FieldThreeClassIndex hF hu, character_GL2Cuspidal,
    cuspidal_apply_gl2FieldThreeNormalForm hF hu]
  set ζ : ℂ := (θ u : ℂ)
  have h8 : ζ ^ 8 = 1 := by
    have hu8 : u ^ 8 = 1 := by
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hu4]
      simp
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hu8, map_one, Units.val_one]
  -- `θ ^ q ≠ θ` says exactly that `ζ² ≠ 1`, since `u` generates `Eˣ`
  have h2 : ζ ^ 2 ≠ 1 := fun hζ => hθ <| MonoidHom.ext fun v => by
    have hw : θ u * θ u = 1 := Units.ext (by rw [Units.val_mul, ← pow_two]; exact hζ)
    obtain ⟨n, rfl⟩ := exists_zpow_eq hF hu v
    simp [hF, pow_three, ← mul_zpow, hw]
  have hI : (Complex.I * √2) ^ 2 = -2 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rcases mul_eq_zero.mp (show (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 by linear_combination h8)
    with h4 | h4
  · -- `ζ` is a primitive fourth root of unity
    have hz : ζ ^ 2 = -1 := by
      rcases mul_eq_zero.mp (show (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 by linear_combination h4)
        with h | h
      · exact absurd (sub_eq_zero.mp h) h2
      · linear_combination h
    have p3 : ζ ^ 3 = -ζ := by linear_combination ζ * hz
    have p4 : ζ ^ 4 = 1 := by linear_combination h4
    have p5 : ζ ^ 5 = ζ := by linear_combination (ζ ^ 3 - ζ) * hz
    have p6 : ζ ^ 6 = -1 := by linear_combination (ζ ^ 4 - ζ ^ 2 + 1) * hz
    have p15 : ζ ^ 15 = -ζ := by
      linear_combination ζ * (ζ ^ 12 - ζ ^ 10 + ζ ^ 8 - ζ ^ 6 + ζ ^ 4 - ζ ^ 2 + 1) * hz
    refine ⟨2, fun j => ?_⟩
    fin_cases j <;> simp [hz, p3, p4, p5, p6, p15, one_add_one_eq_two]
  · -- `ζ` is a primitive eighth root of unity, and `(ζ + ζ³)² = -2`
    have hs : (ζ + ζ ^ 3) ^ 2 = (Complex.I * √2) ^ 2 := by
      rw [hI]
      linear_combination (ζ ^ 2 + 2) * h4
    have p4 : ζ ^ 4 = -1 := by linear_combination h4
    have p5 : ζ ^ 5 = -ζ := by linear_combination ζ * h4
    have p6 : ζ ^ 6 = -ζ ^ 2 := by linear_combination ζ ^ 2 * h4
    have p15 : ζ ^ 15 = -ζ ^ 3 := by linear_combination ζ ^ 3 * (ζ ^ 8 - ζ ^ 4 + 1) * h4
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · refine ⟨3, fun j => ?_⟩
      fin_cases j <;> simp [p4, p5, p6, p15, add_comm (ζ ^ 3) ζ, hs]
    · refine ⟨4, fun j => ?_⟩
      fin_cases j <;> simp [p4, p5, p6, p15, add_comm (ζ ^ 3) ζ, hs]

variable (E) in
/-- **The character table of `GL₂(𝔽₃)`.** For a field `F` with three elements and any quadratic
extension `E/F`, some enumeration of the parameters of the irreducible characters turns the
character table `TauCeti.GL2CharacterTable F E`, read in the columns labelled by
`TauCeti.gl2FieldThreeClassIndex`, into the explicit matrix `TauCeti.gl2FieldThreeCharacterTable`.
Those columns list every conjugacy class exactly once (`TauCeti.bijective_gl2FieldThreeClassIndex`),
so this is the whole table. -/
theorem exists_equiv_submatrix_GL2CharacterTable_eq_gl2FieldThreeCharacterTable
    (hF : Fintype.card F = 3) :
    ∃ e : Fin 8 ≃ GL2CharacterParam F E,
      (GL2CharacterTable F E).submatrix e (conjClassesGLFinTwoEquiv ∘ gl2FieldThreeClassIndex F) =
        gl2FieldThreeCharacterTable := by
  obtain ⟨u, hu⟩ := exists_units_mul_self_eq_add_one (E := E) hF
  -- every row of the parametrized table is a row of the explicit matrix
  have hrow : ∀ i : GL2CharacterParam F E, ∃ k, ∀ j,
      GL2CharacterTable F E i (conjClassesGLFinTwoEquiv (gl2FieldThreeClassIndex F j)) =
        gl2FieldThreeCharacterTable k j := by
    intro i
    simp only [conjClassesGLFinTwoEquiv_apply, GL2CharacterTable_apply]
    rcases i with α | α | ⟨s, hs⟩ | o
    · exact exists_linear_row α
    · exact exists_steinbergTwist_row hF hu α
    · exact exists_principalSeries_row hF hu s hs
    · exact exists_cuspidal_row hF hu o
  apply exists_equiv_submatrix_GL2CharacterTable_eq
    (conjClassesGLFinTwoEquiv ∘ gl2FieldThreeClassIndex F)
    ((conjClassesGLFinTwoEquiv (F := F)).bijective.comp (bijective_gl2FieldThreeClassIndex hF))
    gl2FieldThreeCharacterTable hrow
  rw [natCard_GL2CharacterParam, hF, Nat.card_fin]
  norm_num

end TauCeti
