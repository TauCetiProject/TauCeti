/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Solvable
public import TauCeti.FieldTheory.Normal.AlgClosed
public import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
public import TauCeti.NumberTheory.ModularForms.Newforms.Hecke.Charpoly
public import TauCeti.NumberTheory.NumberField.NormalClosure

import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.Minpoly

/-!
# Galois closures and Galois-group certification for newform coefficient fields

For a newform `f` of level `N` and weight `k ≥ 2`, the coefficient field `CoefficientField f` is a
number field embedded in `ℂ` (`TauCeti.numberField_CoefficientField`). Because `ℂ / ℚ` is
algebraically closed rather than algebraic, Mathlib's `[Normal ℚ Ω]`-based normal-closure API does
not apply directly to `IntermediateField.normalClosure ℚ (CoefficientField f) ℂ`. Combining the
algebraically closed normal-closure API of `TauCeti.FieldTheory.Normal.AlgClosed` with the
polynomial Galois-group certificates of `TauCeti.FieldTheory.GaloisGroups.Certificate.Solvable`
yields a complete certification pipeline for the Galois closure of `CoefficientField f` over `ℚ`:

1. **Galois closure of the coefficient field.** `CoefficientFieldGaloisClosure f` is the normal
   closure of `CoefficientField f` inside `ℂ`. In weight `k ≥ 2` it is a number field, Galois over
   `ℚ`, and canonically equipped with `TauCeti.NumberField.NormalClosureData`.
2. **Single-coefficient generation and Galois restriction.** Every positive Fourier coefficient
   `aₙ(f)` is a root of the Hecke characteristic polynomial
   `(heckeTCuspNewCharEnd k f.χ n).charpoly` (`TauCeti.isRoot_charpoly_heckeTCuspNewCharEnd`).
   Whenever `aₙ(f)` is annihilated by a monic polynomial `P : ℤ[X]` irreducible over `ℚ`,
   `minpoly ℚ aₙ(f)` equals `P.map (Int.castRingHom ℚ)`, restriction gives a surjective
   homomorphism `Gal(CoefficientFieldGaloisClosure f/ℚ) →* (P.map (Int.castRingHom ℚ)).Gal`, and
   when `[CoefficientField f : ℚ] ≤ P.natDegree` the single coefficient `aₙ(f)` generates
   `CoefficientField f` and this restriction upgrades to a group isomorphism.
3. **Certificate-driven solvability and full symmetric group theorems.**
   * Any `cert : SolvabilityCertificate` with `cert.check P = true` and `cert.isSolvable = false`
     for a monic integral polynomial `P` vanishing at `aₙ(f)` refutes solvability of
     `Gal(CoefficientFieldGaloisClosure f/ℚ)` directly
     (`not_isSolvable_CoefficientFieldGaloisClosure_of_check_eq_true`), with irreducibility of `P`
     extracted automatically from the certificate.
   * When `[CoefficientField f : ℚ] ≤ P.natDegree` and `P` is irreducible over `ℚ`, a verified
     `SolvabilityCertificate` decides solvability of `Gal(CoefficientFieldGaloisClosure f/ℚ)` in
     both directions (`isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true`), and a
     verified `{d}` + `{1, …, 1, 2}` Frobenius-cycle certificate (`primeLinearQuadratic d p q`)
     proves non-solvability
     (`not_isSolvable_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`),
     single-coefficient generation (`CoefficientField_eq_adjoin_of_primeLinearQuadratic`), and
     `|Gal(CoefficientFieldGaloisClosure f/ℚ)| = d!`
     (`natCard_gal_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`).
4. **The Ramanujan discriminant newform.** Upgrading `discriminantEigenform` via
   `HeckeRing.GL2.Eigenform.toNewformOfLevelOne` gives `discriminantNewform : Newform 1 12` with
   `CoefficientField discriminantNewform = ⊥`, `CoefficientFieldGaloisClosure discriminantNewform =
   ⊥`, and certified solvability via `τ(2) = -24` and `X + 24`.

## Main definitions and results

* `TauCeti.CoefficientFieldGaloisClosure`: the Galois closure of `CoefficientField f` in `ℂ`.
* `TauCeti.numberField_CoefficientFieldGaloisClosure`,
  `TauCeti.isGalois_CoefficientFieldGaloisClosure`,
  `TauCeti.normalClosureDataCoefficientField`: number-field and Galois-closure structure in weight
  `k ≥ 2`.
* `TauCeti.restrictCoefficientFieldGalHom`, `TauCeti.restrictCoefficientFieldGalHom_commutes`,
  `TauCeti.coe_restrictCoefficientFieldGalHom_commutes`,
  `TauCeti.restrictCoefficientFieldGalHom_surjective`,
  `TauCeti.galCoefficientFieldGaloisClosureEquiv`,
  `TauCeti.galCoefficientFieldGaloisClosureEquiv_commutes`,
  `TauCeti.coe_galCoefficientFieldGaloisClosureEquiv_commutes`,
  `TauCeti.galCoefficientFieldGaloisClosureEquiv_symm_apply`: restriction to and isomorphism with
  `(minpoly ℚ α).Gal`, together with their action-intertwining lemmas.
* `TauCeti.not_isSolvable_CoefficientFieldGaloisClosure_of_check_eq_true`,
  `TauCeti.isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true`,
  `TauCeti.not_isSolvable_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`,
  `TauCeti.CoefficientField_eq_adjoin_of_primeLinearQuadratic`,
  `TauCeti.natCard_gal_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`: certificate-driven
  Galois-group and solvability theorems for newforms.
* `TauCeti.discriminantNewform`,
  `TauCeti.isSolvable_CoefficientFieldGaloisClosure_discriminantNewform`: concrete end-to-end
  instantiation on `Δ`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.8 and §6.5.
-/

public section
noncomputable section

open IntermediateField Polynomial UpperHalfPlane ModularForm CongruenceSubgroup HeckeRing.GL2
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace TauCeti

section NewformGaloisClosure

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The **Galois closure of the coefficient field** of a newform `f` inside `ℂ`: the normal closure
over `ℚ` of `CoefficientField f = ℚ(aₙ(f) : n ≥ 1)`. -/
def CoefficientFieldGaloisClosure (f : Newform N k) : IntermediateField ℚ ℂ :=
  IntermediateField.normalClosure ℚ (CoefficientField f) ℂ

/-- Defining equation for `CoefficientFieldGaloisClosure`. -/
theorem CoefficientFieldGaloisClosure_def (f : Newform N k) :
    CoefficientFieldGaloisClosure f =
      IntermediateField.normalClosure ℚ (CoefficientField f) ℂ := (rfl)

/-- `CoefficientField f` is contained in its Galois closure `CoefficientFieldGaloisClosure f`. -/
theorem le_CoefficientFieldGaloisClosure (f : Newform N k) :
    CoefficientField f ≤ CoefficientFieldGaloisClosure f :=
  IntermediateField.le_normalClosure (CoefficientField f)

/-- Every positive-index Fourier coefficient of `f` belongs to `CoefficientFieldGaloisClosure f`. -/
@[simp]
theorem coeff_mem_CoefficientFieldGaloisClosure (f : Newform N k) (n : ℕ+) :
    (qExpansion 1 f.toCuspForm).coeff (n : ℕ) ∈ CoefficientFieldGaloisClosure f :=
  le_CoefficientFieldGaloisClosure f (coeff_mem_CoefficientField f n)

/-- The character field `CharacterField f.χ` is contained in `CoefficientFieldGaloisClosure f`. -/
theorem CharacterField_le_CoefficientFieldGaloisClosure (f : Newform N k) :
    CharacterField f.χ ≤ CoefficientFieldGaloisClosure f :=
  (CharacterField_le_CoefficientField f).trans (le_CoefficientFieldGaloisClosure f)

/-- **Universal property of `CoefficientFieldGaloisClosure`.** A normal intermediate field
`M / ℚ` inside `ℂ` contains `CoefficientFieldGaloisClosure f` if and only if it contains
`CoefficientField f` (equivalently, every positive-index Fourier coefficient of `f`). -/
@[simp]
theorem CoefficientFieldGaloisClosure_le_iff_of_normal (f : Newform N k)
    (M : IntermediateField ℚ ℂ) [Normal ℚ M] :
    CoefficientFieldGaloisClosure f ≤ M ↔ CoefficientField f ≤ M :=
  normalClosure_le_iff_le_of_normal

/-- In weight at least two, `CoefficientField f` is finite-dimensional over `ℚ`. -/
theorem finiteDimensional_CoefficientField (f : Newform N k) (hk : 2 ≤ k) :
    FiniteDimensional ℚ (CoefficientField f) :=
  (numberField_CoefficientField f hk).to_finiteDimensional

/-- In weight at least two, `CoefficientFieldGaloisClosure f` is finite-dimensional over `ℚ`. -/
theorem finiteDimensional_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k) :
    FiniteDimensional ℚ (CoefficientFieldGaloisClosure f) := by
  have := finiteDimensional_CoefficientField f hk
  rw [CoefficientFieldGaloisClosure_def]
  exact normalClosure.is_finiteDimensional ℚ (CoefficientField f) ℂ

/-- **In weight at least two, the Galois closure of the coefficient field of a newform is a number
field.** -/
theorem numberField_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k) :
    NumberField (CoefficientFieldGaloisClosure f) :=
  { to_charZero := inferInstance
    to_finiteDimensional := finiteDimensional_CoefficientFieldGaloisClosure f hk }

/-- In weight at least two, `CoefficientFieldGaloisClosure f` is a normal closure of
`CoefficientField f` over `ℚ`. -/
theorem isNormalClosure_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k) :
    IsNormalClosure ℚ (CoefficientField f) (CoefficientFieldGaloisClosure f) := by
  have := finiteDimensional_CoefficientField f hk
  exact isNormalClosure_normalClosure_of_isAlgClosed (CoefficientField f)

/-- In weight at least two, `CoefficientFieldGaloisClosure f` is normal over `ℚ`. -/
theorem normal_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k) :
    Normal ℚ (CoefficientFieldGaloisClosure f) := by
  have := finiteDimensional_CoefficientField f hk
  exact normal_normalClosure_of_isAlgClosed (CoefficientField f)

/-- **In weight at least two, `CoefficientFieldGaloisClosure f` is Galois over `ℚ`.** -/
theorem isGalois_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k) :
    IsGalois ℚ (CoefficientFieldGaloisClosure f) := by
  have := finiteDimensional_CoefficientField f hk
  exact isGalois_normalClosure_of_isAlgClosed (CoefficientField f)

/-- Bundled `TauCeti.NumberField.NormalClosureData` exhibiting `CoefficientFieldGaloisClosure f` as
the normal closure of `CoefficientField f` over `ℚ` for `k ≥ 2`, connecting newform coefficient
fields to the embedding action and subfield dictionary of `TauCeti.NumberTheory.NumberField`. -/
def normalClosureDataCoefficientField (f : Newform N k) (hk : 2 ≤ k) :
    letI := numberField_CoefficientField f hk
    letI := numberField_CoefficientFieldGaloisClosure f hk
    TauCeti.NumberField.NormalClosureData (CoefficientField f) (CoefficientFieldGaloisClosure f) :=
  letI := numberField_CoefficientField f hk
  letI := numberField_CoefficientFieldGaloisClosure f hk
  { embedding := IntermediateField.inclusion (le_CoefficientFieldGaloisClosure f)
    isNormalClosure := isNormalClosure_CoefficientFieldGaloisClosure f hk }

/-! ### Single-element generation of `CoefficientField f` -/

/-- An element `α ∈ CoefficientField f` whose minimal polynomial over `ℚ` has degree at least
`[CoefficientField f : ℚ]` generates `CoefficientField f` over `ℚ`. -/
theorem CoefficientField_eq_adjoin_of_finrank_le (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f)
    (hdeg : haveI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f) ≤ (minpoly ℚ α).natDegree) :
    CoefficientField f = ℚ⟮α⟯ := by
  have := finiteDimensional_CoefficientField f hk
  exact (TauCeti.IntermediateField.adjoin_simple_eq_of_finrank_le_natDegree_minpoly hα hdeg).symm

/-- A positive-index Fourier coefficient `aₙ(f)` whose minimal polynomial over `ℚ` has degree at
least `[CoefficientField f : ℚ]` generates `CoefficientField f` over `ℚ`. -/
theorem CoefficientField_eq_adjoin_coeff_of_finrank_le (f : Newform N k) (hk : 2 ≤ k) (n : ℕ+)
    (hdeg : haveI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f) ≤
        (minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n)).natDegree) :
    CoefficientField f = ℚ⟮(qExpansion 1 f.toCuspForm).coeff n⟯ :=
  CoefficientField_eq_adjoin_of_finrank_le f hk (coeff_mem_CoefficientField f n) hdeg

/-! ### Restriction and isomorphism between `Gal(CoefficientFieldGaloisClosure f/ℚ)` and
polynomial Galois groups -/

/-- Every element of `CoefficientField f` (in weight `k ≥ 2`) is integral over `ℚ`. -/
theorem isIntegral_rat_of_mem_CoefficientField (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f) : IsIntegral ℚ α := by
  have := finiteDimensional_CoefficientField f hk
  exact IntermediateField.isIntegral_iff.mp
    (Algebra.IsIntegral.isIntegral (⟨α, hα⟩ : CoefficientField f))

/-- For every `α ∈ CoefficientField f` in weight `k ≥ 2`, the normal closure of `ℚ⟮α⟯` in `ℂ`
is contained in `CoefficientFieldGaloisClosure f`. -/
theorem normalClosure_adjoin_le_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hα : α ∈ CoefficientField f) :
    IntermediateField.normalClosure ℚ ℚ⟮α⟯ ℂ ≤ CoefficientFieldGaloisClosure f := by
  have := finiteDimensional_CoefficientField f hk
  exact normalClosure_mono_of_isAlgClosed (adjoin_simple_le_iff.mpr hα)

/-- Restriction of automorphisms from `Gal(CoefficientFieldGaloisClosure f/ℚ)` to
`(minpoly ℚ α).Gal` for any element `α ∈ CoefficientField f` in weight `k ≥ 2`. -/
def restrictCoefficientFieldGalHom (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f) :
    Gal(CoefficientFieldGaloisClosure f/ℚ) →* (minpoly ℚ α).Gal :=
  letI := finiteDimensional_CoefficientField f hk
  restrictGalMinpolyHom hα

/-- `restrictCoefficientFieldGalHom` intertwines the Galois action on
`(minpoly ℚ α).SplittingField` with `Gal(CoefficientFieldGaloisClosure f/ℚ)` along
`splittingFieldEquivNormalClosureOfIsAlgClosed` and the ambient normal-closure inclusion. -/
@[simp]
theorem restrictCoefficientFieldGalHom_commutes (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f) (hα_int : IsIntegral ℚ α)
    (hle : IntermediateField.normalClosure ℚ ℚ⟮α⟯ ℂ ≤ CoefficientFieldGaloisClosure f)
    (σ : Gal(CoefficientFieldGaloisClosure f/ℚ)) (y : (minpoly ℚ α).SplittingField) :
    IntermediateField.inclusion hle
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int
          (restrictCoefficientFieldGalHom f hk hα σ y)) =
      σ (IntermediateField.inclusion hle
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int y)) := by
  let _ := finiteDimensional_CoefficientField f hk
  exact restrictGalMinpolyHom_commutes hα hα_int hle σ y

/-- Ambient-field form of `restrictCoefficientFieldGalHom_commutes`: coerced to `ℂ`,
`splittingFieldEquivNormalClosureOfIsAlgClosed` intertwines
`restrictCoefficientFieldGalHom f hk hα σ` with `σ`. -/
@[simp]
theorem coe_restrictCoefficientFieldGalHom_commutes (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f) (hα_int : IsIntegral ℚ α)
    (σ : Gal(CoefficientFieldGaloisClosure f/ℚ)) (y : (minpoly ℚ α).SplittingField) :
    (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int
        (restrictCoefficientFieldGalHom f hk hα σ y) : ℂ) =
      (σ (IntermediateField.inclusion
        (normalClosure_adjoin_le_CoefficientFieldGaloisClosure f hk hα)
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int y)) : ℂ) :=
  congrArg Subtype.val (restrictCoefficientFieldGalHom_commutes f hk hα hα_int
    (normalClosure_adjoin_le_CoefficientFieldGaloisClosure f hk hα) σ y)

/-- **Surjectivity of Galois restriction to the minimal polynomial of any element of
`CoefficientField f`.** -/
theorem restrictCoefficientFieldGalHom_surjective (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f) :
    Function.Surjective (restrictCoefficientFieldGalHom f hk hα) := by
  have := finiteDimensional_CoefficientField f hk
  exact restrictGalMinpolyHom_surjective hα

/-- If `Gal(CoefficientFieldGaloisClosure f/ℚ)` is solvable, then so is `(minpoly ℚ α).Gal` for
every `α ∈ CoefficientField f`. -/
theorem isSolvable_gal_minpoly_of_mem_CoefficientField (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hα : α ∈ CoefficientField f)
    [Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ)] :
    Group.IsSolvable (minpoly ℚ α).Gal :=
  Group.isSolvable_of_surjective (restrictCoefficientFieldGalHom_surjective f hk hα)

/-- If some element `α ∈ CoefficientField f` has non-solvable `(minpoly ℚ α).Gal`, then
`Gal(CoefficientFieldGaloisClosure f/ℚ)` is not solvable. -/
theorem not_isSolvable_CoefficientFieldGaloisClosure_of_mem (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hα : α ∈ CoefficientField f) (hns : ¬ Group.IsSolvable (minpoly ℚ α).Gal) :
    ¬ Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ) := by
  have := finiteDimensional_CoefficientField f hk
  exact not_isSolvable_gal_normalClosure_of_mem hα hns

/-- For every `α ∈ CoefficientField f` (with `k ≥ 2`), `|(minpoly ℚ α).Gal|` divides
`|Gal(CoefficientFieldGaloisClosure f/ℚ)|`. -/
theorem natCard_gal_minpoly_dvd_CoefficientFieldGaloisClosure (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hα : α ∈ CoefficientField f) :
    Nat.card (minpoly ℚ α).Gal ∣ Nat.card Gal(CoefficientFieldGaloisClosure f/ℚ) := by
  have := finiteDimensional_CoefficientField f hk
  exact natCard_gal_minpoly_dvd_of_mem hα

/-- When `CoefficientField f = ℚ⟮α⟯` (in weight `k ≥ 2`), `Gal(CoefficientFieldGaloisClosure f/ℚ)`
is isomorphic to `(minpoly ℚ α).Gal`. -/
def galCoefficientFieldGaloisClosureEquiv (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hK : CoefficientField f = ℚ⟮α⟯) :
    Gal(CoefficientFieldGaloisClosure f/ℚ) ≃* (minpoly ℚ α).Gal :=
  have hα_int : IsIntegral ℚ α :=
    isIntegral_rat_of_mem_CoefficientField f hk
      (hK.symm ▸ IntermediateField.mem_adjoin_simple_self ℚ α)
  galNormalClosureEquivGalMinpoly hα_int hK.symm

/-- `galCoefficientFieldGaloisClosureEquiv` intertwines the Galois action on
`(minpoly ℚ α).SplittingField` with `Gal(CoefficientFieldGaloisClosure f/ℚ)` along
`splittingFieldEquivNormalClosureOfIsAlgClosed` and the ambient normal-closure inclusion. -/
@[simp]
theorem galCoefficientFieldGaloisClosureEquiv_commutes (f : Newform N k) (hk : 2 ≤ k) {α : ℂ}
    (hK : CoefficientField f = ℚ⟮α⟯) (hα_int : IsIntegral ℚ α)
    (hle : IntermediateField.normalClosure ℚ ℚ⟮α⟯ ℂ ≤ CoefficientFieldGaloisClosure f)
    (σ : Gal(CoefficientFieldGaloisClosure f/ℚ)) (y : (minpoly ℚ α).SplittingField) :
    IntermediateField.inclusion hle
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int
          (galCoefficientFieldGaloisClosureEquiv f hk hK σ y)) =
      σ (IntermediateField.inclusion hle
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int y)) :=
  galNormalClosureEquivGalMinpoly_commutes hα_int hK.symm hle σ y

/-- Ambient-field form of `galCoefficientFieldGaloisClosureEquiv_commutes`. -/
@[simp]
theorem coe_galCoefficientFieldGaloisClosureEquiv_commutes (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hK : CoefficientField f = ℚ⟮α⟯) (hα_int : IsIntegral ℚ α)
    (σ : Gal(CoefficientFieldGaloisClosure f/ℚ)) (y : (minpoly ℚ α).SplittingField) :
    (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int
        (galCoefficientFieldGaloisClosureEquiv f hk hK σ y) : ℂ) =
      (σ (IntermediateField.inclusion
        (normalClosure_adjoin_le_CoefficientFieldGaloisClosure f hk
          (hK.symm ▸ IntermediateField.mem_adjoin_simple_self ℚ α))
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int y)) : ℂ) :=
  congrArg Subtype.val (galCoefficientFieldGaloisClosureEquiv_commutes f hk hK hα_int
    (normalClosure_adjoin_le_CoefficientFieldGaloisClosure f hk
      (hK.symm ▸ IntermediateField.mem_adjoin_simple_self ℚ α)) σ y)

/-- `(galCoefficientFieldGaloisClosureEquiv f hk hK).symm` intertwines `(minpoly ℚ α).Gal`
with `Gal(CoefficientFieldGaloisClosure f/ℚ)` along
`splittingFieldEquivNormalClosureOfIsAlgClosed` and the ambient normal-closure inclusion. -/
@[simp]
theorem galCoefficientFieldGaloisClosureEquiv_symm_apply (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hK : CoefficientField f = ℚ⟮α⟯) (hα_int : IsIntegral ℚ α)
    (hle : IntermediateField.normalClosure ℚ ℚ⟮α⟯ ℂ ≤ CoefficientFieldGaloisClosure f)
    (τ : (minpoly ℚ α).Gal) (y : (minpoly ℚ α).SplittingField) :
    (galCoefficientFieldGaloisClosureEquiv f hk hK).symm τ
        (IntermediateField.inclusion hle
          (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int y)) =
      IntermediateField.inclusion hle
        (splittingFieldEquivNormalClosureOfIsAlgClosed hα_int (τ y)) :=
  galNormalClosureEquivGalMinpoly_symm_apply hα_int hK.symm hle τ y

/-- As a group homomorphism, `galCoefficientFieldGaloisClosureEquiv` agrees with
`restrictCoefficientFieldGalHom`. -/
theorem coe_galCoefficientFieldGaloisClosureEquiv_eq_restrictCoefficientFieldGalHom
    (f : Newform N k) (hk : 2 ≤ k) {α : ℂ} (hK : CoefficientField f = ℚ⟮α⟯)
    (hα : α ∈ CoefficientField f) :
    (galCoefficientFieldGaloisClosureEquiv f hk hK :
        Gal(CoefficientFieldGaloisClosure f/ℚ) →* (minpoly ℚ α).Gal) =
      restrictCoefficientFieldGalHom f hk hα := by
  let _ := finiteDimensional_CoefficientField f hk
  exact coe_galNormalClosureEquivGalMinpoly_eq_restrictGalMinpolyHom
    (isIntegral_rat_of_mem_CoefficientField f hk hα) hK.symm hα

/-- When `CoefficientField f = ℚ⟮α⟯` (in weight `k ≥ 2`), `Gal(CoefficientFieldGaloisClosure f/ℚ)`
is solvable if and only if `(minpoly ℚ α).Gal` is solvable. -/
theorem isSolvable_CoefficientFieldGaloisClosure_iff_of_eq_adjoin (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hK : CoefficientField f = ℚ⟮α⟯) :
    Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ) ↔
      Group.IsSolvable (minpoly ℚ α).Gal := by
  let e := galCoefficientFieldGaloisClosureEquiv f hk hK
  exact ⟨fun _ ↦ Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
    fun _ ↦ Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

/-- When `CoefficientField f = ℚ⟮α⟯` (in weight `k ≥ 2`), `Gal(CoefficientFieldGaloisClosure f/ℚ)`
and `(minpoly ℚ α).Gal` have the same order. -/
theorem natCard_gal_CoefficientFieldGaloisClosure_eq_of_eq_adjoin (f : Newform N k) (hk : 2 ≤ k)
    {α : ℂ} (hK : CoefficientField f = ℚ⟮α⟯) :
    Nat.card Gal(CoefficientFieldGaloisClosure f/ℚ) = Nat.card (minpoly ℚ α).Gal :=
  Nat.card_congr (galCoefficientFieldGaloisClosureEquiv f hk hK).toEquiv

/-! ### Certificate-driven Galois-group and solvability theorems for newforms -/

/-- **Certificate refutation of solvability for a newform's coefficient-field Galois closure.**
Let `f` be a newform of weight `k ≥ 2` and `aₙ(f)` a positive-index Fourier coefficient annihilated
by a monic polynomial `P : ℤ[X]`. If a `cert : SolvabilityCertificate` checks on `P` with
`cert.isSolvable = false`, then `Gal(CoefficientFieldGaloisClosure f/ℚ)` is not solvable.

Neither irreducibility of `P` nor a degree bound on `CoefficientField f` is needed as an extra
hypothesis: `cert` certifies irreducibility of `P` over `ℚ`, identifying `P` with `minpoly ℚ aₙ(f)`,
and surjectivity of restriction transfers non-solvability to the full Galois closure. -/
theorem not_isSolvable_CoefficientFieldGaloisClosure_of_check_eq_true (f : Newform N k)
    (hk : 2 ≤ k) (n : ℕ+) {P : ℤ[X]} (hP : P.Monic)
    (hroot : aeval ((qExpansion 1 f.toCuspForm).coeff n) P = 0)
    {cert : SolvabilityCertificate} (hcheck : cert.check P = true)
    (hns : cert.isSolvable = false) :
    ¬ Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ) := by
  have hirr : Irreducible (P.map (Int.castRingHom ℚ)) :=
    SolvabilityCertificate.check_irreducible_map_rat_of_isSolvable_eq_false hP hcheck hns
  have hmin : minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n) = P.map (Int.castRingHom ℚ) := by
    have hhom : Int.castRingHom ℚ = algebraMap ℤ ℚ := RingHom.ext_int _ _
    rw [hhom] at hirr ⊢
    exact minpoly_eq_map_of_aeval_eq_zero hP hirr hroot
  refine not_isSolvable_CoefficientFieldGaloisClosure_of_mem f hk
    (coeff_mem_CoefficientField f n) ?_
  rw [hmin]
  exact SolvabilityCertificate.check_not_isSolvable hP hcheck hns

/-- **Bidirectional solvability certification for a newform's coefficient-field Galois closure.**
Let `f` be a newform of weight `k ≥ 2` and `aₙ(f)` a positive-index Fourier coefficient annihilated
by a monic polynomial `P : ℤ[X]` irreducible over `ℚ` with `[CoefficientField f : ℚ] ≤ P.natDegree`.
If `cert.check P = true`, then `Gal(CoefficientFieldGaloisClosure f/ℚ)` is solvable if and only if
`cert.isSolvable = true`. -/
theorem isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true (f : Newform N k)
    (hk : 2 ≤ k) (n : ℕ+) {P : ℤ[X]} (hP : P.Monic)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hroot : aeval ((qExpansion 1 f.toCuspForm).coeff n) P = 0)
    (hdeg : haveI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f) ≤ P.natDegree)
    {cert : SolvabilityCertificate} (hcheck : cert.check P = true) :
    Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ) ↔ cert.isSolvable = true := by
  have hmin : minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n) = P.map (Int.castRingHom ℚ) := by
    have hhom : Int.castRingHom ℚ = algebraMap ℤ ℚ := RingHom.ext_int _ _
    rw [hhom] at hirr ⊢
    exact minpoly_eq_map_of_aeval_eq_zero hP hirr hroot
  have hdeg' : (letI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f)) ≤
        (minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n)).natDegree := by
    rw [hmin, hP.natDegree_map]
    exact hdeg
  have hadj : CoefficientField f = ℚ⟮(qExpansion 1 f.toCuspForm).coeff n⟯ :=
    CoefficientField_eq_adjoin_coeff_of_finrank_le f hk n hdeg'
  rw [isSolvable_CoefficientFieldGaloisClosure_iff_of_eq_adjoin f hk hadj, hmin]
  exact SolvabilityCertificate.check_sound hP hcheck

/-- **Prime-degree `{d}` + `{1, …, 1, 2}` Frobenius refutation of solvability for a newform.**
If `aₙ(f)` is annihilated by a monic polynomial `P : ℤ[X]` on which
`SolvabilityCertificate.primeLinearQuadratic d p q` checks, then
`Gal(CoefficientFieldGaloisClosure f/ℚ)` is not solvable (without any degree bound on
`CoefficientField f`). -/
theorem not_isSolvable_CoefficientFieldGaloisClosure_of_primeLinearQuadratic (f : Newform N k)
    (hk : 2 ≤ k) (n : ℕ+) {P : ℤ[X]} (hP : P.Monic)
    (hroot : aeval ((qExpansion 1 f.toCuspForm).coeff n) P = 0)
    {d p q : ℕ}
    (hcheck : (SolvabilityCertificate.primeLinearQuadratic d p q).check P = true) :
    ¬ Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ) :=
  not_isSolvable_CoefficientFieldGaloisClosure_of_check_eq_true f hk n hP hroot hcheck
    (SolvabilityCertificate.isSolvable_primeLinearQuadratic d p q)

/-- **Single-coefficient generation from a `primeLinearQuadratic` certificate.** If `aₙ(f)` is
annihilated by a monic polynomial `P : ℤ[X]` on which `primeLinearQuadratic d p q` checks and
`[CoefficientField f : ℚ] ≤ d`, then `CoefficientField f = ℚ⟮aₙ(f)⟯`. -/
theorem CoefficientField_eq_adjoin_of_primeLinearQuadratic (f : Newform N k)
    (hk : 2 ≤ k) (n : ℕ+) {P : ℤ[X]} (hP : P.Monic)
    (hroot : aeval ((qExpansion 1 f.toCuspForm).coeff n) P = 0)
    {d p q : ℕ}
    (hcheck : (SolvabilityCertificate.primeLinearQuadratic d p q).check P = true)
    (hdeg : haveI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f) ≤ d) :
    CoefficientField f = ℚ⟮(qExpansion 1 f.toCuspForm).coeff n⟯ := by
  have hPdeg : P.natDegree = d :=
    SolvabilityCertificate.check_natDegree_eq_of_primeLinearQuadratic hP hcheck
  have hirr : Irreducible (P.map (Int.castRingHom ℚ)) :=
    SolvabilityCertificate.check_irreducible_map_rat_of_isSolvable_eq_false hP hcheck
      (SolvabilityCertificate.isSolvable_primeLinearQuadratic d p q)
  have hmin : minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n) = P.map (Int.castRingHom ℚ) := by
    have hhom : Int.castRingHom ℚ = algebraMap ℤ ℚ := RingHom.ext_int _ _
    rw [hhom] at hirr ⊢
    exact minpoly_eq_map_of_aeval_eq_zero hP hirr hroot
  have hdeg' : (letI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f)) ≤
        (minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n)).natDegree := by
    rw [hmin, hP.natDegree_map, hPdeg]
    exact hdeg
  exact CoefficientField_eq_adjoin_coeff_of_finrank_le f hk n hdeg'

/-- **Order `d!` of `Gal(CoefficientFieldGaloisClosure f/ℚ)` from a `primeLinearQuadratic`
certificate.** Let `f` be a newform of weight `k ≥ 2` and `aₙ(f)` a positive-index Fourier
coefficient annihilated by a monic polynomial `P : ℤ[X]`. If
`(SolvabilityCertificate.primeLinearQuadratic d p q).check P = true` and
`[CoefficientField f : ℚ] ≤ d`, then `|Gal(CoefficientFieldGaloisClosure f/ℚ)| = d!`. -/
theorem natCard_gal_CoefficientFieldGaloisClosure_of_primeLinearQuadratic (f : Newform N k)
    (hk : 2 ≤ k) (n : ℕ+) {P : ℤ[X]} (hP : P.Monic)
    (hroot : aeval ((qExpansion 1 f.toCuspForm).coeff n) P = 0)
    {d p q : ℕ}
    (hcheck : (SolvabilityCertificate.primeLinearQuadratic d p q).check P = true)
    (hdeg : haveI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f) ≤ d) :
    Nat.card Gal(CoefficientFieldGaloisClosure f/ℚ) = d.factorial := by
  have hsym :=
    SolvabilityCertificate.check_hasFullSymmetricGaloisGroup_of_primeLinearQuadratic hP hcheck
  have hPdeg : P.natDegree = d :=
    SolvabilityCertificate.check_natDegree_eq_of_primeLinearQuadratic hP hcheck
  have hirr : Irreducible (P.map (Int.castRingHom ℚ)) :=
    SolvabilityCertificate.check_irreducible_map_rat_of_isSolvable_eq_false hP hcheck
      (SolvabilityCertificate.isSolvable_primeLinearQuadratic d p q)
  have hmin : minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n) = P.map (Int.castRingHom ℚ) := by
    have hhom : Int.castRingHom ℚ = algebraMap ℤ ℚ := RingHom.ext_int _ _
    rw [hhom] at hirr ⊢
    exact minpoly_eq_map_of_aeval_eq_zero hP hirr hroot
  have hadj : CoefficientField f = ℚ⟮(qExpansion 1 f.toCuspForm).coeff n⟯ :=
    CoefficientField_eq_adjoin_of_primeLinearQuadratic f hk n hP hroot hcheck hdeg
  rw [natCard_gal_CoefficientFieldGaloisClosure_eq_of_eq_adjoin f hk hadj, hmin,
    (hasFullSymmetricGaloisGroup_iff_natCard_gal_eq_factorial_natDegree hsym.separable).mp hsym,
    hP.natDegree_map, hPdeg]

end NewformGaloisClosure

/-! ### Concrete instantiation: the Ramanujan discriminant newform `Δ ∈ S₁₂(Γ₁(1))ⁿᵉʷ` -/

/-- The modular discriminant `Δ`, bundled as a newform of level `1` and weight `12`. -/
def discriminantNewform : Newform 1 12 :=
  discriminantEigenform.toNewformOfLevelOne (by simpa using discriminant_qExpansion_coeff_one)

/-- The underlying function of `discriminantNewform` is `discriminant`. -/
@[simp]
theorem coe_discriminantNewform :
    (discriminantNewform.toCuspForm : ℍ → ℂ) = discriminant := by
  simp [discriminantNewform]

/-- `discriminantNewform` has trivial nebentypus character. -/
@[simp]
theorem discriminantNewform_χ : discriminantNewform.χ = 1 := by
  simp [discriminantNewform]

/-- Every Fourier coefficient of `Δ` is an integer, so `CoefficientField discriminantNewform = ⊥`.
-/
@[simp]
theorem CoefficientField_discriminantNewform :
    CoefficientField discriminantNewform = ⊥ := by
  apply eq_bot_iff.mpr
  rw [CoefficientField_le_iff]
  intro n
  obtain ⟨m, hm⟩ := TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n
  rw [coe_discriminantNewform, hm]
  exact (⊥ : IntermediateField ℚ ℂ).intCast_mem m

/-- The Galois closure of `CoefficientField discriminantNewform` in `ℂ` is `⊥` (`ℚ`). -/
@[simp]
theorem CoefficientFieldGaloisClosure_discriminantNewform :
    CoefficientFieldGaloisClosure discriminantNewform = ⊥ := by
  have : Normal ℚ (⊥ : IntermediateField ℚ ℂ) :=
    Normal.of_algEquiv (IntermediateField.botEquiv ℚ ℂ).symm
  apply eq_bot_iff.mpr
  rw [CoefficientFieldGaloisClosure_le_iff_of_normal, CoefficientField_discriminantNewform]

/-- End-to-end solvability certification of
`Gal(CoefficientFieldGaloisClosure discriminantNewform/ℚ)` via
`isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true` at `n = 2` (`τ(2) = -24`,
annihilated by `X + 24`). -/
theorem isSolvable_CoefficientFieldGaloisClosure_discriminantNewform :
    Group.IsSolvable Gal(CoefficientFieldGaloisClosure discriminantNewform/ℚ) := by
  have hP : (X + 24 : ℤ[X]).Monic := by
    rw [← C_ofNat 24]
    exact monic_X_add_C 24
  have hirr : Irreducible ((X + 24 : ℤ[X]).map (Int.castRingHom ℚ)) := by
    rw [← C_ofNat 24, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    exact irreducible_of_degree_eq_one (degree_X_add_C _)
  have hroot : aeval ((qExpansion 1 discriminantNewform.toCuspForm).coeff (2 : ℕ+))
      (X + 24 : ℤ[X]) = 0 := by
    have h2 : ((2 : ℕ+) : ℕ) = 2 := rfl
    rw [h2, coe_discriminantNewform, map_add, aeval_X, map_ofNat,
      TauCeti.ModularForm.discriminant_qExpansion_coeff_two]
    norm_num
  have hdeg : (letI := finiteDimensional_CoefficientField discriminantNewform (by decide)
      Module.finrank ℚ (CoefficientField discriminantNewform)) ≤ (X + 24 : ℤ[X]).natDegree := by
    have hd1 : (X + 24 : ℤ[X]).natDegree = 1 := by compute_degree!
    rw [CoefficientField_discriminantNewform, IntermediateField.finrank_bot, hd1]
  exact (isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true
    discriminantNewform (by decide) 2 hP hirr hroot hdeg
    SolvabilityCertificate.check_smallDegree_X_add_twenty_four).mpr
    SolvabilityCertificate.isSolvable_smallDegree

end TauCeti
