/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Solvable
public import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantNewform
public import TauCeti.NumberTheory.ModularForms.Newforms.NumberField
public import TauCeti.NumberTheory.NumberField.NormalClosure

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.ComputeDegree
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Galois closures and Galois-group certification for newform coefficient fields

For a newform `f` of level `N` and weight `k ≥ 2`, the coefficient field `CoefficientField f` is a
number field embedded in `ℂ` (`TauCeti.numberField_CoefficientField`). Because `ℂ / ℚ` is
algebraically closed rather than algebraic, Mathlib's `[Normal ℚ Ω]`-based normal-closure API does
not apply directly to `IntermediateField.normalClosure ℚ (CoefficientField f) ℂ`. Combining the
`[IsAlgClosed Ω]` normal-closure API of `TauCeti.FieldTheory.Normal.Closure` and
`TauCeti.FieldTheory.GaloisGroups.NormalClosure` with the general certificate-transfer theorems of
`TauCeti.FieldTheory.GaloisGroups.Certificate.Solvable` yields a certification pipeline for the
Galois closure of `CoefficientField f` over `ℚ`:

1. **Galois closure of the coefficient field.** `CoefficientFieldGaloisClosure f` is the normal
   closure of `CoefficientField f` inside `ℂ`. In weight `k ≥ 2` it is a number field, Galois over
   `ℚ`, and canonically equipped with `TauCeti.NumberField.NormalClosureData`.
2. **Single-coefficient generation.** When an element `α ∈ CoefficientField f` — in particular a
   positive Fourier coefficient `aₙ(f)`, which is a root of the Hecke characteristic polynomial on
   `S_k(N, f.χ)ⁿᵉʷ` (`TauCeti.isRoot_charpoly_heckeTCuspNewCharEnd`) — has minimal polynomial of
   degree at least `[CoefficientField f : ℚ]`, it generates `CoefficientField f` over `ℚ`, giving
   access to `TauCeti.restrictGalMinpolyHom` and `TauCeti.galNormalClosureEquivGalMinpoly`.
3. **Certificate-driven solvability and full symmetric group theorems.** Specializing the
   intermediate-field transfer theorems of `TauCeti.SolvabilityCertificate` to Fourier coefficients
   `aₙ(f) ∈ CoefficientField f`:
   * Any `cert : SolvabilityCertificate` with `cert.check P = true` and `cert.isSolvable = false`
     for a monic integral polynomial `P` vanishing at `aₙ(f)` refutes solvability of
     `Gal(CoefficientFieldGaloisClosure f/ℚ)` directly
     (`not_isSolvable_CoefficientFieldGaloisClosure_of_check_eq_true`).
   * When `[CoefficientField f : ℚ] ≤ P.natDegree` and `P` is irreducible over `ℚ`, a verified
     `SolvabilityCertificate` decides solvability of `Gal(CoefficientFieldGaloisClosure f/ℚ)` in
     both directions (`isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true`), and a
     verified `{d}` + `{1, …, 1, 2}` Frobenius-cycle certificate (`primeLinearQuadratic d p q`)
     proves non-solvability
     (`not_isSolvable_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`),
     single-coefficient generation (`CoefficientField_eq_adjoin_of_primeLinearQuadratic`), and
     `|Gal(CoefficientFieldGaloisClosure f/ℚ)| = d!`
     (`natCard_gal_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`).
4. **The Ramanujan discriminant newform.** For `discriminantNewform : Newform 1 12` (defined in
   `TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantNewform`),
   `CoefficientFieldGaloisClosure discriminantNewform = ⊥`, and solvability is certified end-to-end
   via `τ(2) = -24` and `X + 24`.

## Main definitions and results

* `TauCeti.CoefficientFieldGaloisClosure`: the Galois closure of `CoefficientField f` in `ℂ`.
* `TauCeti.numberField_CoefficientFieldGaloisClosure`,
  `TauCeti.isGalois_CoefficientFieldGaloisClosure`,
  `TauCeti.normalClosureDataCoefficientField`: number-field and Galois-closure structure in weight
  `k ≥ 2`.
* `TauCeti.CoefficientField_eq_adjoin_coeff_of_finrank_le`: single-coefficient generation of
  `CoefficientField f`.
* `TauCeti.not_isSolvable_CoefficientFieldGaloisClosure_of_check_eq_true`,
  `TauCeti.isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true`,
  `TauCeti.not_isSolvable_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`,
  `TauCeti.CoefficientField_eq_adjoin_of_primeLinearQuadratic`,
  `TauCeti.natCard_gal_CoefficientFieldGaloisClosure_of_primeLinearQuadratic`: certificate-driven
  Galois-group and solvability theorems for newforms.
* `TauCeti.CoefficientFieldGaloisClosure_discriminantNewform`,
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

open IntermediateField Polynomial UpperHalfPlane ModularForm HeckeRing.GL2
open scoped ModularForm

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

/-! ### Single-coefficient generation of `CoefficientField f` -/

/-- A positive-index Fourier coefficient `aₙ(f)` whose minimal polynomial over `ℚ` has degree at
least `[CoefficientField f : ℚ]` generates `CoefficientField f` over `ℚ`. -/
theorem CoefficientField_eq_adjoin_coeff_of_finrank_le (f : Newform N k) (hk : 2 ≤ k) (n : ℕ+)
    (hdeg : haveI := finiteDimensional_CoefficientField f hk
      Module.finrank ℚ (CoefficientField f) ≤
        (minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n)).natDegree) :
    CoefficientField f = ℚ⟮(qExpansion 1 f.toCuspForm).coeff n⟯ := by
  let _ := finiteDimensional_CoefficientField f hk
  exact (TauCeti.IntermediateField.adjoin_simple_eq_of_finrank_le_natDegree_minpoly
    (coeff_mem_CoefficientField f n) hdeg).symm

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
  have := finiteDimensional_CoefficientField f hk
  exact SolvabilityCertificate.not_isSolvable_gal_normalClosure_of_check_eq_true
    (coeff_mem_CoefficientField f n) hP hroot hcheck hns

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
  let _ := finiteDimensional_CoefficientField f hk
  exact SolvabilityCertificate.isSolvable_gal_normalClosure_iff_of_check_eq_true
    (coeff_mem_CoefficientField f n) hP hirr hroot hdeg hcheck

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
    ¬ Group.IsSolvable Gal(CoefficientFieldGaloisClosure f/ℚ) := by
  have := finiteDimensional_CoefficientField f hk
  exact SolvabilityCertificate.not_isSolvable_gal_normalClosure_of_primeLinearQuadratic
    (coeff_mem_CoefficientField f n) hP hroot hcheck

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
  let _ := finiteDimensional_CoefficientField f hk
  exact (SolvabilityCertificate.adjoin_simple_eq_of_primeLinearQuadratic
    (coeff_mem_CoefficientField f n) hP hroot hcheck hdeg).symm

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
  let _ := finiteDimensional_CoefficientField f hk
  exact SolvabilityCertificate.natCard_gal_normalClosure_of_primeLinearQuadratic
    (coeff_mem_CoefficientField f n) hP hroot hcheck hdeg

end NewformGaloisClosure

/-! ### Concrete instantiation: the Ramanujan discriminant newform `Δ ∈ S₁₂(Γ₁(1))ⁿᵉʷ` -/

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
