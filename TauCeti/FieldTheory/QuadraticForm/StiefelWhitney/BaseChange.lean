/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Class
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange

/-!
# Restriction naturality of the Stiefel-Whitney classes

For a finite extension `L/K` of fields in which two is invertible, scalar extension of a regular
quadratic form restricts its first and second Stiefel-Whitney classes from `G_K` to `G_L`.
These identities compare the descended invariants of the forms themselves, so they require no
chosen diagonalization. They allow invariants of transferred forms to be compared after extending
scalars to the extension field.

Restriction is `TauCeti.galoisRes`, attached to an embedding of `L` into a separable closure of
`K`. The identities hold for every such embedding. On diagonal tuples they follow from the
restriction law for Kummer classes and the naturality of the cup product.

## Main results

* `TauCeti.galoisRes_sw1`, `TauCeti.galoisRes_sw2`: restriction maps the classes of a diagonal
  tuple to those of the tuple of images of its coefficients.
* `TauCeti.galoisRes_sw1Class`, `TauCeti.galoisRes_sw2Class`: the descended classes commute
  with scalar extension.
* `TauCeti.galoisRes_sw1Class_formClass`, `TauCeti.galoisRes_sw2Class_formClass`: the same
  identities for a regular quadratic form on an arbitrary finite-dimensional space.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* A. Delzant, *Définition des classes de Stiefel-Whitney d'un module quadratique sur un corps de
  caractéristique différente de 2*, C. R. Acad. Sci. Paris 255 (1962), 1366-1368.
-/

public section

noncomputable section

namespace TauCeti

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Invertible (2 : K)] [Invertible (2 : L)] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- Restriction of `w₁` maps each diagonal coefficient to its image in the extension field. -/
@[simp]
theorem galoisRes_sw1 {n : ℕ} (w : Fin n → Kˣ) :
    galoisRes K L σ 1 (sw1 w) =
      sw1 (fun i => Units.map (algebraMap K L).toMonoidHom (w i)) := by
  simp only [sw1_def, map_sum, galoisRes_kummerClass]

/-- Restriction of `w₂` maps each diagonal coefficient to its image in the extension field. -/
@[simp]
theorem galoisRes_sw2 {n : ℕ} (w : Fin n → Kˣ) :
    galoisRes K L σ 2 (sw2 w) =
      sw2 (fun i => Units.map (algebraMap K L).toMonoidHom (w i)) := by
  simp only [sw2_def, map_sum, kummerCup_squareClass_squareClass]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [galoisRes_cup K L σ 1 1, galoisRes_kummerClass, galoisRes_kummerClass]

/-- Restriction of the first Stiefel-Whitney class is the class of the scalar extension. -/
@[simp]
theorem galoisRes_sw1Class (q : RegularFormClass K) :
    galoisRes K L σ 1 (sw1Class q) = sw1Class (RegularFormClass.baseChange L q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.baseChange_mk, sw1Class_mk, sw1Class_mk,
      RegularFormPresentation.baseChange_def, galoisRes_sw1]

/-- Restriction of `w₁` of a regular form equals `w₁` of the scalar-extended form,
without choosing a diagonalization. -/
theorem galoisRes_sw1Class_formClass {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    galoisRes K L σ 1 (sw1Class (formClass Q hQ)) =
      sw1Class (formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) := by
  rw [QuadraticForm.formClass_baseChange, galoisRes_sw1Class]

section SecondClass

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [Invertible (2 : K)] [Invertible (2 : L)] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- Restriction of the second Stiefel-Whitney class is the class of the scalar extension. -/
@[simp]
theorem galoisRes_sw2Class (q : RegularFormClass K) :
    galoisRes K L σ 2 (sw2Class q) = sw2Class (RegularFormClass.baseChange L q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.baseChange_mk, sw2Class_mk, sw2Class_mk,
      RegularFormPresentation.baseChange_def, galoisRes_sw2]

/-- Restriction of `w₂` of a regular form equals `w₂` of the scalar-extended form,
without choosing a diagonalization. -/
theorem galoisRes_sw2Class_formClass {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    galoisRes K L σ 2 (sw2Class (formClass Q hQ)) =
      sw2Class (formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) := by
  rw [QuadraticForm.formClass_baseChange, galoisRes_sw2Class]

end SecondClass

end TauCeti
