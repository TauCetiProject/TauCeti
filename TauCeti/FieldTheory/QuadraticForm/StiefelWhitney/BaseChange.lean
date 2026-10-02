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
# Restriction of Stiefel–Whitney classes

For a finite field extension `L/K` with two invertible and an embedding
`σ : L →ₐ[K] SeparableClosure K`, the first and second Stiefel–Whitney classes commute with
restriction of Galois cohomology and scalar extension of quadratic forms:

```text
res(w₁(q)) = w₁(q ⊗ L),     res(w₂(q)) = w₂(q ⊗ L).
```

The formulas hold on diagonal tuples, on isometry classes of regular forms, and on regular forms
on arbitrary finite-dimensional spaces. In particular the form-level statements require no
chosen diagonalization. They compare the existing `galoisRes` with the existing
`RegularFormClass.baseChange`, using restriction of Kummer classes and naturality of cup products.
The right-hand sides do not depend on the embedding `σ`, so neither do the restricted classes.
The class-level results use the same universe generality as the existing invariants: `w₁` is
universe-polymorphic, whereas the descended `w₂` is defined for fields in `Type`.

## Main results

* `TauCeti.galoisRes_sw1`, `TauCeti.galoisRes_sw2`: restriction on diagonal tuples.
* `TauCeti.galoisRes_sw1Class`, `TauCeti.galoisRes_sw2Class`: restriction on regular form classes.
* `TauCeti.galoisRes_sw1Class_formClass`, `TauCeti.galoisRes_sw2Class_formClass`: restriction on
  the class of a regular form extended to `L`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1)–(6.2.2), for the Kummer classes and their cup products.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology

universe u

section Tuples

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)

/-- Restriction of `w₁` of a diagonal tuple is `w₁` of the tuple of extended coefficients. -/
@[simp]
theorem galoisRes_sw1 {n : ℕ} (w : Fin n → Kˣ) :
    galoisRes K L σ 1 (sw1 w) =
      sw1 (fun i => Units.map (algebraMap K L).toMonoidHom (w i)) := by
  simp only [sw1_def, map_sum, galoisRes_kummerClass]

/-- Restriction of `w₂` of a diagonal tuple is `w₂` of the tuple of extended coefficients. -/
@[simp]
theorem galoisRes_sw2 {n : ℕ} (w : Fin n → Kˣ) :
    galoisRes K L σ 2 (sw2 w) =
      sw2 (fun i => Units.map (algebraMap K L).toMonoidHom (w i)) := by
  rw [sw2_def, sw2_def]
  simp only [map_sum, kummerCup_squareClass_squareClass]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [galoisRes_eq_map, trivialF2Map_cup _ 1 1, ← galoisRes_eq_map]
  simp only [galoisRes_kummerClass]

end Tuples

section FirstClass

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)

/-- The first Stiefel–Whitney class commutes with restriction and scalar extension of regular
form classes. -/
@[simp]
theorem galoisRes_sw1Class (q : RegularFormClass K) :
    galoisRes K L σ 1 (sw1Class q) = sw1Class (RegularFormClass.baseChange L q) := by
  refine Quotient.inductionOn q fun p => ?_
  rw [RegularFormClass.baseChange_mk, sw1Class_mk, sw1Class_mk,
    RegularFormPresentation.baseChange_def]
  exact galoisRes_sw1 K L σ p.2

/-- Restriction of the first Stiefel–Whitney class of a regular form is the first class of its
scalar extension, without choosing a diagonalization. -/
theorem galoisRes_sw1Class_formClass {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    galoisRes K L σ 1 (sw1Class (formClass Q hQ)) =
      sw1Class (formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) := by
  rw [QuadraticForm.formClass_baseChange]
  exact galoisRes_sw1Class K L σ (formClass Q hQ)

end FirstClass

section SecondClass

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)

/-- The second Stiefel–Whitney class commutes with restriction and scalar extension of regular
form classes. -/
@[simp]
theorem galoisRes_sw2Class (q : RegularFormClass K) :
    galoisRes K L σ 2 (sw2Class q) = sw2Class (RegularFormClass.baseChange L q) := by
  refine Quotient.inductionOn q fun p => ?_
  rw [RegularFormClass.baseChange_mk, sw2Class_mk, sw2Class_mk,
    RegularFormPresentation.baseChange_def]
  exact galoisRes_sw2 K L σ p.2

/-- Restriction of the second Stiefel–Whitney class of a regular form is the second class of its
scalar extension, without choosing a diagonalization. -/
theorem galoisRes_sw2Class_formClass {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    galoisRes K L σ 2 (sw2Class (formClass Q hQ)) =
      sw2Class (formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) := by
  rw [QuadraticForm.formClass_baseChange]
  exact galoisRes_sw2Class K L σ (formClass Q hQ)

end SecondClass

end TauCeti
