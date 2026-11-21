/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Differential
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The ordinary algebraic de Rham complex

For an `A`-algebra `B`, the algebraic de Rham complex `Ω•_(B/A)` is the cochain complex of
`A`-modules, indexed by `ℕ`, whose degree-`n` object is the module of differential forms
`Ωⁿ = ⋀[B]^n Ω[B⁄A]` and whose differential is the de Rham differential `TauCeti.DeRham.d`.
Its objects are `B`-modules, but it is a complex of `A`-modules only: the differential is not
`B`-linear.

## Main definitions

* `TauCeti.DeRham.complex A B`: the de Rham complex, a `CochainComplex (ModuleCat A) ℕ`.

## Main results

* `TauCeti.DeRham.complex_X`: its degree-`n` object is `Forms A B n`.
* `TauCeti.DeRham.complex_d`: its differential from degree `n` to `n + 1` is `d A B n`.

## Implementation notes

The body of `complex` is exposed: the degree-`n` object is the module of forms only
definitionally, and the statement of `complex_d` relies on this.

## References

* The Stacks Project, Section 10.132 (Tag 0FKF).
-/

universe u v

namespace TauCeti.DeRham

open CategoryTheory

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

public section

/-- **The ordinary algebraic de Rham complex** `Ω•_(B/A)`: the cochain complex of `A`-modules
`Ω⁰ → Ω¹ → Ω² → ⋯` of differential forms `Ωⁿ = ⋀[B]^n Ω[B⁄A]`, with the de Rham
differential. -/
@[expose]
noncomputable def complex : CochainComplex (ModuleCat.{v} A) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of A (Forms A B n)) (fun n => ModuleCat.ofHom (d A B n))
    fun n => by
      ext ω
      simp

/-- The degree-`n` object of the de Rham complex is the module of differential `n`-forms. -/
@[simp]
theorem complex_X (n : ℕ) : (complex A B).X n = ModuleCat.of A (Forms A B n) :=
  rfl

/-- The differential of the de Rham complex from degree `n` to degree `n + 1` is `d A B n`. -/
@[simp]
theorem complex_d (n : ℕ) : (complex A B).d n (n + 1) = ModuleCat.ofHom (d A B n) := by
  simp only [complex, CochainComplex.of_d]

/-- Pointwise evaluation of the differential of `complex A B` from degree `n` to `n + 1`. -/
theorem complex_d_apply (n : ℕ) (ω : Forms A B n) :
    (complex A B).d n (n + 1) ω = d A B n ω := by
  rw [complex_d]
  exact ModuleCat.ofHom_apply (d A B n) ω

/-- Differentials of `complex A B` vanish outside adjacent degrees `i ↦ i + 1`. -/
theorem complex_d_ne {i j : ℕ} (h : i + 1 ≠ j) : (complex A B).d i j = 0 := by
  apply CochainComplex.of_d_ne
  exact h

end

end TauCeti.DeRham
