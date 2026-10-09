/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Lie algebras over `R[X]` from an endomorphism commuting with inner derivations

Let `L` be a Lie algebra over a commutative ring `R` and `φ : Module.End R L` an endomorphism that
commutes with every inner derivation, `φ ⁅x, y⁆ = ⁅x, φ y⁆`. Then every polynomial `f(φ)` does
too, so the bracket of `L` is bilinear for the `R[X]`-module structure in which `X` acts by `φ`.
That module is Mathlib's `Module.AEval' φ`; this file puts the Lie ring of `L` on it and makes it
a Lie algebra over `R[X]`.

## Main definitions

* The `LieRing` and `LieAlgebra R` instances on `Module.AEval' φ`, transported from `L`.
* `TauCeti.Module.AEval'.lieAlgebra`: the `LieAlgebra R[X]` structure on `Module.AEval' φ`, for
  `φ` commuting with every inner derivation. It takes that hypothesis as an argument, so it is not
  an instance.

## Main results

* `TauCeti.Module.End.aeval_lie_right_of_lie_right`: if `φ` commutes with every inner derivation,
  so does every polynomial in `φ`.
-/

public section

open Polynomial

namespace TauCeti

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **Every polynomial in an endomorphism commuting with inner derivations commutes with them**:
if `φ ⁅x, y⁆ = ⁅x, φ y⁆` for all `x, y`, then `f(φ) ⁅x, y⁆ = ⁅x, f(φ) y⁆` for every `f ∈ R[X]`. -/
theorem Module.End.aeval_lie_right_of_lie_right {φ : Module.End R L}
    (h : ∀ x y : L, φ ⁅x, y⁆ = ⁅x, φ y⁆) (f : R[X]) (x y : L) :
    aeval φ f ⁅x, y⁆ = ⁅x, aeval φ f y⁆ := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg, lie_add]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, lie_smul]
    congr 1
    induction n generalizing y with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, ih]

/-- The Lie ring of `L`, on its `R[X]`-module `Module.AEval' φ`. -/
instance Module.AEval'.instLieRing (φ : Module.End R L) : LieRing (Module.AEval' φ) :=
  inferInstanceAs (LieRing L)

/-- The `R`-Lie algebra `L`, on its `R[X]`-module `Module.AEval' φ`. -/
instance Module.AEval'.instLieAlgebra (φ : Module.End R L) : LieAlgebra R (Module.AEval' φ) :=
  inferInstanceAs (LieAlgebra R L)

/-- The bracket on `Module.AEval' φ` is the bracket of `L`. -/
@[simp]
theorem Module.AEval'.of_lie_of (φ : Module.End R L) (x y : L) :
    ⁅Module.AEval'.of φ x, Module.AEval'.of φ y⁆ = Module.AEval'.of φ ⁅x, y⁆ :=
  (rfl)

/-- **The Lie algebra over `R[X]` attached to an endomorphism commuting with inner derivations**:
if `φ ⁅x, y⁆ = ⁅x, φ y⁆` for all `x, y`, the bracket of `L` on `Module.AEval' φ`, where `X` acts
by `φ` (`Module.AEval'.X_smul_of`), is `R[X]`-bilinear, by
`TauCeti.Module.End.aeval_lie_right_of_lie_right`. -/
noncomputable abbrev Module.AEval'.lieAlgebra {φ : Module.End R L}
    (h : ∀ x y : L, φ ⁅x, y⁆ = ⁅x, φ y⁆) : LieAlgebra R[X] (Module.AEval' φ) where
  lie_smul f x y := by
    obtain ⟨x, rfl⟩ := (Module.AEval'.of φ).surjective x
    obtain ⟨y, rfl⟩ := (Module.AEval'.of φ).surjective y
    rw [← Module.AEval.of_aeval_smul, Module.AEval'.of_lie_of, Module.AEval'.of_lie_of,
      ← Module.AEval.of_aeval_smul, Module.End.smul_def, Module.End.smul_def,
      Module.End.aeval_lie_right_of_lie_right h]

end TauCeti
