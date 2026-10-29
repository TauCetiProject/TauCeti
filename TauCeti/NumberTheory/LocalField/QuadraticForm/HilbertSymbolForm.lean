/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.Data.ZMod.IntUnitsPower
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity

/-!
# The local Hilbert symbol as a nondegenerate symmetric bilinear form

Let `K` be a nonarchimedean local field in which `2` is invertible, in any residue characteristic.
The Hilbert symbol `(a, b)_K ∈ {±1}` only depends on the square classes of `a` and `b`, so it is a
pairing on the finite `𝔽₂`-vector space `Kˣ/(Kˣ)²`. Read additively through the sign dictionary
`+1 ↦ 0`, `-1 ↦ 1` (`TauCeti.hilbertSign`), this pairing is a **nondegenerate symmetric
`𝔽₂`-bilinear form** `TauCeti.hilbertSymbolForm` on `TauCeti.SquareClassGroup K`.

The three properties are the square-class forms of the field-level results: symmetry is
`TauCeti.hilbertSymbol_comm`, bilinearity is the bimultiplicativity
`TauCeti.hilbertSymbol_mul_right` coming from the norm index theorem, and nondegeneracy is
`TauCeti.exists_hilbertSymbol_eq_neg_one`.

Over a finite extension of `ℚ_2` there is no closed formula for the symbol of Serre's shape, and
this form, on a group of order `4 · q ^ e` (`TauCeti.natCard_squareClassGroup_dyadic`), is what
determines it: a finite Gram matrix in any `𝔽₂`-basis of the square classes. Over `ℚ_2` that
matrix is `TauCeti.toMatrix_hilbertSymbolForm_padicTwo`.

## Main definitions

* `TauCeti.hilbertSymbolForm`: the Hilbert symbol as a `ZMod 2`-bilinear form on the square-class
  group.

## Main results

* `TauCeti.hilbertSymbolOnSquareClasses_add_left` and
  `TauCeti.hilbertSymbolOnSquareClasses_add_right`: the symbol on square classes is
  bimultiplicative.
* `TauCeti.exists_hilbertSymbolOnSquareClasses_eq_neg_one`: every nonzero square class pairs to
  `-1` with some square class.
* `TauCeti.hilbertSign_hilbertSymbolForm`, `TauCeti.hilbertSymbolForm_eq_zero_iff` and
  `TauCeti.hilbertSymbolForm_eq_one_iff`: the sign of the form is the Hilbert symbol.
* `TauCeti.isSymm_hilbertSymbolForm` and `TauCeti.nondegenerate_hilbertSymbolForm`: the form is
  symmetric and nondegenerate.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 2.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-! ### The symbol on square classes -/

/-- **Bimultiplicativity on square classes, in the second argument.** Over a nonarchimedean local
field in which `2` is invertible, `(x, y + z)_K = (x, y)_K · (x, z)_K` for square classes. -/
theorem hilbertSymbolOnSquareClasses_add_right (x y z : SquareClassGroup K) :
    hilbertSymbolOnSquareClasses x (y + z) =
      hilbertSymbolOnSquareClasses x y * hilbertSymbolOnSquareClasses x z := by
  rw [← squareClass_toMul_out x, ← squareClass_toMul_out y, ← squareClass_toMul_out z,
    ← squareClass_mul]
  simp only [hilbertSymbolOnSquareClasses_squareClass]
  exact hilbertSymbol_mul_right (Invertible.ne_zero 2) _ _ _

/-- **Bimultiplicativity on square classes, in the first argument.** Over a nonarchimedean local
field in which `2` is invertible, `(x + y, z)_K = (x, z)_K · (y, z)_K` for square classes. -/
theorem hilbertSymbolOnSquareClasses_add_left (x y z : SquareClassGroup K) :
    hilbertSymbolOnSquareClasses (x + y) z =
      hilbertSymbolOnSquareClasses x z * hilbertSymbolOnSquareClasses y z := by
  simp only [hilbertSymbolOnSquareClasses_comm _ z]
  exact hilbertSymbolOnSquareClasses_add_right z x y

/-- **Nondegeneracy on square classes.** Over a nonarchimedean local field in which `2` is
invertible, every nonzero square class `x` has `(x, y)_K = -1` for some square class `y`. -/
theorem exists_hilbertSymbolOnSquareClasses_eq_neg_one {x : SquareClassGroup K} (hx : x ≠ 0) :
    ∃ y : SquareClassGroup K, hilbertSymbolOnSquareClasses x y = -1 := by
  rw [← squareClass_toMul_out x, Ne, squareClass_eq_zero_iff] at hx
  obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one (Invertible.ne_zero 2) hx
  exact ⟨squareClass b, by
    rw [← squareClass_toMul_out x, hilbertSymbolOnSquareClasses_squareClass, hb]⟩

/-! ### The bilinear form -/

variable (K) in
/-- **The Hilbert symbol as a bilinear form over `𝔽₂`.** Over a nonarchimedean local field in which
`2` is invertible, the Hilbert symbol on square classes, read in `ZMod 2` through the dictionary
`+1 ↦ 0`, `-1 ↦ 1`, is a `ZMod 2`-bilinear form on `Kˣ/(Kˣ)²`. Its sign is the symbol
(`TauCeti.hilbertSign_hilbertSymbolForm`). -/
noncomputable def hilbertSymbolForm : LinearMap.BilinForm (ZMod 2) (SquareClassGroup K) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y ↦ additiveIntUnitsAddEquiv (Additive.ofMul (hilbertSymbolOnSquareClasses x y)))
    (fun x x' y ↦ by rw [hilbertSymbolOnSquareClasses_add_left, ofMul_mul, map_add])
    (fun c x y ↦ by
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp)
    (fun x y y' ↦ by rw [hilbertSymbolOnSquareClasses_add_right, ofMul_mul, map_add])
    (fun c x y ↦ by
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp)

/-- The Hilbert symbol form is the Hilbert symbol on square classes, read in `ZMod 2` through
`TauCeti.additiveIntUnitsAddEquiv`. -/
theorem hilbertSymbolForm_apply (x y : SquareClassGroup K) :
    hilbertSymbolForm K x y =
      additiveIntUnitsAddEquiv (Additive.ofMul (hilbertSymbolOnSquareClasses x y)) :=
  (rfl)

/-- **The sign of the Hilbert symbol form is the Hilbert symbol.** -/
@[simp]
theorem hilbertSign_hilbertSymbolForm (x y : SquareClassGroup K) :
    hilbertSign (hilbertSymbolForm K x y) = hilbertSymbolOnSquareClasses x y := by
  rw [eq_comm, eq_hilbertSign_iff, hilbertSymbolForm_apply]
  simp

/-- The Hilbert symbol form vanishes exactly where the Hilbert symbol is `+1`. -/
theorem hilbertSymbolForm_eq_zero_iff (x y : SquareClassGroup K) :
    hilbertSymbolForm K x y = 0 ↔ hilbertSymbolOnSquareClasses x y = 1 := by
  rw [← hilbertSign_hilbertSymbolForm, hilbertSign_eq_one_iff]

/-- The Hilbert symbol form is `1` exactly where the Hilbert symbol is `-1`. -/
theorem hilbertSymbolForm_eq_one_iff (x y : SquareClassGroup K) :
    hilbertSymbolForm K x y = 1 ↔ hilbertSymbolOnSquareClasses x y = -1 := by
  rw [← Int.units_ne_iff_eq_neg, Ne, ← hilbertSymbolForm_eq_zero_iff]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (hilbertSymbolForm K x y) with h | h <;>
    simp [h]

/-- **The Hilbert symbol form is symmetric.** -/
theorem isSymm_hilbertSymbolForm : (hilbertSymbolForm K).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ by
    rw [hilbertSymbolForm_apply, hilbertSymbolForm_apply, hilbertSymbolOnSquareClasses_comm]

/-- **The Hilbert symbol form is nondegenerate.** A square class `x` with `(x, y)_K = +1` for every
square class `y` is trivial, in either argument. -/
theorem nondegenerate_hilbertSymbolForm : (hilbertSymbolForm K).Nondegenerate := by
  have hleft : LinearMap.SeparatingLeft (hilbertSymbolForm K) := fun x hx ↦ by
    by_contra h
    obtain ⟨y, hy⟩ := exists_hilbertSymbolOnSquareClasses_eq_neg_one h
    exact absurd ((hilbertSymbolForm_eq_one_iff x y).mpr hy) (by simp [hx y])
  refine ⟨hleft, fun y hy ↦ hleft y fun x ↦ ?_⟩
  rw [isSymm_hilbertSymbolForm.eq]
  exact hy x

end TauCeti
