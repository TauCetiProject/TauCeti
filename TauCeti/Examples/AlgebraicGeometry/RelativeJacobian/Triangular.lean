/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeJacobian.Triangular
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Checks for the triangular coordinate change

The coordinate operations `TauCeti.RelativeJacobian.triangularEquiv` on pairs and tuples in a
group: the inverse sends `(f, g f⁻¹)` to `(f, g)`; the small diagonal `(f, …, f)` goes to
`(f, 1, …, 1)`; for noncommuting `a, b` (two elementary matrices in `GL₂(𝔽₂)`) the inverse sends
`(a, b)` to `(a, b a)`, not `(a, a b)`; on the diagonal `(a, a)` of a cyclic group of order three
the inverse gives `(a, a²)` and the forward map `(a, 1)`, with distinct tails. Over the dual
numbers `ℚ[ε]`, in the units (the points of `G_m`), the forward map sends `(1 + ε, 1)` to
`(1 + ε, 1 - ε)`, and the inverse restores `(1 + ε, 1)`: a calculation on reduced points would
miss the `ε` terms.
-/

public section

namespace TauCeti.RelativeJacobian

/-- The inverse sends `(f, g f⁻¹)` to `(f, g)`. -/
theorem triangularEquiv_symm_pair {G : Type*} [Group G] (f g : G) :
    (triangularEquiv 1).symm ![f, g / f] = ![f, g] := by
  ext j
  refine Fin.cases ?_ (fun r ↦ ?_) j <;> simp

/-- The small diagonal `(f, …, f)` goes to `(f, 1, …, 1)`. -/
theorem triangularEquiv_const {G : Type*} [Group G] (n : ℕ) (f : G) :
    triangularEquiv n (fun _ ↦ f) = Fin.cases f fun _ ↦ 1 := by
  ext j
  refine Fin.cases ?_ (fun r ↦ ?_) j <;> simp

/-- The upper elementary matrix `((1, 1), (0, 1))` in `GL₂(𝔽₂)`. -/
abbrev upperElementary : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩

/-- The lower elementary matrix `((1, 0), (1, 1))` in `GL₂(𝔽₂)`. -/
abbrev lowerElementary : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩

/-- **The head stands on the right.** In `GL₂(𝔽₂)`, the inverse coordinate change sends
`(a, b)` to `(a, b a)`, where `a b = ((0, 1), (1, 1))` and `b a = ((1, 1), (1, 0))` differ. -/
theorem triangularEquiv_symm_gl_two :
    (triangularEquiv 1).symm ![upperElementary, lowerElementary] =
        ![upperElementary, lowerElementary * upperElementary] ∧
      ((lowerElementary * upperElementary : GL (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, 1; 1, 0] ∧
      ((upperElementary * lowerElementary : GL (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1] ∧
      lowerElementary * upperElementary ≠ upperElementary * lowerElementary := by
  refine ⟨?_, by decide, by decide, fun h ↦ absurd (congrArg Units.val h) (by decide)⟩
  ext1 j
  refine Fin.cases ?_ (fun r ↦ ?_) j <;> simp

/-- On the diagonal `(a, a)` of the cyclic group of order three, with `a` a generator, the inverse
gives `(a, a²)` and the forward map `(a, 1)`; the tails differ. -/
theorem triangularEquiv_diagonal_cyclic :
    let a : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
    (triangularEquiv 1).symm ![a, a] = ![a, a * a] ∧ triangularEquiv 1 ![a, a] = ![a, 1] ∧
      a * a ≠ 1 := by
  refine ⟨?_, ?_, by decide⟩ <;>
  · ext1 j
    refine Fin.cases ?_ (fun r ↦ ?_) j <;> simp

/-- The unit `1 + ε` of the dual numbers `ℚ[ε]`, with inverse `1 - ε`. -/
abbrev onePlusEps : (DualNumber ℚ)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by linear_combination (-1 : DualNumber ℚ) * DualNumber.eps_mul_eps (R := ℚ)
  inv_val := by linear_combination (-1 : DualNumber ℚ) * DualNumber.eps_mul_eps (R := ℚ)

/-- **Nilpotent points.** On the `ℚ[ε]`-points of `G_m`, the forward map sends `(1 + ε, 1)` to
`(1 + ε, 1 - ε)` and the inverse restores `(1 + ε, 1)`. -/
theorem triangularEquiv_dualNumber :
    ((triangularEquiv 1 ![onePlusEps, 1] 1 : (DualNumber ℚ)ˣ) : DualNumber ℚ) =
        1 - DualNumber.eps ∧
      (triangularEquiv 1).symm (triangularEquiv 1 ![onePlusEps, 1]) = ![onePlusEps, 1] := by
  refine ⟨?_, Equiv.symm_apply_apply _ _⟩
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, triangularEquiv_apply_succ]
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, one_div]
  rfl

end TauCeti.RelativeJacobian
