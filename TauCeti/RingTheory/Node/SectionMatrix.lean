/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic

/-!
# The node-section matrix factorization of a binary quadratic form

A binary quadratic form `q = x ^ 2 + γ * x * y + δ * y ^ 2` with unit discriminant
`γ ^ 2 - 4 * δ` describes an ordinary double point `q(x, y) = 0`; over a field this includes
nonsplit nodes and characteristic two. Knudsen studies a node with a section through it by a
matrix factorization. It holds for every binary quadratic form `f = a x² + b x y + c y²` over
every commutative ring, so it is stated for `TauCeti.BinaryQuadraticForm` with no discriminant
hypothesis: the matrix `Φ = !![c y + c t + b x, a x + a s + b t; -(x - s), y - t]` has determinant
`f(x, y) - f(s, t)`, so `Φ` and its adjugate
`Ψ = !![y - t, -(a x + a s + b t); x - s, c y + c t + b x]` satisfy
`Φ * Ψ = Ψ * Φ = (f(x, y) - f(s, t)) • 1`.

On the ring of a section `(s, t)` through the node, where `f(x, y) = f(s, t)`, the two matrices
compose to zero (`TauCeti.PointedNodeRing.sectionMatrix`); Knudsen uses the periodic complex
alternating them to present the ideal of the section and its dual.

## Main declarations

* `TauCeti.BinaryQuadraticForm.nodeForm`: the node form `x ^ 2 + γ * x * y + δ * y ^ 2`.
* `TauCeti.BinaryQuadraticForm.sectionMatrix`: the left matrix `Φ` of the factorization.
* `TauCeti.BinaryQuadraticForm.det_sectionMatrix`: `det Φ = f(x, y) - f(s, t)`.
* `TauCeti.BinaryQuadraticForm.sectionMatrix_mul_adjugate`,
  `TauCeti.BinaryQuadraticForm.adjugate_mul_sectionMatrix`: the matrix factorization.

## References

* F. F. Knudsen, *A closer look at the stacks of stable pointed curves*, arXiv:1106.1588v2
  (2012): Definition 1.1 (the node form) and §3, Key Example (the matrices, for `a = 1`).
-/

public section

namespace TauCeti

namespace BinaryQuadraticForm

open Matrix

section NodeForm

variable {A B : Type*}

section One

variable [One A] (γ δ : A)

/-- The binary quadratic node form `x ^ 2 + γ * x * y + δ * y ^ 2`. It defines an ordinary double
point when its discriminant `γ ^ 2 - 4 * δ` is a unit; that condition is not part of the
definition. -/
def nodeForm : BinaryQuadraticForm A :=
  ⟨1, γ, δ⟩

@[simp]
theorem nodeForm_a : (nodeForm γ δ).a = 1 :=
  (rfl)

@[simp]
theorem nodeForm_b : (nodeForm γ δ).b = γ :=
  (rfl)

@[simp]
theorem nodeForm_c : (nodeForm γ δ).c = δ :=
  (rfl)

end One

section Semiring

variable [Semiring A] [Semiring B] (γ δ : A)

@[simp]
theorem eval_nodeForm (x y : A) : (nodeForm γ δ).eval x y = x ^ 2 + γ * x * y + δ * y ^ 2 := by
  simp [eval_def]

@[simp]
theorem map_nodeForm (φ : A →+* B) : (nodeForm γ δ).map φ = nodeForm (φ γ) (φ δ) := by
  ext <;> simp

/-- A ring homomorphism carries the value of the node form to the value of the mapped node form
at the mapped point. -/
theorem eval_nodeForm_map (φ : A →+* B) (x y : A) :
    (nodeForm (φ γ) (φ δ)).eval (φ x) (φ y) = φ ((nodeForm γ δ).eval x y) := by
  rw [← map_nodeForm, eval_map]

end Semiring

@[simp]
theorem discrim_nodeForm [CommRing A] (γ δ : A) : (nodeForm γ δ).discrim = γ ^ 2 - 4 * δ := by
  simp [discrim_def, discrim, sq]

end NodeForm

variable {R S : Type*} [CommRing R] [CommRing S] (f : BinaryQuadraticForm R)

variable (x y s t : R)

/-- The left matrix `Φ = !![c y + c t + b x, a x + a s + b t; -(x - s), y - t]` of the
node-section matrix factorization of `f = a x² + b x y + c y²` at the points `(x, y)` and
`(s, t)`. Its determinant is `f(x, y) - f(s, t)` and its adjugate is the right matrix `Ψ` of the
factorization. -/
def sectionMatrix : Matrix (Fin 2) (Fin 2) R :=
  !![f.c * y + f.c * t + f.b * x, f.a * x + f.a * s + f.b * t; -(x - s), y - t]

theorem sectionMatrix_def :
    f.sectionMatrix x y s t =
      !![f.c * y + f.c * t + f.b * x, f.a * x + f.a * s + f.b * t; -(x - s), y - t] :=
  (rfl)

@[simp]
theorem sectionMatrix_apply_zero_zero :
    f.sectionMatrix x y s t 0 0 = f.c * y + f.c * t + f.b * x :=
  (rfl)

@[simp]
theorem sectionMatrix_apply_zero_one :
    f.sectionMatrix x y s t 0 1 = f.a * x + f.a * s + f.b * t :=
  (rfl)

@[simp]
theorem sectionMatrix_apply_one_zero : f.sectionMatrix x y s t 1 0 = -(x - s) :=
  (rfl)

@[simp]
theorem sectionMatrix_apply_one_one : f.sectionMatrix x y s t 1 1 = y - t :=
  (rfl)

/-- The right matrix `Ψ` of the node-section factorization, the adjugate of `Φ`. -/
theorem adjugate_sectionMatrix :
    (f.sectionMatrix x y s t).adjugate =
      !![y - t, -(f.a * x + f.a * s + f.b * t); x - s, f.c * y + f.c * t + f.b * x] := by
  rw [sectionMatrix_def, adjugate_fin_two_of, neg_neg]

/-- The determinant of the node-section matrix is the difference `f(x, y) - f(s, t)` of the
values of the form at the two points. -/
@[simp]
theorem det_sectionMatrix : (f.sectionMatrix x y s t).det = f.eval x y - f.eval s t := by
  rw [sectionMatrix_def, det_fin_two_of, eval_def, eval_def]
  ring

/-- The node-section matrix factorization, `Φ * Ψ = (f(x, y) - f(s, t)) • 1`. -/
theorem sectionMatrix_mul_adjugate :
    f.sectionMatrix x y s t * (f.sectionMatrix x y s t).adjugate =
      (f.eval x y - f.eval s t) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [mul_adjugate, det_sectionMatrix]

/-- The node-section matrix factorization, `Ψ * Φ = (f(x, y) - f(s, t)) • 1`. -/
theorem adjugate_mul_sectionMatrix :
    (f.sectionMatrix x y s t).adjugate * f.sectionMatrix x y s t =
      (f.eval x y - f.eval s t) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [adjugate_mul, det_sectionMatrix]

/-- Ring homomorphisms commute with the node-section matrix, acting on the coefficients of the
form and on both points. -/
theorem map_sectionMatrix (φ : R →+* S) :
    (f.sectionMatrix x y s t).map φ = (f.map φ).sectionMatrix (φ x) (φ y) (φ s) (φ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectionMatrix_def]

end BinaryQuadraticForm

end TauCeti
