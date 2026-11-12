/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Coordinate functions on `GLₙ` and their values at points

Evaluating at the points of `GL n k` turns an element of the coordinate Hopf algebra `O(GLₙ)`
over a field `k` into a function `GL n k → k`. This file compares the two descriptions of
regular functions on `GLₙ`.

* The functions obtained this way are exactly the rational functions
  `TauCeti.Matrix.GeneralLinearGroup.rationalFunctions k n`, those of the form
  `g ↦ P(g) / det(g)ᵐ` for a polynomial `P` in the matrix entries.
* Over an infinite field the evaluation is injective: the points of `GL n k` separate the
  elements of `O(GLₙ)`, and pairs of points separate the elements of `O(GLₙ) ⊗ O(GLₙ)`. This is
  the Zariski density of the invertible matrices, `MvPolynomial.eq_of_eval_eq_on_gl`, read
  through the determinant localization.

Together these let identities between coordinate functions, such as the comultiplication of the
matrix coefficients of a representation, be checked on matrices.

## Main results

* `TauCeti.GeneralLinear.mem_rationalFunctions_iff_exists_generalLinearToPoint_apply_eq`: the
  rational functions on `GL n k` are the evaluations of coordinate functions.
* `TauCeti.GeneralLinear.eq_of_forall_generalLinearToPoint_apply_eq`: over an infinite field,
  points of `GL n k` separate coordinate functions.
* `TauCeti.GeneralLinear.tensor_eq_of_forall_lift_generalLinearToPoint_eq`: over an infinite
  field, pairs of points of `GL n k` separate the tensor square of `O(GLₙ)`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

variable {k : Type*} [Field k] {n : ℕ}

/-- Every coordinate function on `GLₙ` is a polynomial in the matrix entries divided by a power
of the determinant. -/
private theorem exists_mul_det_pow_eq (x : coordinateHopfAlgebra k n) :
    ∃ (m : ℕ) (P : MvPolynomial (Fin n × Fin n) k),
      x * (genericMatrix k n).det ^ m =
        coordinateHopfAlgebraAlgEquiv k n (coordinateRingMap k n P) := by
  obtain ⟨m, P, hP⟩ := IsLocalization.Away.surj
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) k))
    ((coordinateHopfAlgebraAlgEquiv k n).symm x)
  have hgen : genericMatrix k n =
      ((coordinateHopfAlgebraAlgEquiv k n).toAlgHom.comp (coordinateRingMap k n)).mapMatrix
        (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by
    ext i j
    simp [genericMatrix_apply]
  refine ⟨m, P, ?_⟩
  rw [hgen, ← AlgHom.map_det]
  simpa using congr(coordinateHopfAlgebraAlgEquiv k n $hP)

/-- **The rational functions on `GL n k` are the coordinate functions**: a function
`f : GL n k → k` is a polynomial in the matrix entries divided by a power of the determinant
exactly when it is evaluation at the points of `GL n k` of an element of `O(GLₙ)`. -/
theorem mem_rationalFunctions_iff_exists_generalLinearToPoint_apply_eq
    {f : GL (Fin n) k → k} :
    f ∈ Matrix.GeneralLinearGroup.rationalFunctions k n ↔
      ∃ x : coordinateHopfAlgebra k n, ∀ g : GL (Fin n) k,
        (generalLinearToPoint n g).ofConv x = f g := by
  constructor
  · intro hf
    obtain ⟨P, m, hP⟩ := Matrix.GeneralLinearGroup.mem_rationalFunctions_iff_inv.mp hf
    obtain ⟨u, hu⟩ := isUnit_det_genericMatrix k n
    refine ⟨(↑u⁻¹ : coordinateHopfAlgebra k n) ^ m *
      coordinateHopfAlgebraAlgEquiv k n (coordinateRingMap k n P), fun g ↦ ?_⟩
    have hmul : (generalLinearToPoint (R := k) n g).ofConv (↑u⁻¹ : coordinateHopfAlgebra k n) *
        (g : Matrix (Fin n) (Fin n) k).det = 1 := by
      rw [← generalLinearToPoint_det (R := k), ← hu, ← map_mul, Units.inv_mul, map_one]
    have hinv := eq_inv_of_mul_eq_one_left hmul
    rw [hP g, map_mul, map_pow, hinv, inv_pow, generalLinearToPoint_coordinateRingMap,
      MvPolynomial.aeval_eq_eval]
  · rintro ⟨x, hx⟩
    obtain ⟨m, P, hP⟩ := exists_mul_det_pow_eq x
    refine Matrix.GeneralLinearGroup.mem_rationalFunctions.mpr ⟨P, m, fun g ↦ ?_⟩
    have h := congr((generalLinearToPoint (R := k) n g).ofConv $hP)
    rw [map_mul, map_pow, hx, generalLinearToPoint_det, generalLinearToPoint_coordinateRingMap,
      MvPolynomial.aeval_eq_eval] at h
    rw [mul_comm, h]

/-- **Points of `GL n k` separate coordinate functions** over an infinite field: two elements of
`O(GLₙ)` with the same value at every invertible matrix are equal. This is the Zariski density of
`GL n k` in `GLₙ`. -/
theorem eq_of_forall_generalLinearToPoint_apply_eq [Infinite k]
    {x y : coordinateHopfAlgebra k n}
    (h : ∀ g : GL (Fin n) k,
      (generalLinearToPoint n g).ofConv x = (generalLinearToPoint n g).ofConv y) :
    x = y := by
  rw [← sub_eq_zero]
  obtain ⟨m, P, hP⟩ := exists_mul_det_pow_eq (x - y)
  have hP0 : P = 0 := MvPolynomial.eq_of_eval_eq_on_gl fun g ↦ by
    have hg := congr((generalLinearToPoint (R := k) n g).ofConv $hP)
    rw [map_mul, map_sub, h g, sub_self, zero_mul, generalLinearToPoint_coordinateRingMap,
      MvPolynomial.aeval_eq_eval] at hg
    rw [map_zero]
    exact hg.symm
  rwa [hP0, map_zero, map_zero, ((isUnit_det_genericMatrix k n).pow m).mul_left_eq_zero] at hP

/-- **Pairs of points of `GL n k` separate the tensor square of `O(GLₙ)`** over an infinite
field: two tensors are equal when the pair `(g, g')` of invertible matrices, sending
`x ⊗ y` to `x(g) y(g')`, takes the same value on both, for every such pair. -/
theorem tensor_eq_of_forall_lift_generalLinearToPoint_eq [Infinite k]
    {s t : coordinateHopfAlgebra k n ⊗[k] coordinateHopfAlgebra k n}
    (h : ∀ g g' : GL (Fin n) k,
      Algebra.TensorProduct.lift (generalLinearToPoint n g).ofConv
          (generalLinearToPoint n g').ofConv (fun _ _ ↦ .all ..) s =
        Algebra.TensorProduct.lift (generalLinearToPoint n g).ofConv
          (generalLinearToPoint n g').ofConv (fun _ _ ↦ .all ..) t) :
    s = t := by
  rw [← sub_eq_zero]
  let ev : GL (Fin n) k → coordinateHopfAlgebra k n →ₗ[k] k :=
    fun g ↦ (generalLinearToPoint (R := k) n g).ofConv.toLinearMap
  have hev : ∀ x, (∀ g, ev g x = 0) → x = 0 := fun x hx ↦
    eq_of_forall_generalLinearToPoint_apply_eq fun g ↦ by simpa [ev] using hx g
  refine tensor_eq_zero_of_forall_lid_map_eq_zero ev ev hev hev _ fun g g' ↦ ?_
  have hlift : ∀ u : coordinateHopfAlgebra k n ⊗[k] coordinateHopfAlgebra k n,
      TensorProduct.lid k k (TensorProduct.map (ev g) (ev g') u) =
        Algebra.TensorProduct.lift (generalLinearToPoint n g).ofConv
          (generalLinearToPoint n g').ofConv (fun _ _ ↦ .all ..) u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul x y => simp [ev]
    | add u v hu hv => simp only [map_add, hu, hv]
  rw [hlift, map_sub, h g g', sub_self]

end GeneralLinear

end TauCeti
