/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.RingTheory.DedekindDomain.Circle
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Evaluating the coordinate ring of the real circle on the unit circle

The coordinate ring `TauCeti.CircleRing ℝ = ℝ[x, y] ⧸ (x² + y² - 1)` of the real algebraic circle
consists of functions on the unit circle `Circle` of the complex plane: `x` and `y` are the real
and imaginary parts of a point. This is the algebra map
`TauCeti.CircleRing.evalCircle : CircleRing ℝ →ₐ[ℝ] C(Circle, ℝ)`.

Consequently an invertible matrix over `CircleRing ℝ` gives a loop of invertible real matrices,
`TauCeti.CircleRing.evalGL : GL n (CircleRing ℝ) →* C(Circle, GL n ℝ)`. The loop of an elementary
matrix is nullhomotopic, and relative to the basepoint `1` when it starts at the identity matrix.
So a matrix over `CircleRing ℝ` none of whose stabilizations by identity blocks has a
nullhomotopic loop is not elementary after any stabilization, and has a nontrivial class in
`K₁(CircleRing ℝ)`. For the rotation matrix `!![x, -y; y, x]`, whose loop is the standard
generator of the rotations, nontriviality of the stabilized loops comes from the Spin double cover.

## Main definitions

* `TauCeti.CircleRing.evalCircle`: the evaluation `CircleRing ℝ →ₐ[ℝ] C(Circle, ℝ)`.
* `TauCeti.CircleRing.evalGL`: the loop `Circle → GL n ℝ` of an invertible matrix over
  `CircleRing ℝ`.

## Main results

* `TauCeti.CircleRing.evalGL_homotopic_one_of_mem_elementarySubgroup`: the loop of an elementary
  matrix is nullhomotopic.
* `TauCeti.CircleRing.evalGL_homotopicRel_one_of_mem_elementarySubgroup`: the loop of an
  elementary matrix which is the identity at `1` is nullhomotopic relative to `1`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.4.
-/

public section

namespace TauCeti.CircleRing

/-- **Evaluation on the unit circle.** The coordinate ring of the real circle maps to the
continuous real functions on the unit circle of `ℂ`, sending `x` to the real part and `y` to the
imaginary part. -/
noncomputable def evalCircle : CircleRing ℝ →ₐ[ℝ] C(Circle, ℝ) :=
  lift ⟨fun z ↦ (z : ℂ).re, by fun_prop⟩ ⟨fun z ↦ (z : ℂ).im, by fun_prop⟩ <| by
    ext z
    simpa [sq, Complex.normSq_apply] using Circle.normSq_coe z

/-- The coordinate `x` evaluates to the real part. -/
@[simp]
theorem evalCircle_x_apply (z : Circle) : evalCircle x z = (z : ℂ).re := by
  simp [evalCircle]

/-- The coordinate `y` evaluates to the imaginary part. -/
@[simp]
theorem evalCircle_y_apply (z : Circle) : evalCircle y z = (z : ℂ).im := by
  simp [evalCircle]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The loop of an invertible matrix over the circle.** An invertible matrix over the coordinate
ring of the real circle evaluates at each point of the unit circle to an invertible real matrix,
continuously in the point. -/
noncomputable def evalGL : GL n (CircleRing ℝ) →* C(Circle, GL n ℝ) :=
  ContinuousMap.evalGL.comp (Units.map evalCircle.toRingHom.mapMatrix.toMonoidHom)

/-- The loop of an invertible matrix over the circle is the pointwise evaluation of its image
under `evalCircle`. -/
theorem evalGL_eq (g : GL n (CircleRing ℝ)) :
    evalGL g = ContinuousMap.evalGL (Units.map evalCircle.toRingHom.mapMatrix.toMonoidHom g) :=
  (rfl)

/-- The entries of the loop of an invertible matrix over the circle are the evaluations of its
entries. -/
@[simp]
theorem coe_evalGL_apply (g : GL n (CircleRing ℝ)) (z : Circle) (i j : n) :
    (evalGL g z : Matrix n n ℝ) i j = evalCircle ((g : Matrix n n (CircleRing ℝ)) i j) z := by
  simp [evalGL]

/-- The entries of the inverse of the loop of an invertible matrix over the circle are the
evaluations of the entries of its inverse. -/
@[simp]
theorem coe_inv_evalGL_apply (g : GL n (CircleRing ℝ)) (z : Circle) (i j : n) :
    (((evalGL g z)⁻¹ : GL n ℝ) : Matrix n n ℝ) i j =
      evalCircle (((g⁻¹ : GL n (CircleRing ℝ)) : Matrix n n (CircleRing ℝ)) i j) z := by
  simp [evalGL]

/-- **Elementary matrices over the circle give nullhomotopic loops.** -/
theorem evalGL_homotopic_one_of_mem_elementarySubgroup {g : GL n (CircleRing ℝ)}
    (hg : g ∈ elementarySubgroup n (CircleRing ℝ)) : (evalGL g).Homotopic 1 :=
  ContinuousMap.evalGL_homotopic_one_of_mem_elementarySubgroup <|
    evalCircle.toRingHom.map_elementarySubgroup_le ⟨g, hg, rfl⟩

/-- **Elementary matrices over the circle give based nullhomotopic loops.** The loop of an
elementary matrix over the circle which is the identity matrix at `1` is homotopic to the constant
loop relative to `1`. -/
theorem evalGL_homotopicRel_one_of_mem_elementarySubgroup {g : GL n (CircleRing ℝ)}
    (hg : g ∈ elementarySubgroup n (CircleRing ℝ)) (h₁ : evalGL g 1 = 1) :
    (evalGL g).HomotopicRel 1 {1} :=
  (ContinuousMap.homotopicRel_singleton_iff_homotopic_of_apply_eq h₁).2 <|
    evalGL_homotopic_one_of_mem_elementarySubgroup hg

end TauCeti.CircleRing
