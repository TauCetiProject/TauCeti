/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# The defining representation of a matrix Lie algebra and its subalgebras

A Lie subalgebra `K` of square matrices acts faithfully on coordinate vectors `n → R`. The
representation of its universal enveloping algebra on this Lie module is
`TauCeti.UniversalEnvelopingAlgebra.representation R K (n → R)`. This file records the values of
that representation on Lie generators in matrix terms and shows that a Lie generator acts
nilpotently exactly when its underlying matrix is nilpotent. For the ambient matrix Lie algebra
`Matrix n n R`, it also identifies `TauCeti.UniversalEnvelopingAlgebra.representation` on canonical
generators with `Matrix.toLinAlgEquiv'` and evaluates the second divided power when a matrix squares
to `2 • D`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representation_ι_matrix` and
  `TauCeti.UniversalEnvelopingAlgebra.representation_ι_matrix_apply`: a Lie generator of a matrix
  Lie subalgebra acts through its underlying matrix.
* `TauCeti.UniversalEnvelopingAlgebra.isNilpotent_representation_ι_matrix_iff`: a Lie generator
  acts nilpotently exactly when its underlying matrix is nilpotent.
* `TauCeti.UniversalEnvelopingAlgebra.representation_matrix_ι` and
  `TauCeti.UniversalEnvelopingAlgebra.dividedPower_two_representation_matrix_apply`: generator and
  divided-square action for `TauCeti.UniversalEnvelopingAlgebra.representation` on `Matrix n n R`.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie generator of a matrix Lie subalgebra acts on coordinate vectors through its underlying
matrix. -/
theorem representation_ι_matrix {K : LieSubalgebra R (Matrix n n R)} (x : K) :
    representation R K (n → R) (_root_.UniversalEnvelopingAlgebra.ι R x) =
      toLinAlgEquiv' (x : Matrix n n R) := by
  ext v
  simp

/-- Pointwise, a Lie generator of a matrix Lie subalgebra acts by matrix-vector multiplication. -/
theorem representation_ι_matrix_apply {K : LieSubalgebra R (Matrix n n R)} (x : K) (v : n → R) :
    representation R K (n → R) (_root_.UniversalEnvelopingAlgebra.ι R x) v =
      (x : Matrix n n R) *ᵥ v := by
  rw [representation_ι_matrix, toLinAlgEquiv'_apply]

/-- A Lie generator of a matrix Lie subalgebra acts nilpotently on coordinate vectors if and only
if its underlying matrix is nilpotent. -/
theorem isNilpotent_representation_ι_matrix_iff {K : LieSubalgebra R (Matrix n n R)} (x : K) :
    IsNilpotent (representation R K (n → R) (_root_.UniversalEnvelopingAlgebra.ι R x)) ↔
      IsNilpotent (x : Matrix n n R) := by
  rw [representation_ι_matrix, IsNilpotent.map_iff toLinAlgEquiv'.injective]

section Matrix

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- In the defining representation of `Matrix n n R`, a canonical Lie generator acts through
`Matrix.toLinAlgEquiv'`. -/
theorem representation_matrix_ι (X : Matrix n n R) :
    representation R (Matrix n n R) (n → R) (_root_.UniversalEnvelopingAlgebra.ι R X) =
      Matrix.toLinAlgEquiv' X :=
  LinearMap.ext fun v => by
    rw [representation_ι_apply, Matrix.lie_apply, Matrix.toLinAlgEquiv'_apply]

/-- When a matrix over a commutative `ℚ`-algebra squares to `2 • D`, the second divided power of
its canonical generator in the defining representation acts by matrix-vector multiplication by
`D`. -/
theorem dividedPower_two_representation_matrix_apply {A : Type*} [CommRing A] [Algebra ℚ A]
    {X D : Matrix n n A} (hsq : X * X = 2 • D) (v : n → A) :
    Associative.dividedPower 2
      (representation A (Matrix n n A) (n → A) (_root_.UniversalEnvelopingAlgebra.ι A X)) v =
      D *ᵥ v := by
  have hsq' : representation A (Matrix n n A) (n → A)
      (_root_.UniversalEnvelopingAlgebra.ι A X) ^ 2 =
      (2 : ℕ) • Matrix.toLinAlgEquiv' D := by
    rw [representation_matrix_ι, ← map_pow, sq, hsq, map_nsmul]
  rw [Associative.dividedPower_def, LinearMap.smul_apply, hsq', LinearMap.smul_apply,
    Matrix.toLinAlgEquiv'_apply, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  norm_num [Nat.factorial]

end Matrix

end TauCeti.UniversalEnvelopingAlgebra
