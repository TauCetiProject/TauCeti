/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# The defining representation of a matrix Lie subalgebra

A Lie subalgebra `K` of square matrices acts faithfully on coordinate vectors `n → R`. The
representation of its universal enveloping algebra on this Lie module is
`TauCeti.UniversalEnvelopingAlgebra.representation R K (n → R)`. This file records the values of
that representation on Lie generators in matrix terms and
that a Lie generator acts nilpotently exactly when its underlying matrix is nilpotent.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representation_ι_matrix`: a Lie generator acts through its
  underlying matrix.
* `TauCeti.UniversalEnvelopingAlgebra.isNilpotent_representation_ι_matrix_iff`: a Lie generator
  acts nilpotently exactly when its underlying matrix is nilpotent.
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

end TauCeti.UniversalEnvelopingAlgebra
