/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Path-algebra maps into scalar extensions

For a finite quiver, a `k`-algebra homomorphism `q : kQ →ₐ[k] A` induces an `l`-algebra
homomorphism `lQ →ₐ[l] l ⊗[k] A`, sending each path to the unit pure tensor of its image under
`q`. This construction depends only on the path-algebra homomorphism, so relation-quotient
comparisons can share it before checking their particular relations.

The construction and its path equation are extracted from the skew-zigzag scalar-extension
comparison in `TauCeti.RepresentationTheory.Quiver.Zigzag.BaseChange.TensorProduct`.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver
open scoped TensorProduct

universe u v w z

variable {k : Type w} {l : Type z} {Q : Type u} {A : Type*}
  [CommSemiring k] [CommSemiring l] [Algebra k l] [Quiver.{v} Q] [Finite Q]
  [Semiring A] [Algebra k A]

/-- Extend a path-algebra homomorphism to the extended coefficient ring by assigning unit
pure tensors to paths. No quotient relations or flatness assumptions are needed. -/
noncomputable def tensorLiftAlgHom (q : pathAlgebra k Q →ₐ[k] A) :
    pathAlgebra l Q →ₐ[l] l ⊗[k] A := by
  let g : pathAlgebra k Q →ₐ[k] l ⊗[k] A :=
    Algebra.TensorProduct.includeRight.comp q
  refine liftAlgHom l (fun p => g (ofPath p)) ?_ ?_ ?_
  · intro a b d p q
    rw [← map_mul, ofPath_mul_ofPath_of_comp]
  · intro p q hpq
    rw [← map_mul, ofPath_mul_ofPath_of_not_composable hpq, map_zero]
  · let _ := Fintype.ofFinite Q
    rw [← map_sum]
    simp only [← vertexIdempotent_eq_ofPath, ← one_def, map_one]

/-- The extended homomorphism sends a path to the unit pure tensor of its original image. -/
@[simp]
theorem tensorLiftAlgHom_ofPath (q : pathAlgebra k Q →ₐ[k] A) (p : Quiver.TotalPath Q) :
    tensorLiftAlgHom (l := l) q (ofPath p) = 1 ⊗ₜ[k] q (ofPath p) := by
  dsimp only [tensorLiftAlgHom]
  refine liftAlgHom_ofPath l _ ?_ ?_ _ p
  · intro a b d p q
    rw [← map_mul, ofPath_mul_ofPath_of_comp]
  · intro p q hpq
    rw [← map_mul, ofPath_mul_ofPath_of_not_composable hpq, map_zero]

end TauCeti.PathAlgebra
