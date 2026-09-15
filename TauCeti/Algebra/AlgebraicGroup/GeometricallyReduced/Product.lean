/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product

/-!
# Geometric reducedness of products of affine groups

The coordinate algebra of a direct product of affine groups is the tensor product of their
coordinate algebras. For affine groups of finite type over a field, geometric reducedness is
equivalent to smoothness, and smoothness is preserved by products. It follows that the tensor
product of two geometrically reduced coordinate Hopf algebras of finite type is geometrically
reduced.

## Main declarations

* `TauCeti.geometricallyReducedCommHopfAlgProperty.tensorProduct`: finite-type geometrically
  reduced affine groups are closed under direct products.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

noncomputable section

namespace geometricallyReducedCommHopfAlgProperty

variable {k : Type u} [Field k]

/-- The tensor product of two finite-type geometrically reduced commutative Hopf algebras is
geometrically reduced. Contravariantly, direct products of geometrically reduced affine groups of
finite type are geometrically reduced. -/
theorem tensorProduct (H K : CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] [Algebra.FiniteType k K]
    (hH : geometricallyReducedCommHopfAlgProperty k H)
    (hK : geometricallyReducedCommHopfAlgProperty k K) :
    geometricallyReducedCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  let _ : Algebra.FiniteType k (H ⊗[k] K) :=
    FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) H K
  rw [← smoothCommHopfAlgProperty_iff_geometricallyReduced] at hH hK ⊢
  exact smoothCommHopfAlgProperty.tensorProduct H K hH hK

end geometricallyReducedCommHopfAlgProperty

end

end TauCeti
