/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basis
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Dimensions of balanced tensor products

A balanced tensor product of two finite modules over the ground ring is finite.
Over a division algebra, a right-module basis of the first factor identifies the
balanced tensor product with a direct sum of copies of the second factor. Thus its
ground-field dimension is the right dimension of the first factor times the
ground-field dimension of the second. When the second factor is nonzero and
finite-dimensional, finiteness of the tensor product detects finiteness of the
first factor over the division algebra.

These statements apply, in particular, to reconstruction of representations from
right modules over their endomorphism division algebras.
-/

public section

namespace TauCeti.BalancedTensorProduct

section Finite

variable {k D M N : Type*} [CommRing k] [Semiring D]
  [AddCommGroup M] [Module k M] [Module Dᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module D N]

/-- A balanced tensor product of finite ground-ring modules is finite. -/
instance [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (BalancedTensorProduct k D M N) :=
  Module.Finite.of_surjective (mkQ k D) (mkQ_surjective k D)

end Finite

section DivisionRing

variable {k D M N : Type*} [Field k] [DivisionRing D] [Algebra k D]
  [AddCommGroup M] [Module k M] [Module Dᵐᵒᵖ M] [IsScalarTower k Dᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- The ground-field dimension of a balanced tensor product over a division algebra.
Only the first factor needs to be finite over the division algebra; the second
factor may be infinite-dimensional over the ground field. -/
@[simp]
theorem finrank [Module.Finite Dᵐᵒᵖ M] :
    Module.finrank k (BalancedTensorProduct k D M N) =
      Module.finrank Dᵐᵒᵖ M * Module.finrank k N := by
  let b := Module.finBasis Dᵐᵒᵖ M
  -- Use the cardinal rank formula because the finite basis and `N` may have different universes.
  rw [(b.balancedTensorProductEquiv (k := k) (N := N)).finrank_eq]
  exact (congrArg Cardinal.toNat
    (rank_finsupp k N (Fin (Module.finrank Dᵐᵒᵖ M)))).trans (by simp [Module.finrank])

/-- Tensoring with a nonzero finite-dimensional left module detects whether a
right module over a division algebra is finite-dimensional over that algebra.
No separate finiteness hypothesis on the division algebra is required. -/
@[simp]
theorem finite_iff [Nontrivial N] [Module.Finite k N] :
    Module.Finite k (BalancedTensorProduct k D M N) ↔ Module.Finite Dᵐᵒᵖ M := by
  classical
  let b := Module.Free.chooseBasis Dᵐᵒᵖ M
  constructor
  · intro h
    have : Module.Finite k (Module.Free.ChooseBasisIndex Dᵐᵒᵖ M →₀ N) :=
      Module.Finite.equiv b.balancedTensorProductEquiv
    have : Finite (Module.Free.ChooseBasisIndex Dᵐᵒᵖ M) := by
      rcases Module.finite_finsupp_iff.mp ‹Module.Finite k (_ →₀ N)› with h | h | h
      · infer_instance
      · exact (not_subsingleton N h).elim
      · exact h.2
    exact Module.Finite.of_basis b
  · intro h
    have : Finite (Module.Free.ChooseBasisIndex Dᵐᵒᵖ M) := Module.Finite.finite_basis b
    exact Module.Finite.equiv b.balancedTensorProductEquiv.symm

end DivisionRing

end TauCeti.BalancedTensorProduct
