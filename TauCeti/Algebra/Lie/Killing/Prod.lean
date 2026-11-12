/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.Killing
public import TauCeti.LinearAlgebra.BilinearForm.Prod
import TauCeti.Algebra.Lie.AdjointAction.Prod
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# The Killing form of a product of Lie algebras

The adjoint action of `L × L'` acts separately on the two factors, so the Killing form of the
product is the sum of the Killing forms of the factors. Consequently a product of two Killing Lie
algebras is again Killing. This lets constructions stated for finite-dimensional Lie algebras with
nondegenerate Killing form, such as the internal Jordan decomposition, be applied to products and
compared with the corresponding constructions on the factors.

The statements hold over any commutative ring for factors that are free of finite rank, which is
what the trace of a product endomorphism needs.

## Main declarations

* `LieAlgebra.killingForm_prod_apply`: the Killing form of `L × L'` is the sum of the Killing
  forms of `L` and `L'`.
* `LieAlgebra.killingForm_prod`: the Killing form of `L × L'` is the product bilinear form of the
  Killing forms of `L` and `L'`.
* `LieAlgebra.IsKilling.instProd`: a product of Killing Lie algebras is Killing.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.2.
-/

public section

open LinearMap

namespace LieAlgebra

variable (R L L' : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [Module.Free R L] [Module.Finite R L] [Module.Free R L'] [Module.Finite R L']

/-- The Killing form of a product of Lie algebras is the sum of the Killing forms of the
factors. -/
@[simp]
theorem killingForm_prod_apply (x y : L × L') :
    killingForm R (L × L') x y = killingForm R L x.1 y.1 + killingForm R L' x.2 y.2 := by
  rw [killingForm_apply_apply, ad_prod, ad_prod, prodMap_comp, trace_prodMap',
    killingForm_apply_apply, killingForm_apply_apply]

/-- The Killing form of a product of Lie algebras is the product bilinear form of the Killing
forms of the factors. -/
theorem killingForm_prod :
    killingForm R (L × L') = (killingForm R L).prod (killingForm R L') :=
  LinearMap.ext₂ fun x y ↦ by simp

/-- A product of two Killing Lie algebras is Killing. -/
instance IsKilling.instProd [IsKilling R L] [IsKilling R L'] : IsKilling R (L × L') :=
  TauCeti.isKilling_of_killingForm_nondegenerate R (L × L') <| killingForm_prod R L L' ▸
    BilinForm.nondegenerate_prod_iff.2
      ⟨IsKilling.killingForm_nondegenerate R L, IsKilling.killingForm_nondegenerate R L'⟩

end LieAlgebra
