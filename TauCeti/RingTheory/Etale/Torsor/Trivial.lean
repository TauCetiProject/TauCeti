/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Basic
public import TauCeti.GroupTheory.GroupAction.DomAct
import TauCeti.RingTheory.Flat.Pi
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The trivial finite étale torsor

For a finite group `G` and any commutative ring `A`, the function algebra `G → A` with right
translation `(h • f) g = f (g * h)` is a finite étale `G`-torsor over `A`.
This includes zero rings and rings whose characteristic divides the group order.

The Galois map is Mathlib's `Algebra.TensorProduct.piScalarRight` followed by the coordinate
change `(g, x) ↦ (x * g, x)`. Thus its component at `g` pairs evaluation at `x` with evaluation at
`x * g`, not at `x * g⁻¹`. This fixes the convention needed for self-products of covers.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3 and proof of Proposition 15.4.
-/

public section

open TensorProduct

namespace TauCeti.Algebra

attribute [local instance] rightRegularMulSemiringAction

variable (G A : Type*) [Group G] [CommRing A]

/-- Scalars are constant in the outer function coordinate, not evaluated at that coordinate. -/
private local instance trivialFunctionAlgebra : Algebra (G → A) (G → G → A) :=
  Function.algebra G (G → A)

-- This shear preserves the left-factor algebra structure. It is only needed to identify the
-- Galois map with Mathlib's canonical tensor-to-functions equivalence.
private def trivialReindex : (G → G → A) ≃ₐ[G → A] (G → G → A) where
  toFun f g x := f (x * g) x
  invFun f y x := f (x⁻¹ * y) x
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] private theorem trivialReindex_apply (f : G → G → A) (g x : G) :
    trivialReindex G A f g x = f (x * g) x := (rfl)

/-- The split function algebra with right translation is a finite étale torsor.
No invertibility of the group order or nontriviality of the base ring is needed. -/
instance IsFiniteEtaleTorsor.trivial [Finite G] : IsFiniteEtaleTorsor G A (G → A) := by
  classical
  let := Fintype.ofFinite G
  let e := (Algebra.TensorProduct.piScalarRight A (G → A) (G → A) G).trans
    (trivialReindex G A)
  have he : e.toAlgHom = MulSemiringAction.tensorToPi A (G → A) G := by
    apply Algebra.TensorProduct.ext'
    intro f k
    ext g x
    simp [e, mul_comm]
  exact ⟨inferInstance, inferInstance, inferInstance, he ▸ e.bijective⟩

end TauCeti.Algebra
