/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# Associativity of the degree-zero Tate cup product

In Tate degree zero, the cup product of two classes of invariant vectors is the class of
their pure tensor. The tensor associator therefore identifies the two ways to cup three
degree-zero classes. This is the degree-zero base of associativity for the Tate cup product.

See Artin and Tate, *Class Field Theory*, Preliminaries §2, and Brown,
*Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The degree-zero Tate cup product is associative, after applying the tensor associator
to the coefficient representation. -/
@[simp]
theorem cupH0_assoc_zero (M N P : Rep k G)
    (x : tateCohomology M 0) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor 0).map (α_ M N P).hom
      (cupH0 (M ⊗ N) P 0 (cupH0 M N 0 x y) z) =
      cupH0 M (N ⊗ P) 0 x (cupH0 N P 0 y z) := by
  induction x using H0_induction_on with
  | h x =>
    induction y using H0_induction_on with
    | h y =>
      induction z using H0_induction_on with
      | h z =>
        rw [cupH0_H0π_H0π, cupH0_H0π_H0π,
          cupH0_H0π_H0π, cupH0_H0π_H0π,
          H0π_comp_tateCohomologyFunctor_map_apply]
        apply congrArg (H0π (M ⊗ (N ⊗ P)))
        apply Subtype.ext
        change (TensorProduct.assoc k M.V N.V P.V)
          (((x : M.V) ⊗ₜ[k] (y : N.V)) ⊗ₜ[k] (z : P.V)) =
            (x : M.V) ⊗ₜ[k] ((y : N.V) ⊗ₜ[k] (z : P.V))
        exact TensorProduct.assoc_tmul (x : M.V) (y : N.V) (z : P.V)

/-- Associativity of the Tate cup product in bidegrees `(0, 0, 0)`. -/
theorem cup_assoc_zero_zero_zero (M N P : Rep k G)
    (x : tateCohomology M 0) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor 0).map (α_ M N P).hom
      (cup (M ⊗ N) P 0 0 0 (by omega)
        (cup M N 0 0 0 (by omega) x y) z) =
      cup M (N ⊗ P) 0 0 0 (by omega) x
        (cup N P 0 0 0 (by omega) y z) := by
  simpa only [cup_zero_right] using cupH0_assoc_zero M N P x y z

end TauCeti.TateCohomology
