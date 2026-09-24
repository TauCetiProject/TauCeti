/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod

/-!
# Additive equivalences of Pi types

Functions into products are additively equivalent to products of function spaces.

## Main definitions

* `TauCeti.AddEquiv.arrowProdEquivProdArrow`: `(∀ i, B i × C i) ≃+ (∀ i, B i) × (∀ i, C i)`.
-/

public section

namespace TauCeti

namespace AddEquiv

/-- Functions into products are additively equivalent to products of function spaces. -/
def arrowProdEquivProdArrow {ι : Type*} (B C : ι → Type*)
    [∀ i, Add (B i)] [∀ i, Add (C i)] :
    (∀ i, B i × C i) ≃+ (∀ i, B i) × (∀ i, C i) :=
  { Equiv.arrowProdEquivProdArrow ι B C with map_add' := fun _ _ ↦ rfl }

/-- `arrowProdEquivProdArrow` maps a function to its two component functions. -/
@[simp]
theorem arrowProdEquivProdArrow_apply (B C : ι → Type*) [∀ i, Add (B i)] [∀ i, Add (C i)]
    (f : ∀ i, B i × C i) : arrowProdEquivProdArrow B C f = (fun i ↦ (f i).1, fun i ↦ (f i).2) :=
  Equiv.arrowProdEquivProdArrow_apply ι B C f

/-- The inverse of `arrowProdEquivProdArrow` pairs component functions pointwise. -/
@[simp]
theorem arrowProdEquivProdArrow_symm_apply (B C : ι → Type*) [∀ i, Add (B i)] [∀ i, Add (C i)]
    (f : (∀ i, B i) × (∀ i, C i)) :
    (arrowProdEquivProdArrow B C).symm f = fun i ↦ (f.1 i, f.2 i) :=
  by
    apply funext
    intro i
    exact Equiv.arrowProdEquivProdArrow_symm_apply ι B C f i

end AddEquiv

end TauCeti
