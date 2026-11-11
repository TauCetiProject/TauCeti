/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Multiplicative and additive equivalences of Pi types

Functions into products are multiplicatively (additively) equivalent to products of function
spaces: a family of pairs regroups into a pair of families. In the torsion decomposition of an
elliptic curve, each primary component of `E[N]` is a product of two cyclic groups; regrouping
lets the Chinese remainder theorem reassemble the first and second cyclic factors separately into
`ZMod N`.

Coordinate transport by `MulEquiv.arrowCongr` (`AddEquiv.arrowCongr`) inverts by reversing both
the coordinate and alphabet equivalences.

## Main declarations

* `TauCeti.MulEquiv.arrowProdEquivProdArrow`:
  `(∀ i, M i × N i) ≃* (∀ i, M i) × (∀ i, N i)`, with additive version
  `TauCeti.AddEquiv.arrowProdEquivProdArrow`.
* `MulEquiv.arrowCongr_symm`, `AddEquiv.arrowCongr_symm`: inversion reverses both equivalences
  in function transport.
-/

public section

/-- Inverting multiplicative function transport reverses the equivalences of both the domain and
the codomain. -/
@[to_additive (attr := simp) /-- Inverting additive function transport reverses the equivalences
of both the domain and the codomain. -/]
theorem MulEquiv.arrowCongr_symm {ι κ M N : Type*} [Mul M] [Mul N] (e : ι ≃ κ) (f : M ≃* N) :
    (MulEquiv.arrowCongr e f).symm = MulEquiv.arrowCongr e.symm f.symm := (rfl)

namespace TauCeti.MulEquiv

variable {ι : Type*} (M N : ι → Type*) [∀ i, Mul (M i)] [∀ i, Mul (N i)]

/-- Functions into products are multiplicatively equivalent to products of function spaces. -/
@[to_additive _root_.TauCeti.AddEquiv.arrowProdEquivProdArrow
/-- Functions into products are additively equivalent to products of function spaces. -/]
def arrowProdEquivProdArrow : (∀ i, M i × N i) ≃* (∀ i, M i) × (∀ i, N i) :=
  { Equiv.arrowProdEquivProdArrow ι M N with map_mul' := fun _ _ ↦ rfl }

/-- `arrowProdEquivProdArrow` maps a function to its two component functions. -/
@[to_additive (attr := simp) _root_.TauCeti.AddEquiv.arrowProdEquivProdArrow_apply
/-- `arrowProdEquivProdArrow` maps a function to its two component functions. -/]
theorem arrowProdEquivProdArrow_apply (f : ∀ i, M i × N i) :
    arrowProdEquivProdArrow M N f = (fun i ↦ (f i).1, fun i ↦ (f i).2) := (rfl)

/-- The inverse of `arrowProdEquivProdArrow` pairs component functions pointwise. -/
@[to_additive (attr := simp) _root_.TauCeti.AddEquiv.arrowProdEquivProdArrow_symm_apply
/-- The inverse of `arrowProdEquivProdArrow` pairs component functions pointwise. -/]
theorem arrowProdEquivProdArrow_symm_apply (f : (∀ i, M i) × (∀ i, N i)) :
    (arrowProdEquivProdArrow M N).symm f = fun i ↦ (f.1 i, f.2 i) := (rfl)

end TauCeti.MulEquiv
