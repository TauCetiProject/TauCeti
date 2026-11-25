/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import TauCeti.Logic.Function.Fiber

/-!
# Finitely supported functions on a fibre

For `p : E → X` and an involution `f : E → E` over `X`, the restriction `Function.fiberMap f hf x`
is an involution of the fibre over `x`. Pushing a finitely supported function on that fibre forward
along it reads its value at the image (`Function.mapDomain_fiberMap_apply_of_involutive`).
-/

public section

namespace Function

variable {E X : Type*} {p : E → X}

/-- Moving the points of a finitely supported function on a fibre by an involution over the base
reads its value at the image. -/
theorem mapDomain_fiberMap_apply_of_involutive {M : Type*} [AddCommMonoid M] {f : E → E}
    (hff : Involutive f) (hf : p ∘ f = p) (x : X) (v : p ⁻¹' {x} →₀ M) (e : p ⁻¹' {x}) :
    Finsupp.mapDomain (fiberMap f hf x) v e = v (fiberMap f hf x e) := by
  conv_lhs => rw [← fiberMap_fiberMap_of_involutive hff hf x e]
  exact Finsupp.mapDomain_apply_of_injective (injective_fiberMap_of_involutive hff hf x) v _

end Function
