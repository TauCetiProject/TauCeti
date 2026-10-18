/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# Tensor products of families of representations

A family of representations `ρ i` of one monoid `G` on modules `M i` gives a representation of
`G` on the indexed tensor product `⨂[R] i, M i`, in which every element acts factorwise:

```text
g • (⨂ₜ i, m i) = ⨂ₜ i, ρ i g (m i).
```

This is the indexed analogue of Mathlib's binary `Representation.tprod`. It is the form in which
the restriction of a tensor-induced representation splits over double cosets: each double coset
contributes one factor, and the subgroup acts on all factors at once.

## Main definitions

* `Representation.piTensorProduct`: the factorwise representation on an indexed tensor product.
-/

public section

open scoped TensorProduct

namespace Representation

universe u v w x

variable {R : Type u} {G : Type v} {ι : Type w} {M : ι → Type x}
  [CommSemiring R] [Monoid G] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The tensor product of a family of representations of `G`: an element of `G` acts on
`⨂[R] i, M i` by acting in every tensor factor. -/
noncomputable def piTensorProduct (ρ : ∀ i, Representation R G (M i)) :
    Representation R G (⨂[R] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

/-- The action on the indexed tensor product is the tensor product of the factor actions. -/
theorem piTensorProduct_apply (ρ : ∀ i, Representation R G (M i)) (g : G) :
    piTensorProduct ρ g = PiTensorProduct.map fun i ↦ ρ i g := (rfl)

/-- On a pure tensor, every factor is acted on by its own representation. -/
@[simp]
theorem piTensorProduct_apply_tprod (ρ : ∀ i, Representation R G (M i)) (g : G)
    (m : ∀ i, M i) :
    piTensorProduct ρ g (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ ρ i g (m i) := by
  rw [piTensorProduct_apply, PiTensorProduct.map_tprod]

end Representation
