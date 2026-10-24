/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Intertwining

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

A family of intertwining maps `f i : ρ i → τ i` tensors to an intertwining map between the
tensor products, applying `f i` in the `i`-th factor; this is functorial in the family.

## Main definitions

* `Representation.piTensorProduct`: the factorwise representation on an indexed tensor product.
* `Representation.IntertwiningMap.piTensorProduct`: the factorwise tensor product of a family of
  intertwining maps.
-/

public section

open scoped TensorProduct

namespace Representation

universe u v w x y z

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

variable {N : ι → Type y} {P : ι → Type z} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  {ρ : ∀ i, Representation R G (M i)} {τ : ∀ i, Representation R G (N i)}
  {υ : ∀ i, Representation R G (P i)}

/-- Applying an intertwining map in every tensor factor intertwines the tensor products of the
two families of representations. -/
noncomputable def IntertwiningMap.piTensorProduct (f : ∀ i, (ρ i).IntertwiningMap (τ i)) :
    (Representation.piTensorProduct ρ).IntertwiningMap (Representation.piTensorProduct τ) where
  toLinearMap := PiTensorProduct.map fun i ↦ (f i).toLinearMap
  isIntertwining' g := by
    ext m
    simp [piTensorProduct_apply_tprod, (f _).isIntertwining]

/-- The underlying linear map applies each intertwining map in its own tensor factor. -/
@[simp]
theorem IntertwiningMap.piTensorProduct_toLinearMap (f : ∀ i, (ρ i).IntertwiningMap (τ i)) :
    (IntertwiningMap.piTensorProduct f).toLinearMap =
      PiTensorProduct.map fun i ↦ (f i).toLinearMap :=
  (rfl)

/-- The tensor product of a family of intertwining maps acts factorwise on pure tensors. -/
@[simp]
theorem IntertwiningMap.piTensorProduct_apply_tprod (f : ∀ i, (ρ i).IntertwiningMap (τ i))
    (m : ∀ i, M i) :
    IntertwiningMap.piTensorProduct f (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ f i (m i) :=
  PiTensorProduct.map_tprod _ m

/-- The tensor product of the identity intertwining maps is the identity. -/
@[simp]
theorem IntertwiningMap.piTensorProduct_id :
    IntertwiningMap.piTensorProduct (fun i ↦ IntertwiningMap.id (ρ i)) =
      IntertwiningMap.id (Representation.piTensorProduct ρ) :=
  IntertwiningMap.ext PiTensorProduct.map_id

/-- The tensor product of a family of composites is the composite of the tensor products. -/
@[simp]
theorem IntertwiningMap.piTensorProduct_comp (g : ∀ i, (τ i).IntertwiningMap (υ i))
    (f : ∀ i, (ρ i).IntertwiningMap (τ i)) :
    IntertwiningMap.piTensorProduct (fun i ↦ (g i).comp (f i)) =
      (IntertwiningMap.piTensorProduct g).comp (IntertwiningMap.piTensorProduct f) :=
  IntertwiningMap.ext (PiTensorProduct.map_comp _ _)

end Representation
