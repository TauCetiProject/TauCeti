/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Products of abstract completions

A product of uniform inducing maps is uniform inducing (`IsUniformInducing.piMap`), so the product
of a family of abstract completions is an abstract completion of the product
(`AbstractCompletion.pi`). This is the indexed analogue of Mathlib's `AbstractCompletion.prod`.

Combined with `AbstractCompletion.compareEquiv`, it identifies the separated completion of a
product with the product of the separated completions (`UniformSpace.Completion.piEquiv`), which
is how completions of free modules `ι → A` are compared with `ι → Completion A`.
-/

public section

/-- A product of uniform inducing maps is uniform inducing. -/
theorem IsUniformInducing.piMap {ι : Type*} {α β : ι → Type*} [∀ i, UniformSpace (α i)]
    [∀ i, UniformSpace (β i)] {f : ∀ i, α i → β i} (hf : ∀ i, IsUniformInducing (f i)) :
    IsUniformInducing (Pi.map f) := by
  simp only [isUniformInducing_iff_uniformSpace, Pi.uniformSpace_eq, UniformSpace.comap_iInf]
    at hf ⊢
  congr! with i
  rw [← hf i, ← UniformSpace.comap_comap, ← UniformSpace.comap_comap]
  rfl

namespace AbstractCompletion

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

variable {ι : Type*} {α : ι → Type*} [∀ i, UniformSpace (α i)]

/-- **Products of completions.** The product of abstract completions of the factors is an abstract
completion of the product, with the product of the completion maps. The body is exposed so that
the completion space is definitionally the product `∀ i, (pkg i).space`. -/
@[expose]
protected def pi (pkg : ∀ i, AbstractCompletion (α i)) : AbstractCompletion (∀ i, α i) where
  space := ∀ i, (pkg i).space
  coe := Pi.map fun i ↦ (pkg i).coe
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := IsUniformInducing.piMap fun i ↦ (pkg i).isUniformInducing
  dense := DenseRange.piMap fun i ↦ (pkg i).dense

end AbstractCompletion

namespace UniformSpace.Completion

variable {ι : Type*} (α : ι → Type*) [∀ i, UniformSpace (α i)]

/-- The separated completion of a product is the product of the separated completions. -/
noncomputable def piEquiv : Completion (∀ i, α i) ≃ᵤ ∀ i, Completion (α i) :=
  cPkg.compareEquiv (AbstractCompletion.pi fun _ ↦ cPkg)

variable {α}

/-- The comparison `piEquiv` sends the image of `x` to the family of images of its coordinates. -/
@[simp]
theorem piEquiv_coe (x : ∀ i, α i) : piEquiv α x = fun i ↦ (x i : Completion (α i)) :=
  cPkg.compare_coe _ x

end UniformSpace.Completion
