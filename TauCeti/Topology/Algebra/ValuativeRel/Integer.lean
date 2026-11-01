/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# The inclusion of the valuation ring

Let `E` be a commutative ring with a valuative relation and valuation ring `𝒪[E]`. The structure
map `Algebra.ofId 𝒪[E] E` is the inclusion of `𝒪[E]` into `E`. When the topology of `E` is
defined by its valuation, `𝒪[E]` is open and closed in `E`, so this inclusion is both a closed and
an open embedding.

## Main results

* `TauCeti.coe_ofId_integer`: the structure map `𝒪[E] → E` is the inclusion.
* `TauCeti.injective_ofId_integer` and `TauCeti.range_ofId_integer`: it is injective with
  image `𝒪[E]`.
* `TauCeti.isClosedEmbedding_ofId_integer` and `TauCeti.isOpenEmbedding_ofId_integer`: it is a
  closed and open embedding.
-/

public section

open Topology ValuativeRel

namespace TauCeti

variable {E : Type*} [CommRing E] [ValuativeRel E]

/-- The structure map of the valuation ring `𝒪[E]` into `E` is its inclusion. -/
theorem coe_ofId_integer : ⇑(Algebra.ofId 𝒪[E] E) = Subtype.val :=
  funext fun r ↦ by rw [Algebra.ofId_apply, Algebra.algebraMap_ofSubsemiring_apply]

/-- The structure map of the valuation ring `𝒪[E]` into `E` is injective. -/
theorem injective_ofId_integer : Function.Injective (Algebra.ofId 𝒪[E] E) := by
  rw [coe_ofId_integer]
  exact Subtype.val_injective

/-- The image of the structure map of the valuation ring `𝒪[E]` into `E` is `𝒪[E]`. -/
theorem range_ofId_integer : Set.range (Algebra.ofId 𝒪[E] E) = 𝒪[E] := by
  rw [coe_ofId_integer, Subtype.range_coe]

variable [TopologicalSpace E] [IsValuativeTopology E]

/-- The inclusion of the valuation ring `𝒪[E]` into `E` is a closed embedding. -/
theorem isClosedEmbedding_ofId_integer : IsClosedEmbedding (Algebra.ofId 𝒪[E] E) := by
  rw [coe_ofId_integer]
  exact Valuation.isClosed_integer.isClosedEmbedding_subtypeVal

/-- The inclusion of the valuation ring `𝒪[E]` into `E` is an open embedding. -/
theorem isOpenEmbedding_ofId_integer : IsOpenEmbedding (Algebra.ofId 𝒪[E] E) := by
  rw [coe_ofId_integer]
  exact Valuation.isOpen_integer.isOpenEmbedding_subtypeVal

end TauCeti
