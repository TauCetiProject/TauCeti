/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import Mathlib.Topology.Algebra.ValuativeRel.Completion
public import TauCeti.Topology.Algebra.IsOpenUnits
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# The inclusion of the valuation ring

Let `E` be a commutative ring with a valuative relation and valuation ring `𝒪[E]`. The structure
map `Algebra.ofId 𝒪[E] E` is the inclusion of `𝒪[E]` into `E`. When the topology of `E` is
defined by its valuation, `𝒪[E]` is open and closed in `E`, so this inclusion is both a closed and
an open embedding. When `E` is a field whose topology is defined by its valuation, such as a
nonarchimedean local field, `E` has open units, and the units of `𝒪[E]` are the elements of
valuation one, an open subset of `𝒪[E]`, so `𝒪[E]` has open units with continuous inversion.
This is the hypothesis under which the points of a scheme over `𝒪[E]` carry their chart topology.

## Main results

* `TauCeti.coe_ofId_integer`: the structure map `𝒪[E] → E` is the inclusion.
* `TauCeti.injective_ofId_integer` and `TauCeti.range_ofId_integer`: it is injective with
  image `𝒪[E]`.
* `TauCeti.isClosedEmbedding_ofId_integer` and `TauCeti.isOpenEmbedding_ofId_integer`: it is a
  closed and open embedding.
* `TauCeti.isOpen_one_submodule_integerRing` and `TauCeti.instDiscreteTopologyQuotientOne`: the
  unit `𝒪[E]`-submodule of `E` is open and `E ⧸ 𝒪[E]` is discrete.
* `TauCeti.completeSpace_integer`: `𝒪[E]` is a complete uniform subspace when `E` is complete.
* `TauCeti.isOpen_setOf_isUnit_integer` and `TauCeti.instIsOpenUnitsInteger`: over a field, the
  units of `𝒪[E]` are open, and `𝒪[E]` has open units.
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

section TopologicalSpace

variable [TopologicalSpace E] [IsValuativeTopology E]

/-- The inclusion of the valuation ring `𝒪[E]` into `E` is a closed embedding. -/
theorem isClosedEmbedding_ofId_integer : IsClosedEmbedding (Algebra.ofId 𝒪[E] E) := by
  rw [coe_ofId_integer]
  exact Valuation.isClosed_integer.isClosedEmbedding_subtypeVal

/-- The inclusion of the valuation ring `𝒪[E]` into `E` is an open embedding. -/
theorem isOpenEmbedding_ofId_integer : IsOpenEmbedding (Algebra.ofId 𝒪[E] E) := by
  rw [coe_ofId_integer]
  exact Valuation.isOpen_integer.isOpenEmbedding_subtypeVal

variable (E) in
/-- The submodule `(1 : Submodule 𝒪[E] E)` is open in `E`, as it coincides with `𝒪[E]`. -/
theorem isOpen_one_submodule_integerRing : IsOpen ((1 : Submodule 𝒪[E] E) : Set E) := by
  have heq : ((1 : Submodule 𝒪[E] E) : Set E) = (𝒪[E] : Set E) := by
    ext x
    rw [SetLike.mem_coe, Submodule.mem_one]
    simp only [Algebra.algebraMap_ofSubsemiring_apply]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  rw [heq]; exact Valuation.isOpen_integer

/-- The quotient `E ⧸ (1 : Submodule 𝒪[E] E)` carries the discrete topology. -/
instance instDiscreteTopologyQuotientOne : DiscreteTopology (E ⧸ (1 : Submodule 𝒪[E] E)) :=
  Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_one_submodule_integerRing E)

end TopologicalSpace

section Field

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]

/-- In a field whose topology is defined by its valuation, the units of the valuation ring
`𝒪[E]`, its elements of valuation one, form an open subset of `𝒪[E]`. -/
theorem isOpen_setOf_isUnit_integer : IsOpen {x : 𝒪[E] | IsUnit x} := by
  have : {x : 𝒪[E] | IsUnit x} = Subtype.val ⁻¹' {y : E | (valuation E).restrict y < 1}ᶜ := by
    ext x
    simp [Valuation.restrict_lt_one_iff, ← Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rw [this]
  exact ((valuation E).isClopen_ball 1).compl.isOpen.preimage continuous_subtypeVal

/-- The valuation ring `𝒪[E]` of a field whose topology is defined by its valuation has open
units: its units are open and inversion is continuous on them. This holds for every
nonarchimedean local field `E`. The field `E` itself has open units, as a Hausdorff topological
division ring. -/
instance instIsOpenUnitsInteger : IsOpenUnits 𝒪[E] :=
  .of_isEmbedding (f := (Subring.subtype 𝒪[E] : 𝒪[E] →* E))
    (by rw [MonoidHom.coe_ofClass, Subring.coe_subtype]; exact .subtypeVal)
    isOpen_setOf_isUnit_integer

end Field

/-- In a complete uniform ring `E` with a valuative topology, the valuation ring `𝒪[E]` is a
complete uniform subspace. -/
theorem completeSpace_integer (E : Type*) [CommRing E] [ValuativeRel E] [UniformSpace E]
    [IsValuativeTopology E] [CompleteSpace E] :
    CompleteSpace 𝒪[E] :=
  Valuation.isClosed_integer.completeSpace_coe

end TauCeti
