/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Second countability of restricted products

A restricted product `Πʳ i, [R i, A i]` indexed by a countable type `ι` is second countable
whenever each factor `R i` is second countable and each reference set `A i` is open.

Each principal stage `Πʳ i, [R i, A i]_[𝓟 S]` embeds into the full product `Π i, R i`
(`RestrictedProduct.isEmbedding_coe_of_principal`), which is second countable for countable `ι`.
Over the cofinite filter, the open sets `Set.range (RestrictedProduct.inclusion R A hS)` as `S`
varies over cofinite complements of finite sets `T : Finset ι` form a countable open cover of
`Πʳ i, [R i, A i]` by second-countable subspaces, so Mathlib's
`TopologicalSpace.secondCountableTopology_of_countable_cover` applies directly.

## Main results

* `TauCeti.instSecondCountableTopologyRestrictedProductPrincipal`: every principal stage
  `Πʳ i, [R i, A i]_[𝓟 S]` over a countable index type with second-countable factors is second
  countable.
* `TauCeti.secondCountableTopology_restrictedProduct`: `Πʳ i, [R i, A i]` is second countable when
  `ι` is countable, each `R i` is second countable, and each `A i` is open.
* `TauCeti.instSecondCountableTopologyRestrictedProduct`: the corresponding typeclass instance
  given `[Fact (∀ i, IsOpen (A i))]`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace TauCeti

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
variable [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]

/-- Every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` over a countable index type with
second-countable factors is second countable, as it embeds into the product `Π i, R i`. -/
instance instSecondCountableTopologyRestrictedProductPrincipal {S : Set ι} :
    SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 S]) :=
  RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology

/-- A restricted product over the cofinite filter on a countable index type is second countable
when each factor is second countable and each reference set is open. -/
theorem secondCountableTopology_restrictedProduct (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  have hle (T : Finset ι) : (cofinite : Filter ι) ≤ 𝓟 (T : Set ι)ᶜ :=
    le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite
  let U (T : Finset ι) : Set (Πʳ i, [R i, A i]) :=
    range (RestrictedProduct.inclusion R A (hle T))
  have hopen (T : Finset ι) : IsOpen (U T) :=
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hle T)).isOpen_range
  have hsc (T : Finset ι) : SecondCountableTopology (U T) :=
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hle T)).toHomeomorph.symm
      |>.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) hopen ?_
  refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ?_
  have hfin : {i | x i ∉ A i}.Finite := mem_cofinite.mp x.2
  refine ⟨hfin.toFinset, ⟨x, eventually_principal.mpr fun i hi ↦ ?_⟩, rfl⟩
  by_contra hxi
  exact hi (hfin.mem_toFinset.mpr hxi)

/-- Typeclass instance for second countability of a restricted product over the cofinite filter
when `[Fact (∀ i, IsOpen (A i))]` is available. -/
instance instSecondCountableTopologyRestrictedProduct [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_restrictedProduct hA.out

end TauCeti
