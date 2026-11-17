/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Logic.Equiv.List

/-!
# Second countability of restricted products

For a countable index type `ι` and second-countable spaces `R i`, every principal stage
`Πʳ i, [R i, A i]_[𝓟 S]` embeds into `Π i, R i` and is therefore second countable. When each `A i`
is open, `Πʳ i, [R i, A i]` is covered by the countably many open ranges of the principal
inclusions indexed by `T : Finset ι`, so it is also second countable.

## Main declarations

* `RestrictedProduct.instSecondCountableTopologyOfPrincipal`,
  `RestrictedProduct.instSecondCountableTopologyOfTop`,
  `RestrictedProduct.instSecondCountableTopologyOfBot`: second countability of principal, top, and
  bottom stages.
* `RestrictedProduct.secondCountableTopology_of_cofinite`,
  `RestrictedProduct.instSecondCountableTopology`: second countability of `Πʳ i, [R i, A i]` when
  each `A i` is open.

## References

* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), Lemma 3.63, pp. 188–189.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
variable [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]

/-- Every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` of a countable family of second-countable
spaces is second countable. -/
instance instSecondCountableTopologyOfPrincipal {S : Set ι} :
    SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 S]) :=
  isEmbedding_coe_of_principal.secondCountableTopology

/-- The everywhere-restricted stage `Πʳ i, [R i, A i]_[⊤]` of a countable family of
second-countable spaces is second countable. -/
instance instSecondCountableTopologyOfTop :
    SecondCountableTopology (Πʳ i, [R i, A i]_[⊤]) :=
  isEmbedding_coe_of_top.secondCountableTopology

/-- The unrestricted stage `Πʳ i, [R i, A i]_[⊥]` of a countable family of second-countable spaces
is second countable. -/
instance instSecondCountableTopologyOfBot :
    SecondCountableTopology (Πʳ i, [R i, A i]_[⊥]) :=
  isEmbedding_coe_of_bot.secondCountableTopology

/-- If `ι` is countable, each `R i` is second countable, and each reference set `A i` is open, then
the cofinite restricted product `Πʳ i, [R i, A i]` is second countable. -/
theorem secondCountableTopology_of_cofinite (hAopen : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  have hT (T : Finset ι) : (cofinite : Filter ι) ≤ 𝓟 (T : Set ι)ᶜ :=
    le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite
  have hU_sc (T : Finset ι) : SecondCountableTopology (range (inclusion R A (hT T))) :=
    (isOpenEmbedding_inclusion_principal hAopen (hT T)).isEmbedding.toHomeomorph.symm
      |>.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T : Finset ι ↦ (isOpenEmbedding_inclusion_principal hAopen (hT T)).isOpen_range) ?_
  refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ⟨(mem_cofinite.mp x.eventually).toFinset, ?_⟩
  exact exists_inclusion_eq_of_eventually R A _
    (eventually_principal.mpr fun i hi ↦ by simpa [Set.Finite.mem_toFinset] using hi)

/-- A cofinite restricted product of countably many second-countable spaces relative to open
reference sets is second countable. -/
instance instSecondCountableTopology [hAopen : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_of_cofinite hAopen.out

end RestrictedProduct
