/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.TraceShortExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence

/-!
# The image of corestriction

Let `U` be an open subgroup of a profinite group `G` and `M` a discrete `G`-module. Corestriction
`cor : Hⁿ(U, M) ⟶ Hⁿ(G, M)` is the inverse of Shapiro's isomorphism
`Hⁿ(G, Coind_U^G M) ≅ Hⁿ(U, M)` followed by the coefficient map of the trace `Coind_U^G M → M`.
The trace is the surjection of the trace short exact sequence

```text
0 → traceKer G U M → Coind_U^G M → M → 0
```

(`TauCeti.DiscreteCoind.traceShortExact`), so its long exact sequence describes the image of
corestriction: the sequence

```text
Hⁿ(U, M) --cor--> Hⁿ(G, M) --δ--> Hⁿ⁺¹(G, traceKer G U M)
```

is exact. A class of `Hⁿ(G, M)` is therefore a corestriction exactly when its connecting image
vanishes. This is the first step of the proof that, for a group of strict cohomological
dimension `n`, corestriction onto the `p`-primary part of `Hⁿ` is surjective (NSW (3.3.11)).

## Main results

* `TauCeti.ContinuousCohomology.exact_corestriction_delta`: corestriction followed by the
  connecting map of the trace short exact sequence is exact.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.4) and the
  proof of (3.3.11).
-/

public section

namespace TauCeti.ContinuousCohomology

open CategoryTheory TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (U : Subgroup G) [U.FiniteIndex] (M : Type u) [AddCommGroup M]
  [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G))

/-- **The image of corestriction is the kernel of the trace connecting map.** For an open subgroup
`U` of a profinite group `G` and a discrete `G`-module `M`, the sequence
`Hⁿ(U, M) ⟶ Hⁿ(G, M) ⟶ Hⁿ⁺¹(G, traceKer G U M)` formed by corestriction and the connecting map of
the trace short exact sequence `0 → traceKer G U M → Coind_U^G M → M → 0` is exact. -/
theorem exact_corestriction_delta (n : ℕ) :
    Function.Exact (corestriction U M hU n) ((DiscreteCoind.traceShortExact G U M hU).delta n) := by
  intro x
  rw [(DiscreteCoind.traceShortExact G U M hU).longExact_exact₃ n x]
  -- the second map of the trace short exact sequence is the trace
  have hτ : ofDiscreteModuleMap (DiscreteCoind.traceShortExact G U M hU).proj.toIntLinearMap
        (DiscreteCoind.traceShortExact G U M hU).proj_equivariant =
      ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f := by
    simp only [DiscreteCoind.traceShortExact_proj]
  rw [hτ]
  -- the coefficient map of the trace and corestriction differ by the Shapiro isomorphism
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨shapiroMap U M n z,
      ConcreteCategory.congr_hom (shapiroMap_comp_corestriction U M hU n) z⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(shapiroIso U (U.isClosed_of_isOpen hU) M n).inv y,
      (ConcreteCategory.congr_hom (corestriction_def U M hU n) y).symm⟩

end TauCeti.ContinuousCohomology
