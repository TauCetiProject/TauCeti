/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees

/-!
# Corestriction and the connecting maps of continuous cohomology

Let `0 → A → B → C → 0` be a short exact sequence of discrete `G`-modules over a profinite group
`G`, and `U` an open subgroup of finite index. Restricting the sequence to `U` gives a short exact
sequence of discrete `U`-modules, and corestriction `Hⁿ(U, -) ⟶ Hⁿ(G, -)` commutes with the
connecting maps of the two long exact sequences, in every degree:

```text
Hⁿ(U, C) ---δ---> Hⁿ⁺¹(U, A)
   |                  |
  cor                cor
   v                  v
Hⁿ(G, C) ---δ---> Hⁿ⁺¹(G, A)
```

This is Neukirch–Schmidt–Wingberg (1.5.2) in every degree; in degrees `0` and `1` it is the
explicit statement `TauCeti.ContCohomology.DiscreteShortExact.explicitCor_delta0` and
`explicitCor_delta1` on inhomogeneous cochains.

Corestriction here is the all-degree map of `Corestriction/AllDegrees.lean`, built through the
coinduced module `Coind_U^G M` and its trace (Brown, Chapter III, §9), and the statement is the
counterpart for corestriction of `Inflation/ConnectingMap.lean`.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.delta_corestriction`: **corestriction commutes with
  the connecting map** in every degree, as morphisms of `TopModuleCat ℤ`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_corestriction_apply`: the same identity on
  classes, `cor (δ x) = δ (cor x)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.5.2) and (1.6.4).
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9, the coinduced-module construction of the
  transfer.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology.DiscreteShortExact

open TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  [ContinuousSMul G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C) (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-! ### Corestriction commutes with the connecting maps -/

/-- **Corestriction commutes with the connecting map** (NSW (1.5.2)) in every degree: for an open
finite-index subgroup `U` of a profinite group `G` and a short exact sequence `S` of discrete
`G`-modules, the connecting map of `S` restricted to `U`, followed by corestriction, is
corestriction followed by the connecting map of `S`:

```text
Hⁿ(U, C) ---δ---> Hⁿ⁺¹(U, A)
   |                  |
  cor                cor
   v                  v
Hⁿ(G, C) ---δ---> Hⁿ⁺¹(G, A)
```

The connecting map of `U` needs `U` compact, which follows from its openness in the compact
group `G`. -/
@[reassoc]
theorem delta_corestriction (n : ℕ) :
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
    (S.restrict U).delta n ≫ corestriction U A hU (n + 1) =
      corestriction U C hU n ≫ S.delta n := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  have hU' := U.isClosed_of_isOpen hU
  -- Cancel the Shapiro isomorphism of `C` on the left. The connecting map of `S.restrict U`
  -- then becomes that of the coinduced sequence (`delta_shapiroMap`), and the Shapiro map followed
  -- by corestriction is the coefficient map of the trace on both sides, leaving the naturality of
  -- the connecting map in the morphism of short exact sequences given by the traces.
  have := isIso_shapiroMap U hU' C n
  rw [← cancel_epi (shapiroMap U C n), ← delta_shapiroMap_assoc, shapiroMap_comp_corestriction,
    shapiroMap_comp_corestriction_assoc]
  -- The traces commute with the coinduced inclusion and projection: both sides are the finite sum
  -- `∑ g • S.incl (a g⁻¹)` (resp. with `S.proj`), the maps of `S` being additive and equivariant.
  exact (coind U hU' (S.restrict U)).delta_naturality S (DiscreteCoind.trace G U A)
    (DiscreteCoind.trace G U B) (DiscreteCoind.trace G U C)
    (fun a => by
      simp only [DiscreteCoind.trace_apply, map_sum, coind_incl_apply, restrict_incl,
        S.incl_equivariant])
    (fun b => by
      simp only [DiscreteCoind.trace_apply, map_sum, coind_proj_apply, restrict_proj,
        S.proj_equivariant]) n

/-- **`cor (δ x) = δ (cor x)`** for every class `x ∈ Hⁿ(U, C)` (NSW (1.5.2)): corestriction
commutes with the connecting maps in every degree. -/
@[simp]
theorem delta_corestriction_apply (n : ℕ)
    (x : continuousCohomology n (ofDiscreteModule ℤ U C)) :
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
    corestriction U A hU (n + 1) ((S.restrict U).delta n x) =
      S.delta n (corestriction U C hU n x) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  rw [← ConcreteCategory.comp_apply, S.delta_corestriction U hU n, ConcreteCategory.comp_apply]

end TauCeti.ContCohomology.DiscreteShortExact
