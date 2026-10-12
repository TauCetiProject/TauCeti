/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison

/-!
# Inflation and the connecting maps of continuous cohomology

Let `0 → A → B → C → 0` be a short exact sequence of discrete `G`-modules over a compact group
`G`, and `N` a normal subgroup. Taking `N`-invariants gives a sequence
`0 → A ^ N → B ^ N → C ^ N → 0` of discrete `G ⧸ N`-modules which is left exact but in general not
exact on the right: the obstruction is `H¹(N, A)`. When it *is* short exact, inflation along
`G → G ⧸ N` commutes with the connecting maps of the two long exact sequences, in every degree:

```text
Hⁿ(G ⧸ N, C ^ N) ---δ---> Hⁿ⁺¹(G ⧸ N, A ^ N)
       |                          |
      inf                        inf
       v                          v
   Hⁿ(G, C) -------δ------> Hⁿ⁺¹(G, A)
```

The short exact sequence of invariants is therefore a hypothesis, `SN`, together with the
compatibility of its maps with those of the sequence over `G`. Inflation is Mathlib's
compatible-pair map read through the coefficient dictionary
(`TauCeti.ContCohomology.coeffMap_ofDiscreteModuleQuotient_comp_infl`), so the square is an
instance of the naturality of the connecting map in compatible pairs,
`TauCeti.ContCohomology.DiscreteShortExact.delta_map`.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.delta_infl`: inflation commutes with the connecting
  map in every degree.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.3.2) and Ch. I, §5.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology.DiscreteShortExact

open _root_.TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- **Inflation commutes with the connecting map.** For a normal subgroup `N` of `G`, let `SN` be a
short exact sequence of the `N`-invariants `A ^ N → B ^ N → C ^ N` whose maps are the
restrictions of those of `S`. Then inflation along `G → G ⧸ N`, read through the coefficient
dictionary `TauCeti.ofDiscreteModuleQuotient`, carries the connecting map of `SN` to that of `S`
in every degree. -/
@[reassoc]
theorem delta_infl (N : Subgroup G) [N.Normal]
    (SN : DiscreteShortExact (G ⧸ N) (FixedPoints.addSubgroup N A)
      (FixedPoints.addSubgroup N B) (FixedPoints.addSubgroup N C))
    (hincl : ∀ a, (SN.incl a : B) = S.incl a) (hproj : ∀ b, (SN.proj b : C) = S.proj b)
    (n : ℕ) :
    SN.delta n ≫ coeffMap (ofDiscreteModuleQuotient G A N) (n + 1) ≫
        infl N (ofDiscreteModule ℤ G A) (n + 1) =
      coeffMap (ofDiscreteModuleQuotient G C N) n ≫ infl N (ofDiscreteModule ℤ G C) n ≫
        S.delta n := by
  rw [coeffMap_ofDiscreteModuleQuotient_comp_infl,
    coeffMap_ofDiscreteModuleQuotient_comp_infl_assoc]
  exact SN.delta_map S (ContinuousMonoidHom.quotientMk N) (FixedPoints.addSubgroup N A).subtype
    (FixedPoints.addSubgroup N B).subtype (FixedPoints.addSubgroup N C).subtype
    (subtype_quotientMk_smul G A N) (subtype_quotientMk_smul G B N)
    (subtype_quotientMk_smul G C N) hincl hproj n

end TauCeti.ContCohomology.DiscreteShortExact
