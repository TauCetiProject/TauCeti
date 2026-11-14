/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius

/-!
# Character maps of half-Frobenius maps on simply connected points

For a Suzuki--Ree index `d`, the exceptional isogeny `τ` of the simply connected Chevalley group
of the underlying Dynkin type is pinned by its values on the positive and negative simple root
subgroups,

```text
τ (x_{±αᵢ}(u)) = x_{±α_{σ i}}(cᵢ^{±1} u ^ eᵢ),
```

where `σ` is the length permutation `TauCeti.SuzukiReeIndex.lengthPerm`, the exponent
`eᵢ = TauCeti.SuzukiReeIndex.exponent i` is `1` at a long node and the defining characteristic at a
short one, and the units `cᵢ` are signs. This file proves that every endomorphism of the points
of `G_sc(t)` with these simple-root values pulls characters of the whole torus back by the weight
map of the independently defined root-datum isogeny
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny`, and that its `2m + 1`-st power, the Steinberg map of
the index, pulls them back by the weight map of `TauCeti.SuzukiReeIndex.datumSteinberg`.

The value ring is any commutative ring of the defining exponential characteristic, in particular
the algebraic closure `TauCeti.ValidLieTypeIndex.Closure` of the index. The construction of `τ`
itself is not addressed here: these statements reduce its character compatibility to its pinned
simple-root equations, through the generic computation
`TauCeti.DynkinType.isCharacterMap_scChevalleyDatum_of_rootSubgroupPoints` and the coordinate form
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny_weightMap_apply` of the root-datum isogeny.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3–12.4.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.SuzukiReeIndex

open DynkinType

universe v

variable (d : SuzukiReeIndex) {A : Type v} [CommRing A] [ExpChar A d.1.characteristic]

/-- **Character compatibility of the exceptional isogeny.** An endomorphism of the points of the
simply connected Chevalley group of a Suzuki--Ree index which sends `x_{±αᵢ}(u)` to
`x_{±α_{σ i}}(cᵢ^{±1} u ^ eᵢ)`, for the length permutation `σ` and the exponents `eᵢ` of the index,
pulls characters of the torus back by the weight map of the root-datum special isogeny. -/
theorem isCharacterMap_datumSpecialIsogeny_of_rootSubgroupPoints
    (τ : (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).points A →*
      (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).points A)
    (c : Fin d.1.rank → Aˣ)
    (hpos : ∀ i (u : A),
      τ ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) A (Multiplicative.ofAdd u)) =
        (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.lengthPerm i)) A
          (Multiplicative.ofAdd (c i * u ^ d.exponent i)))
    (hneg : ∀ i (u : A),
      τ ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)) A (Multiplicative.ofAdd u)) =
        (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.lengthPerm i))
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.lengthPerm i))) A
          (Multiplicative.ofAdd (((c i)⁻¹ : Aˣ) * u ^ d.exponent i))) :
    IsCharacterMap ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).torusPoints A) τ
      d.datumSpecialIsogeny.weightMap :=
  isCharacterMap_scChevalleyDatum_of_rootSubgroupPoints τ d.lengthPerm c d.exponent
    d.neg_one_pow_exponent hpos hneg _ d.datumSpecialIsogeny_weightMap_apply

/-- **Character compatibility of the Suzuki--Ree Steinberg map.** For an endomorphism with the
pinned simple-root values of the exceptional isogeny, its power with the index's odd field
exponent `2m + 1` pulls characters of the torus back by the weight map of the root-datum
Steinberg map of the index. -/
theorem isCharacterMap_datumSteinberg_of_rootSubgroupPoints
    (τ : Monoid.End ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).points A))
    (c : Fin d.1.rank → Aˣ)
    (hpos : ∀ i (u : A),
      τ ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) A (Multiplicative.ofAdd u)) =
        (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.lengthPerm i)) A
          (Multiplicative.ofAdd (c i * u ^ d.exponent i)))
    (hneg : ∀ i (u : A),
      τ ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)) A (Multiplicative.ofAdd u)) =
        (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).rootSubgroupPoints
          ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.lengthPerm i))
            (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.lengthPerm i))) A
          (Multiplicative.ofAdd (((c i)⁻¹ : Aˣ) * u ^ d.exponent i))) :
    IsCharacterMap ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).torusPoints A)
      (τ ^ d.1.fieldExponent) d.datumSteinberg.weightMap := by
  rw [datumSteinberg_weightMap_eq_pow]
  exact (d.isCharacterMap_datumSpecialIsogeny_of_rootSubgroupPoints τ c hpos hneg).pow
    d.1.fieldExponent

end TauCeti.SuzukiReeIndex
