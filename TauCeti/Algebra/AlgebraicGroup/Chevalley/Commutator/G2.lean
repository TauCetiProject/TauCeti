/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortLong
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortPair

/-!
# The Chevalley commutator formula in type `G₂`

For a Chevalley datum `D` of type `G₂` and a commutative ring `A`, this file records Chevalley's
commutator formula

```text
⁅x_α(u), x_β(v)⁆ = x_α(u) x_β(v) x_α(u)⁻¹ x_β(v)⁻¹ = ∏ x_{iα+jβ}(c_{ij} uⁱ vʲ),
```

the product over the roots `iα + jβ` with `i, j > 0` in increasing `i + j`, on the points of `D`
for the pairs of roots not already covered by
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.Basic`. The coefficients are integers built
from the structure constants `N_{α,β}` of the pinned Chevalley system, with the divisions by two
and three performed in `ℤ`, so the formulas hold over every commutative ring, including rings of
characteristic two and three.

* If `α + β` is a long root, `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v)`.
* If `α`, `β` and `α + β` are short, the other roots `iα + jβ` are `2α + β` and `α + 2β`, both
  long, and the commutator has three factors.
* If `α` is short, `β` is long and `α + β` is a root, the roots `iα + jβ` are `α + β`, `2α + β`,
  `3α + β` and `3α + 2β`, and the commutator has four factors. The commutator with the long root
  first has the same four factors with other coefficients; its coefficient of `x_{3α+2β}` is half
  the one with the short root first.

Together with the commuting and one-factor cases of
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.Basic`, these give the commutator formula for
every pair of roots `α ≠ -β` of `G₂`. They are the identities
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_G2_of_long_sum`,
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_short_pair`,
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_short_long` and
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_long_short` on the lattice of
`D`, written in its weight basis.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_G2_of_long_sum`: the
  one-factor formula when `α + β` is long.
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_g2_short_pair`: the
  three-factor formula for two short roots with short sum.
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_g2_short_long`: the
  four-factor formula with the short root first.
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_g2_long_short`: the
  four-factor formula with the long root first.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2. The commutator convention here is
  `x y x⁻¹ y⁻¹`, not Carter's `x⁻¹ y⁻¹ x y`.
-/

public section

open scoped commutatorElement

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {ht : G2.Valid} (D : ChevalleyDatum G2 ht)

/-- **The `G₂` commutator formula with a long sum.** If `γ = α + β` is a long root, then
`⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v)` in the points of a `G₂` datum over every commutative
ring. -/
theorem commutatorElement_rootSubgroup_G2_of_long_sum {α β γ : Fin G2.numRoots}
    (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A
        (Multiplicative.ofAdd ((G2.structureConstant ht α β : A) * (u * v))) := by
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, commutatorElement_chevalleyRootSubgroup_G2_of_long_sum
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator hγ hadd (CommAlgCat.of ℤ A) u v]

/-- **The `G₂` short-pair commutator formula.** Let `i`, `j` be short roots whose sum `k` is
short, and let `l = 2i + j` and `m = i + 2j`. Then in the points of a `G₂` datum over every
commutative ring

```text
⁅x_i(u), x_j(v)⁆ = x_k(2c u v) x_l(3d u² v) x_m(-3a u v²),
```

where `c = N_{i,j} / 2`, `d = c (N_{i,k} / 3)` and `a = c (N_{k,j} / 3)`; the divisions are exact
in `ℤ`. -/
theorem commutatorElement_rootSubgroup_of_g2_short_pair {i j k l m : Fin G2.numRoots}
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints i A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints j A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints k A
          (Multiplicative.ofAdd (((G2.structureConstant ht i j / 2 : ℤ) : A) * (2 * u * v))) *
        D.rootSubgroupPoints l A
          (Multiplicative.ofAdd
            (((G2.structureConstant ht i j / 2 * (G2.structureConstant ht i k / 3) : ℤ) : A) *
              (3 * u ^ 2 * v))) *
        D.rootSubgroupPoints m A
          (Multiplicative.ofAdd
            (-((G2.structureConstant ht i j / 2 * (G2.structureConstant ht k j / 3) : ℤ) : A) *
              (3 * u * v ^ 2))) := by
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, ← map_mul, ← map_mul,
    commutatorElement_chevalleyRootSubgroup_of_g2_short_pair D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hi hj hk hij hik hkj
      (CommAlgCat.of ℤ A) u v]

/-- **The `G₂` commutator formula, short root first.** Let `α` be short and `β` long, with
`γ = α + β`, `δ = 2α + β`, `ε = 3α + β` and `ζ = 3α + 2β` roots. Then in the points of a `G₂`
datum over every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(c u v) x_δ(d u² v) x_ε(a u³ v) x_ζ(2b u³ v²),
```

where `c = N_{α,β}`, `d = c (N_{α,γ} / 2)`, `a = d (N_{α,δ} / 3)` and `b = d c (N_{δ,γ} / 3)`;
the divisions are exact in `ℤ`. -/
theorem commutatorElement_rootSubgroup_of_g2_short_long {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A
          (Multiplicative.ofAdd ((G2.structureConstant ht α β : A) * (u * v))) *
        D.rootSubgroupPoints δ A
          (Multiplicative.ofAdd
            (((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) : ℤ) : A) *
              (u ^ 2 * v))) *
        D.rootSubgroupPoints ε A
          (Multiplicative.ofAdd
            (((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
                (G2.structureConstant ht α δ / 3) : ℤ) : A) * (u ^ 3 * v))) *
        D.rootSubgroupPoints ζ A
          (Multiplicative.ofAdd
            (((2 * (G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
                G2.structureConstant ht α β * (G2.structureConstant ht δ γ / 3)) : ℤ) : A) *
              (u ^ 3 * v ^ 2))) := by
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, ← map_mul, ← map_mul, ← map_mul,
    commutatorElement_chevalleyRootSubgroup_of_g2_short_long D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hγ hδ hε hζ
      (CommAlgCat.of ℤ A) u v]

/-- **The `G₂` commutator formula, long root first.** Let `α` be short and `β` long, with
`γ = α + β`, `δ = 2α + β`, `ε = 3α + β` and `ζ = 3α + 2β` roots. Then in the points of a `G₂`
datum over every commutative ring

```text
⁅x_β(v), x_α(u)⁆ = x_γ(-c u v) x_δ(-d u² v) x_ε(-a u³ v) x_ζ(b u³ v²),
```

with `c`, `d`, `a` and `b` as in `commutatorElement_rootSubgroup_of_g2_short_long`. -/
theorem commutatorElement_rootSubgroup_of_g2_long_short {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints β A (Multiplicative.ofAdd v),
        D.rootSubgroupPoints α A (Multiplicative.ofAdd u)⁆ =
      D.rootSubgroupPoints γ A
          (Multiplicative.ofAdd (-(G2.structureConstant ht α β : A) * (u * v))) *
        D.rootSubgroupPoints δ A
          (Multiplicative.ofAdd
            (-((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) : ℤ) : A) *
              (u ^ 2 * v))) *
        D.rootSubgroupPoints ε A
          (Multiplicative.ofAdd
            (-((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
                (G2.structureConstant ht α δ / 3) : ℤ) : A) * (u ^ 3 * v))) *
        D.rootSubgroupPoints ζ A
          (Multiplicative.ofAdd
            (((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
                G2.structureConstant ht α β * (G2.structureConstant ht δ γ / 3) : ℤ) : A) *
              (u ^ 3 * v ^ 2))) := by
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, ← map_mul, ← map_mul, ← map_mul,
    commutatorElement_chevalleyRootSubgroup_of_g2_long_short D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hγ hδ hε hζ
      (CommAlgCat.of ℤ A) u v]

end TauCeti.DynkinType.ChevalleyDatum
