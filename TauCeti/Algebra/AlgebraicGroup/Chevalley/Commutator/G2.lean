/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortPair
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortLong

/-!
# The Chevalley commutator formula for Chevalley data of type `G₂`

For a Chevalley datum `D` of type `G₂` and a commutative ring `A`, the root subgroups `x_α` of
`D.points A` satisfy Chevalley's commutator formula

```text
⁅x_α(u), x_β(v)⁆ = x_α(u) x_β(v) x_α(u)⁻¹ x_β(v)⁻¹ = ∏ x_{iα+jβ}(c_{ij} uⁱ vʲ),
```

the product over the roots `iα + jβ` with `i, j > 0` in increasing `i + j`. Besides the commuting
case `ChevalleyDatum.commute_rootSubgroup`, a pair of roots `α ≠ -β` of `G₂` whose sum is a root
falls under exactly one of the following configurations, recorded here on the points of `D`:

* the sum `α + β` is long: one factor, `x_{α+β}(N_{α,β} u v)`;
* `α`, `β` and `α + β` are short: three factors, at `α + β`, `2α + β` and `α + 2β`;
* `α` is short and `β` is long: four factors, at `α + β`, `2α + β`, `3α + β` and `3α + 2β`;
* `α` is long and `β` is short: four factors, at `α + β`, `α + 2β`, `α + 3β` and `2α + 3β`.

Together with `TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.Basic`, this gives the
commutator formula for every pair of linearly independent roots in every valid type. All
coefficients are integers computed from the structure constants `N_{α,β}` of the pinned Chevalley
system, with the divisions by two and three exact in `ℤ`, so the formulas hold over every
commutative ring, including rings of characteristic two and three.

The formulas are the lattice identities
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_G2_of_long_sum`,
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_short_pair`,
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_short_long` and
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_g2_long_short` on the admissible
lattice of `D`, written in its weight basis.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_G2_of_long_sum`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_g2_short_pair`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_g2_short_long`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_g2_long_short`

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

/-- **The `G₂` commutator formula for a long sum.** If `γ = α + β` is a long root, then
`⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v)` in the points of `D` over every commutative ring. -/
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

/-- **The `G₂` commutator formula for a short pair.** If `α`, `β` and `γ = α + β` are short
roots, and `δ = α + γ`, `ε = γ + β`, then in the points of `D` over every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(2c u v) x_δ(3d u² v) x_ε(-3a u v²),
```

with `c = N_{α,β} / 2`, `d = c N_{α,γ} / 3` and `a = c N_{γ,β} / 3`, exact divisions in `ℤ`. -/
theorem commutatorElement_rootSubgroup_of_g2_short_pair {α β γ δ ε : Fin G2.numRoots}
    (hα : g2Length α = 1) (hβ : g2Length β = 1) (hγ : g2Length γ = 1)
    (hαβ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hαγ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hγβ : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root γ + (G2.simplyConnectedRootDatum ht).root β)
    (A : Type v) [CommRing A] (u v : A) :
    let c := G2.structureConstant ht α β / 2
    let d := c * (G2.structureConstant ht α γ / 3)
    let a := c * (G2.structureConstant ht γ β / 3)
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A (Multiplicative.ofAdd ((c : A) * (2 * u * v))) *
        D.rootSubgroupPoints δ A (Multiplicative.ofAdd ((d : A) * (3 * u ^ 2 * v))) *
        D.rootSubgroupPoints ε A (Multiplicative.ofAdd (-(a : A) * (3 * u * v ^ 2))) := by
  have h := commutatorElement_chevalleyRootSubgroup_of_g2_short_pair D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hα hβ hγ hαβ hαγ
    hγβ (CommAlgCat.of ℤ A) u v
  intro c d a
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, h, map_mul, map_mul]

/-- **The short–long `G₂` commutator formula.** For a short root `α` and a long root `β` with
`γ = α + β`, `δ = α + γ = 2α + β`, `ε = α + δ = 3α + β` and `ζ = δ + γ = 3α + 2β` roots, in the
points of `D` over every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(c u v) x_δ(d u² v) x_ε(a u³ v) x_ζ(2b u³ v²),
```

with `c = N_{α,β}`, `d = c (N_{α,γ} / 2)`, `a = d (N_{α,δ} / 3)` and `b = d c (N_{δ,γ} / 3)`,
exact divisions in `ℤ`. -/
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
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A (Multiplicative.ofAdd ((c : A) * (u * v))) *
        D.rootSubgroupPoints δ A (Multiplicative.ofAdd ((d : A) * (u ^ 2 * v))) *
        D.rootSubgroupPoints ε A (Multiplicative.ofAdd ((a : A) * (u ^ 3 * v))) *
        D.rootSubgroupPoints ζ A (Multiplicative.ofAdd (((2 * b : ℤ) : A) * (u ^ 3 * v ^ 2))) := by
  have h := commutatorElement_chevalleyRootSubgroup_of_g2_short_long D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hγ hδ hε hζ
    (CommAlgCat.of ℤ A) u v
  intro N c d a b
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, h, map_mul, map_mul, map_mul]

/-- **The long–short `G₂` commutator formula.** For a short root `α` and a long root `β` with
`γ = α + β`, `δ = α + γ = 2α + β`, `ε = α + δ = 3α + β` and `ζ = δ + γ = 3α + 2β` roots, in the
points of `D` over every commutative ring

```text
⁅x_β(v), x_α(u)⁆ = x_γ(-c u v) x_δ(-d u² v) x_ε(-a u³ v) x_ζ(b u³ v²),
```

with `c`, `d`, `a`, `b` as in `commutatorElement_rootSubgroup_of_g2_short_long`. The factors are
in increasing total degree, now with the long root `β` first. -/
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
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    ⁅D.rootSubgroupPoints β A (Multiplicative.ofAdd v),
        D.rootSubgroupPoints α A (Multiplicative.ofAdd u)⁆ =
      D.rootSubgroupPoints γ A (Multiplicative.ofAdd ((-c : A) * (u * v))) *
        D.rootSubgroupPoints δ A (Multiplicative.ofAdd ((-d : A) * (u ^ 2 * v))) *
        D.rootSubgroupPoints ε A (Multiplicative.ofAdd ((-a : A) * (u ^ 3 * v))) *
        D.rootSubgroupPoints ζ A (Multiplicative.ofAdd ((b : A) * (u ^ 3 * v ^ 2))) := by
  have h := commutatorElement_chevalleyRootSubgroup_of_g2_long_short D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hγ hδ hε hζ
    (CommAlgCat.of ℤ A) u v
  intro N c d a b
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, h, map_mul, map_mul, map_mul]

end TauCeti.DynkinType.ChevalleyDatum
