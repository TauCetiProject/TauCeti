/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB2

/-!
# The Steinberg endomorphism of the Suzuki family

The Steinberg endomorphism of `²B₂(2^(2m+1))` is not a Frobenius but an odd power of a
half-Frobenius: the exceptional isogeny `τ` of the ambient group, which squares to the prime-field
Frobenius, raised to the odd exponent `2m+1`. This file forms that map on the ambient group of a
Suzuki index and proves the relation the CFSG roadmap requires of it,

```text
steinberg (m) ^ 2 = Frob_(2 ^ (2m+1)).
```

The half-Frobenius is available because the ambient group of a Suzuki index is the rank-two
type-`C` carrier over an algebraically closed field of characteristic two, and that carrier already
carries the special isogeny. So nothing is constructed here: the half-Frobenius *is* that isogeny,
and the work is the odd power and its square.

The exponent is not a new parameter. `TauCeti.ValidLieTypeIndex.fieldExponent` already writes the
field order of an index as a power of its characteristic, and on a Suzuki index it is the odd
number `2m+1`, so the Steinberg map is the `fieldExponent`-th power throughout and squaring it
lands on the `q`-power Frobenius `TauCeti.RankTwoBLieIndex.frobenius` that the index records rather
than on a separately tabulated field order.

## The pinning

Milestone `L2` fixes the exponent convention: `1` on a long simple root and the defining
characteristic on a short one. On the `B₂` diagram the long simple root is the one whose carrier
node is the final one, and the two equations below are that convention. They are stated at the
carrier nodes rather than through `TauCeti.SuzukiReeIndex.lengthPerm` and
`TauCeti.SuzukiReeIndex.exponent`; identifying those two with the equations here is the numbering
bookkeeping that remains of `L2` for this branch.

## Main definitions

* `TauCeti.SuzukiLieIndex.halfFrobenius`: the special isogeny of the ambient group.
* `TauCeti.SuzukiLieIndex.steinberg`: its odd power `τ ^ (2m+1)`.
* `TauCeti.SuzukiLieIndex.Group`: the candidate simple group of milestone `L3`.

## Main results

* `TauCeti.SuzukiLieIndex.halfFrobenius_halfFrobenius`: the half-Frobenius squares to the
  prime-field Frobenius.
* `TauCeti.SuzukiLieIndex.halfFrobenius_simpleRootSubgroup_long` and
  `TauCeti.SuzukiLieIndex.halfFrobenius_simpleRootSubgroup_short`: the pinning equations, with
  exponent one on the long simple root subgroup and two on the short one.
* `TauCeti.SuzukiLieIndex.steinberg_steinberg`: the square of the Steinberg endomorphism is the
  `q`-power Frobenius.

## The candidate group

With the Steinberg map in hand the milestone `L3` recipe runs on this branch:
`TauCeti.SuzukiLieIndex.Group` is the derived subgroup of its fixed points modulo the centre of
that derived subgroup, and it carries a group instance.

## What is not here

Nothing is proved finite, perfect or simple, the carrier is not claimed to be the pinned one
milestone `L0` asks for, and Mathlib's separate `suzukiGroup` is not mentioned: relating the two is
milestone `L4`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ^ 2 = Frob_p` and
  its odd powers.

## Roadmap

This advances milestone `L2`, "Suzuki--Ree Steinberg maps", of
`TauCetiRoadmap/CFSGStatement/README.md`, on the Suzuki branch: that milestone owns "everything
between that isogeny and a finite group", namely selecting the isogeny for a given index, checking
that it is the one the roadmap's conventions describe, and taking the odd power. The isogeny itself
is Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` and is consumed rather than built here.
The `²G₂` and `²F₄` branches, whose carriers need the characteristic-three and characteristic-two
special isogenies of `G₂` and `F₄`, are untouched.
-/
public section

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

/-- The algebraic closure attached to a Suzuki index has characteristic two. -/
instance charP_closure_two : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

/-- **The half-Frobenius of a Suzuki index**: the special isogeny of its ambient group. -/
noncomputable def halfFrobenius :
    d.toRankTwoBLieIndex.AmbientGroup →* d.toRankTwoBLieIndex.AmbientGroup :=
  SpStd.specialIsogeny d.1.Closure

/-- The half-Frobenius is the carrier's special isogeny. -/
theorem halfFrobenius_def :
    d.halfFrobenius = SpStd.specialIsogeny d.1.Closure :=
  (rfl)

/-- **The half-Frobenius squares to the prime-field Frobenius.** -/
theorem halfFrobenius_halfFrobenius (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = SpStd.frobenius 1 2 1 d.1.Closure g := by
  rw [halfFrobenius_def, SpStd.specialIsogeny_specialIsogeny]

/-- The half-Frobenius as an element of the endomorphism monoid, where composition is the
multiplication its odd powers are taken in. -/
noncomputable def halfFrobeniusEnd : Monoid.End d.toRankTwoBLieIndex.AmbientGroup :=
  d.halfFrobenius

@[simp]
theorem halfFrobeniusEnd_apply (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.halfFrobeniusEnd g = d.halfFrobenius g :=
  (rfl)

private theorem halfFrobenius_iterate_two_mul (k : ℕ) (g : d.toRankTwoBLieIndex.AmbientGroup) :
    (⇑d.halfFrobenius)^[2 * k] g =
      SpStd.frobenius 1 (d.toRankTwoBLieIndex.1).characteristic k
        (d.toRankTwoBLieIndex.1).Closure g := by
  have hchar : (d.toRankTwoBLieIndex.1).characteristic = 2 := d.characteristic_eq_two
  induction k generalizing g with
  | zero =>
      apply Subtype.ext
      apply Units.ext
      ext a b
      rw [Nat.mul_zero, Function.iterate_zero_apply, SpStd.coe_frobenius_apply]
      simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, Function.iterate_add_apply, ih]
      change d.halfFrobenius (d.halfFrobenius _) = _
      rw [halfFrobenius_halfFrobenius]
      apply Subtype.ext
      apply Units.ext
      ext a b
      rw [SpStd.coe_frobenius_apply, SpStd.coe_frobenius_apply, SpStd.coe_frobenius_apply,
        ← pow_mul]
      congr 1
      rw [pow_succ, hchar]
      ring

/-- **The Steinberg endomorphism of a Suzuki index**: the odd power `τ ^ (2m+1)` of the
half-Frobenius, for `2m+1` the field exponent the index records. -/
noncomputable def steinberg :
    d.toRankTwoBLieIndex.AmbientGroup →* d.toRankTwoBLieIndex.AmbientGroup :=
  d.halfFrobeniusEnd ^ d.1.fieldExponent

/-- The Steinberg endomorphism is the `fieldExponent`-th power of the half-Frobenius. -/
theorem steinberg_def : d.steinberg = d.halfFrobeniusEnd ^ d.1.fieldExponent :=
  (rfl)

/-- The Steinberg endomorphism iterates the half-Frobenius `2m+1` times. -/
theorem steinberg_apply (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.steinberg g = (⇑d.halfFrobenius)^[d.1.fieldExponent] g :=
  (rfl)

/-- **The square of the Steinberg endomorphism is the `q`-power Frobenius**, which is the relation
`steinberg (m) ^ 2 = Frob_(p ^ (2m+1))` that milestone `L2` requires of the odd half-Frobenius
power. -/
theorem steinberg_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.toRankTwoBLieIndex.frobenius g := by
  rw [steinberg_apply, steinberg_apply, ← Function.iterate_add_apply,
    show d.1.fieldExponent + d.1.fieldExponent = 2 * d.1.fieldExponent by ring,
    halfFrobenius_iterate_two_mul, RankTwoBLieIndex.frobenius_def]

/-- **The half-Frobenius carries the long simple root subgroup to the short one and keeps the
parameter.** The long simple root of `B₂` is the one whose carrier node is the final one, and the
exponent `1` here is the convention that milestone `L2` attaches to a long simple root. -/
theorem halfFrobenius_simpleRootSubgroup_long (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.toRankTwoBLieIndex.simpleRootSubgroup
        (d.toRankTwoBLieIndex.carrierNode.symm 1) u) =
      d.toRankTwoBLieIndex.simpleRootSubgroup (d.toRankTwoBLieIndex.carrierNode.symm 0) u := by
  rw [RankTwoBLieIndex.simpleRootSubgroup_def, RankTwoBLieIndex.simpleRootSubgroup_def,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, halfFrobenius_def,
    show (1 : Fin 2) = Fin.last 1 from rfl]
  exact SpStd.specialIsogeny_rootSubgroupPoints_inl_last _ _

/-- **The half-Frobenius carries the short simple root subgroup to the long one and squares the
parameter.** The exponent two here is the defining characteristic, which is the convention that
milestone `L2` attaches to a short simple root. -/
theorem halfFrobenius_simpleRootSubgroup_short (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.toRankTwoBLieIndex.simpleRootSubgroup
        (d.toRankTwoBLieIndex.carrierNode.symm 0) u) =
      d.toRankTwoBLieIndex.simpleRootSubgroup (d.toRankTwoBLieIndex.carrierNode.symm 1)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2)) := by
  rw [RankTwoBLieIndex.simpleRootSubgroup_def, RankTwoBLieIndex.simpleRootSubgroup_def,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, halfFrobenius_def,
    show (1 : Fin 2) = Fin.last 1 from rfl]
  exact SpStd.specialIsogeny_rootSubgroupPoints_inl_zero _ _

/-! ## The classification candidate -/

/-- **The candidate simple group of the Suzuki family `²B₂(2^(2m+1))`**: the derived subgroup of
the fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the milestone `L3` recipe on the Suzuki branch, run on the rank-two type-`C` carrier.
Nothing below asserts that it is finite, perfect, or simple, nor that the carrier is the pinned
one milestone `L0` asks for, nor that it is Mathlib's `suzukiGroup`. -/
noncomputable abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone `L3` asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
noncomputable example : _root_.Group d.Group := inferInstance

end TauCeti.SuzukiLieIndex
