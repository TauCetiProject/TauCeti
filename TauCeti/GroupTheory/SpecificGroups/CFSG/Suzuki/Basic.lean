/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two

/-!
# The Steinberg endomorphism of the Suzuki family

The Steinberg endomorphism of `²B₂(2^(2m+1))` is not a Frobenius but an odd power of a
half-Frobenius: the exceptional isogeny `τ` of the ambient group, which squares to the prime-field
Frobenius, raised to the odd exponent `2m+1`. This file forms that map on the ambient group of a
Suzuki index and proves the required square relation,

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

What is recorded of `τ` is its action on the numbered simple root subgroups:

```text
τ (x_{α i}(t)) = x_{α (σ i)}(t ^ e i),
```

for `σ` the permutation exchanging the long and short simple roots and `e` the exponent that is
`1` on a long simple root and the defining characteristic on a short one. Those are
`TauCeti.SuzukiReeIndex.lengthPerm` and `TauCeti.SuzukiReeIndex.exponent`. On the `B₂` diagram the
long simple root is Bourbaki node zero, which `TauCeti.RankTwoBLieIndex.carrierNode` carries to the
final carrier node, so the indexed equation is proved from the two equations at the carrier nodes
and that numbering correspondence.

## Main definitions

* `TauCeti.SuzukiLieIndex.halfFrobenius`: the special isogeny of the ambient group.
* `TauCeti.SuzukiLieIndex.steinberg`: its odd power `τ ^ (2m+1)`.
* `TauCeti.SuzukiLieIndex.CarrierFixedPointQuotient`: the quotient the classification's recipe
  produces from that Steinberg map on this carrier,
  the derived subgroup of its fixed points modulo the centre of that derived subgroup.

## Main results

* `TauCeti.SuzukiLieIndex.steinberg_simpleRootSubgroup`: the Steinberg map's own pinning equation
  at every numbered simple root, exchanging the two roots and raising the parameter to
  `p ^ m * exponent i`.
* `TauCeti.SuzukiLieIndex.halfFrobenius_simpleRootSubgroup`: the pinning equation at every
  numbered simple root, against the index's own length permutation and exponent.
* `TauCeti.SuzukiLieIndex.halfFrobenius_halfFrobenius`: the square of the half-Frobenius is the
  prime-field Frobenius, with `TauCeti.SuzukiLieIndex.halfFrobenius_comp_halfFrobenius` for the
  composite itself.
* `TauCeti.SuzukiLieIndex.steinberg_steinberg`: the square of the Steinberg endomorphism is the
  `q`-power Frobenius, with `TauCeti.SuzukiLieIndex.steinberg_comp_steinberg` for the composite
  itself.

## What is not here

The group below is named but not identified. Nothing is proved finite, perfect or simple, and
Mathlib's separate `suzukiGroup` is not mentioned, so no comparison with it is claimed. The
Steinberg map here is an odd power of the half-Frobenius rather than a Frobenius, so the untwisted
families' description of the fixed points by matrix entries lying in a subfield does not apply, and
no description of them is offered.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ^ 2 = Frob_p` and
  its odd powers.
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

/-- **The square of the half-Frobenius is the prime-field Frobenius**, that is `τ ^ 2 = Frob_p` at
the defining characteristic `p = 2`. No uniqueness is claimed: nothing here shows that this
relation, or the action on the simple root subgroups, determines an endomorphism of the ambient
group. -/
@[simp]
theorem halfFrobenius_halfFrobenius (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.toRankTwoBLieIndex.primeFrobenius g := by
  -- The carrier's square relation is stated at the literal `2`, the index's at its characteristic.
  -- Identifying the two is the one step that descends to matrix entries: the characteristic cannot
  -- be rewritten at the exponent of `SpStd.frobenius`, whose instances depend on it.
  have hchar : (d.toRankTwoBLieIndex.1).characteristic = 2 := d.characteristic_eq_two
  rw [halfFrobenius_def, SpStd.specialIsogeny_specialIsogeny,
    RankTwoBLieIndex.primeFrobenius_def]
  apply Subtype.ext
  apply Units.ext
  ext a b
  rw [SpStd.coe_frobenius_apply, SpStd.coe_frobenius_apply]
  congr 1
  rw [hchar]

/-- **The square of the half-Frobenius is the prime-field Frobenius**, as an identity of monoid
homomorphisms, so a consumer taking odd powers can rewrite the composite itself. -/
@[simp]
theorem halfFrobenius_comp_halfFrobenius :
    d.halfFrobenius.comp d.halfFrobenius = d.toRankTwoBLieIndex.primeFrobenius :=
  MonoidHom.ext d.halfFrobenius_halfFrobenius

private theorem halfFrobenius_iterate_two_mul (k : ℕ) (g : d.toRankTwoBLieIndex.AmbientGroup) :
    (⇑d.halfFrobenius)^[2 * k] g =
      SpStd.frobenius 1 (d.toRankTwoBLieIndex.1).characteristic k
        (d.toRankTwoBLieIndex.1).Closure g := by
  induction k generalizing g with
  | zero => simp [SpStd.frobenius_zero]
  | succ k ih =>
      have hsucc : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have hk : k + 1 = 1 + k := Nat.add_comm k 1
      rw [hsucc, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        d.halfFrobenius_halfFrobenius, RankTwoBLieIndex.primeFrobenius_def, hk,
        SpStd.frobenius_add, MonoidHom.comp_apply]

/-- **The Steinberg endomorphism of a Suzuki index**: the odd power `τ ^ (2m+1)` of the
half-Frobenius, for `2m+1` the field exponent the index records. -/
noncomputable def steinberg :
    d.toRankTwoBLieIndex.AmbientGroup →* d.toRankTwoBLieIndex.AmbientGroup :=
  HPow.hPow (α := Monoid.End d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- The Steinberg endomorphism is the `fieldExponent`-th power of the half-Frobenius. -/
theorem steinberg_def :
    d.steinberg =
      HPow.hPow (α := Monoid.End d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius
        d.1.fieldExponent :=
  (rfl)

/-- **The square of the Steinberg endomorphism is the `q`-power Frobenius**: squaring the odd
power `τ ^ (2m+1)` doubles the exponent, and `τ ^ 2` is the prime-field Frobenius. -/
@[simp]
theorem steinberg_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.toRankTwoBLieIndex.frobenius g := by
  have hpow : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius d.1.fieldExponent
  have hdouble : d.1.fieldExponent + d.1.fieldExponent = 2 * d.1.fieldExponent := by ring
  rw [hpow, ← Function.iterate_add_apply, hdouble, halfFrobenius_iterate_two_mul,
    RankTwoBLieIndex.frobenius_def]

/-- The final node of the two-node carrier is the numeral one. -/
private theorem one_eq_last : (1 : Fin 2) = Fin.last 1 := rfl

/-- **The half-Frobenius carries the long simple root subgroup to the short one and keeps the
parameter.** The long simple root of `B₂` is the one whose carrier node is the final one, and the
exponent `1` here is the one the isogeny takes on a long simple root. -/
private theorem halfFrobenius_simpleRootSubgroup_long (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.toRankTwoBLieIndex.simpleRootSubgroup
        (d.toRankTwoBLieIndex.carrierNode.symm 1) u) =
      d.toRankTwoBLieIndex.simpleRootSubgroup (d.toRankTwoBLieIndex.carrierNode.symm 0) u := by
  rw [RankTwoBLieIndex.simpleRootSubgroup_def, RankTwoBLieIndex.simpleRootSubgroup_def,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, halfFrobenius_def,
    one_eq_last]
  exact SpStd.specialIsogeny_rootSubgroupPoints_inl_last _ _

/-- **The half-Frobenius carries the short simple root subgroup to the long one and squares the
parameter.** The exponent two here is the defining characteristic, which is the one the isogeny
takes on a short simple root. -/
private theorem halfFrobenius_simpleRootSubgroup_short (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.toRankTwoBLieIndex.simpleRootSubgroup
        (d.toRankTwoBLieIndex.carrierNode.symm 0) u) =
      d.toRankTwoBLieIndex.simpleRootSubgroup (d.toRankTwoBLieIndex.carrierNode.symm 1)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2)) := by
  rw [RankTwoBLieIndex.simpleRootSubgroup_def, RankTwoBLieIndex.simpleRootSubgroup_def,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, halfFrobenius_def,
    one_eq_last]
  exact SpStd.specialIsogeny_rootSubgroupPoints_inl_zero _ _

/-- **The final carrier node is the long simple root.** The `B₂` diagram's long simple root is
Bourbaki node zero, and `carrierNode` swaps the two numberings. -/
private theorem carrierNode_eq_one_iff (i : Fin d.1.rank) :
    d.toRankTwoBLieIndex.carrierNode i = 1 ↔ d.1.dynkinType.IsLongSimpleRoot i := by
  have hcarrier : d.toRankTwoBLieIndex.carrierNode i = 1 ↔ (i : ℕ) = 0 := by
    rw [RankTwoBLieIndex.carrierNode_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    simp [Fin.ext_iff]
  have hlong : d.1.dynkinType.IsLongSimpleRoot i ↔ (i : ℕ) = 0 := by
    obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
    simp only [ValidLieTypeIndex.dynkinType]
    rw [DynkinType.isLongSimpleRoot_congr (LieTypeIndex.dynkinType_suzuki m)]
    simp only [DynkinType.isLongSimpleRoot_B, finCongr_apply, Fin.val_cast]
    omega
  exact hcarrier.trans hlong.symm

/-- The length permutation of the index exchanges the two carrier nodes. -/
private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    d.toRankTwoBLieIndex.carrierNode (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) =
      Equiv.swap 0 1 (d.toRankTwoBLieIndex.carrierNode i) := by
  have hswap : d.toRankTwoBLieIndex.carrierNode
        (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) = 1 ↔
      ¬d.toRankTwoBLieIndex.carrierNode i = 1 :=
    (d.carrierNode_eq_one_iff _).trans
      ((SuzukiReeIndex.isLongSimpleRoot_lengthPerm d.toSuzukiReeIndex i).trans
        (not_congr (d.carrierNode_eq_one_iff i)).symm)
  revert hswap
  generalize d.toRankTwoBLieIndex.carrierNode
    (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) = a
  generalize d.toRankTwoBLieIndex.carrierNode i = b
  revert a b
  decide

/-- The exponent of the index is one at the final carrier node and two at the other. -/
private theorem exponent_eq (i : Fin d.1.rank) :
    SuzukiReeIndex.exponent d.toSuzukiReeIndex i =
      if d.toRankTwoBLieIndex.carrierNode i = 1 then 1 else 2 := by
  have hnode := d.carrierNode_eq_one_iff i
  by_cases hi : d.1.dynkinType.IsLongSimpleRoot i
  · rw [SuzukiReeIndex.exponent_of_isLongSimpleRoot _ _ hi]
    simp [hnode.mpr hi]
  · rw [SuzukiReeIndex.exponent_of_not_isLongSimpleRoot _ _ hi, d.characteristic_eq_two]
    exact (ite_eq_right_iff.mpr fun h => absurd (hnode.mp h) hi).symm

/-- **The pinning equation of the half-Frobenius at every numbered simple root**, stated against
the index's own length permutation and exponent rather than against the two carrier nodes:

```text
τ (x_{α i}(t)) = x_{α (lengthPerm i)}(t ^ exponent i).
```

The permutation exchanges the long and short simple roots and the exponent is `1` on the long one
and the defining characteristic `2` on the short one, so this is the two equations above read
through the Bourbaki numbering the index carries. -/
@[simp]
theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.toRankTwoBLieIndex.simpleRootSubgroup i u) =
      d.toRankTwoBLieIndex.simpleRootSubgroup
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  obtain ⟨c, rfl⟩ : ∃ c, i = d.toRankTwoBLieIndex.carrierNode.symm c :=
    ⟨d.toRankTwoBLieIndex.carrierNode i, (Equiv.symm_apply_apply _ _).symm⟩
  have hj : SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex
        (d.toRankTwoBLieIndex.carrierNode.symm c) =
      d.toRankTwoBLieIndex.carrierNode.symm (Equiv.swap 0 1 c) := by
    rw [Equiv.eq_symm_apply, d.carrierNode_lengthPerm, Equiv.apply_symm_apply]
  rw [hj, d.exponent_eq, Equiv.apply_symm_apply]
  fin_cases c
  · simpa using d.halfFrobenius_simpleRootSubgroup_short u
  · simpa using d.halfFrobenius_simpleRootSubgroup_long u

/-- **The square of the Steinberg endomorphism is the `q`-power Frobenius**, as an identity of
monoid homomorphisms. -/
@[simp]
theorem steinberg_comp_steinberg :
    d.steinberg.comp d.steinberg = d.toRankTwoBLieIndex.frobenius :=
  MonoidHom.ext d.steinberg_steinberg

/-- **The pinning equation of the Steinberg endomorphism at every numbered simple root.** It
exchanges the two simple roots exactly as the half-Frobenius does, its odd power acting on the
parameter by the remaining even power of the characteristic:

```text
steinberg (x_{α i}(t)) = x_{α (lengthPerm i)}(t ^ (p ^ m * exponent i)).
```
-/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.toRankTwoBLieIndex.simpleRootSubgroup i u) =
      d.toRankTwoBLieIndex.simpleRootSubgroup
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^
            (d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex *
              SuzukiReeIndex.exponent d.toSuzukiReeIndex i))) := by
  have hpow : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius d.1.fieldExponent
  have hodd : d.1.fieldExponent = 2 * SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1 :=
    SuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one d.toSuzukiReeIndex
  have hexp : d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex *
      SuzukiReeIndex.exponent d.toSuzukiReeIndex i =
        SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
          d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex :=
    Nat.mul_comm _ _
  rw [hpow, hodd, Function.iterate_succ_apply, d.halfFrobenius_simpleRootSubgroup i u,
    d.halfFrobenius_iterate_two_mul, RankTwoBLieIndex.simpleRootSubgroup_def,
    SpStd.frobenius_rootSubgroupPoints, ← RankTwoBLieIndex.simpleRootSubgroup_def, hexp]
  congr 2
  exact (pow_mul _ _ _).symm

/-! ## The attached group -/

/-- The derived subgroup of the fixed points of the Suzuki Steinberg map on this carrier, modulo
the centre of that derived subgroup.

This is the classification's recipe, run on the rank-two type-`C` carrier. It is not the Suzuki
group `²B₂(2 ^ (2m+1))`: that is the same recipe run on the points of the pinned simply connected
`B₂` group scheme, and no identification of this carrier with that group is available. Nothing
below asserts that the quotient is finite, perfect, or simple. -/
abbrev CarrierFixedPointQuotient : Type := FixedPointCandidate d.steinberg

/-- The quotient construction supplies its group structure. -/
noncomputable example : _root_.Group d.CarrierFixedPointQuotient := inferInstance

end TauCeti.SuzukiLieIndex
