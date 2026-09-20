/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.IterateOneParameter
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two

/-!
# The Steinberg endomorphism and candidate group of the Suzuki family

The Steinberg endomorphism of `²B₂(2^(2m+1))` is not a Frobenius but an odd power of a
half-Frobenius: the exceptional isogeny `τ` of the ambient group, which squares to the prime-field
Frobenius, raised to the odd exponent `2m+1`. This file forms that map on the ambient group of a
Suzuki index, proves the required square relation,

```text
steinberg (m) ^ 2 = Frob_(2 ^ (2m+1)),
```

and names the family's candidate group: the derived subgroup of the Steinberg fixed points modulo
its centre.

The half-Frobenius is available because the ambient group of a Suzuki index is the rank-two
type-`C` carrier over an algebraically closed field of characteristic two, and that carrier already
carries the special isogeny. So nothing is constructed here: the half-Frobenius *is* that isogeny,
and the work is the odd power and its square.

The exponent is not a new parameter. `TauCeti.ValidLieTypeIndex.fieldExponent` already writes the
field order of an index as a power of its characteristic, and on a Suzuki index it is the odd
number `2m+1`, so the Steinberg map is the `fieldExponent`-th power throughout and squaring it
lands on the `q`-power Frobenius `TauCeti.RankTwoBLieIndex.frobenius` that the index records rather
than on a separately tabulated field order.

## The simple-root-subgroup action

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
* `TauCeti.SuzukiLieIndex.FixedPoints`: the fixed subgroup of `steinberg`.
* `TauCeti.SuzukiLieIndex.Group`: the candidate group, `FixedPointCandidate steinberg`.

## Main results

* `TauCeti.SuzukiLieIndex.steinberg_simpleRootSubgroup`: the Steinberg map's own action formula at
  every numbered simple root, exchanging the two roots and raising the parameter to
  `p ^ m * exponent i`.
* `TauCeti.SuzukiLieIndex.halfFrobenius_simpleRootSubgroup`: the action formula at every numbered
  simple root, against the index's own length permutation and exponent.
* `TauCeti.SuzukiLieIndex.halfFrobenius_halfFrobenius`: the square of the half-Frobenius is the
  prime-field Frobenius.
* `TauCeti.SuzukiLieIndex.steinberg_steinberg`: the square of the Steinberg endomorphism is the
  `q`-power Frobenius.

## What is not here

Nothing is proved finite, perfect or simple of `Group`, and Mathlib's separate `suzukiGroup` is not
mentioned, so no comparison with it is claimed. The fixed points of an odd half-Frobenius power are
not the `𝔽_q` points of the carrier, which is why this family is not an instance of the Frobenius
machinery the untwisted ones use.

The ambient group is the explicit rank-two type-`C` carrier, and it is not identified with the
pinned simply connected group scheme of type `B₂`: no pinning datum is constructed for the carrier
here or in the files it imports, and the constructions below transfer to that pinned group only
along such an identification, once one is proved. The identification with the `B₂` diagram that
is available is the one on numbered root characters,
`TauCeti.RankTwoBLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`, and the
simple-root-subgroup action equations below are stated against it.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ^ 2 = Frob_p` and
  its odd powers.
-/

-- Reinstates, unchanged, the half-Frobenius, its odd power and the two square relations first
-- formalized in https://github.com/TauCetiProject/TauCeti/pull/5921.

public section

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

-- The construction below follows the `SuzukiReeIndex.halfFrobenius` and
-- `ValidLieTypeIndex.steinberg` target signatures in
-- `TauCetiRoadmap/CFSGStatement/Suggested.lean`.

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

/-- Applying the half-Frobenius after the Suzuki Steinberg map gives the
`2^(m+1)`-power Frobenius. -/
@[simp]
theorem halfFrobenius_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.halfFrobenius (d.steinberg g) =
      SpStd.frobenius 1 d.1.characteristic
        (SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1) d.1.Closure g := by
  have hpow : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] := by
    rw [steinberg_def]
    exact Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.AmbientGroup) _ _
  have hexp : d.1.fieldExponent + 1 =
      2 * (SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1) := by
    rw [SuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one d.toSuzukiReeIndex]
    omega
  rw [hpow, ← Function.iterate_succ_apply' (⇑d.halfFrobenius),
    Nat.succ_eq_add_one, hexp, halfFrobenius_iterate_two_mul]

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

/-- **The simple-root-subgroup action formula for the half-Frobenius at every numbered simple
root**, stated against the index's own length permutation and exponent rather than against the two
carrier nodes:

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

/-- **The simple-root-subgroup action formula for the Steinberg endomorphism at every numbered
simple root.** It exchanges the two simple roots exactly as the half-Frobenius does, its odd power
acting on the parameter by the remaining even power of the characteristic:

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
  have hsq : ∀ (j : Fin d.1.rank) (t : Multiplicative d.1.Closure),
      d.halfFrobenius (d.halfFrobenius (d.toRankTwoBLieIndex.simpleRootSubgroup j t)) =
        d.toRankTwoBLieIndex.simpleRootSubgroup j
          (Multiplicative.ofAdd (Multiplicative.toAdd t ^ d.1.characteristic)) := fun j t => by
    rw [halfFrobenius_halfFrobenius, RankTwoBLieIndex.primeFrobenius_simpleRootSubgroup]
  have hpow : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius d.1.fieldExponent
  rw [hpow, SuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one d.toSuzukiReeIndex]
  exact iterate_two_mul_add_one_apply_ofAdd_pow d.halfFrobenius_simpleRootSubgroup hsq
    (SuzukiReeIndex.halfExponent d.toSuzukiReeIndex) i u

/-! ## The finite-group candidate -/

noncomputable section

/-- The fixed subgroup of the Steinberg endomorphism attached to a Suzuki index. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a Suzuki index**: the derived subgroup of the
Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or simplicity
assertion is part of this definition, and no comparison with Mathlib's `suzukiGroup` is made. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.SuzukiLieIndex
