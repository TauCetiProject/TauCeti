/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Index

/-!
# The Steinberg endomorphism and candidate group of the Ree family of type `G₂`

The Steinberg endomorphism of `²G₂(3^(2m+1))` is not a Frobenius but an odd power of a
half-Frobenius: the special isogeny `τ` of the ambient group, which squares to the prime-field
Frobenius, raised to the odd exponent `2m+1`. This file attaches the ambient group to a Ree index
of type `G₂`, forms that map on it, proves the required square relation,

```text
steinberg (m) ^ 2 = Frob_(3 ^ (2m+1)),
```

and names the family's candidate group: the derived subgroup of the Steinberg fixed points modulo
its centre.

The ambient group is the short-root type-`G₂` carrier over the prime field of characteristic
three, evaluated on the algebraic closure the index names, and that carrier already carries the
special isogeny. So the half-Frobenius is not constructed here: it *is* that isogeny, and the work
is the odd power and its square.

The exponent is not a new parameter. `TauCeti.ValidLieTypeIndex.fieldExponent` already writes the
field order of an index as a power of its characteristic, and on a Ree index of type `G₂` it is the
odd number `2m+1`, so the Steinberg map is the `fieldExponent`-th power throughout and squaring it
lands on the `q`-power Frobenius of the carrier rather than on a separately tabulated field order.

## The simple-root-subgroup action

What is recorded of `τ` is its action on the numbered simple root subgroups:

```text
τ (x_{α i}(t)) = x_{α (σ i)}(t ^ e i),
```

for `σ` the permutation exchanging the long and short simple roots and `e` the exponent that is
`1` on a long simple root and the defining characteristic on a short one. Those are
`TauCeti.SuzukiReeIndex.lengthPerm` and `TauCeti.SuzukiReeIndex.exponent`. On the `G₂` diagram the
long simple root is Bourbaki node one, and the carrier numbers its nodes the same way, node zero
being the short simple root and node one the long one, so the node correspondence
`TauCeti.ReeG2LieIndex.carrierNode` is the rank identification alone and carries no swap.

## Main definitions

* `TauCeti.ReeG2LieIndex.AmbientGroup`: the points of the short-root type-`G₂` carrier over the
  prime field, taken over the algebraic closure the index names, with
  `TauCeti.ReeG2LieIndex.simpleRootSubgroup` its Bourbaki-numbered positive simple root subgroups.
* `TauCeti.ReeG2LieIndex.frobenius` and `TauCeti.ReeG2LieIndex.primeFrobenius`: the `q`-power and
  the `p`-power Frobenius of that group.
* `TauCeti.ReeG2LieIndex.halfFrobenius`: the special isogeny of the ambient group.
* `TauCeti.ReeG2LieIndex.steinberg`: its odd power `τ ^ (2m+1)`.
* `TauCeti.ReeG2LieIndex.FixedPoints`: the fixed subgroup of `steinberg`.
* `TauCeti.ReeG2LieIndex.Group`: the candidate group, `FixedPointCandidate steinberg`.

## Main results

* `TauCeti.ReeG2LieIndex.halfFrobenius_halfFrobenius`: the square of the half-Frobenius is the
  prime-field Frobenius.
* `TauCeti.ReeG2LieIndex.halfFrobenius_simpleRootSubgroup`: the action formula at every numbered
  simple root, against the index's own length permutation and exponent, with
  `TauCeti.ReeG2LieIndex.frobenius_simpleRootSubgroup` and
  `TauCeti.ReeG2LieIndex.primeFrobenius_simpleRootSubgroup` recording that the two Frobenius maps
  fix each simple root and raise the parameter to the field order and to the characteristic.
* `TauCeti.ReeG2LieIndex.steinberg_steinberg`: the square of the Steinberg endomorphism is the
  `q`-power Frobenius.
* `TauCeti.ReeG2LieIndex.steinberg_simpleRootSubgroup`: the Steinberg map's own action formula at
  every numbered simple root, exchanging the two roots and raising the parameter to
  `p ^ m * exponent i`.

## What is not here

Nothing is proved finite, perfect or simple of `Group`. The fixed points of an odd half-Frobenius
power are not the `𝔽_q` points of the carrier, which is why this family is not an instance of the
Frobenius machinery the untwisted ones use.

The ambient group is the explicit short-root type-`G₂` carrier over `𝔽₃`, and it is not identified
with the pinned simply connected group scheme of type `G₂`: no pinning datum is constructed for the
carrier here or in the files it imports, and the constructions below transfer to that pinned group
only along such an identification, once one is proved. The identification with the `G₂` diagram
that is available is the one on numbered root characters,
`TauCeti.ReeG2LieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`, and the
simple-root-subgroup action equations below are stated against it.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ^ 2 = Frob_p` and
  its odd powers.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX, for the numbering of the
  `G₂` diagram.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic`, the same
-- construction for the Suzuki family, with the same declaration order.

public section

namespace TauCeti.ReeG2LieIndex

open DynkinType

variable (d : ReeG2LieIndex)

/-- The algebraic closure attached to a Ree index of type `G₂` is an algebra over the prime field
of characteristic three. It has characteristic three, and an algebra structure over `ZMod 3` is
unique, so no choice is made here. -/
noncomputable instance algebraZModThreeClosure : Algebra (ZMod 3) d.1.Closure :=
  ZMod.algebra _ 3

noncomputable section

/-! ## The node correspondence -/

/-- **The carrier node corresponding to a Bourbaki-numbered node of `G₂`**, with the inverse
equivalence giving the correspondence back. Unlike the rank-two type-`C` carrier of the Suzuki
family, the short-root type-`G₂` carrier numbers its nodes exactly as Bourbaki does, node zero
being the short simple root and node one the long one, so this is the rank equality
`TauCeti.ReeG2LieIndex.rank_eq_two` and nothing more. -/
def carrierNode : Fin d.1.rank ≃ Fin 2 :=
  finCongr d.rank_eq_two

@[simp] theorem carrierNode_apply (i : Fin d.1.rank) :
    d.carrierNode i = finCongr d.rank_eq_two i :=
  (rfl)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group attached to a Ree index of type `G₂`**: the points of the explicit
full-weight short-root type-`G₂` Chevalley carrier over the prime field of characteristic three,
taken over the algebraic closure of that prime field. It is infinite; no finiteness, reductivity,
pinning or maximality statement is attached to it, and it is not claimed to be the points of the
pinned simply connected group scheme of type `G₂`; no such identification is available, as the
module docstring explains. -/
abbrev AmbientGroup : Type := G2ShortRoot.PrimeField.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `G₂` diagram. It is
the carrier's numbered raising subgroup at the node that `carrierNode` names. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.rootSubgroupPoints (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`. It is not a `simp` lemma: the simple-root-subgroup action equations of this
file are the normal forms, and unfolding to
`TauCeti.G2ShortRoot.PrimeField.rootSubgroupPoints` would keep them from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      G2ShortRoot.PrimeField.rootSubgroupPoints (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `G₂` root datum.** The character by
which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read in the same
node correspondence, is the `i`-th simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at
`G₂`. This is the sense in which the short-root carrier serves the diagram that the Ree family of
type `G₂` names; it is not a claim that the carrier is the pinned group of that diagram, no pinning
being constructed for it. -/
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    G2.rootGeneratorWeight valid_G2 (.inl (d.carrierNode i)) (d.carrierNode j) =
      (G2.simplyConnectedRootDatum valid_G2).root
        (G2.simpleIndex valid_G2 (finCongr d.rank_eq_two i)) (finCongr d.rank_eq_two j) := by
  rw [carrierNode_apply, carrierNode_apply]
  exact congrFun (G2.rootGeneratorWeight_inl_eq_root_simpleIndex valid_G2 _) _

/-! ## The Frobenius endomorphisms -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a Ree index of type `G₂`**, for
`q` the field order the index records. It is the map the Steinberg endomorphism of the family
squares to. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure

/-- The `q`-power Frobenius is the carrier's Frobenius at the exponent the index records. This is
its unfolding lemma; the definition itself stays sealed. It is deliberately not a `simp` lemma, the
action equations stated against it being the normal forms. -/
theorem frobenius_def :
    d.frobenius = G2ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- **The prime-field Frobenius endomorphism of the ambient group of a Ree index of type `G₂`**,
the `p`-power map for `p = 3` the defining characteristic. It is the map the half-Frobenius squares
to, and it agrees with the `q`-power map above only when the index has field order three, which
validity excludes. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.frobenius 1 d.1.Closure

/-- The prime-field Frobenius is the carrier's Frobenius at exponent one. This is its unfolding
lemma; the definition itself stays sealed. -/
theorem primeFrobenius_def :
    d.primeFrobenius = G2ShortRoot.PrimeField.frobenius 1 d.1.Closure :=
  (rfl)

/-! ## The half-Frobenius and the Steinberg endomorphism -/

/-- **The half-Frobenius of a Ree index of type `G₂`**: the special isogeny of its ambient
group. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius is the carrier's special isogeny. -/
theorem halfFrobenius_def :
    d.halfFrobenius = G2ShortRoot.PrimeField.specialIsogeny d.1.Closure :=
  (rfl)

/-- **The square of the half-Frobenius is the prime-field Frobenius**, that is `τ ^ 2 = Frob_p` at
the defining characteristic `p = 3`. No uniqueness is claimed: nothing here shows that this
relation, or the action on the simple root subgroups, determines an endomorphism of the ambient
group. -/
@[simp]
theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius_def, primeFrobenius_def,
    G2ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem halfFrobenius_iterate_two_mul (k : ℕ) (g : d.AmbientGroup) :
    (⇑d.halfFrobenius)^[2 * k] g = G2ShortRoot.PrimeField.frobenius k d.1.Closure g := by
  induction k generalizing g with
  | zero => simp [G2ShortRoot.PrimeField.frobenius_zero]
  | succ k ih =>
      have hsucc : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have hk : k + 1 = 1 + k := Nat.add_comm k 1
      rw [hsucc, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        d.halfFrobenius_halfFrobenius, primeFrobenius_def, hk,
        G2ShortRoot.PrimeField.frobenius_add, MonoidHom.comp_apply]

/-- **The Steinberg endomorphism of a Ree index of type `G₂`**: the odd power `τ ^ (2m+1)` of the
half-Frobenius, for `2m+1` the field exponent the index records. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  HPow.hPow (α := Monoid.End d.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- The Steinberg endomorphism is the `fieldExponent`-th power of the half-Frobenius. -/
theorem steinberg_def :
    d.steinberg =
      HPow.hPow (α := Monoid.End d.AmbientGroup) d.halfFrobenius d.1.fieldExponent :=
  (rfl)

/-- **The Steinberg endomorphism acts as the iterate of the half-Frobenius**, iterated as many
times as the field exponent the index records. -/
theorem coe_steinberg : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] := by
  rw [steinberg_def]
  exact Monoid.End.coe_pow (M := d.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- **The square of the Steinberg endomorphism is the `q`-power Frobenius**: squaring the odd
power `τ ^ (2m+1)` doubles the exponent, and `τ ^ 2` is the prime-field Frobenius. -/
@[simp]
theorem steinberg_steinberg (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  have hdouble : d.1.fieldExponent + d.1.fieldExponent = 2 * d.1.fieldExponent := by ring
  rw [d.coe_steinberg, ← Function.iterate_add_apply, hdouble, halfFrobenius_iterate_two_mul,
    frobenius_def]

/-! ## The simple-root-subgroup action -/

/-- **The carrier node one is the long simple root.** The `G₂` diagram's long simple root is
Bourbaki node one, and the node correspondence keeps the numbering. -/
private theorem carrierNode_eq_one_iff (i : Fin d.1.rank) :
    d.carrierNode i = 1 ↔ d.1.dynkinType.IsLongSimpleRoot i := by
  have hlong : d.1.dynkinType.IsLongSimpleRoot i ↔ (i : ℕ) = 1 :=
    DynkinType.isLongSimpleRoot_iff_of_eq (p := fun n => n = 1) d.dynkinType_eq
      (fun j => by rw [isLongSimpleRoot_G2]) i
  have hcarrier : d.carrierNode i = 1 ↔ (i : ℕ) = 1 := by
    rw [carrierNode_apply]
    simp [Fin.ext_iff]
  exact hcarrier.trans hlong.symm

/-- The length permutation of the index exchanges the two carrier nodes. -/
private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    d.carrierNode (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) =
      Equiv.swap 0 1 (d.carrierNode i) := by
  have hswap : d.carrierNode (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) = 1 ↔
      ¬d.carrierNode i = 1 :=
    (d.carrierNode_eq_one_iff _).trans
      ((SuzukiReeIndex.isLongSimpleRoot_lengthPerm d.toSuzukiReeIndex i).trans
        (not_congr (d.carrierNode_eq_one_iff i)).symm)
  revert hswap
  generalize d.carrierNode (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) = a
  generalize d.carrierNode i = b
  revert a b
  decide

/-- The exponent of the index is the carrier's special-isogeny exponent at the corresponding
node. -/
private theorem exponent_eq (i : Fin d.1.rank) :
    SuzukiReeIndex.exponent d.toSuzukiReeIndex i =
      G2ShortRoot.specialIsogenyExponent (.inl (d.carrierNode i)) := by
  rw [G2ShortRoot.specialIsogenyExponent_inl_eq_ite]
  have hnode := d.carrierNode_eq_one_iff i
  by_cases hi : d.1.dynkinType.IsLongSimpleRoot i
  · rw [SuzukiReeIndex.exponent_of_isLongSimpleRoot _ _ hi]
    simp [hnode.mpr hi]
  · rw [SuzukiReeIndex.exponent_of_not_isLongSimpleRoot _ _ hi, d.characteristic_eq_three]
    exact (ite_eq_right_iff.mpr fun h => absurd (hnode.mp h) hi).symm

/-- **The simple-root-subgroup action formula for the half-Frobenius at every numbered simple
root**, stated against the index's own length permutation and exponent:

```text
τ (x_{α i}(t)) = x_{α (lengthPerm i)}(t ^ exponent i).
```

The permutation exchanges the long and short simple roots and the exponent is `1` on the long one
and the defining characteristic `3` on the short one, so this is the carrier's root-subgroup
action equation read through the Bourbaki numbering the index carries. -/
@[simp]
theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  obtain ⟨t, rfl⟩ : ∃ t : d.1.Closure, Multiplicative.ofAdd t = u :=
    ⟨Multiplicative.toAdd u, rfl⟩
  rw [simpleRootSubgroup_def, simpleRootSubgroup_def, halfFrobenius_def, d.exponent_eq i,
    G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints,
    G2ShortRoot.specialIsogenyRootIndex_inl, d.carrierNode_lengthPerm i,
    lengthPermRankTwo_eq_swap, toAdd_ofAdd]

/-- **The simple-root-subgroup action formula for the `q`-power Frobenius.** It fixes every
numbered simple root and raises the parameter to the field order `q` the index records. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  obtain ⟨t, rfl⟩ : ∃ t : d.1.Closure, Multiplicative.ofAdd t = u :=
    ⟨Multiplicative.toAdd u, rfl⟩
  -- Rewrite the power towards the field order, the characteristic occurring in the type of the
  -- coefficient field.
  have horder : (3 : ℕ) ^ d.1.fieldExponent = d.1.fieldOrder := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, d.characteristic_eq_three]
  rw [simpleRootSubgroup_def, frobenius_def,
    G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints, horder, toAdd_ofAdd]

/-- **The simple-root-subgroup action formula for the prime-field Frobenius.** It fixes every
numbered simple root and raises the parameter to the defining characteristic. -/
@[simp]
theorem primeFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.characteristic)) := by
  obtain ⟨t, rfl⟩ : ∃ t : d.1.Closure, Multiplicative.ofAdd t = u :=
    ⟨Multiplicative.toAdd u, rfl⟩
  -- Rewrite the power towards the characteristic, which occurs in the type of the coefficient
  -- field.
  have hchar : (3 : ℕ) ^ 1 = d.1.characteristic := by rw [d.characteristic_eq_three, pow_one]
  rw [simpleRootSubgroup_def, primeFrobenius_def,
    G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints, hchar, toAdd_ofAdd]

/-- **The simple-root-subgroup action formula for the Steinberg endomorphism at every numbered
simple root.** One of the `2m+1` half-Frobenius steps exchanges the two simple roots exactly as
the half-Frobenius does; the remaining even iterate `τ ^ (2m)` fixes each simple root and acts on
the parameter by the `p ^ m`-power Frobenius:

```text
steinberg (x_{α i}(t)) = x_{α (lengthPerm i)}(t ^ (p ^ m * exponent i)).
```
-/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^
            (d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex *
              SuzukiReeIndex.exponent d.toSuzukiReeIndex i))) := by
  have hodd : d.1.fieldExponent = 2 * SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1 :=
    SuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one d.toSuzukiReeIndex
  have hexp : d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex *
      SuzukiReeIndex.exponent d.toSuzukiReeIndex i =
        SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
          d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex :=
    Nat.mul_comm _ _
  have hchar : SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
      (3 : ℕ) ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex =
        SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
          d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex := by
    rw [d.characteristic_eq_three]
  rw [d.coe_steinberg, hodd, Function.iterate_succ_apply, d.halfFrobenius_simpleRootSubgroup i u,
    d.halfFrobenius_iterate_two_mul, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints, ← simpleRootSubgroup_def, hexp]
  congr 2
  rw [toAdd_ofAdd, ← pow_mul, hchar]

/-! ## The finite-group candidate -/

/-- The fixed subgroup of the Steinberg endomorphism attached to a Ree index of type `G₂`. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a Ree index of type `G₂`**: the derived
subgroup of the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness
or simplicity assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeG2LieIndex
