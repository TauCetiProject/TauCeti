/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Index

/-!
# The Steinberg endomorphism and candidate group of the Ree family of type `F₄` and of the Tits
group

The Steinberg endomorphism of `²F₄(2^(2m+1))` is not a Frobenius but an odd power of a
half-Frobenius: the special isogeny `τ` of the ambient group, which squares to the prime-field
Frobenius, raised to the odd exponent `2m+1`. This file attaches the ambient group to an index in
the type-`F₄` half-Frobenius family, forms that map on it, proves the required square relation,

```text
steinberg (m) ^ 2 = Frob_(2 ^ (2m+1)),
```

and names the family's candidate group: the derived subgroup of the Steinberg fixed points modulo
its centre.

The Tits index is the `m = 0` member of the same family and needs no separate treatment. Its field
exponent is one, so its Steinberg map is the special isogeny itself, and everything below applies
to it verbatim.

The ambient group is the short-root type-`F₄` carrier over the prime field of characteristic two,
evaluated on the algebraic closure the index names, and that carrier already carries the special
isogeny. So the half-Frobenius is not constructed here: it *is* that isogeny, and the work is the
odd power and its square.

The exponent is not a new parameter. `TauCeti.ValidLieTypeIndex.fieldExponent` already writes the
field order of an index as a power of its characteristic, and on this family it is the odd number
`2m+1`, one at the Tits index, so the Steinberg map is the `fieldExponent`-th power throughout and
squaring it lands on the `q`-power Frobenius of the carrier rather than on a separately tabulated
field order.

## The simple-root-subgroup action

What is recorded of `τ` is its action on the numbered simple root subgroups:

```text
τ (x_{α i}(t)) = x_{α (σ i)}(t ^ e i),
```

for `σ` the permutation exchanging the long and short simple roots and `e` the exponent that is
`1` on a long simple root and the defining characteristic on a short one. Those are
`TauCeti.SuzukiReeIndex.lengthPerm` and `TauCeti.SuzukiReeIndex.exponent`. On the `F₄` diagram the
length-exchanging map is the reversal of the four-node chain and the long simple roots are Bourbaki
nodes zero and one, and the short-root type-`F₄` carrier numbers its nodes the same way, its own
length-exchanging involution being the same reversal, so the node correspondence
`TauCeti.ReeF4LieIndex.carrierNode` is the rank identification alone and carries no relabelling.

## Main definitions

* `TauCeti.ReeF4LieIndex.AmbientGroup`: the points of the short-root type-`F₄` carrier over the
  prime field, taken over the algebraic closure the index names, with
  `TauCeti.ReeF4LieIndex.simpleRootSubgroup` its Bourbaki-numbered positive simple root subgroups.
* `TauCeti.ReeF4LieIndex.frobenius` and `TauCeti.ReeF4LieIndex.primeFrobenius`: the `q`-power and
  the `p`-power Frobenius of that group.
* `TauCeti.ReeF4LieIndex.halfFrobenius`: the special isogeny of the ambient group.
* `TauCeti.ReeF4LieIndex.steinberg`: its odd power `τ ^ (2m+1)`, the isogeny itself at the Tits
  index.
* `TauCeti.ReeF4LieIndex.FixedPoints`: the fixed subgroup of `steinberg`.
* `TauCeti.ReeF4LieIndex.Group`: the candidate group, `FixedPointCandidate steinberg`.

## Main results

* `TauCeti.ReeF4LieIndex.frobenius_simpleRootSubgroup` and
  `TauCeti.ReeF4LieIndex.primeFrobenius_simpleRootSubgroup`: the two Frobenius maps raise the
  parameter of a numbered simple root subgroup to the field order and to the characteristic.
* `TauCeti.ReeF4LieIndex.halfFrobenius_halfFrobenius`: the square of the half-Frobenius is the
  prime-field Frobenius.
* `TauCeti.ReeF4LieIndex.halfFrobenius_simpleRootSubgroup`: the action formula at every numbered
  simple root, against the index's own length permutation and exponent.
* `TauCeti.ReeF4LieIndex.steinberg_steinberg`: the square of the Steinberg endomorphism is the
  `q`-power Frobenius.
* `TauCeti.ReeF4LieIndex.steinberg_simpleRootSubgroup`: the Steinberg map's own action formula at
  every numbered simple root, reversing the diagram and raising the parameter to
  `p ^ m * exponent i`.

## What is not here

Nothing is proved finite, perfect or simple of `Group`. The fixed points of an odd half-Frobenius
power are not the `𝔽_q` points of the carrier, which is why this family is not an instance of the
Frobenius machinery the untwisted ones use.

The ambient group is the explicit short-root type-`F₄` carrier over `𝔽₂`, and it is not identified
with the pinned simply connected group scheme of type `F₄`: no pinning datum is constructed for the
carrier here or in the files it imports, and the constructions below transfer to that pinned group
only along such an identification, once one is proved. The identification with the `F₄` diagram
that is available is the one on numbered root characters,
`TauCeti.ReeF4LieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`, and the
simple-root-subgroup action equations below are stated against it.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* J. Tits, *Algebraic and abstract simple groups*, Ann. of Math. **80** (1964), for the group the
  first power of `τ` cuts out.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII, for the numbering of the
  `F₄` diagram.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic`, the Steinberg endomorphism
-- and candidate group of the Ree family of type G₂, and from
-- `TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC` for the Suzuki family, with the same shape of
-- definitions and equations.

public section

namespace TauCeti.ReeF4LieIndex

open DynkinType

variable (d : ReeF4LieIndex)

/-- The algebraic closure attached to an index in the type-`F₄` half-Frobenius family is an algebra
over the prime field of characteristic two. It has characteristic two, and an algebra structure
over `ZMod 2` is unique, so no choice is made here. -/
noncomputable instance algebraZModTwoClosure : Algebra (ZMod 2) d.1.Closure :=
  ZMod.algebra _ 2

noncomputable section

/-! ## The node correspondence -/

/-- **The carrier node corresponding to a Bourbaki-numbered node of `F₄`**, with the inverse
equivalence giving the correspondence back. The short-root type-`F₄` carrier numbers its nodes
exactly as Bourbaki does, nodes zero and one being the long simple roots, and its own
length-exchanging involution is the reversal of the chain, the same permutation the index selects,
so this is the rank equality `TauCeti.ReeF4LieIndex.rank_eq_four` and nothing more. -/
def carrierNode : Fin d.1.rank ≃ Fin 4 :=
  finCongr d.rank_eq_four

@[simp] theorem carrierNode_apply (i : Fin d.1.rank) :
    d.carrierNode i = finCongr d.rank_eq_four i :=
  (rfl)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group attached to an index in the type-`F₄` half-Frobenius family**: the points
of the explicit full-weight short-root type-`F₄` Chevalley carrier over the prime field of
characteristic two, taken over the algebraic closure of that prime field. It is infinite; no
finiteness, reductivity, pinning or maximality statement is attached to it, and it is not claimed
to be the points of the pinned simply connected group scheme of type `F₄`; no such identification
is available, as the module docstring explains. -/
abbrev AmbientGroup : Type := F4ShortRoot.PrimeField.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `F₄` diagram. It is
the carrier's numbered raising subgroup at the node that `carrierNode` names. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`. It is not a `simp` lemma: the simple-root-subgroup action equations of this
file are the normal forms, and unfolding to
`TauCeti.F4ShortRoot.PrimeField.rootSubgroupPoints` would keep them from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `F₄` root datum.** The character by
which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read in the same
node correspondence, is the `i`-th simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at
`F₄`. This is the sense in which the short-root carrier serves the diagram that this family names;
it is not a claim that the carrier is the pinned group of that diagram, no pinning being
constructed for it. -/
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    F4.rootGeneratorWeight valid_F4 (.inl (d.carrierNode i)) (d.carrierNode j) =
      (F4.simplyConnectedRootDatum valid_F4).root
        (F4.simpleIndex valid_F4 (finCongr d.rank_eq_four i)) (finCongr d.rank_eq_four j) := by
  rw [carrierNode_apply, carrierNode_apply]
  exact congrFun (F4.rootGeneratorWeight_inl_eq_root_simpleIndex valid_F4 _) _

/-! ## The Frobenius endomorphisms -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of an index in the type-`F₄`
half-Frobenius family**, for `q` the field order the index records. It is the map the Steinberg
endomorphism of the family squares to. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure

/-- The `q`-power Frobenius is the carrier's Frobenius at the exponent the index records. This is
its unfolding lemma; the definition itself stays sealed. It is deliberately not a `simp` lemma, the
action equations stated against it being the normal forms. -/
theorem frobenius_def :
    d.frobenius = F4ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- **The prime-field Frobenius endomorphism of the ambient group of an index in the type-`F₄`
half-Frobenius family**, the `p`-power map for `p = 2` the defining characteristic. It is the map
the half-Frobenius squares to, and it agrees with the `q`-power map above exactly at the Tits
index, whose field order is two. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.frobenius 1 d.1.Closure

/-- The prime-field Frobenius is the carrier's Frobenius at exponent one. This is its unfolding
lemma; the definition itself stays sealed. -/
theorem primeFrobenius_def :
    d.primeFrobenius = F4ShortRoot.PrimeField.frobenius 1 d.1.Closure :=
  (rfl)

/-- **The `q`-power Frobenius raises the parameter of every numbered simple root subgroup to its
`q`-th power**, for `q` the field order the index records. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  have hq : d.1.fieldOrder = 2 ^ d.1.fieldExponent := by
    rw [d.1.fieldOrder_eq_characteristic_pow, d.characteristic_eq_two]
  rw [hq, frobenius_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, ← simpleRootSubgroup_def]

/-- **The prime-field Frobenius raises the parameter of every numbered simple root subgroup to its
`p`-th power**, for `p = 2` the defining characteristic. -/
@[simp]
theorem primeFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.characteristic)) := by
  have hexp : (2 : ℕ) ^ (1 : ℕ) = d.1.characteristic := by
    rw [d.characteristic_eq_two, pow_one]
  rw [primeFrobenius_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, ← simpleRootSubgroup_def]
  exact congrArg
    (fun n : ℕ => d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ n))) hexp

/-! ## The half-Frobenius and the Steinberg endomorphism -/

/-- **The half-Frobenius of an index in the type-`F₄` half-Frobenius family**: the special isogeny
of its ambient group. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius is the carrier's special isogeny. -/
theorem halfFrobenius_def :
    d.halfFrobenius = F4ShortRoot.PrimeField.specialIsogeny d.1.Closure :=
  (rfl)

/-- **The square of the half-Frobenius is the prime-field Frobenius**, that is `τ ^ 2 = Frob_p` at
the defining characteristic `p = 2`. No uniqueness is claimed: nothing here shows that this
relation, or the action on the simple root subgroups, determines an endomorphism of the ambient
group. -/
@[simp]
theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius_def, primeFrobenius_def,
    F4ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem halfFrobenius_iterate_two_mul (k : ℕ) (g : d.AmbientGroup) :
    (⇑d.halfFrobenius)^[2 * k] g = F4ShortRoot.PrimeField.frobenius k d.1.Closure g := by
  induction k generalizing g with
  | zero => simp [F4ShortRoot.PrimeField.frobenius_zero]
  | succ k ih =>
      have hsucc : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have hk : k + 1 = 1 + k := Nat.add_comm k 1
      rw [hsucc, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        d.halfFrobenius_halfFrobenius, primeFrobenius_def, hk,
        F4ShortRoot.PrimeField.frobenius_add, MonoidHom.comp_apply]

/-- **The Steinberg endomorphism of an index in the type-`F₄` half-Frobenius family**: the odd
power `τ ^ (2m+1)` of the half-Frobenius, for `2m+1` the field exponent the index records. At the
Tits index that exponent is one and the map is the half-Frobenius itself. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  HPow.hPow (α := Monoid.End d.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- The Steinberg endomorphism is the `fieldExponent`-th power of the half-Frobenius. -/
theorem steinberg_def :
    d.steinberg =
      HPow.hPow (α := Monoid.End d.AmbientGroup) d.halfFrobenius d.1.fieldExponent :=
  (rfl)

/-- The Steinberg endomorphism acts as the `fieldExponent`-fold iterate of the half-Frobenius.
This is the form in which its two action equations below use `steinberg_def`. -/
theorem coe_steinberg : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] := by
  rw [steinberg_def]
  exact Monoid.End.coe_pow (M := d.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- **The square of the Steinberg endomorphism is the `q`-power Frobenius**: squaring the odd
power `τ ^ (2m+1)` doubles the exponent, and `τ ^ 2` is the prime-field Frobenius. -/
@[simp]
theorem steinberg_steinberg (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  have hpow := d.coe_steinberg
  have hdouble : d.1.fieldExponent + d.1.fieldExponent = 2 * d.1.fieldExponent := by ring
  rw [hpow, ← Function.iterate_add_apply, hdouble, halfFrobenius_iterate_two_mul, frobenius_def]

/-! ## The simple-root-subgroup action -/

-- Transporting a long-root statement along an equality of Dynkin types, rather than rewriting
-- the type of the node index that the statement depends on.
private theorem isLongSimpleRoot_iff_of_eq {t u : DynkinType} (h : t = u)
    (hu : ∀ j : Fin u.rank, u.IsLongSimpleRoot j ↔ (j : ℕ) < 2) (i : Fin t.rank) :
    t.IsLongSimpleRoot i ↔ (i : ℕ) < 2 := by
  subst h
  exact hu i

-- Reading a permutation transported along a rank equality back on the transported index.
private theorem finCongr_permCongr_apply {r : ℕ} (h : r = 4) (p : Equiv.Perm (Fin 4))
    (i : Fin r) :
    finCongr h (((finCongr h).symm.permCongr p) i) = p (finCongr h i) := by
  subst h
  simp

/-- The length permutation of the index is the `F₄` diagram reversal, transported along the rank
equality. Both introduction forms select it. -/
private theorem lengthPerm_eq :
    SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex =
      (finCongr d.rank_eq_four).symm.permCongr lengthPermF4 := by
  obtain (⟨m, hvalid, rfl⟩ | rfl) := d.exists_eq_of
  · exact SuzukiReeIndex.lengthPerm_reeF4 m hvalid
  · exact SuzukiReeIndex.lengthPerm_tits

/-- The length permutation of the index reverses the carrier's four nodes. -/
private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    d.carrierNode (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i) =
      lengthPermF4 (d.carrierNode i) := by
  rw [carrierNode_apply, carrierNode_apply, d.lengthPerm_eq]
  exact finCongr_permCongr_apply d.rank_eq_four lengthPermF4 i

/-- **The carrier nodes zero and one are the long simple roots.** The `F₄` diagram's long simple
roots are Bourbaki nodes zero and one, and the node correspondence keeps the numbering. -/
private theorem carrierNode_lt_two_iff (i : Fin d.1.rank) :
    ((d.carrierNode i : Fin 4) : ℕ) < 2 ↔ d.1.dynkinType.IsLongSimpleRoot i := by
  have hlong : d.1.dynkinType.IsLongSimpleRoot i ↔ (i : ℕ) < 2 :=
    isLongSimpleRoot_iff_of_eq d.dynkinType_eq
      (fun j => by rw [isLongSimpleRoot_F4]) i
  have hcarrier : ((d.carrierNode i : Fin 4) : ℕ) < 2 ↔ (i : ℕ) < 2 := by
    rw [carrierNode_apply]
    rfl
  exact hcarrier.trans hlong.symm

/-- The carrier's isogeny exponent is one at the two long carrier nodes and two at the two short
ones. -/
private theorem isogenyExponent_inl_eq (c : Fin 4) :
    F4ShortRoot.isogenyExponent (.inl c) = if (c : ℕ) < 2 then 1 else 2 := by
  revert c
  decide

/-- The carrier's length-exchanging involution is the `F₄` diagram reversal on the raising
generators. -/
private theorem isogenyReverse_inl (c : Fin 4) :
    F4ShortRoot.isogenyReverse (.inl c) = .inl (lengthPermF4 c) := by
  rw [lengthPermF4_apply]
  revert c
  decide

/-- The exponent of the index is the carrier's isogeny exponent at the corresponding node. -/
private theorem exponent_eq (i : Fin d.1.rank) :
    SuzukiReeIndex.exponent d.toSuzukiReeIndex i =
      F4ShortRoot.isogenyExponent (.inl (d.carrierNode i)) := by
  rw [isogenyExponent_inl_eq]
  have hnode := d.carrierNode_lt_two_iff i
  by_cases hi : d.1.dynkinType.IsLongSimpleRoot i
  · rw [SuzukiReeIndex.exponent_of_isLongSimpleRoot _ _ hi]
    split_ifs with h
    · rfl
    · exact absurd (hnode.mpr hi) h
  · rw [SuzukiReeIndex.exponent_of_not_isLongSimpleRoot _ _ hi, d.characteristic_eq_two]
    split_ifs with h
    · exact absurd (hnode.mp h) hi
    · rfl

/-- **The simple-root-subgroup action formula for the half-Frobenius at every numbered simple
root**, stated against the index's own length permutation and exponent:

```text
τ (x_{α i}(t)) = x_{α (lengthPerm i)}(t ^ exponent i).
```

The permutation reverses the four-node chain, exchanging the long and short simple roots, and the
exponent is `1` on a long one and the defining characteristic `2` on a short one, so this is the
carrier's pinning equation read through the Bourbaki numbering the index carries. -/
@[simp]
theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  obtain ⟨t, rfl⟩ : ∃ t : d.1.Closure, Multiplicative.ofAdd t = u :=
    ⟨Multiplicative.toAdd u, rfl⟩
  rw [simpleRootSubgroup_def, simpleRootSubgroup_def, halfFrobenius_def, d.exponent_eq i,
    F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, isogenyReverse_inl,
    d.carrierNode_lengthPerm i, toAdd_ofAdd]

/-- **The simple-root-subgroup action formula for the Steinberg endomorphism at every numbered
simple root.** It reverses the diagram exactly as the half-Frobenius does, and the remaining
iterate `τ ^ (2m)` acts on the parameter by the `p ^ m`-power Frobenius:

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
  have hpow := d.coe_steinberg
  have hodd : d.1.fieldExponent = 2 * SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1 :=
    SuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one d.toSuzukiReeIndex
  have hexp : d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex *
      SuzukiReeIndex.exponent d.toSuzukiReeIndex i =
        SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
          d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex :=
    Nat.mul_comm _ _
  have hchar : SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
      (2 : ℕ) ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex =
        SuzukiReeIndex.exponent d.toSuzukiReeIndex i *
          d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex := by
    rw [d.characteristic_eq_two]
  rw [hpow, hodd, Function.iterate_succ_apply, d.halfFrobenius_simpleRootSubgroup i u,
    d.halfFrobenius_iterate_two_mul, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, ← simpleRootSubgroup_def, hexp]
  congr 2
  rw [toAdd_ofAdd, ← pow_mul, hchar]

/-! ## The finite-group candidate -/

/-- The fixed subgroup of the Steinberg endomorphism attached to an index in the type-`F₄`
half-Frobenius family. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a Ree or Tits index of type F₄**: the derived
subgroup of the Steinberg fixed points, modulo the centre of that derived subgroup; at the Tits
index the fixed points are ²F₄(2) and the derived subgroup is the Tits group. No finiteness or
simplicity assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeF4LieIndex
