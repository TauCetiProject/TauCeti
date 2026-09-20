/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure

/-!
# The ambient group of the Ree family of type `G₂`

The Ree family `²G₂(3^(2m+1))` is built inside the group of algebraic-closure-valued points of
the short-root type-`G₂` carrier over the prime field `𝔽₃`. That carrier is the closed subgroup
scheme of `GL₇` generated over `𝔽₃` by the reductions of the numbered simple root subgroups and
the weight torus of the Kostant toral closure of the seven-dimensional module `V(ϖ₁)`. This file
attaches it to a validated Ree index, together with its numbered positive simple root subgroups
and the two Frobenius endomorphisms used in the fixed-point construction.

The carrier is taken over `𝔽₃`, rather than obtained by base change from its integral toral
closure, because the characteristic-three exceptional isogeny is constructed on the prime-field
carrier. The base change of the integral closure is only known to contain this carrier; no
flatness statement identifying them is assumed here.

## The two Frobenius maps

`TauCeti.ReeG2LieIndex.frobenius` is the `q`-power Frobenius, where
`q = 3 ^ (2m+1)` is the field order of the index. The map
`TauCeti.ReeG2LieIndex.primeFrobenius` is the `3`-power Frobenius, and the former is the
`(2m+1)`-st power of the latter.

Neither is the family's Steinberg endomorphism. That endomorphism is the odd power
`τ ^ (2m+1)` of the exceptional isogeny `τ`, which exchanges the two root lengths and squares to
the prime-field Frobenius. Thus the prime-field Frobenius is the map `τ` squares to, and the
`q`-power Frobenius is the map the Steinberg endomorphism squares to.

The numbering is the Bourbaki numbering of the `G₂` diagram carried by the index. No renumbering
adapter is needed: every numbered object below is indexed by `Fin d.1.rank`, identified with the
carrier's `Fin 2` by `TauCeti.ReeG2LieIndex.rank_eq_two`.

The carrier is not identified with the pinned simply connected group scheme of type `G₂`.
Constructions on it transfer to that pinned group only along such an identification, once one is
proved. Nothing here asserts that the carrier is reductive, that its weight torus is maximal, or
that any group below is finite, perfect, or simple.

## Main definitions

* `TauCeti.ReeG2LieIndex.AmbientGroup`: the algebraic-closure-valued points of the carrier.
* `TauCeti.ReeG2LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.
* `TauCeti.ReeG2LieIndex.frobenius` and `TauCeti.ReeG2LieIndex.primeFrobenius`: the `q`-power and
  `3`-power Frobenius endomorphisms of the ambient group.

## Main results

* `TauCeti.ReeG2LieIndex.frobenius_simpleRootSubgroup` and
  `TauCeti.ReeG2LieIndex.primeFrobenius_simpleRootSubgroup` give the two Frobenius actions on the
  numbered root subgroups.
* `TauCeti.ReeG2LieIndex.frobenius_eq_primeFrobenius_pow` identifies the `q`-power Frobenius as
  the recorded iterate of the prime-field one.
* `TauCeti.ReeG2LieIndex.mem_fixedSubgroup_frobenius_iff` characterizes the `q`-rational points
  by their matrix entries.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX, for the numbering of `G₂`.
-/

/- Formal source: the declaration order, statements, and proof plan are adapted from the
characteristic-two sibling `TauCeti.ReeF4LieIndex` introduced in TauCetiProject/TauCeti#7666,
specialized to the seven-dimensional characteristic-three carrier. That sibling in turn follows
the earlier attachments `TauCeti.TypeE6LieIndex` and `TauCeti.RankTwoBLieIndex`. -/

public section

namespace TauCeti

namespace ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group attached to a validated Ree index of type `G₂`**: the points, over the
algebraic closure of the prime field, of the short-root type-`G₂` carrier over `𝔽₃`. It is a
subgroup of `GL₇` over that closure.

The carrier is independent of the parameter `m`; that parameter enters through the endomorphism
whose fixed points are taken. No finiteness or simplicity assertion is part of this definition. -/
abbrev AmbientGroup : Type := G2ShortRoot.PrimeField.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `G₂` diagram. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_two i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
node. This is the unfolding equation for the sealed definition.

It is deliberately not a simp lemma: the Frobenius action lemmas below are the normal forms for
the public API. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      G2ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_two i)) d.1.Closure :=
  (rfl)

/-! ## The Frobenius endomorphisms -/

/-- **The `q`-power Frobenius endomorphism of the ambient group**, where
`q = 3 ^ d.1.fieldExponent` is the field order of the Ree index.

This is not the Steinberg endomorphism; it is the map that the odd power of the exceptional
isogeny squares to. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure

/-- The Frobenius of a Ree index is the carrier's Frobenius at the exponent recorded by the
index. This is the unfolding equation for the sealed definition. -/
theorem frobenius_def :
    d.frobenius = G2ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 7) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 7) d.1.Closure) :
        Matrix (Fin 7) (Fin 7) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 7) d.1.Closure) :
        Matrix (Fin 7) (Fin 7) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.fieldOrder_eq_three_pow]
  exact G2ShortRoot.PrimeField.coe_frobenius_apply _ _ g r c

/-- **The Frobenius preserves each numbered simple-root subgroup and raises its parameter to the
`q`-th power**: `Frob_q (x_i(u)) = x_i(u ^ q)`. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints, d.fieldOrder_eq_three_pow]

/-- **A point is fixed by the `q`-power Frobenius exactly when all of its matrix entries lie in
the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, these are
the points of the carrier whose entries lie in `𝔽_q`.

This is not a simp lemma because membership in `TauCeti.fixedSubgroup` simplifies first to an
equality with the Frobenius image. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 7) d.1.Closure) :
        Matrix (Fin 7) (Fin 7) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, G2ShortRoot.PrimeField.frobenius_eq_self_iff]
  simp only [FiniteField.mem_frobeniusFixedSubalgebra, Nat.card_zmod,
    ValidLieTypeIndex.mem_fixedField, d.fieldOrder_eq_three_pow]

/-- **The prime-field Frobenius endomorphism of the ambient group**, cubing each matrix entry.
It is the map the exceptional isogeny squares to. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.frobenius 1 d.1.Closure

/-- The prime-field Frobenius is the carrier's first Frobenius iterate. This is the unfolding
equation for the sealed definition. -/
theorem primeFrobenius_def :
    d.primeFrobenius = G2ShortRoot.PrimeField.frobenius 1 d.1.Closure :=
  (rfl)

/-- The prime-field Frobenius acts by cubing every matrix entry. -/
@[simp]
theorem coe_primeFrobenius_apply (g : d.AmbientGroup) (r c : Fin 7) :
    ((d.primeFrobenius g : Matrix.GeneralLinearGroup (Fin 7) d.1.Closure) :
        Matrix (Fin 7) (Fin 7) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 7) d.1.Closure) :
        Matrix (Fin 7) (Fin 7) d.1.Closure) r c ^ 3 := by
  rw [primeFrobenius_def, G2ShortRoot.PrimeField.coe_frobenius_apply, pow_one]

/-- **The prime-field Frobenius preserves each numbered simple-root subgroup and cubes its
parameter**: `Frob_3 (x_i(u)) = x_i(u ^ 3)`. -/
@[simp]
theorem primeFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 3)) := by
  rw [primeFrobenius_def, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints, pow_one]

/-- **The `q`-power Frobenius is the recorded power of the prime-field Frobenius.** This is the
relation against which the square of the odd-power Steinberg endomorphism is measured. -/
theorem frobenius_eq_primeFrobenius_pow :
    d.frobenius = (show Monoid.End _ from d.primeFrobenius) ^ d.1.fieldExponent := by
  rw [primeFrobenius_def, frobenius_def, G2ShortRoot.PrimeField.frobenius_pow, Nat.one_mul]

end

end ReeG2LieIndex

end TauCeti
