/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Closure

/-!
# The ambient group of the Ree family of type `F₄`

The Ree family `²F₄(2^(2m+1))` is built inside the group of algebraic-closure-valued points of
the short-root type-`F₄` carrier over the prime field `𝔽₂`: the closed subgroup scheme of `GL₂₆`
generated over `𝔽₂` by the reductions of the numbered simple root subgroups and of the weight
torus of the Kostant toral closure of the twenty-six-dimensional module `V(ϖ₄)`. This file
attaches that carrier to a validated Ree index of type `F₄`, and supplies the numbered simple
root subgroups and the two Frobenius endomorphisms the family's construction runs against.

The carrier is taken over `𝔽₂` rather than over `ℤ` because the construction planned for the
family's Steinberg map lives in characteristic two: carrying an exceptional isogeny from matrices
to an endomorphism of the carrier needs the defining Hopf ideal to be the largest one killed by
the generator coordinate maps *over `𝔽₂`*; the base change of the integral toral closure is only
known to contain the carrier, new equations being possible over a base that is not flat.

## The two Frobenius maps

`TauCeti.ReeF4LieIndex.frobenius` is the `q`-power Frobenius, for `q = 2^(2m+1)` the field order
the index records, and `TauCeti.ReeF4LieIndex.primeFrobenius` is the `2`-power one; the former is
the `(2m+1)`-st power of the latter, `frobenius_eq_primeFrobenius_pow`.

Neither is the family's Steinberg endomorphism, which is not a Frobenius at all. In the
literature it is an odd power of an exceptional isogeny of the carrier, a map available only in
characteristic two that exchanges the two root lengths (Steinberg, §11). That isogeny is not
constructed here, no declaration below mentions one, and nothing in this file asserts its
existence or any relation between it and the two Frobenius maps; building it is the next step on
this branch. The two maps are named after what they are.
`TauCeti.ReeF4LieIndex.mem_fixedSubgroup_frobenius_iff` describes the group the `q`-power one
fixes: the points whose matrix entries lie in the field of definition `𝔽_q`.

The carrier is numbered by the Bourbaki numbering of the `F₄` diagram that the index itself
carries: the character by which the carrier's split torus rescales the parameter of its `i`-th
numbered raising subgroup is `TauCeti.DynkinType.rootGeneratorWeight` at `.inl i`, which
`TauCeti.ReeF4LieIndex.rootGeneratorWeight_eq_root_simpleIndex` identifies with the `i`-th simple
root of `TauCeti.DynkinType.simplyConnectedRootDatum` at `F₄`. No renumbering adapter is needed,
and every numbered object below is indexed by `Fin d.1.rank`, the upstream Bourbaki index type of
the index's own Dynkin type.

The carrier is not identified with the pinned simply connected group scheme of type `F₄`, and the
constructions below transfer to that group scheme only along such an identification, once one is
proved. Nothing here asserts that the carrier is reductive, that its weight torus is maximal, or
that any group below is finite, perfect, or simple.

## Main definitions

* `TauCeti.ReeF4LieIndex.AmbientGroup`: the algebraic-closure-valued points of the carrier, with
  the group structure it inherits as a subgroup of `GL₂₆`.
* `TauCeti.ReeF4LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.
* `TauCeti.ReeF4LieIndex.frobenius` and `TauCeti.ReeF4LieIndex.primeFrobenius`: the `q`-power and
  `2`-power Frobenius endomorphisms of the ambient group.

## Main results

* `TauCeti.ReeF4LieIndex.rootGeneratorWeight_eq_root_simpleIndex`: the character by which the
  carrier's torus rescales the parameter of the `i`-th simple-root subgroup is the `i`-th simple
  root of the `F₄` root datum, in the same Bourbaki numbering.
* `TauCeti.ReeF4LieIndex.frobenius_simpleRootSubgroup` and
  `TauCeti.ReeF4LieIndex.primeFrobenius_simpleRootSubgroup`: both Frobenius maps fix the numbering
  of a simple-root subgroup and raise its parameter, `Frob_q (x_i(u)) = x_i(u ^ q)` and
  `Frob_2 (x_i(u)) = x_i(u ^ 2)`.
* `TauCeti.ReeF4LieIndex.frobenius_eq_primeFrobenius_pow`: the `q`-power Frobenius is the
  `(2m+1)`-st power of the `2`-power one.
* `TauCeti.ReeF4LieIndex.mem_fixedSubgroup_frobenius_iff`: the `q`-power Frobenius fixes exactly
  the points whose matrix entries lie in the field of definition.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII, for the numbering of the
  `F₄` diagram the index's rank and root lengths are read in.
-/

-- The declaration order and the shape of the Frobenius API follow the sibling carrier
-- attachments `TauCeti.TypeE6LieIndex` and `TauCeti.RankTwoBLieIndex`, in
-- `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
-- `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`.

public section

namespace TauCeti

namespace ReeF4LieIndex

noncomputable section

variable (d : ReeF4LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated Ree index of type `F₄`**: the points,
over the algebraic closure of the prime field, of the short-root type-`F₄` carrier over `𝔽₂`. It
is a subgroup of `GL₂₆` over that closure.

It is infinite, and it is the same group for every Ree index of type `F₄`, the parameter `m`
entering only through the endomorphism whose fixed points are taken. No finiteness, reductivity,
pinning or maximality statement is attached to it, and it is not identified with the points of the
pinned simply connected `F₄` group scheme. -/
abbrev AmbientGroup : Type := F4ShortRoot.PrimeField.points d.1.Closure

/-- The classification recipe runs its fixed-point and quotient construction inside this group, so
it carries a group structure; the carrier being a subgroup of a general linear group supplies
it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `F₄` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure

-- Deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` and its prime-field counterpart
-- are the normal forms the equations of this file are stated against, and unfolding to
-- `TauCeti.F4ShortRoot.PrimeField.rootSubgroupPoints` would keep them from firing.
/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `F₄` root datum.** The character by
which the carrier's split weight torus rescales the parameter of `simpleRootSubgroup i` is the
`i`-th simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at `F₄`, in the same Bourbaki
numbering; `TauCeti.F4ShortRoot.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex` is the
carrier-level conjugation equation this character governs. This is the sense in which the carrier
serves the diagram the index names; it is not a claim that the carrier is the pinned group of that
diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i : Fin d.1.rank) :
    DynkinType.F4.rootGeneratorWeight DynkinType.valid_F4 (.inl (finCongr d.rank_eq_four i)) =
      (DynkinType.F4.simplyConnectedRootDatum DynkinType.valid_F4).root
        (DynkinType.F4.simpleIndex DynkinType.valid_F4 (finCongr d.rank_eq_four i)) := by
  simpa only [DynkinType.rank_F4] using
    DynkinType.F4.rootGeneratorWeight_inl_eq_root_simpleIndex DynkinType.valid_F4
      (finCongr d.rank_eq_four i)

/-! ## The Frobenius endomorphisms -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a Ree index of type `F₄`**, for
`q = 2^(2m+1)` the field order the index records.

It is not the family's Steinberg endomorphism: that map is not a Frobenius, and it is a later
step on this branch rather than anything constructed here. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure

-- Deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are
-- the normal forms the equations of this file are stated against, and unfolding to
-- `TauCeti.F4ShortRoot.PrimeField.frobenius` would keep them from firing.
/-- The Frobenius of a Ree index of type `F₄` is the carrier's Frobenius at the exponent the index
records. -/
theorem frobenius_def :
    d.frobenius = F4ShortRoot.PrimeField.frobenius d.1.fieldExponent d.1.Closure := (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 26) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.fieldOrder_eq_two_pow]
  exact F4ShortRoot.PrimeField.coe_frobenius_apply _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. In particular it does
not permute the numbered nodes: the length exchange of this family belongs to its Steinberg map,
which is not built here. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, d.fieldOrder_eq_two_pow]

-- As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp`
-- lemma: `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites
-- its left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF`
-- linter rejects the annotation.
/-- **A point of the ambient group is fixed by the `q`-power Frobenius exactly when all of its
matrix entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, these are the points of the carrier with entries in `𝔽_q`. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, F4ShortRoot.PrimeField.frobenius_eq_self_iff]
  simp only [FiniteField.mem_frobeniusFixedSubalgebra, Nat.card_zmod,
    ValidLieTypeIndex.mem_fixedField, d.fieldOrder_eq_two_pow]

/-- **The prime-field Frobenius endomorphism of the ambient group of a Ree index of type `F₄`**,
squaring each matrix entry. The `q`-power Frobenius is its `(2m+1)`-st power, by
`frobenius_eq_primeFrobenius_pow`. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.frobenius 1 d.1.Closure

-- Deliberately not a `simp` lemma, for the reason `frobenius_def` is not.
/-- The prime-field Frobenius of a Ree index of type `F₄` is the carrier's Frobenius at exponent
one. -/
theorem primeFrobenius_def :
    d.primeFrobenius = F4ShortRoot.PrimeField.frobenius 1 d.1.Closure := (rfl)

/-- The prime-field Frobenius acts on the ambient group by squaring every matrix entry. -/
@[simp]
theorem coe_primeFrobenius_apply (g : d.AmbientGroup) (r c : Fin 26) :
    ((d.primeFrobenius g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c ^ 2 := by
  rw [primeFrobenius_def, F4ShortRoot.PrimeField.coe_frobenius_apply, pow_one]

/-- **The prime-field Frobenius fixes the Bourbaki numbering of a simple-root subgroup and squares
its parameter**, that is, `Frob_2 (x_i(u)) = x_i(u ^ 2)`. -/
@[simp]
theorem primeFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2)) := by
  rw [primeFrobenius_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, pow_one]

-- The `show` reads the prime-field Frobenius in the endomorphism monoid of the ambient group,
-- there being no power operation on `MonoidHom` itself; this is the form
-- `TauCeti.F4ShortRoot.PrimeField.frobenius_pow` states the carrier's iteration law in.
/-- **The `q`-power Frobenius is the `(2m+1)`-st power of the prime-field Frobenius**, the
exponent being the one the index records. -/
theorem frobenius_eq_primeFrobenius_pow :
    d.frobenius = (show Monoid.End _ from d.primeFrobenius) ^ d.1.fieldExponent := by
  rw [primeFrobenius_def, frobenius_def, F4ShortRoot.PrimeField.frobenius_pow, Nat.one_mul]

end

end ReeF4LieIndex

end TauCeti
