/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Basic

/-!
# The Steinberg endomorphism and candidate group of `E₇(q)`

`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE7/Basic.lean` attaches to a validated `E₇` index the
points of the explicit full-weight minuscule carrier `TauCeti.E7Minuscule.groupScheme`, with its
Bourbaki-numbered simple root subgroups. This file forms the Steinberg endomorphism of the
untwisted family `E₇(q)` on that carrier, which is its `q`-power Frobenius, records its fixed
points, and names the family's candidate group: the derived subgroup of those fixed points modulo
its centre.

The carrier Frobenius preserves the numbered simple root subgroups and split weight torus, raising
their parameters to the `q`-th power. Its fixed points are precisely the carrier points whose
matrix entries lie in the copy `TauCeti.ValidLieTypeIndex.fixedField` of `𝔽_q` inside the closure.

The minuscule carrier is not identified with the pinned simply connected Chevalley--Demazure group
scheme of type `E₇`, and nothing here identifies the two: the constructions below transfer to that
pinned group only along such an identification, once one is proved. Nor is the candidate group
asserted to be finite, perfect, or simple.

## Main declarations

* `TauCeti.TypeE7LieIndex.steinberg`: the Steinberg endomorphism of `E₇(q)`, the `q`-power
  Frobenius of the minuscule carrier.
* `TauCeti.TypeE7LieIndex.Group`: the candidate group `FixedPointCandidate steinberg`, the
  quotient `[H, H] / Z([H, H])` of the fixed points `H` of `steinberg`.

## Main results

* `TauCeti.TypeE7LieIndex.steinberg_simpleRootSubgroup` and
  `TauCeti.TypeE7LieIndex.steinberg_weightTorusPoints`: Frobenius raises the parameters
  of the carrier's numbered root subgroups and weight torus to the `q`-th power.
* `TauCeti.TypeE7LieIndex.coe_steinberg_apply`: Frobenius raises every matrix coefficient
  to the `q`-th power.
* `TauCeti.TypeE7LieIndex.mem_fixedSubgroup_steinberg_iff`: a carrier point is fixed
  exactly when its entries lie in the field of definition.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

-- Reinstates the declarations of https://github.com/TauCetiProject/TauCeti/pull/5968 under the
-- names the CFSG roadmap fixes for every branch.

public section

namespace TauCeti

namespace TypeE7LieIndex

noncomputable section

variable (d : TypeE7LieIndex)

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of `E₇(q)` on the minuscule carrier**: the `q`-power Frobenius of
the carrier, for `q` the field order recorded by the index. The family is untwisted, so its
Steinberg endomorphism is the Frobenius itself, with no graph automorphism. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  E7Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg endomorphism is the carrier Frobenius at the exponent recorded by the `E₇`
index. -/
-- Not `@[simp]`: `steinberg_simpleRootSubgroup`, `steinberg_weightTorusPoints`
-- and `coe_steinberg_apply` are the normal forms the equations of this file are stated
-- against, and unfolding to the carrier's Frobenius would keep them from firing.
theorem steinberg_def :
    d.steinberg =
      E7Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The minuscule-carrier Frobenius raises every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_steinberg_apply (g : d.AmbientGroup) (r c : Fin 56) :
    ((d.steinberg g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [steinberg_def, d.1.fieldOrder_eq_characteristic_pow]
  exact E7Minuscule.coe_frobenius_apply _ _ _ g r c

/-- **The minuscule-carrier Frobenius fixes the Bourbaki numbering of a simple-root subgroup and
raises its parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, simpleRootSubgroup_def,
    E7Minuscule.frobenius_rootSubgroupPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The minuscule-carrier Frobenius preserves the weight torus and raises each coordinate to the
`q`-th power**, that is, `Frob_q (t(s)) = t(s ^ q)`. -/
@[simp]
theorem steinberg_weightTorusPoints (s : Fin 7 → d.1.Closureˣ) :
    d.steinberg (E7Minuscule.weightTorusPoints d.1.Closure s) =
      E7Minuscule.weightTorusPoints d.1.Closure (s ^ d.1.fieldOrder) := by
  rw [steinberg_def, E7Minuscule.frobenius_weightTorusPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The fixed subgroup contains the `𝔽_q`-points of every numbered simple root subgroup.** A
simple-root point `x_i(u)` is fixed by the carrier Frobenius as soon as its parameter lies in the
field of definition, so the group `H` below is at least as large as the subgroup those points
generate. -/
theorem simpleRootSubgroup_mem_fixedSubgroup_steinberg (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) (hu : Multiplicative.toAdd u ∈ d.1.fixedField) :
    d.simpleRootSubgroup i u ∈ fixedSubgroup d.steinberg := by
  rw [mem_fixedSubgroup, steinberg_simpleRootSubgroup,
    ValidLieTypeIndex.mem_fixedField.mp hu, ofAdd_toAdd]

/-- **The fixed subgroup contains the weight-torus points with `𝔽_q` coordinates.** A torus point
`t(s)` is fixed by the carrier Frobenius as soon as each of its coordinates lies in the field of
definition. -/
theorem weightTorusPoints_mem_fixedSubgroup_steinberg (s : Fin 7 → d.1.Closureˣ)
    (hs : ∀ k, ((s k : d.1.Closure)) ∈ d.1.fixedField) :
    E7Minuscule.weightTorusPoints d.1.Closure s ∈ fixedSubgroup d.steinberg := by
  rw [mem_fixedSubgroup, steinberg_weightTorusPoints]
  congr 1
  funext k
  apply Units.ext
  simpa using ValidLieTypeIndex.mem_fixedField.mp (hs k)

/-- **A point of the minuscule carrier is fixed by Frobenius exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the group `H` cut out below is therefore the group of points of the minuscule carrier
whose entries lie in `𝔽_q`. -/
-- Not `@[simp]`: `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp`
-- rewrites this left-hand side through `MonoidHom.mem_eqLocus` and the `simpNF` linter rejects
-- the annotation.
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, steinberg_def, E7Minuscule.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The finite-group candidate -/

/-- **The finite-simple-group candidate attached to an `E₇` index**: the derived subgroup of the
Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or simplicity
assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- The quotient construction supplies its group structure. -/
example : _root_.Group d.Group := inferInstance

end

end TypeE7LieIndex

end TauCeti
