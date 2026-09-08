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
# Frobenius fixed points of the `E₇` minuscule carrier

`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE7/Basic.lean` attaches to a validated `E₇` index the
points of the explicit full-weight minuscule carrier `TauCeti.E7Minuscule.groupScheme`, with its
Bourbaki-numbered simple root subgroups. This file records the carrier's `q`-power Frobenius, its
fixed points, and the derived-subgroup-modulo-centre quotient of those fixed points.

The carrier Frobenius preserves the numbered simple root subgroups and split weight torus, raising
their parameters to the `q`-th power. Its fixed points are precisely the carrier points whose
matrix entries lie in the copy `TauCeti.ValidLieTypeIndex.fixedField` of `𝔽_q` inside the closure.

Nothing here identifies the minuscule carrier with the pinned simply connected
Chevalley--Demazure group scheme of type `E₇`. Consequently this file does not define the
Steinberg endomorphism or candidate group of `E₇(q)`: those declarations require the Layer 9
pinned carrier that milestone L0 of the CFSG roadmap consumes. The results here are carrier-side
computations that can be transported when that identification exists. Nor is the fixed-point
quotient asserted to be finite, perfect, or simple.

## Main declarations

* `TauCeti.TypeE7LieIndex.minusculeFrobenius`: the `q`-power Frobenius of the minuscule carrier.
* `TauCeti.TypeE7LieIndex.MinusculeFixedPointQuotient`: the carrier-side quotient
  `[H, H] / Z([H, H])` of its fixed points.

## Main results

* `TauCeti.TypeE7LieIndex.minusculeFrobenius_simpleRootSubgroup` and
  `TauCeti.TypeE7LieIndex.minusculeFrobenius_weightTorusPoints`: Frobenius raises the parameters
  of the carrier's numbered root subgroups and weight torus to the `q`-th power.
* `TauCeti.TypeE7LieIndex.coe_minusculeFrobenius_apply`: Frobenius raises every matrix coefficient
  to the `q`-th power.
* `TauCeti.TypeE7LieIndex.mem_fixedSubgroup_minusculeFrobenius_iff`: a carrier point is fixed
  exactly when its entries lie in the field of definition.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

public section

namespace TauCeti

namespace TypeE7LieIndex

noncomputable section

variable (d : TypeE7LieIndex)

/-! ## Frobenius on the minuscule carrier -/

/-- The `q`-power Frobenius of the `E₇` minuscule carrier, for `q` the field order recorded by the
index. This is the carrier-side map that can be transported to the Steinberg endomorphism once
Layer 9 identifies the carrier with the pinned simply connected `E₇` group scheme. -/
def minusculeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  E7Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The minuscule-carrier Frobenius uses the exponent recorded by the `E₇` index. This is its
unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `minusculeFrobenius_simpleRootSubgroup`,
`minusculeFrobenius_weightTorusPoints` and `coe_minusculeFrobenius_apply` are the normal forms the
equations of this file are stated against. -/
theorem minusculeFrobenius_def :
    d.minusculeFrobenius =
      E7Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The minuscule-carrier Frobenius raises every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_minusculeFrobenius_apply (g : d.AmbientGroup) (r c : Fin 56) :
    ((d.minusculeFrobenius g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [minusculeFrobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact E7Minuscule.coe_frobenius_apply _ _ _ g r c

/-- **The minuscule-carrier Frobenius fixes the Bourbaki numbering of a simple-root subgroup and
raises its parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. -/
@[simp]
theorem minusculeFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.minusculeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [minusculeFrobenius_def, simpleRootSubgroup_def,
    E7Minuscule.frobenius_rootSubgroupPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The minuscule-carrier Frobenius preserves the weight torus and raises each coordinate to the
`q`-th power**, that is, `Frob_q (t(s)) = t(s ^ q)`. -/
@[simp]
theorem minusculeFrobenius_weightTorusPoints (s : Fin 7 → d.1.Closureˣ) :
    d.minusculeFrobenius (E7Minuscule.weightTorusPoints d.1.Closure s) =
      E7Minuscule.weightTorusPoints d.1.Closure (s ^ d.1.fieldOrder) := by
  rw [minusculeFrobenius_def, E7Minuscule.frobenius_weightTorusPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The fixed subgroup contains the `𝔽_q`-points of every numbered simple root subgroup.** A
simple-root point `x_i(u)` is fixed by the carrier Frobenius as soon as its parameter lies in the
field of definition, so the group `H` below is at least as large as the subgroup those points
generate. -/
theorem simpleRootSubgroup_mem_fixedSubgroup_minusculeFrobenius (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) (hu : Multiplicative.toAdd u ∈ d.1.fixedField) :
    d.simpleRootSubgroup i u ∈ fixedSubgroup d.minusculeFrobenius := by
  rw [mem_fixedSubgroup, minusculeFrobenius_simpleRootSubgroup,
    ValidLieTypeIndex.mem_fixedField.mp hu, ofAdd_toAdd]

/-- **A point of the minuscule carrier is fixed by Frobenius exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the group `H` cut out below is therefore the group of points of the minuscule carrier
whose entries lie in `𝔽_q`.

This is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side through `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects the annotation. -/
theorem mem_fixedSubgroup_minusculeFrobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.minusculeFrobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, minusculeFrobenius_def, E7Minuscule.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The carrier-side fixed-point quotient -/

/-- The derived subgroup of the minuscule Frobenius fixed points, modulo the centre of that derived
subgroup. This is not the candidate group of `E₇(q)` without the Layer 9 identification of the
minuscule carrier with the pinned simply connected `E₇` group scheme. -/
abbrev MinusculeFixedPointQuotient : Type := FixedPointCandidate d.minusculeFrobenius

/-- The quotient construction supplies its group structure. -/
example : _root_.Group d.MinusculeFixedPointQuotient := inferInstance

end

end TypeE7LieIndex

end TauCeti
