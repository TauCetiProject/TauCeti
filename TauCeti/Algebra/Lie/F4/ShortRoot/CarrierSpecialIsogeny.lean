/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Frobenius
public import TauCeti.Algebra.Lie.F4.ShortRoot.SpecialIsogeny

/-!
# The special isogeny on the numbered root subgroups of the short-root type-F4 carrier

`TauCeti.F4ShortRoot.specialIsogenyMatrix` is the matrix formula for the special isogeny `τ` of
type `F4` in characteristic two, and `TauCeti.F4ShortRoot.points` realizes the short-root
carrier's points as a subgroup of `GL₂₆`. This file reads the formula on the carrier's eight
numbered simple root subgroups: the matrix of a numbered simple-root point is the numbered simple
root element matrix of the same parameter, so the pinning equations and the square relation
proved for those matrices become statements about the carrier's own root subgroup points and its
own Frobenius.

Only the numbered simple root subgroups are covered. The formula is not shown to be
multiplicative, to carry points of the carrier to points of the carrier, or to have any property
at all at a point that is not one of the numbered simple root elements; the square relation
below is the one on those elements, not an identity of endomorphisms. The carrier is not
identified with the pinned simply connected group scheme of type `F4`, and constructions made
here transfer to that group scheme only along such an identification.

## Main results

* `TauCeti.F4ShortRoot.coe_rootSubgroupPoints_eq_rootElementMatrix`: the matrix of a numbered
  simple-root point is the numbered simple root element matrix.
* `TauCeti.F4ShortRoot.specialIsogenyMatrix_rootSubgroupPoints`: **the pinning equations** on the
  carrier's numbered simple root subgroups, exchanging the two root lengths.
* `TauCeti.F4ShortRoot.specialIsogenyMatrix_specialIsogenyMatrix_rootSubgroupPoints`: **the
  square relation** on those subgroups, against the carrier's own Frobenius at exponent one.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3 and §13.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe v

variable {A : Type v} [CommRing A] [CharP A 2]

omit [CharP A 2] in
/-- The matrix of a numbered simple-root point of the short-root carrier is the numbered simple
root element matrix of the same parameter. -/
-- Not a `simp` lemma: `TauCeti.F4ShortRoot.coe_rootSubgroupPoints` already rewrites the coercion
-- of a numbered simple-root point into the Kostant root-subgroup matrix, so it reaches the
-- left-hand side of this equation, and of the two below, before any of them can fire.
theorem coe_rootSubgroupPoints_eq_rootElementMatrix (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    ((rootSubgroupPoints k A u : GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) =
      rootElementMatrix k (Multiplicative.toAdd u) := by
  rw [coe_rootSubgroupPoints_eq, rootElementMatrix_def]

/-- **The pinning equations of the special isogeny on the carrier's numbered simple root
subgroups**: the numbered simple-root point of index `k` and parameter `u` is carried to the one
of the length-exchanged index, with the parameter raised to the length exponent. -/
-- Not a `simp` lemma, for the reason given at `coe_rootSubgroupPoints_eq_rootElementMatrix`.
theorem specialIsogenyMatrix_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    specialIsogenyMatrix
        (rootSubgroupPoints k A u : GeneralLinearGroup (Fin 26) A) =
      ((rootSubgroupPoints (isogenyReverse k) A
          (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) :
        GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
  rw [coe_rootSubgroupPoints_eq_rootElementMatrix]
  exact specialIsogenyMatrix_of_coe_eq k (Multiplicative.toAdd u)
    (coe_rootSubgroupPoints_eq_rootElementMatrix k u)

/-- **The square relation on the carrier's numbered simple root subgroups**: applying the special
isogeny twice to a numbered simple-root point gives the carrier's Frobenius at exponent one of
that point. -/
-- Not a `simp` lemma, for the reason given at `coe_rootSubgroupPoints_eq_rootElementMatrix`.
theorem specialIsogenyMatrix_specialIsogenyMatrix_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4)
    (u : Multiplicative A) :
    specialIsogenyMatrix
        (rootSubgroupPoints (isogenyReverse k) A
          (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) :
          GeneralLinearGroup (Fin 26) A) =
      ((frobenius 2 1 A (rootSubgroupPoints k A u) : GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  rw [specialIsogenyMatrix_specialIsogenyMatrix k (Multiplicative.toAdd u)
      (coe_rootSubgroupPoints_eq_rootElementMatrix k u)
      (specialIsogenyMatrix_rootSubgroupPoints k u).symm,
    rootElementMatrix_map_pow_two, frobenius_rootSubgroupPoints,
    coe_rootSubgroupPoints_eq_rootElementMatrix]
  norm_num

end TauCeti.F4ShortRoot
