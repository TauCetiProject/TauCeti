/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Base
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation

/-!
# Comparing the type-C standard carrier with symplectic matrices

Over a field, the points of the full-weight type-`C_(n+1)` carrier are precisely the matrices in
`Sp_(2n+2)`. This file records how the existing multiplicative equivalence respects the numbered
positive simple-root subgroups and entrywise Frobenius. These are the two compatibilities needed to
compare constructions on the carrier with constructions on the symplectic group scheme.

## Main results

* `TauCeti.SpStd.pointsMulEquivGLSymplecticFin_simpleRootSubgroup`: the carrier and symplectic
  descriptions of every positive simple-root subgroup agree.
* `TauCeti.SpStd.pointsMulEquivGLSymplecticFin_frobenius`: the carrier equivalence intertwines
  entrywise Frobenius.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
-/

public section

namespace TauCeti.SpStd

universe u

variable (n : ℕ) {K : Type u} [Field K]

/-- **The carrier equivalence identifies every numbered positive simple-root subgroup with the
corresponding root subgroup of the standard symplectic group.** The last node is the long root
`2e_(n+1)` and every preceding node is the difference root `e_i - e_(i+1)`. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_simpleRootSubgroup
    (i : Fin (n + 1)) (a : Multiplicative K) :
    pointsMulEquivGLSymplecticFin n K (rootSubgroupPoints n (.inl i) K a) =
      (Symplectic.diagonalSimpleRootIndex (n + 1) i).hom a := by
  by_cases hi : (i : ℕ) + 1 < n + 1
  · have hilast : i ≠ Fin.last n := by
      intro h
      subst h
      simp only [Fin.val_last] at hi
      omega
    have hnext : next n i hilast = ⟨i + 1, hi⟩ := by
      apply Fin.ext
      exact val_next n i hilast
    rw [Symplectic.diagonalSimpleRootIndex_of_lt i hi]
    simpa only [GLSymplecticFin.RootSubgroupIndex.hom_difference,
      GLSymplecticFin.differenceShortRootHom_apply, hnext] using
      pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_of_ne_last n i hilast a
  · have hilast : i = Fin.last n := by
      apply Fin.ext
      have hle := i.isLt
      simp only [Fin.val_last]
      omega
    subst i
    rw [Symplectic.diagonalSimpleRootIndex_of_not_lt (Fin.last n) (by simp),
      pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_last,
      GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
      GLSymplecticFin.positiveLongRootTransvectionHom_apply]

variable (p k : ℕ) [ExpChar K p]

/-- **The carrier equivalence intertwines the carrier Frobenius with entrywise Frobenius on
symplectic matrices.** -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_frobenius (g : points n K) :
    pointsMulEquivGLSymplecticFin n K (frobenius n p k K g) =
      GLSymplecticFin.map (n + 1) K (iterateFrobenius K p k)
        (pointsMulEquivGLSymplecticFin n K g) := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map, coe_pointsMulEquivGLSymplecticFin_apply,
    coe_frobenius, coe_pointsMulEquivGLSymplecticFin_apply]

end TauCeti.SpStd
