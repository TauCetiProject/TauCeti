/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Change of scalars on general linear groups

`Matrix.GeneralLinearGroup.map f : GL n R →* GL n S` applies a ring hom `f : R →+* S` entrywise.
Mathlib gives its functoriality (`map_id`, `map_comp`, `map_comp_apply`) but says nothing about
injectivity or negation, nor about how the map interacts with the positive-determinant subgroup,
all of which a construction transporting a group of matrices along a change of scalars needs.

## Main results

* `Matrix.GeneralLinearGroup.map_injective`: entrywise application of an injective ring hom is
  injective on general linear groups.
* `Matrix.GeneralLinearGroup.map_surjective`: a surjective ring hom that reflects units is
  surjective on general linear groups.
* `Matrix.GeneralLinearGroup.map_neg`: change of scalars commutes with negation.
* `Matrix.GeneralLinearGroup.map_mem_glpos_iff`: a monotone ring hom preserves and reflects
  membership in the positive-determinant subgroups.
* `Subgroup.map_mapGL`: extending a subgroup of `SL(n, R)` to `GL n S` and then to `GL n T`
  agrees with extending it directly to `GL n T`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R S : Type*} [DecidableEq n] [Fintype n] [CommRing R] [CommRing S]

/-- **Entrywise application of an injective ring hom is injective on `GL n`.** A matrix over `R`
is determined by its image over `S`, and a unit by its underlying matrix. -/
theorem map_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Units.map_injective (Matrix.map_injective hf)

/-- **Invertible matrices lift along a surjective local ring hom**: if `f` is surjective and
reflects units, then entrywise application of `f` is surjective on general linear groups. -/
theorem map_surjective {f : R →+* S} [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) f) := by
  intro g
  choose a ha using fun i j ↦ hf ((g : Matrix n n S) i j)
  set M : Matrix n n R := Matrix.of a
  have hM : M.map f = g := by
    ext i j
    simp [M, ha]
  have hunit : IsUnit M.det := (isUnit_map_iff f M.det).1 <| by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  exact ⟨Matrix.GeneralLinearGroup.mk'' M hunit, Units.ext <| by
    simpa only [val_map_apply, val_mk''] using hM⟩

/-- Change of scalars commutes with negation. Together with Mathlib's `map_one`, `map_mul` and
`map_inv`, this lets subgroup constructions involving `-1`, such as `Subgroup.adjoinNegOne`, be
transported along `Matrix.GeneralLinearGroup.map f`. -/
@[simp]
protected theorem map_neg (f : R →+* S) (g : GL n R) :
    Matrix.GeneralLinearGroup.map f (-g) = -Matrix.GeneralLinearGroup.map f g := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

section StrictOrdered

variable [LinearOrder R] [IsStrictOrderedRing R] [LinearOrder S] [IsStrictOrderedRing S]

/-- A monotone change of scalars preserves and reflects positive determinant.

This characterizes membership in the positive-determinant subgroup after applying
`Matrix.GeneralLinearGroup.map f`. Monotonicity suffices: a unit determinant cannot map to zero.
For `f = algebraMap ℚ ℝ`, use `Rat.cast_strictMono.monotone`. -/
-- Not a simp lemma: `Matrix.mem_glpos` already rewrites membership to determinant positivity.
theorem map_mem_glpos_iff {f : R →+* S} (hf : Monotone f) {g : GL n R} :
    g.map f ∈ GLPos n S ↔ g ∈ GLPos n R := by
  rw [mem_glpos, mem_glpos, GeneralLinearGroup.map_det, Units.coe_map]
  constructor
  · intro h
    exact hf.reflect_lt (by simpa only [MonoidHom.coe_ofClass, map_zero] using h)
  · intro h
    exact lt_of_le_of_ne (by simpa using hf h.le) (Ne.symm (g.det.isUnit.map f).ne_zero)

end StrictOrdered

end Matrix.GeneralLinearGroup

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R] (S : Type*) [CommRing S]
  [Algebra R S]

/-- The image of an element of `SL(n, R)` in `GL n S` has determinant `1` as a matrix. -/
theorem det_coe_mapGL (g : SpecialLinearGroup n R) :
    ((mapGL S g : GL n S) : Matrix n n S).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]

/-- The image of an element of `SL(n, R)` in `GL n S` has positive determinant, when `S` is an
ordered ring. -/
theorem det_coe_mapGL_pos [PartialOrder S] [IsStrictOrderedRing S] (g : SpecialLinearGroup n R) :
    0 < ((mapGL S g : GL n S) : Matrix n n S).det := by
  rw [det_coe_mapGL]
  exact one_pos

end Matrix.SpecialLinearGroup

namespace Subgroup

open Matrix.SpecialLinearGroup in
/-- Extending a subgroup of the special linear group first to `S` and then to `T` agrees with
extending it directly to `T`. This is the subgroup form of `Matrix.SpecialLinearGroup.map_mapGL`,
used for instance for integral levels extended to `ℚ` and then to `ℝ`. -/
@[simp] theorem map_mapGL {n R S T : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (G : Subgroup (Matrix.SpecialLinearGroup n R)) :
    (G.map (mapGL S)).map (Matrix.GeneralLinearGroup.map (algebraMap S T)) = G.map (mapGL T) := by
  rw [Subgroup.map_map]
  exact congrArg (Subgroup.map · G) (MonoidHom.ext fun g ↦ Matrix.SpecialLinearGroup.map_mapGL g)

end Subgroup
