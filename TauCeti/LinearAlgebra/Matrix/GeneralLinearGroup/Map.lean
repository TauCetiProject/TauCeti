/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Change of scalars on general linear groups

`Matrix.GeneralLinearGroup.map f : GL n R →* GL n S` applies a ring hom `f : R →+* S` entrywise.
Mathlib gives its functoriality (`map_id`, `map_comp`, `map_comp_apply`) but says nothing about
injectivity or negation, nor about how the map interacts with the positive-determinant subgroup,
all of which a construction transporting a group of matrices along a change of scalars needs.

## Main results

* `Matrix.GeneralLinearGroup.map_injective`: entrywise application of an injective ring hom is
  injective on general linear groups.
* `Matrix.GeneralLinearGroup.map_neg`: change of scalars commutes with negation.
* `Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff`: the kernel of reduction modulo an ideal
  `I` consists of the matrices congruent to the identity matrix entrywise modulo `I`.
* `Matrix.GeneralLinearGroup.map_mem_glpos_iff`: a monotone ring hom preserves and reflects
  membership in the positive-determinant subgroups.
* `Matrix.SpecialLinearGroup.map_mapGL_int`: over `ℤ`, applying any ring hom `S →+* T` after
  `mapGL S` is `mapGL T`; for instance reducing `SL(n, ℤ)` modulo `m` and then modulo `n ∣ m` is
  reducing modulo `n`.
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

/-- Change of scalars commutes with negation. Together with Mathlib's `map_one`, `map_mul` and
`map_inv`, this lets subgroup constructions involving `-1`, such as `Subgroup.adjoinNegOne`, be
transported along `Matrix.GeneralLinearGroup.map f`. -/
@[simp]
protected theorem map_neg (f : R →+* S) (g : GL n R) :
    Matrix.GeneralLinearGroup.map f (-g) = -Matrix.GeneralLinearGroup.map f g := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

/-- The kernel of reduction `GL n R → GL n (R ⧸ I)`, the principal congruence level of `I`,
consists of the matrices congruent to the identity matrix entrywise modulo `I`. -/
theorem mem_ker_map_quotientMk_iff (I : Ideal R) {g : GL n R} :
    g ∈ (Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk I)).ker ↔
      ∀ i j, (g : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  rw [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.ext_iff]
  refine forall₂_congr fun i j ↦ ?_
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, ← Ideal.Quotient.eq,
    Matrix.one_apply, Matrix.one_apply, apply_ite (Ideal.Quotient.mk I), map_one, map_zero]

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

section Int

variable {S} {T : Type*} [CommRing T]

/-- **Over `ℤ`, change of scalars commutes with `mapGL`** along any ring hom `f : S →+* T`, since
there is only one ring hom out of `ℤ`. Unlike Mathlib's `Matrix.SpecialLinearGroup.map_mapGL`, this
needs no algebra structure on `T` over `S`; for instance it applies to `ZMod.castHom`. -/
@[simp]
theorem map_mapGL_int (f : S →+* T) (g : SpecialLinearGroup n ℤ) :
    Matrix.GeneralLinearGroup.map f (mapGL S g) = mapGL T g := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

/-- The homomorphism form of `Matrix.SpecialLinearGroup.map_mapGL_int`. -/
theorem map_comp_mapGL_int (f : S →+* T) :
    (Matrix.GeneralLinearGroup.map f).comp (mapGL (R := ℤ) (n := n) S) = mapGL T :=
  MonoidHom.ext (map_mapGL_int f)

end Int

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
