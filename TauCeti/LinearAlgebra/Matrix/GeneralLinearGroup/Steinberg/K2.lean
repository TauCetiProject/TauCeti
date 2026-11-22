/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Centrality

/-!
# Milnor's algebraic `K₂`

For an associative unital ring `R`, **Milnor's algebraic `K₂(R)`** is the kernel of the canonical
homomorphism `TauCeti.SteinbergGroup.toStableGL : St(R) →* GL_∞(R)`. By
`TauCeti.SteinbergGroup.ker_toStableGL_le_center`, `K₂(R)` lies in the center of `St(R)`, so it is
a commutative group, functorial in `R`, and fits into the exact sequence
`1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`.

## Main definitions

* `TauCeti.AlgebraicK2`: Milnor's algebraic `K₂(R) := ker (St(R) →* GL_∞(R))`.
* `TauCeti.AlgebraicK2.mk`, `TauCeti.AlgebraicK2.subtype`: the constructor from elements of
  `St(R)` mapping to `1` in `GL_∞(R)` and the canonical inclusion `K₂(R) →* St(R)`.
* `TauCeti.AlgebraicK2.map`: the homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism.

## Main results

* `TauCeti.AlgebraicK2.instCommGroup`: `AlgebraicK2 R` is a commutative group.
* `TauCeti.AlgebraicK2.map_id`, `TauCeti.AlgebraicK2.map_comp`, `TauCeti.AlgebraicK2.map_map`:
  functoriality of `AlgebraicK2`.
* `TauCeti.AlgebraicK2.mulExact_subtype_toStableGL`,
  `TauCeti.SteinbergGroup.mulExact_toStableGL_abelianizationOf`: exactness at `St(R)` and `GL_∞(R)`
  of `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Theorem 5.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.1.
-/

public section

noncomputable section

open Subgroup

namespace TauCeti

universe u

/-! ## Algebraic `K₂` -/

variable (R : Type u) [Ring R]

/-- **Algebraic `K₂`** of a ring `R`: the kernel of the canonical homomorphism
`St(R) →* GL_∞(R)`. By `TauCeti.SteinbergGroup.ker_toStableGL_le_center`, `K₂(R)` is central in
`St(R)` and hence a commutative group. -/
abbrev AlgebraicK2 : Type u :=
  (SteinbergGroup.toStableGL R).ker

namespace AlgebraicK2

/-- Algebraic `K₂(R)` is a commutative group, because `ker (St(R) →* GL_∞(R))` is central in
`St(R)`. -/
instance instCommGroup : CommGroup (AlgebraicK2 R) :=
  { (inferInstance : Group (SteinbergGroup.toStableGL R).ker) with
    mul_comm := fun a b ↦ Subtype.ext <|
      (Subgroup.mem_center_iff.mp (SteinbergGroup.ker_toStableGL_le_center (R := R) b.property)
        a.val) }

section

variable {R}

/-- Construct an element of `K₂(R)` from an element of `St(R)` in the kernel of `toStableGL R`. -/
def mk (z : SteinbergGroup R) (hz : SteinbergGroup.toStableGL R z = 1) : AlgebraicK2 R :=
  ⟨z, hz⟩

/-- The underlying element in `St(R)` of `AlgebraicK2.mk z hz` is `z`. -/
@[simp]
theorem coe_mk (z : SteinbergGroup R) (hz : SteinbergGroup.toStableGL R z = 1) :
    (mk z hz : SteinbergGroup R) = z :=
  (rfl)

/-- Every element of `K₂(R)` maps to `1` under `toStableGL R`. -/
@[simp]
theorem toStableGL_coe (x : AlgebraicK2 R) :
    SteinbergGroup.toStableGL R (x : SteinbergGroup R) = 1 :=
  x.property

end

/-- The canonical inclusion `K₂(R) →* St(R)`. -/
def subtype : AlgebraicK2 R →* SteinbergGroup R :=
  (SteinbergGroup.toStableGL R).ker.subtype

/-- Evaluating `AlgebraicK2.subtype R` yields the underlying element of `St(R)`. -/
@[simp]
theorem subtype_apply (x : AlgebraicK2 R) :
    subtype R x = (x : SteinbergGroup R) :=
  (rfl)

/-- Evaluating `AlgebraicK2.subtype R` on `AlgebraicK2.mk z hz` gives `z`. -/
theorem subtype_mk (z : SteinbergGroup R) (hz : SteinbergGroup.toStableGL R z = 1) :
    subtype R (mk z hz) = z :=
  (rfl)

/-- The canonical inclusion `K₂(R) →* St(R)` is injective. -/
theorem subtype_injective : Function.Injective (subtype R) :=
  Subtype.val_injective

/-- The composition of `toStableGL R` with `AlgebraicK2.subtype R` is trivial. -/
theorem toStableGL_comp_subtype :
    (SteinbergGroup.toStableGL R).comp (subtype R) = 1 :=
  MonoidHom.ext fun x ↦ x.property

/-- Every element in the image of `AlgebraicK2.subtype R` maps to `1` under `toStableGL R`. -/
theorem toStableGL_subtype (x : AlgebraicK2 R) :
    SteinbergGroup.toStableGL R (subtype R x) = 1 :=
  DFunLike.congr_fun (toStableGL_comp_subtype R) x

/-- Exactness at `St(R)` of `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`: the kernel of
`St(R) →* GL_∞(R)` equals the image of the inclusion `AlgebraicK2.subtype R : K₂(R) →* St(R)`. -/
theorem mulExact_subtype_toStableGL :
    Function.MulExact (subtype R) (SteinbergGroup.toStableGL R) := by
  rw [MonoidHom.mulExact_iff, subtype, Subgroup.range_subtype]

variable {R} {S T : Type*} [Ring S] [Ring T]

/-- The homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism `f : R →+* S`, restricting
`IndexedSteinbergGroup.map f` to the kernels. -/
def map (f : R →+* S) : AlgebraicK2 R →* AlgebraicK2 S :=
  ((IndexedSteinbergGroup.map f).comp (subtype R)).codRestrict _ fun x ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, subtype_apply,
      SteinbergGroup.toStableGL_map, toStableGL_coe, map_one]

/-- The inclusion `K₂ →* St` intertwines `AlgebraicK2.map` with `IndexedSteinbergGroup.map`. -/
theorem subtype_comp_map (f : R →+* S) :
    (subtype S).comp (map f) = (IndexedSteinbergGroup.map f).comp (subtype R) :=
  (rfl)

/-- Applying `AlgebraicK2.subtype` to `AlgebraicK2.map f x` yields
`IndexedSteinbergGroup.map f (subtype R x)`. -/
theorem subtype_map (f : R →+* S) (x : AlgebraicK2 R) :
    subtype S (map f x) = IndexedSteinbergGroup.map f (subtype R x) :=
  DFunLike.congr_fun (subtype_comp_map f) x

/-- The underlying element in `St(S)` of `AlgebraicK2.map f x` is
`IndexedSteinbergGroup.map f x`. -/
@[simp]
theorem coe_map_apply (f : R →+* S) (x : AlgebraicK2 R) :
    (map f x : SteinbergGroup S) = IndexedSteinbergGroup.map f x :=
  (rfl)

/-- Applying `AlgebraicK2.map f` to `AlgebraicK2.mk z hz` yields
`AlgebraicK2.mk (IndexedSteinbergGroup.map f z) _`. -/
@[simp]
theorem map_mk (f : R →+* S) (z : SteinbergGroup R)
    (hz : SteinbergGroup.toStableGL R z = 1) :
    map f (mk z hz) =
      mk (IndexedSteinbergGroup.map f z) (by rw [SteinbergGroup.toStableGL_map, hz, map_one]) :=
  (rfl)

/-- The identity ring homomorphism induces the identity of algebraic `K₂`. -/
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (AlgebraicK2 R) := by
  ext x
  simp

/-- Algebraic `K₂` is functorial in ring homomorphisms. -/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp

/-- Applying `AlgebraicK2.map f` followed by `AlgebraicK2.map g` equals
`AlgebraicK2.map (g.comp f)`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : AlgebraicK2 R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

end AlgebraicK2

namespace SteinbergGroup

/-- Exactness at `GL_∞(R)` of `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`: `toStableGL R` and
`Group.Abelianization.of` form an exact pair. -/
theorem mulExact_toStableGL_abelianizationOf :
    Function.MulExact (toStableGL R)
      (Group.Abelianization.of : StableGeneralLinearGroup R →* AlgebraicK1 R) :=
  MonoidHom.mulExact_iff.mpr (range_toStableGL_eq_ker_abelianizationOf R).symm

end SteinbergGroup

end TauCeti
