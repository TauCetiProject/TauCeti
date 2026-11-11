/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Lattice points of cones

The inverse image of a cone under an additive map is an additive monoid of lattice
points. Membership is unchanged by multiplication by a positive integer. In
particular, when a positive multiple of a primitive vector lies in the cone,
the primitive vector itself lies in the cone. These statements require neither
rationality nor salience, and the additive map need not be injective.
The monoid construction allows ordered semirings; the positive-multiple
characterizations use an ordered field.

Adapted from `Mei/Geometry/Convex/Cone/LatticePoints.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace PointedCone

variable {R N V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid N] [AddCommMonoid V] [Module R V]

/-- The additive monoid of vectors whose images under `i` belong to `σ`. -/
def latticePoints (σ : PointedCone R V) (i : N →+ V) : AddSubmonoid N :=
  σ.toAddSubmonoid.comap i

/-- The lattice-point monoid is the inverse image of the cone's additive monoid. -/
theorem latticePoints_def (σ : PointedCone R V) (i : N →+ V) :
    σ.latticePoints i = σ.toAddSubmonoid.comap i := (rfl)

/-- A vector is a lattice point of a cone exactly when its image belongs to the cone. -/
@[simp]
theorem mem_latticePoints {σ : PointedCone R V} {i : N →+ V} {n : N} :
    n ∈ σ.latticePoints i ↔ i n ∈ σ := Iff.rfl

/-- Enlarging the cone enlarges its lattice-point monoid. -/
@[gcongr]
theorem latticePoints_mono {σ τ : PointedCone R V} (h : σ ≤ τ) (i : N →+ V) :
    σ.latticePoints i ≤ τ.latticePoints i := fun _ hn ↦ h hn

/-- The lattice-point monoid is monotone in the cone. -/
theorem latticePoints_monotone (i : N →+ V) :
    Monotone (fun σ : PointedCone R V => σ.latticePoints i) := fun _ _ h ↦ latticePoints_mono h i

/-- Lattice points commute with intersection of cones. -/
@[simp]
theorem latticePoints_inf (σ τ : PointedCone R V) (i : N →+ V) :
    (σ ⊓ τ).latticePoints i = σ.latticePoints i ⊓ τ.latticePoints i := by
  ext n
  simp

variable {K W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommMonoid W] [Module K W]

/-- A positive natural multiple belongs to the lattice-point monoid exactly when
the original vector does. -/
theorem nsmul_mem_latticePoints_iff (σ : PointedCone K W) (i : N →+ W)
    {a : ℕ} (ha : 0 < a) (n : N) :
    a • n ∈ σ.latticePoints i ↔ n ∈ σ.latticePoints i := by
  simp only [mem_latticePoints, map_nsmul, ← Nat.cast_smul_eq_nsmul K]
  exact σ.smul_mem_iff (by exact_mod_cast ha)

/-- A positive integer multiple belongs to the lattice-point monoid exactly when
the original vector does. -/
theorem zsmul_mem_latticePoints_iff {G U : Type*} [AddCommGroup G]
    [AddCommGroup U] [Module K U]
    (σ : PointedCone K U) (i : G →+ U) {a : ℤ} (ha : 0 < a) (n : G) :
    a • n ∈ σ.latticePoints i ↔ n ∈ σ.latticePoints i := by
  simp only [mem_latticePoints, map_zsmul, ← Int.cast_smul_eq_zsmul K]
  exact σ.smul_mem_iff (by exact_mod_cast ha)

end PointedCone
