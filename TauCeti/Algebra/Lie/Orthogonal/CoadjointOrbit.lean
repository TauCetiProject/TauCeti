/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares

/-!
# The coadjoint orbits of the rotation group `SO(3)`

The orthogonal group `O(n) = Matrix.orthogonalGroup n R` acts on its Lie algebra
`so(n) = LieAlgebra.Orthogonal.so n R` of skew-symmetric matrices by conjugation,
`Ad_g A = g A g⁻¹ = g A gᵀ` (`TauCeti.orthogonalAdjointRepresentation`), by Lie algebra
automorphisms (`TauCeti.orthogonalAdjointRepresentation_lie`). The coadjoint action is its dual,
`(Ad*_g ν)(A) = ν (Ad_(g⁻¹) A)` (`TauCeti.orthogonalCoadjointRepresentation`), as for the
coadjoint representation of a Lie group. Both restrict to the special orthogonal group
`SO(n) = Matrix.specialOrthogonalGroup n R` (`TauCeti.specialOrthogonalAdjointRepresentation`,
`TauCeti.specialOrthogonalCoadjointRepresentation`).

For `n = 3`, identify `so(3)` with `R³` by the hat map `u ↦ û` (`TauCeti.soThreeEquiv`) and
`so(3)*` with `R³` by the dot product, `ν_m(û) = m ⬝ᵥ u` (`TauCeti.soThreeDualEquiv`). A rotation
conjugates `û` to `(g u)^` (`TauCeti.mul_crossProductMatrix_mul_transpose`), so in these
coordinates both actions are the standard action of `SO(3)` on `R³`:

`Ad_g û = (g u)^`, `Ad*_g ν_m = ν_(g m)`

(`TauCeti.specialOrthogonalAdjointRepresentation_soThreeEquiv`,
`TauCeti.specialOrthogonalCoadjointRepresentation_soThreeDualEquiv`). Hence the coadjoint stabilizer
of `ν_m` is the group of rotations fixing `m`
(`TauCeti.mem_stabilizer_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv_iff`).

Over `ℝ`, rotations preserve the dot product, and they act transitively on each sphere about the
origin (`Matrix.exists_mem_specialOrthogonalGroup_mulVec_eq`). So **the coadjoint orbit of `SO(3)`
through `ν_m` is the sphere of radius `√(m ⬝ᵥ m)`**:

`{Ad*_g ν_m | g ∈ SO(3)} = {ν_p | p ⬝ᵥ p = m ⬝ᵥ m}`

(`TauCeti.range_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv`). For `m = 0` this is
the single point `0`. The infinitesimal counterparts, the coadjoint action
`⁅ξ̂, ν_m⁆ = ν_(ξ ⨯₃ m)` of `so(3)` and the tangent plane `m^⊥` of the orbit, are in
`TauCeti.Algebra.Lie.Orthogonal.CrossProduct`, and the Kirillov–Kostant–Souriau form of these
spheres is in `TauCeti.Geometry.Symplectic.Coadjoint.Sphere`.

## Main definitions

* `TauCeti.orthogonalAdjointRepresentation`, `TauCeti.orthogonalCoadjointRepresentation`: the
  adjoint and coadjoint representations of `O(n)`.
* `TauCeti.specialOrthogonalAdjointRepresentation`,
  `TauCeti.specialOrthogonalCoadjointRepresentation`: their restrictions to `SO(n)`.

## Main results

* `TauCeti.orthogonalAdjointRepresentation_lie`,
  `TauCeti.specialOrthogonalAdjointRepresentation_lie`: the adjoint action is by Lie algebra
  automorphisms.
* `TauCeti.specialOrthogonalAdjointRepresentation_soThreeEquiv`,
  `TauCeti.specialOrthogonalCoadjointRepresentation_soThreeDualEquiv`: for `SO(3)` both actions
  are the rotation of `R³`.
* `TauCeti.mem_stabilizer_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv_iff`: the
  coadjoint stabilizer of `ν_m` consists of the rotations fixing `m`.
* `TauCeti.soThreeDualEquiv_mem_range_specialOrthogonalCoadjointRepresentation_iff`,
  `TauCeti.range_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv`: the coadjoint orbits
  of `SO(3)` are the spheres about the origin.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Texts
  in Applied Mathematics 17, Springer, 1999, Section 14.2 (the coadjoint orbits of `SO(3)`).
* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open Matrix Module LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-! ### The adjoint and coadjoint representations of `O(n)` and `SO(n)` -/

variable (n R) in
/-- The **adjoint representation** of the orthogonal group `O(n)` on its Lie algebra `so(n)` of
skew-symmetric matrices, by conjugation `Ad_g A = g A g⁻¹ = g A gᵀ`. -/
def orthogonalAdjointRepresentation : Representation R (orthogonalGroup n R) (so n R) where
  toFun g :=
    { toFun A :=
        ⟨(g : Matrix n n R) * A * (g : Matrix n n R)ᵀ, mul_mul_transpose_mem_so _ A.property⟩
      map_add' A B := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
      map_smul' c A := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun A ↦ Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun A ↦ Subtype.ext (by simp [Matrix.mul_assoc])

@[simp]
theorem coe_orthogonalAdjointRepresentation_apply (g : orthogonalGroup n R) (A : so n R) :
    (orthogonalAdjointRepresentation n R g A : Matrix n n R) =
      (g : Matrix n n R) * A * (g : Matrix n n R)ᵀ :=
  (rfl)

/-- **The adjoint action is by Lie algebra automorphisms**: `Ad_g ⁅A, B⁆ = ⁅Ad_g A, Ad_g B⁆`. -/
theorem orthogonalAdjointRepresentation_lie (g : orthogonalGroup n R) (A B : so n R) :
    orthogonalAdjointRepresentation n R g ⁅A, B⁆ =
      ⁅orthogonalAdjointRepresentation n R g A, orthogonalAdjointRepresentation n R g B⁆ := by
  have hg : (g : Matrix n n R)ᵀ * g = 1 := (mem_orthogonalGroup_iff' _ _).1 g.property
  apply Subtype.ext
  simp only [coe_orthogonalAdjointRepresentation_apply, LieSubalgebra.coe_bracket,
    Ring.lie_def, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (g : Matrix n n R)ᵀ, hg, Matrix.one_mul]

variable (n R) in
/-- The **coadjoint representation** of `O(n)` on the dual of `so(n)`,
`(Ad*_g ν)(A) = ν (Ad_(g⁻¹) A)`, the dual of the adjoint representation. -/
def orthogonalCoadjointRepresentation :
    Representation R (orthogonalGroup n R) (Dual R (so n R)) :=
  (orthogonalAdjointRepresentation n R).dual

@[simp]
theorem orthogonalCoadjointRepresentation_apply_apply (g : orthogonalGroup n R)
    (ν : Dual R (so n R)) (A : so n R) :
    orthogonalCoadjointRepresentation n R g ν A = ν (orthogonalAdjointRepresentation n R g⁻¹ A) :=
  (rfl)

variable (n R) in
/-- The **adjoint representation** of the special orthogonal group `SO(n)` on `so(n)`, the
restriction of `TauCeti.orthogonalAdjointRepresentation` to `SO(n) ≤ O(n)`. -/
def specialOrthogonalAdjointRepresentation :
    Representation R (specialOrthogonalGroup n R) (so n R) :=
  (orthogonalAdjointRepresentation n R).comp specialOrthogonalGroup.toOrthogonalGroup

theorem specialOrthogonalAdjointRepresentation_apply (g : specialOrthogonalGroup n R) :
    specialOrthogonalAdjointRepresentation n R g =
      orthogonalAdjointRepresentation n R (specialOrthogonalGroup.toOrthogonalGroup g) :=
  (rfl)

@[simp]
theorem coe_specialOrthogonalAdjointRepresentation_apply (g : specialOrthogonalGroup n R)
    (A : so n R) :
    (specialOrthogonalAdjointRepresentation n R g A : Matrix n n R) =
      (g : Matrix n n R) * A * (g : Matrix n n R)ᵀ := by
  simp [specialOrthogonalAdjointRepresentation_apply]

/-- **The adjoint action of `SO(n)` is by Lie algebra automorphisms**:
`Ad_g ⁅A, B⁆ = ⁅Ad_g A, Ad_g B⁆`. -/
theorem specialOrthogonalAdjointRepresentation_lie (g : specialOrthogonalGroup n R)
    (A B : so n R) :
    specialOrthogonalAdjointRepresentation n R g ⁅A, B⁆ =
      ⁅specialOrthogonalAdjointRepresentation n R g A,
        specialOrthogonalAdjointRepresentation n R g B⁆ := by
  simp only [specialOrthogonalAdjointRepresentation_apply, orthogonalAdjointRepresentation_lie]

variable (n R) in
/-- The **coadjoint representation** of `SO(n)` on the dual of `so(n)`, the restriction of
`TauCeti.orthogonalCoadjointRepresentation` to `SO(n) ≤ O(n)`. -/
def specialOrthogonalCoadjointRepresentation :
    Representation R (specialOrthogonalGroup n R) (Dual R (so n R)) :=
  (orthogonalCoadjointRepresentation n R).comp specialOrthogonalGroup.toOrthogonalGroup

theorem specialOrthogonalCoadjointRepresentation_apply (g : specialOrthogonalGroup n R) :
    specialOrthogonalCoadjointRepresentation n R g =
      orthogonalCoadjointRepresentation n R (specialOrthogonalGroup.toOrthogonalGroup g) :=
  (rfl)

@[simp]
theorem specialOrthogonalCoadjointRepresentation_apply_apply (g : specialOrthogonalGroup n R)
    (ν : Dual R (so n R)) (A : so n R) :
    specialOrthogonalCoadjointRepresentation n R g ν A =
      ν (specialOrthogonalAdjointRepresentation n R g⁻¹ A) := by
  simp [specialOrthogonalCoadjointRepresentation_apply,
    specialOrthogonalAdjointRepresentation_apply, orthogonalCoadjointRepresentation_apply_apply]

/-! ### `SO(3)` in the coordinates of the hat map -/

section Three

variable [NoZeroDivisors R] [NeZero (2 : R)]

/-- **The adjoint action of `SO(3)` is the rotation of `R³`**: `Ad_g û = (g u)^`. -/
@[simp]
theorem specialOrthogonalAdjointRepresentation_soThreeEquiv
    (g : specialOrthogonalGroup (Fin 3) R) (u : Fin 3 → R) :
    specialOrthogonalAdjointRepresentation (Fin 3) R g (soThreeEquiv R u) =
      soThreeEquiv R ((g : Matrix (Fin 3) (Fin 3) R) *ᵥ u) :=
  Subtype.ext (by
    rw [coe_specialOrthogonalAdjointRepresentation_apply, coe_soThreeEquiv, coe_soThreeEquiv,
      mul_crossProductMatrix_mul_transpose g.property])

/-- **The coadjoint action of `SO(3)` is the rotation of `R³`**: `Ad*_g ν_m = ν_(g m)`. -/
@[simp]
theorem specialOrthogonalCoadjointRepresentation_soThreeDualEquiv
    (g : specialOrthogonalGroup (Fin 3) R) (m : Fin 3 → R) :
    specialOrthogonalCoadjointRepresentation (Fin 3) R g (soThreeDualEquiv R m) =
      soThreeDualEquiv R ((g : Matrix (Fin 3) (Fin 3) R) *ᵥ m) := by
  refine LinearMap.ext fun A ↦ ?_
  obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective A
  simp [specialOrthogonalCoadjointRepresentation_apply_apply, dotProduct_mulVec, vecMul_transpose]

/-- **The coadjoint stabilizer of `ν_m` is the group of rotations fixing `m`.** -/
theorem mem_stabilizer_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv_iff
    {g : specialOrthogonalGroup (Fin 3) R} {m : Fin 3 → R} :
    g ∈ (specialOrthogonalCoadjointRepresentation (Fin 3) R).stabilizer (soThreeDualEquiv R m) ↔
      (g : Matrix (Fin 3) (Fin 3) R) *ᵥ m = m := by
  rw [Representation.mem_stabilizer, specialOrthogonalCoadjointRepresentation_soThreeDualEquiv,
    (soThreeDualEquiv R).injective.eq_iff]

end Three

/-! ### The coadjoint orbits of `SO(3)` are spheres -/

/-- **The coadjoint orbits of `SO(3)` are the spheres about the origin**: `ν_p` lies in the orbit
of `ν_m` exactly when `p ⬝ᵥ p = m ⬝ᵥ m`. -/
theorem soThreeDualEquiv_mem_range_specialOrthogonalCoadjointRepresentation_iff
    {m p : Fin 3 → ℝ} :
    soThreeDualEquiv ℝ p ∈ Set.range (fun g ↦
        specialOrthogonalCoadjointRepresentation (Fin 3) ℝ g (soThreeDualEquiv ℝ m)) ↔
      p ⬝ᵥ p = m ⬝ᵥ m := by
  simp only [specialOrthogonalCoadjointRepresentation_soThreeDualEquiv, Set.mem_range,
    (soThreeDualEquiv ℝ).injective.eq_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact mem_orthogonalGroup_iff_dotProduct_mulVec.1 g.property.1 m m
  · intro h
    obtain ⟨A, hA, hAm⟩ := exists_mem_specialOrthogonalGroup_mulVec_eq (by simp) h.symm
    exact ⟨⟨A, hA⟩, hAm⟩

/-- **The coadjoint orbit of `SO(3)` through `ν_m` is the sphere of radius `√(m ⬝ᵥ m)`**, read in
`so(3)*` through the dot product. -/
theorem range_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv (m : Fin 3 → ℝ) :
    Set.range (fun g ↦
        specialOrthogonalCoadjointRepresentation (Fin 3) ℝ g (soThreeDualEquiv ℝ m)) =
      soThreeDualEquiv ℝ '' {p | p ⬝ᵥ p = m ⬝ᵥ m} := by
  ext ν
  obtain ⟨p, rfl⟩ := (soThreeDualEquiv ℝ).surjective ν
  rw [soThreeDualEquiv_mem_range_specialOrthogonalCoadjointRepresentation_iff,
    (soThreeDualEquiv ℝ).injective.mem_set_image, Set.mem_ofPred_eq]

end TauCeti
