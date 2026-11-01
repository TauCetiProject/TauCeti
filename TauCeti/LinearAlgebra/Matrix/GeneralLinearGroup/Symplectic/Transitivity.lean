/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transvection
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Transitivity of the symplectic group

Over any field, any two nonzero vectors in the standard symplectic space are connected by a
product of two symplectic transvections. If their pairing is nonzero, one transvection suffices:
use the direction `y - x` and the inverse of the pairing of `y` with `x`. In general, a vector
outside the two orthogonal hyperplanes provides an intermediate point. This argument works
also over the field with two elements and in rank one.

Consequently `Sp₂ₘ` acts transitively on projective points. This supplies transitivity for the
projective action whose point stabilizers and transvection subgroups enter the simplicity
criterion; primitivity is a separate assertion. The vector theorem retains the explicit bound
of two transvections, rather than only asserting existence of a symplectic matrix.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, §§4--5.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.

The transvections and their vector-action formula are those of
`TauCeti.GLSymplecticFin.symplecticTransvection`.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ}

variable {K : Type u} [Field K]

/-- When `ω(y,x) ≠ 0`, the transvection along `y - x` with parameter `ω(y,x)⁻¹` sends
`x` to `y`. -/
theorem symplecticTransvection_sub_mulVec {x y : Fin (m + m) → K}
    (hxy : y ⬝ᵥ (JFin m K *ᵥ x) ≠ 0) :
    (((symplecticTransvection (y - x) (y ⬝ᵥ (JFin m K *ᵥ x))⁻¹ :
        GLSymplecticFin m K) : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = y := by
  rw [coe_symplecticTransvection_mulVec, sub_dotProduct, dotProduct_JFin_mulVec_self,
    sub_zero, inv_mul_cancel₀ hxy, one_smul]
  abel

/-- Any two nonzero vectors are connected by a product of at most two symplectic transvections,
over every field. -/
theorem exists_symplecticTransvection_mul_mulVec_eq {x y : Fin (m + m) → K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (v w : Fin (m + m) → K) (a b : K),
      (((symplecticTransvection v a * symplecticTransvection w b : GLSymplecticFin m K) :
          GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = y := by
  obtain ⟨z, hzx, hzy⟩ := exists_dotProduct_JFin_mulVec_ne_zero_pair hx hy
  have hyz : y ⬝ᵥ (JFin m K *ᵥ z) ≠ 0 := by
    rw [dotProduct_JFin_mulVec_eq_neg z y]
    exact neg_ne_zero.mpr hzy
  refine ⟨y - z, z - x, (y ⬝ᵥ (JFin m K *ᵥ z))⁻¹,
    (z ⬝ᵥ (JFin m K *ᵥ x))⁻¹, ?_⟩
  rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec,
    symplecticTransvection_sub_mulVec hzx, symplecticTransvection_sub_mulVec hyz]

/-- The standard symplectic group sends any nonzero vector to any other nonzero vector. -/
theorem exists_mulVec_eq {x y : Fin (m + m) → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : GLSymplecticFin m K,
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = y := by
  obtain ⟨v, w, a, b, h⟩ := exists_symplecticTransvection_mul_mulVec_eq hx hy
  exact ⟨symplecticTransvection v a * symplecticTransvection w b, h⟩

/-- The symplectic group acts transitively on projective points, in every rank and over every
field. In rank zero the projective space is empty. -/
instance : MulAction.IsPretransitive (GLSymplecticFin m K) (ℙ K (Fin (m + m) → K)) where
  exists_smul_eq p q := by
    induction p using Projectivization.ind with
    | h x hx =>
    induction q using Projectivization.ind with
    | h y hy =>
    obtain ⟨g, hg⟩ := exists_mulVec_eq hx hy
    refine ⟨g, ?_⟩
    rw [Subgroup.smul_def, Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    exact ⟨1, by simp [Units.smul_def, Matrix.smul_eq_mulVec, hg]⟩

end TauCeti.GLSymplecticFin
