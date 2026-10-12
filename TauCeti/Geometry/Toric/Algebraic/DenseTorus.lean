/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.AffineScheme

/-!
# The dense torus of an integral lattice

The zero cone has no nonzero inequalities on integral characters, so its dual semigroup is the
whole character lattice.  This module records the resulting additive equivalence and transports it
to the monoid algebra.  The resulting affine scheme is the coordinate-free dense torus used as
the zero-cone chart of every toric fan.

The definitions here depend only on an integral lattice.  The fan-specific open immersion into a
realized fan lives in `Algebraic/Fan/DenseTorus.lean`, where the zero cone is known to belong to
the fan.

## Main declarations

* `TauCeti.Toric.denseTorusScheme`: the affine spectrum of the zero-cone monoid algebra.
* `TauCeti.Toric.denseTorusDualEquiv`: the zero-cone dual semigroup is the full character lattice.
* `TauCeti.Toric.denseTorusDualEquiv_apply` and `_symm_apply`: the two computation lemmas.
* `TauCeti.Toric.denseTorusCoordinateRingEquiv`: the corresponding algebra equivalence.
* `TauCeti.Toric.denseTorusCoordinateRingEquiv_single` and `_symm_single`: monomial computations.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.1.
-/

public section

open AlgebraicGeometry Multiplicative

namespace TauCeti.Toric

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The affine toric scheme of the zero cone is the coordinate-free dense torus of the lattice. -/
noncomputable abbrev denseTorusScheme (hi : IsIntegralLattice i) : Scheme :=
  affineToricScheme hi (⊥ : PointedCone ℝ V)

/-- The dual semigroup of the zero cone is additively equivalent to the full character lattice. -/
noncomputable def denseTorusDualEquiv (hi : IsIntegralLattice i) :
    dualSemigroup hi (⊥ : PointedCone ℝ V) ≃+ (N →+ ℤ) where
  toFun := Subtype.val
  invFun m := ⟨m, by simp⟩
  left_inv m := rfl
  right_inv m := rfl
  map_add' := fun _ _ => rfl

/-- Transporting the monoid-algebra structure along the zero-cone character equivalence gives the
canonical algebra equivalence for the coordinate ring of the dense torus. -/
noncomputable def denseTorusCoordinateRingEquiv (hi : IsIntegralLattice i) :
    affineCoordinateRing hi (⊥ : PointedCone ℝ V) ≃ₐ[ℂ]
      MonoidAlgebra ℂ (Multiplicative (N →+ ℤ)) :=
  MonoidAlgebra.domCongr (R := ℂ) (A := ℂ) (denseTorusDualEquiv hi).toMultiplicative

/-- The zero-cone character equivalence is the identity on the ambient character lattice. -/
@[simp]
theorem denseTorusDualEquiv_apply (hi : IsIntegralLattice i)
    (m : dualSemigroup hi (⊥ : PointedCone ℝ V)) :
    denseTorusDualEquiv hi m = (m : N →+ ℤ) := by
  simp [denseTorusDualEquiv]

/-- The inverse zero-cone character equivalence records the ambient character as a member of the
full dual semigroup. -/
@[simp]
theorem denseTorusDualEquiv_symm_apply (hi : IsIntegralLattice i) (m : N →+ ℤ) :
    (denseTorusDualEquiv hi).symm m = ⟨m, by simp⟩ := by
  simp [denseTorusDualEquiv]

/-- The coordinate-ring equivalence sends a monomial to the monomial of its ambient character. -/
@[simp]
theorem denseTorusCoordinateRingEquiv_single (hi : IsIntegralLattice i)
    (m : dualSemigroup hi (⊥ : PointedCone ℝ V)) (z : ℂ) :
    denseTorusCoordinateRingEquiv hi (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd (m : N →+ ℤ)) z := by
  simp [denseTorusCoordinateRingEquiv, MonoidAlgebra.domCongr_single,
    denseTorusDualEquiv_apply]

/-- The inverse coordinate-ring equivalence sends an ambient-character monomial to the monomial
of its zero-cone dual-semigroup representative. -/
@[simp]
theorem denseTorusCoordinateRingEquiv_symm_single (hi : IsIntegralLattice i)
    (m : N →+ ℤ) (z : ℂ) :
    (denseTorusCoordinateRingEquiv hi).symm (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd ((denseTorusDualEquiv hi).symm m)) z := by
  simp [denseTorusCoordinateRingEquiv, MonoidAlgebra.domCongr_symm,
    denseTorusDualEquiv_symm_apply]

end TauCeti.Toric
