/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.Kernel
public import TauCeti.LinearAlgebra.ExteriorPower.Determinant

/-!
# The special orthogonal exterior-square action of `SL₄`

Over a nontrivial commutative ring, the exterior-square action of `SL₄` on `⋀²(K⁴)` has
determinant one: the determinant of an exterior-square action in rank four is the cube
of the original determinant.

We lift the action to the special isometry group of the wedge form, retaining its
scalar `±1` kernel over a domain, of order two away from characteristic two. Over `ℂ`,
this is the `SL₄ → SO₆` homomorphism needed for the exceptional comparison `Spin₆ ≅ SL₄`.
Surjectivity and comparison with the spin cover
are separate steps.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
-/

public section

namespace TauCeti

variable (K : Type*) [CommRing K]

section Ring

variable [Nontrivial K]

/-- The exterior-square orthogonal action of `SL₄` has determinant one. -/
@[simp]
theorem spinSixSpecialLinearToIsometryGroup_det
    (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    LinearEquiv.det (spinSixSpecialLinearToIsometryGroup K g).1 = 1 := by
  apply Units.ext
  have hmap : (spinSixSpecialLinearToIsometryGroup K g).1.toLinearMap =
      exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) K)) := by
    have hrep : stdSLRep K 4 g = Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) K) := by
      rw [stdSLRep_apply, Matrix.toLin'_apply']
    apply LinearMap.ext
    intro x
    simpa only [LinearEquiv.coe_coe, Representation.exteriorPower_apply, hrep] using
      spinSixSpecialLinearToIsometryGroup_apply K g x
  simp only [LinearEquiv.coe_det, hmap, Units.val_one]
  rw [(Pi.basisFun K (Fin 4)).det_exteriorPower_two, LinearMap.det_toLin', g.property]
  exact one_pow 3

/-- The exterior-square action of `SL₄`, as a homomorphism to the determinant-one
isometries of the wedge form. -/
noncomputable def spinSixSpecialLinearToSpecialIsometryGroup :
    Matrix.SpecialLinearGroup (Fin 4) K →*
      LinearMap.BilinForm.specialIsometryGroup (spinSixWedgeForm K) :=
  ((BilinForm.isometryGroup (spinSixWedgeForm K)).subtype.comp
    (spinSixSpecialLinearToIsometryGroup K)).codRestrict
      (LinearMap.BilinForm.specialIsometryGroup (spinSixWedgeForm K))
      (fun g ↦ LinearMap.BilinForm.mem_specialIsometryGroup_iff.mpr
        ⟨(spinSixSpecialLinearToIsometryGroup K g).2,
          spinSixSpecialLinearToIsometryGroup_det K g⟩)

/-- The determinant-one lift acts by the exterior-square standard representation. -/
@[simp]
theorem spinSixSpecialLinearToSpecialIsometryGroup_apply
    (g : Matrix.SpecialLinearGroup (Fin 4) K) (x : ⋀[K]^2 (Fin 4 → K)) :
    (spinSixSpecialLinearToSpecialIsometryGroup K g).1 x =
      (stdSLRep K 4).exteriorPower 2 g x :=
  spinSixSpecialLinearToIsometryGroup_apply K g x

/-- Forgetting the determinant-one condition recovers the exterior-square isometry action. -/
@[simp]
theorem specialIsometryToIsometry_comp_spinSixSpecialLinearToSpecialIsometryGroup :
    (LinearMap.BilinForm.specialIsometryToIsometry (spinSixWedgeForm K)).comp
      (spinSixSpecialLinearToSpecialIsometryGroup K) =
        spinSixSpecialLinearToIsometryGroup K := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [MonoidHom.comp_apply, LinearMap.BilinForm.coe_specialIsometryToIsometry]
  rfl

/-- Lifting to determinant-one isometries leaves the kernel unchanged. -/
@[simp]
theorem ker_spinSixSpecialLinearToSpecialIsometryGroup :
    (spinSixSpecialLinearToSpecialIsometryGroup K).ker =
      (spinSixSpecialLinearToIsometryGroup K).ker := by
  rw [← specialIsometryToIsometry_comp_spinSixSpecialLinearToSpecialIsometryGroup K,
    MonoidHom.ker_comp_of_injective _ _
      (LinearMap.BilinForm.specialIsometryToIsometry_injective)]

end Ring

variable [IsDomain K]
/-- Over a domain, the kernel of the determinant-one exterior-square action consists of
the scalar matrices `±1`, which coincide in characteristic two. -/
@[simp]
theorem spinSixSpecialLinearToSpecialIsometryGroup_eq_one_iff
    (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    spinSixSpecialLinearToSpecialIsometryGroup K g = 1 ↔
      (g : Matrix (Fin 4) (Fin 4) K) = 1 ∨ (g : Matrix (Fin 4) (Fin 4) K) = -1 := by
  rw [← MonoidHom.mem_ker, ker_spinSixSpecialLinearToSpecialIsometryGroup,
    MonoidHom.mem_ker, spinSixSpecialLinearToIsometryGroup_eq_one_iff]

/-- The special orthogonal exterior-square action of `SL₄` has kernel of order two. -/
theorem card_ker_spinSixSpecialLinearToSpecialIsometryGroup [NeZero (2 : K)] :
    Nat.card (spinSixSpecialLinearToSpecialIsometryGroup K).ker = 2 := by
  rw [ker_spinSixSpecialLinearToSpecialIsometryGroup,
    card_ker_spinSixSpecialLinearToIsometryGroup]

end TauCeti
