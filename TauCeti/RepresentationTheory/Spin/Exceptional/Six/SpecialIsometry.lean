/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.Kernel
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ExponentTwo

/-!
# The special orthogonal exterior-square action of `SL₄`

Over a field of characteristic different from two, the exterior-square action of `SL₄`
on `⋀²(K⁴)` has determinant one. Indeed, its determinant is a character whose values
square to one because the wedge form is nondegenerate; transvection generation forces
this character to be trivial.

We lift the action to the special isometry group of the wedge form, retaining its
kernel of order two. Over `ℂ`, this is the `SL₄ → SO₆` homomorphism needed for the
exceptional comparison `Spin₆ ≅ SL₄`. Surjectivity and comparison with the spin cover
are separate steps.
-/

public section

namespace TauCeti

variable (K : Type*) [Field K] [NeZero (2 : K)]

/-- The exterior-square orthogonal action of `SL₄` has determinant one. -/
@[simp]
theorem spinSixSpecialLinearToIsometryGroup_det
    (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    LinearEquiv.det (spinSixSpecialLinearToIsometryGroup K g).1 = 1 := by
  have hchar : (LinearMap.BilinForm.isometryDet (spinSixWedgeForm K)).comp
      (spinSixSpecialLinearToIsometryGroup K) = 1 := by
    apply MonoidHom.eq_one_of_sq_eq_one_on_specialLinearGroup
    intro s
    apply Units.ext
    let b := Module.Free.chooseBasis K (⋀[K]^2 (Fin 4 → K))
    have hG : (LinearMap.BilinForm.toMatrix b (spinSixWedgeForm K)).det ∈
        nonZeroDivisors K :=
      mem_nonZeroDivisors_of_ne_zero
        ((LinearMap.separatingLeft_iff_det_ne_zero b).mp
          (spinSixWedgeForm_isPerfPair K).separatingLeft)
    have hs := BilinForm.mem_isometryGroup.mp
      (spinSixSpecialLinearToIsometryGroup K s).2
    simpa only [MonoidHom.comp_apply, LinearMap.BilinForm.isometryDet_apply,
      Units.val_pow_eq_pow_val, Units.val_one, LinearEquiv.coe_det] using
      hs.det_sq_eq_one b hG
  simpa only [MonoidHom.comp_apply, LinearMap.BilinForm.isometryDet_apply,
    MonoidHom.one_apply] using DFunLike.congr_fun hchar g

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

/-- The special orthogonal exterior-square action of `SL₄` has kernel of order two. -/
theorem card_ker_spinSixSpecialLinearToSpecialIsometryGroup :
    Nat.card (spinSixSpecialLinearToSpecialIsometryGroup K).ker = 2 := by
  rw [ker_spinSixSpecialLinearToSpecialIsometryGroup,
    card_ker_spinSixSpecialLinearToIsometryGroup]

end TauCeti
