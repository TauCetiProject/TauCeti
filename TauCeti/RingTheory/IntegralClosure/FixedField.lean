/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
import TauCeti.RingTheory.LocalRing.FixedPoints

/-!
# Integral closures in Galois fixed fields

For a Galois subgroup `H ≤ Gal(L/K)` and a subring or base ring `A` acting on `L` through `K`, the
`H`-fixed subalgebra `(integralClosure A L)^H` is isomorphic as an `A`-algebra to
`integralClosure A (IntermediateField.fixedField H)`
(`TauCeti.fixedPointsSubalgebraIntegralClosureEquiv`). When `H` is normal, this equivalence
intertwines the quotient action of `Gal(L/K) ⧸ H` with `IsGalois.normalAutEquivQuotient H`
(`TauCeti.fixedPointsSubalgebraIntegralClosureEquiv_smul`), and transfers `IsLocalRing` and
`IsDiscreteValuationRing` from `integralClosure A L` to `integralClosure A (fixedField H)`.

## Main definitions and results

* `TauCeti.fixedPointsSubalgebraIntegralClosureEquiv`:
  `(integralClosure A L)^H ≃ₐ[A] integralClosure A (fixedField H)`.
* `TauCeti.fixedPointsSubalgebraIntegralClosureEquiv_smul` and
  `TauCeti.fixedPointsSubalgebraIntegralClosureEquiv_symm_smul`: equivariance under the quotient
  action of `Gal(L/K) ⧸ H` and `IsGalois.normalAutEquivQuotient H`.
* `TauCeti.instIsLocalRingIntegralClosureFixedField`: transfers `IsLocalRing` to
  `integralClosure A (fixedField H)`.
* `TauCeti.instIsDiscreteValuationRingIntegralClosureFixedField`: transfers
  `IsDiscreteValuationRing` to `integralClosure A (fixedField H)`.
-/

public section

namespace TauCeti

section FixedFieldEquiv

open _root_.IntermediateField

variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] (H : Subgroup (L ≃ₐ[K] L))

/-- The `A`-subalgebra of `H`-fixed elements of `integralClosure A L` is isomorphic as an
`A`-algebra to `integralClosure A (IntermediateField.fixedField H)`. -/
def fixedPointsSubalgebraIntegralClosureEquiv :
    FixedPoints.subalgebra A (integralClosure A L) H ≃ₐ[A] integralClosure A (fixedField H) :=
  haveI := IsScalarTower.to₁₃₄ A K (fixedField H) L
  { toFun x := ⟨⟨(x.val : L), fun h ↦ congrArg Subtype.val (x.property h)⟩,
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (fixedField H) L)
        (fixedField H).val.injective).mp x.val.property⟩
    invFun y := ⟨⟨(y.val : L), y.property.map (IsScalarTower.toAlgHom A (fixedField H) L)⟩,
      fun h ↦ Subtype.ext (y.val.property h)⟩
    left_inv _ := rfl, right_inv _ := rfl, map_mul' _ _ := rfl, map_add' _ _ := rfl
    commutes' r := Subtype.ext <| Subtype.ext <| by
      simp [IsScalarTower.algebraMap_apply A K L r,
        IsScalarTower.algebraMap_apply A K (fixedField H) r] }

@[simp]
theorem coe_fixedPointsSubalgebraIntegralClosureEquiv_apply
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    (((fixedPointsSubalgebraIntegralClosureEquiv A H x : integralClosure A (fixedField H)) :
      fixedField H) : L) = ((x : integralClosure A L) : L) :=
  (rfl)

@[simp]
theorem coe_fixedPointsSubalgebraIntegralClosureEquiv_symm_apply
    (y : integralClosure A (fixedField H)) :
    (((fixedPointsSubalgebraIntegralClosureEquiv A H).symm y : integralClosure A L) : L) =
      ((y : fixedField H) : L) :=
  (rfl)

section Galois

variable [FiniteDimensional K L] [IsGalois K L] [H.Normal]

/-- `fixedPointsSubalgebraIntegralClosureEquiv` intertwines the quotient action of `Gal(L/K) ⧸ H`
with the Galois action of `Gal(fixedField H / K)` via `IsGalois.normalAutEquivQuotient H`. -/
@[simp]
theorem fixedPointsSubalgebraIntegralClosureEquiv_smul (q : (L ≃ₐ[K] L) ⧸ H)
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    fixedPointsSubalgebraIntegralClosureEquiv A H (q • x) =
      IsGalois.normalAutEquivQuotient H q • fixedPointsSubalgebraIntegralClosureEquiv A H x := by
  induction q using QuotientGroup.induction_on with | H σ =>
    exact Subtype.ext <| Subtype.ext <| by
      simp [IsGalois.normalAutEquivQuotient_apply, AlgEquiv.restrictNormalHom_apply,
        AlgEquiv.smul_def, Subgroup.coe_mk_smul]

/-- `(fixedPointsSubalgebraIntegralClosureEquiv A H).symm` intertwines the Galois action of
`Gal(fixedField H / K)` with `(IsGalois.normalAutEquivQuotient H).symm`. -/
@[simp]
theorem fixedPointsSubalgebraIntegralClosureEquiv_symm_smul
    (τ : fixedField H ≃ₐ[K] fixedField H) (y : integralClosure A (fixedField H)) :
    (fixedPointsSubalgebraIntegralClosureEquiv A H).symm (τ • y) =
      (IsGalois.normalAutEquivQuotient H).symm τ •
        (fixedPointsSubalgebraIntegralClosureEquiv A H).symm y :=
  (fixedPointsSubalgebraIntegralClosureEquiv A H).injective <| by simp

end Galois

variable {A H} in
/-- If `integralClosure A L` is local, so is `integralClosure A (fixedField H)`. -/
instance instIsLocalRingIntegralClosureFixedField [IsLocalRing (integralClosure A L)] :
    IsLocalRing (integralClosure A (fixedField H)) :=
  (fixedPointsSubalgebraIntegralClosureEquiv A H).toRingEquiv.isLocalRing

/-- If `integralClosure A L` is a DVR and `H ≤ Gal(L/K)`, then
`integralClosure A (fixedField H)` is a DVR. -/
instance instIsDiscreteValuationRingIntegralClosureFixedField {A K L : Type*} [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [_root_.IsDiscreteValuationRing (integralClosure A L)] {H : Subgroup (L ≃ₐ[K] L)} :
    _root_.IsDiscreteValuationRing (integralClosure A (IntermediateField.fixedField H)) :=
  have : Algebra.IsIntegral (FixedPoints.subalgebra A (integralClosure A L) H)
      (integralClosure A L) := Algebra.IsIntegral.tower_top A
  have := isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral
    (A := A) (B := integralClosure A L) (G := H)
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubalgebraIntegralClosureEquiv A H)

end FixedFieldEquiv

end TauCeti
