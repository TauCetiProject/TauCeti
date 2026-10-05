/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Basic

/-!
# The spin group acting on its quadratic space

The spin group is a subgroup of the Lipschitz group, and its action is the restriction of the
common twisted-conjugation action on the quadratic space. This file packages that restriction as
`spinToOrthogonal Q : spinGroup Q →* QuadraticMap.orthogonalGroup Q` and records its Clifford
application formula.

This is the representation underlying the double cover from the spin group to the special
orthogonal group. The determinant-one property and surjectivity require the later
Cartan--Dieudonné argument and are deliberately not asserted here.

## Main definitions

* `CliffordAlgebra.spinVectorAction Q x` is the restriction of
  `CliffordAlgebra.lipschitzVectorAction` along the canonical Spin inclusion.
* `CliffordAlgebra.spinToOrthogonal Q` is the resulting homomorphism into `O(Q)`.
* `CliffordAlgebra.rightIotaEven Q e` embeds a vector as `ι(m)ι(e)` in the even algebra.
* `CliffordAlgebra.conjugateNegativeIotaEven Q e he` restricts conjugation by `-ι(e)` to the
  even algebra when `Q(e) = -1`.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section


universe u v

namespace CliffordAlgebra

open TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

private def spinToLipschitz : spinGroup Q →* lipschitzGroup Q :=
  (pinToLipschitz Q).comp (spinToPin Q)

omit [Invertible (2 : R)] in
private theorem coe_spinToLipschitz_apply (x : spinGroup Q) :
    (((spinToLipschitz Q x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) = (x : CliffordAlgebra Q) := by
  simp [spinToLipschitz]

/-- The action of a spin element on the generating vectors of its Clifford algebra, transported
back to the underlying module. It is characterized by
`ι_spinVectorAction_apply`, which identifies it with conjugation inside the Clifford algebra. -/
noncomputable def spinVectorAction (x : spinGroup Q) : M ≃ₗ[R] M :=
  lipschitzVectorAction Q (spinToLipschitz Q x)

/-- The identity Spin element acts by the identity linear equivalence. -/
@[simp]
theorem spinVectorAction_one : spinVectorAction Q 1 = LinearEquiv.refl R M := by
  simp [spinVectorAction]

/-- The Spin vector action sends products to composition of linear equivalences. -/
@[simp]
theorem spinVectorAction_mul (x y : spinGroup Q) :
    spinVectorAction Q (x * y) = spinVectorAction Q x * spinVectorAction Q y := by
  simp [spinVectorAction]

/-- A spin element acts on a vector by conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_spinVectorAction_apply (x : spinGroup Q) (m : M) :
    ι Q (spinVectorAction Q x m) =
      (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) :=
  by
    rw [spinVectorAction, ι_lipschitzVectorAction_apply]
    rw [coe_spinToLipschitz_apply, spinGroup.involute_eq x.2]
    have hunit :
        ((spinToLipschitz Q x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) =
          spinGroup.toUnits x := by
      apply Units.ext
      exact coe_spinToLipschitz_apply Q x
    have hinv :
        (((spinGroup.toUnits x)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
          star (x : CliffordAlgebra Q) := by
      rw [← map_inv (spinGroup.toUnits (Q := Q)) x]
      rw [← spinGroup.star_eq_inv x]
      exact spinGroup.coe_star
    rw [hunit, hinv]

/-- Conjugation by a spin element preserves the quadratic form. -/
@[simp]
theorem spinVectorAction_map_app (x : spinGroup Q) (m : M) :
    Q (spinVectorAction Q x m) = Q m := by
  exact lipschitzVectorAction_map_app (Q := Q) (spinToLipschitz Q x) m

/-- The representation of the spin group on the quadratic space by Clifford conjugation. -/
noncomputable def spinToOrthogonal : spinGroup Q →* QuadraticMap.orthogonalGroup Q :=
  (lipschitzToOrthogonal Q).comp (spinToLipschitz Q)

@[simp]
theorem coe_spinToOrthogonal_apply (x : spinGroup Q) (m : M) :
    ((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m =
      spinVectorAction Q x m := by
  rw [spinToOrthogonal, MonoidHom.comp_apply, coe_lipschitzToOrthogonal_apply]
  rfl

/-- The Spin action on its quadratic space, for every quadratic form with `2` invertible. -/
noncomputable instance instMulActionSpinGroup : MulAction (spinGroup Q) M :=
  MulAction.compHom _ (spinToOrthogonal Q)

/-- The induced `MulAction` agrees pointwise with the transported Clifford-conjugation action. -/
@[simp]
theorem spinGroup_smul_apply (s : spinGroup Q) (x : M) :
    s • x = spinVectorAction Q s x := by
  rw [MulAction.compHom_smul_def]
  exact coe_spinToOrthogonal_apply Q s x

/-! ### Even-algebra transport along a negative vector -/

/-- The even-Clifford embedding obtained by multiplying a generating vector on the right by
another generating vector. -/
@[expose]
def rightIotaEven (e : M) : M →ₗ[R] even Q :=
  (even.ι Q).bilin.flip e

omit [Invertible (2 : R)] in
/-- Evaluating `rightIotaEven` gives the canonical bilinear generator of the even algebra. -/
@[simp]
theorem rightIotaEven_apply (e m : M) :
    rightIotaEven Q e m = (even.ι Q).bilin m e :=
  rfl

omit [Invertible (2 : R)] in
/-- The ambient Clifford value of `rightIotaEven`. -/
@[simp]
theorem coe_rightIotaEven (e m : M) :
    (rightIotaEven Q e m : CliffordAlgebra Q) = ι Q m * ι Q e :=
  by
    -- Expose the bilinear even embedding before coercing its value to the ambient algebra.
    change (((even.ι Q).bilin m e : even Q) : CliffordAlgebra Q) = ι Q m * ι Q e
    rfl

omit [Invertible (2 : R)] in
private theorem iota_sq_neg_one (e : M) (he : Q e = -1) :
    ι Q e * ι Q e = -1 := by
  rw [ι_sq_scalar, he, map_neg, map_one]

private def negativeIotaUnit (e : M) (he : Q e = -1) : (CliffordAlgebra Q)ˣ where
  val := -ι Q e
  inv := ι Q e
  val_inv := by rw [neg_mul, iota_sq_neg_one Q e he, neg_neg]
  inv_val := by rw [mul_neg, iota_sq_neg_one Q e he, neg_neg]

private noncomputable def conjugateNegativeIota
    (e : M) (he : Q e = -1) : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  MulSemiringAction.toAlgEquiv R _ (ConjAct.toConjAct (negativeIotaUnit Q e he))

omit [Invertible (2 : R)] in
private theorem conjugateNegativeIota_apply (e : M) (he : Q e = -1)
    (x : CliffordAlgebra Q) :
    conjugateNegativeIota Q e he x = (-ι Q e * x) * ι Q e := by
  simp [conjugateNegativeIota, negativeIotaUnit, ConjAct.units_smul_def]

/-- If `Q(e) = -1`, conjugation by the unit `-ι(e)` preserves the even Clifford algebra. -/
noncomputable def conjugateNegativeIotaEven (e : M) (he : Q e = -1) :
    even Q →ₐ[R] even Q where
  toFun x := ⟨conjugateNegativeIota Q e he (x : CliffordAlgebra Q), by
    rw [conjugateNegativeIota_apply]
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    have hleft : -ι Q e ∈ evenOdd Q 1 :=
      Submodule.neg_mem _ (ι_mem_evenOdd_one _ _)
    have h := SetLike.mul_mem_graded (SetLike.mul_mem_graded hleft x.2)
      (ι_mem_evenOdd_one Q e)
    -- The two odd factors have degree zero in the `ZMod 2` grading.
    exact (show (1 + 1 : ZMod 2) = 0 by decide) ▸ (by simpa only [add_zero] using h)⟩
  map_one' := Subtype.ext (map_one (conjugateNegativeIota Q e he))
  map_mul' x y := Subtype.ext (map_mul (conjugateNegativeIota Q e he)
    (x : CliffordAlgebra Q) y)
  map_zero' := Subtype.ext (map_zero (conjugateNegativeIota Q e he))
  map_add' x y := Subtype.ext (map_add (conjugateNegativeIota Q e he)
    (x : CliffordAlgebra Q) y)
  commutes' r := Subtype.ext (AlgEquiv.commutes (conjugateNegativeIota Q e he) r)

omit [Invertible (2 : R)] in
/-- The ambient Clifford value of conjugation by `-ι(e)` on the even subalgebra. -/
@[simp]
theorem coe_conjugateNegativeIotaEven (e : M) (he : Q e = -1) (x : even Q) :
    (conjugateNegativeIotaEven Q e he x : CliffordAlgebra Q) =
      (-ι Q e * (x : CliffordAlgebra Q)) * ι Q e :=
  conjugateNegativeIota_apply Q e he x

end CliffordAlgebra
