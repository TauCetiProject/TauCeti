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

end CliffordAlgebra
