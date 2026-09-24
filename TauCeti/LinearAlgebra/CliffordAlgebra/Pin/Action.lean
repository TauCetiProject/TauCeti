/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Action

/-!
# The Pin group acting on its quadratic space by twisted conjugation

The Pin group is the subgroup of the Lipschitz group consisting of elements whose Clifford norm
`star x * x` is one. This file packages its twisted-conjugation homomorphism, reflection formulas,
and comparison with the independently defined Spin action. The common Lipschitz action is defined
in `TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Action`.

## Main definitions

* `CliffordAlgebra.pinToOrthogonal` is the induced orthogonal action of the Pin group.

## Main results

* `CliffordAlgebra.pinToOrthogonal_ι_apply` gives the explicit reflection
  `m ↦ m + polar Q v m • v` induced by a vector of norm `-1`.
* `CliffordAlgebra.pinToOrthogonal_spinToPin` identifies the Pin restriction with the Spin action.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2, and C. Chevalley,
*The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open QuadraticMap

universe u v

namespace CliffordAlgebra

open TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-! ### The Pin group -/

variable {Q}

variable (Q)

/-- The twisted-conjugation homomorphism `Pin(Q) → O(Q)`. -/
def pinToOrthogonal : pinGroup Q →* QuadraticMap.orthogonalGroup Q :=
  (lipschitzToOrthogonal Q).comp (pinToLipschitz Q)

variable {Q}

omit [Invertible (2 : R)] in
private theorem pinToLipschitz_inv_coe (x : pinGroup Q) :
    (((pinToLipschitz Q x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) = star (x : CliffordAlgebra Q) :=
  Units.inv_eq_of_mul_eq_one_right (by
    rw [coe_pinToLipschitz_apply]
    exact pinGroup.mul_star_self_of_mem x.2)

/-- A Pin element acts through its image in the Lipschitz group. This is not `@[simp]`: it would
rewrite away the `pinToOrthogonal` head of `ι_pinToOrthogonal_apply` and `pinToOrthogonal_ι_apply`,
which are the intended normal forms for the Pin action. -/
theorem coe_pinToOrthogonal_apply (x : pinGroup Q) (m : M) :
    ((pinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m =
      lipschitzVectorAction Q (pinToLipschitz Q x) m := by
  rw [pinToOrthogonal, MonoidHom.comp_apply, coe_lipschitzToOrthogonal_apply]

/-- The Pin action is the Lipschitz action through the canonical inclusion. -/
theorem pinToOrthogonal_eq_lipschitzToOrthogonal (x : pinGroup Q) :
    pinToOrthogonal Q x = lipschitzToOrthogonal Q (pinToLipschitz Q x) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  simp only [coe_pinToOrthogonal_apply, coe_lipschitzToOrthogonal_apply]

/-- A Pin element acts on a vector by twisted conjugation inside the Clifford algebra. Since a Pin
element is unitary, the inverse appearing there is `star`. -/
@[simp]
theorem ι_pinToOrthogonal_apply (x : pinGroup Q) (m : M) :
    ι Q (((pinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m) =
      involute (Q := Q) (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) := by
  simp only [coe_pinToOrthogonal_apply, ι_lipschitzVectorAction_apply,
    coe_pinToLipschitz_apply, pinToLipschitz_inv_coe]

/-- The reflection cut out by a Pin group vector with norm `-1`. -/
@[simp]
theorem pinToOrthogonal_ι_apply {v : M} (hv : Q v = -1) (m : M) :
    ((pinToOrthogonal Q ⟨ι Q v, ι_mem_pinGroup hv⟩ : QuadraticMap.orthogonalGroup Q) :
        M ≃ₗ[R] M) m = m + polar Q v m • v := by
  let : Invertible (Q v) := ⟨-1, by rw [hv]; ring, by rw [hv]; ring⟩
  have hinvOf : ⅟(Q v) = -1 := invOf_eq_right_inv (by rw [hv]; ring)
  have hpin : pinToLipschitz Q ⟨ι Q v, ι_mem_pinGroup hv⟩ =
      ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ :=
    Subtype.ext (Units.ext (by rw [coe_pinToLipschitz_apply, coe_unitι]))
  rw [coe_pinToOrthogonal_apply, hpin, lipschitzVectorAction_unitι, QuadraticMap.reflection_apply,
    hinvOf, neg_mul, one_mul, neg_smul, sub_neg_eq_add]

/-- On Spin, twisted conjugation agrees with the plain Spin action. -/
@[simp]
theorem pinToOrthogonal_spinToPin (x : spinGroup Q) :
    pinToOrthogonal Q (spinToPin Q x) = spinToOrthogonal Q x := by
  refine Subtype.ext (LinearEquiv.ext fun m => ι_injective Q ?_)
  rw [ι_pinToOrthogonal_apply, coe_spinToPin_apply, spinGroup.involute_eq x.2,
    coe_spinToOrthogonal_apply, ι_spinVectorAction_apply]

/-- A Spin element equal to `ι Q v * ι Q w` acts by the product
`reflectionOrthogonal Q v * reflectionOrthogonal Q w`. -/
theorem spinToOrthogonal_eq_reflection_mul_reflection_of_coe_eq
    (x : spinGroup Q) (v w : M) [Invertible (Q v)] [Invertible (Q w)]
    (hx : (x : CliffordAlgebra Q) = ι Q v * ι Q w) :
    spinToOrthogonal Q x =
      QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w := by
  let a : lipschitzGroup Q :=
    ⟨unitι Q v * unitι Q w,
      mul_mem (unitι_mem_lipschitzGroup v) (unitι_mem_lipschitzGroup w)⟩
  have hpin : pinToLipschitz Q (spinToPin Q x) = a := by
    apply Subtype.ext
    apply Units.ext
    simp only [coe_pinToLipschitz_apply, coe_spinToPin_apply, hx, a, Units.val_mul, coe_unitι]
  have hmul : a =
      (⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ : lipschitzGroup Q) *
        ⟨unitι Q w, unitι_mem_lipschitzGroup w⟩ := by
    apply Subtype.ext
    simp only [a, Subgroup.coe_mul]
  have ha : lipschitzToOrthogonal Q a =
      QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w := by
    rw [hmul, map_mul, lipschitzToOrthogonal_unitι, lipschitzToOrthogonal_unitι]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [← pinToOrthogonal_spinToPin, coe_pinToOrthogonal_apply, hpin]
  exact (coe_lipschitzToOrthogonal_apply Q a m).symm.trans
    (congrArg (fun y : QuadraticMap.orthogonalGroup Q => (y : M ≃ₗ[R] M) m) ha)

end CliffordAlgebra
