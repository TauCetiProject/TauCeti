/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Hopf
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# The square and the inverse of the antipode of `U_q(sl₂)`

For a nonzero parameter `q`, the antipode `S` of `UqSl2 q` need not be involutive. Its square is
the inner automorphism given by conjugation with the group-like element `K⁻¹`:

`S² x = K⁻¹ x K`, so that `S² E = q⁻² E`, `S² F = q² F` and `S² K = K`.

Since conjugation by a unit is bijective, so is `S`. Being antimultiplicative, `S` is therefore an
algebra isomorphism from `UqSl2 q` onto its opposite algebra, whose inverse is

`S⁻¹ x = K S(x) K⁻¹`, so that `S⁻¹ E = -E K⁻¹`, `S⁻¹ F = -K F` and `S⁻¹ K = K⁻¹`.

Bijectivity of the antipode is what makes the left duals of finite-dimensional modules, built with
`S⁻¹`, available alongside the right duals built with `S`.

## Main results

* `TauCeti.UqSl2.antipode_antipode`: `S (S x) = K⁻¹ x K`.
* `TauCeti.UqSl2.antipode_bijective`: the antipode is bijective.
* `TauCeti.UqSl2.antipodeEquiv`: the antipode as an algebra isomorphism onto the opposite
  algebra.
* `TauCeti.UqSl2.antipodeEquiv_symm_apply`: its inverse is `x ↦ K S(x) K⁻¹`.

## References

* A. Virelizier, *Quantum groups*, Section 2.3, for this rank-one Hopf convention.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VII.1, for the Hopf
  structure on `U_q(sl₂)` in the opposite coproduct convention.
-/

public section

open HopfAlgebra

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-- Applying the opposite-valued antipode twice is conjugation by `K⁻¹`. -/
private theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp q)).comp (antipodeOp q) =
      (MulSemiringAction.toAlgEquiv ℂ (UqSl2 q) (ConjAct.toConjAct (kUnit q)⁻¹)).toAlgHom := by
  apply hom_ext <;>
    simp [ConjAct.units_smul_def, antipode_mul_antidistrib, mul_assoc]

/-- The square of the antipode is conjugation by `K⁻¹`. -/
theorem antipode_antipode (x : UqSl2 q) :
    antipode ℂ (antipode ℂ x) = kInv q * x * k q := by
  simpa [ConjAct.units_smul_def] using
    AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp q) x

/-- The square of the antipode rescales the raising generator by `q⁻²`. -/
theorem antipode_antipode_e : antipode ℂ (antipode ℂ (e q)) = q⁻¹ ^ 2 • e q := by
  rw [antipode_antipode, kInv_mul_e, smul_mul_assoc, mul_assoc, kInv_mul_k, mul_one]

/-- The square of the antipode rescales the lowering generator by `q²`. -/
theorem antipode_antipode_f : antipode ℂ (antipode ℂ (f q)) = q ^ 2 • f q := by
  rw [antipode_antipode, kInv_mul_f, smul_mul_assoc, mul_assoc, kInv_mul_k, mul_one]

/-- The antipode of `UqSl2 q` is bijective. -/
theorem antipode_bijective :
    Function.Bijective (antipode ℂ : UqSl2 q →ₗ[ℂ] UqSl2 q) := by
  have h : Function.Bijective ((antipode ℂ : UqSl2 q →ₗ[ℂ] UqSl2 q) ∘ antipode ℂ) := by
    convert (MulSemiringAction.toAlgEquiv ℂ (UqSl2 q)
      (ConjAct.toConjAct (kUnit q)⁻¹)).bijective using 1
    ext x
    simp [antipode_antipode, ConjAct.units_smul_def]
  exact ⟨.of_comp h.1, .of_comp h.2⟩

/-- The antipode of `UqSl2 q`, as an algebra isomorphism onto the opposite algebra. -/
noncomputable def antipodeEquiv : UqSl2 q ≃ₐ[ℂ] (UqSl2 q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp q)
    ((MulOpposite.opEquiv.bijective).comp (antipode_bijective q))

/-- The algebra homomorphism underlying `antipodeEquiv` is `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_toAlgHom : (antipodeEquiv q).toAlgHom = antipodeOp q := (rfl)

/-- The isomorphism `antipodeEquiv` acts by the antipode. -/
@[simp]
theorem antipodeEquiv_apply (x : UqSl2 q) :
    antipodeEquiv q x = MulOpposite.op (antipode ℂ x) := (rfl)

/-- The inverse of the antipode is `x ↦ K S(x) K⁻¹`. -/
theorem antipodeEquiv_symm_apply (x : (UqSl2 q)ᵐᵒᵖ) :
    (antipodeEquiv q).symm x = k q * antipode ℂ x.unop * kInv q := by
  rw [AlgEquiv.symm_apply_eq, antipodeEquiv_apply, ← MulOpposite.unop_inj, MulOpposite.unop_op]
  simp only [antipode_mul_antidistrib, antipode_antipode, antipode_k, antipode_kInv]
  -- `K (K⁻¹ x K K⁻¹) = x`
  rw [mul_assoc, mul_assoc, k_mul_kInv, mul_one, ← mul_assoc, k_mul_kInv, one_mul]

/-- The inverse of the antipode sends `E` to `-E K⁻¹`. -/
@[simp]
theorem antipodeEquiv_symm_op_e :
    (antipodeEquiv q).symm (MulOpposite.op (e q)) = -(e q * kInv q) := by
  simp [antipodeEquiv_symm_apply, ← mul_assoc]

/-- The inverse of the antipode sends `F` to `-K F`. -/
@[simp]
theorem antipodeEquiv_symm_op_f :
    (antipodeEquiv q).symm (MulOpposite.op (f q)) = -(k q * f q) := by
  simp [antipodeEquiv_symm_apply, mul_assoc]

/-- The inverse of the antipode sends `K` to `K⁻¹`. -/
@[simp]
theorem antipodeEquiv_symm_op_k :
    (antipodeEquiv q).symm (MulOpposite.op (k q)) = kInv q := by
  simp [antipodeEquiv_symm_apply]

/-- The inverse of the antipode sends `K⁻¹` to `K`. -/
@[simp]
theorem antipodeEquiv_symm_op_kInv :
    (antipodeEquiv q).symm (MulOpposite.op (kInv q)) = k q := by
  simp [antipodeEquiv_symm_apply, mul_assoc]

end TauCeti.UqSl2
