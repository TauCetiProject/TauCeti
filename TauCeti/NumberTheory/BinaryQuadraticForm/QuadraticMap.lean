/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# The binary form of a quadratic map in a basis

Let `Q` be a quadratic map on a module `M` over a commutative ring `R`, and let `e` be a basis of
`M` indexed by `Fin 2`. Then `Q(x e₀ + y e₁) = a x² + b x y + c y²` with `a = Q(e₀)`, `c = Q(e₁)`
and `b` the polar form `Q(e₀ + e₁) - Q(e₀) - Q(e₁)`. This binary quadratic form is
`QuadraticMap.toBinaryQuadraticForm Q e`. No hypothesis on `2` is needed, since the middle
coefficient is the polar form and not twice an associated bilinear form.

Writing a linear automorphism of `M` as its matrix in `e` identifies the special orthogonal group
of `Q` with the stabilizer in `SL(2, R)` of this binary form under the action `γ • f = f ∘ γ⁻¹`
(`QuadraticMap.specialOrthogonalGroupEquivStabilizer`). Combined with the description of the
automorphs of a binary form by norm-one elements of a quadratic order
(`TauCeti.BinaryQuadraticForm.stabilizerEquivUnitary`), this computes the special orthogonal
group of `Q` whenever its binary form is read from an integral form whose coefficients generate
the unit ideal of `R`, and `2` is not a zero divisor in `R`. The first identification alone holds
over any commutative ring.

## Main definitions

* `QuadraticMap.toBinaryQuadraticForm`: the binary quadratic form of `Q` in a basis indexed by
  `Fin 2`.
* `QuadraticMap.specialOrthogonalGroupEquivStabilizer`: `SO(Q)` is the stabilizer of this form
  in `SL(2, R)`.

## Main results

* `QuadraticMap.eval_toBinaryQuadraticForm`: the binary form evaluates `Q` in coordinates.
* `QuadraticMap.toLin_equiv_mem_orthogonalGroup_iff`: a matrix of determinant one is the matrix
  of an isometry exactly when it fixes the binary form.
-/

public section

open Matrix MulAction Module
open scoped MatrixGroups

namespace QuadraticMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticMap R M R) (e : Basis (Fin 2) R M)

/-- The binary quadratic form `Q(e₀) x² + B(e₀, e₁) x y + Q(e₁) y²` of `Q` in a basis `e` of a
rank-two module, where `B` is the polar form of `Q`. Its value at `(x, y)` is `Q(x e₀ + y e₁)`
(`QuadraticMap.eval_toBinaryQuadraticForm`). -/
noncomputable def toBinaryQuadraticForm : TauCeti.BinaryQuadraticForm R :=
  ⟨Q (e 0), polar Q (e 0) (e 1), Q (e 1)⟩

@[simp]
theorem toBinaryQuadraticForm_a : (Q.toBinaryQuadraticForm e).a = Q (e 0) := (rfl)

@[simp]
theorem toBinaryQuadraticForm_b : (Q.toBinaryQuadraticForm e).b = polar Q (e 0) (e 1) := (rfl)

@[simp]
theorem toBinaryQuadraticForm_c : (Q.toBinaryQuadraticForm e).c = Q (e 1) := (rfl)

/-- The binary form of `Q` in `e` evaluates `Q` in the coordinates of `e`. -/
@[simp]
theorem eval_toBinaryQuadraticForm (x y : R) :
    (Q.toBinaryQuadraticForm e).eval x y = Q (x • e 0 + y • e 1) := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, TauCeti.BinaryQuadraticForm.eval_def, toBinaryQuadraticForm_a,
    toBinaryQuadraticForm_b, toBinaryQuadraticForm_c]
  simp only [smul_eq_mul]
  ring

/-- **Isometries of a rank-two module are automorphs of its binary form.** A matrix `γ` of
determinant one is the matrix in `e` of an isometry of `Q` exactly when it fixes the binary form of
`Q` in `e`. -/
theorem toLin_equiv_mem_orthogonalGroup_iff (γ : SL(2, R)) :
    (SpecialLinearGroup.toLin_equiv e γ : M ≃ₗ[R] M) ∈ TauCeti.QuadraticMap.orthogonalGroup Q ↔
      γ ∈ stabilizer SL(2, R) (Q.toBinaryQuadraticForm e) := by
  have hv (v : M) : v = e.repr v 0 • e 0 + e.repr v 1 • e 1 := by
    simpa only [Fin.sum_univ_two] using (e.sum_repr v).symm
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, mem_stabilizer_iff]
  constructor
  · -- Both sides of `γ • f = f` evaluate `Q` at the same vector, the image under `γ⁻¹`.
    intro h
    refine TauCeti.BinaryQuadraticForm.eval_injective (funext₂ fun x y ↦ ?_)
    have hinv := Matrix.toLin_apply_fin_two e e ((γ⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) x y
    simp only [SpecialLinearGroup.inv_apply_zero_zero, SpecialLinearGroup.inv_apply_zero_one,
      SpecialLinearGroup.inv_apply_one_zero, SpecialLinearGroup.inv_apply_one_one] at hinv
    have hu (w : M) : ((SpecialLinearGroup.toLin_equiv e γ : M ≃ₗ[R] M) : M → M)
        ((SpecialLinearGroup.toLin_equiv e γ⁻¹ : M ≃ₗ[R] M) w) = w := by
      rw [← mul_apply_eq_comp, map_inv]
      simp
    have hw : (γ 1 1 * x - γ 0 1 * y) • e 0 + (-γ 1 0 * x + γ 0 0 * y) • e 1 =
        ((SpecialLinearGroup.toLin_equiv e γ⁻¹ : M ≃ₗ[R] M) : M → M) (x • e 0 + y • e 1) := by
      rw [← LinearEquiv.coe_coe, SpecialLinearGroup.toLin_equiv.toLinearMap_eq, hinv]
      congr 2
      ring
    rw [TauCeti.BinaryQuadraticForm.eval_smul, eval_toBinaryQuadraticForm,
      eval_toBinaryQuadraticForm, hw, ← h, hu]
  · intro h v
    obtain ⟨x, y, rfl⟩ : ∃ x y : R, x • e 0 + y • e 1 = v := ⟨_, _, (hv v).symm⟩
    rw [← LinearEquiv.coe_coe, SpecialLinearGroup.toLin_equiv.toLinearMap_eq,
      Matrix.toLin_apply_fin_two, ← eval_toBinaryQuadraticForm,
      ← eval_toBinaryQuadraticForm,
      ← TauCeti.BinaryQuadraticForm.eval_smul_apply γ (Q.toBinaryQuadraticForm e) x y, h]

/-- **The special orthogonal group of a rank-two module.** Writing a proper isometry of `Q` as its
matrix in a basis `e` identifies the special orthogonal group of `Q` with the stabilizer in
`SL(2, R)` of the binary form of `Q` in `e`. -/
noncomputable def specialOrthogonalGroupEquivStabilizer :
    TauCeti.QuadraticMap.specialOrthogonalGroup Q ≃*
      stabilizer SL(2, R) (Q.toBinaryQuadraticForm e) where
  toFun g := ⟨(SpecialLinearGroup.toLin_equiv e).symm
      ⟨g, (TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.property).2⟩, by
    rw [← toLin_equiv_mem_orthogonalGroup_iff, MulEquiv.apply_symm_apply]
    exact (TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.property).1⟩
  invFun γ := ⟨SpecialLinearGroup.toLin_equiv e γ,
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr
      ⟨(toLin_equiv_mem_orthogonalGroup_iff Q e γ).mpr γ.property,
        (SpecialLinearGroup.toLin_equiv e γ).property⟩⟩
  left_inv g := by
    ext1
    simp only [MulEquiv.apply_symm_apply]
  right_inv γ := by
    ext1
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  map_mul' g h := by
    ext1
    simp only [Subgroup.coe_mul, ← map_mul]
    -- The product in the special linear group of `M` is the product of the linear equivalences.
    refine congrArg _ (Subtype.ext ?_)
    rw [_root_.SpecialLinearGroup.coe_mul]

/-- The automorph attached to a proper isometry is its matrix in `e`. -/
@[simp]
theorem coe_specialOrthogonalGroupEquivStabilizer_apply
    (g : TauCeti.QuadraticMap.specialOrthogonalGroup Q) :
    ((specialOrthogonalGroupEquivStabilizer Q e g : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      LinearMap.toMatrix e e (g : M ≃ₗ[R] M).toLinearMap :=
  SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq e _

/-- The proper isometry attached to an automorph `γ` is the linear map with matrix `γ` in `e`. -/
@[simp]
theorem coe_specialOrthogonalGroupEquivStabilizer_symm_apply
    (γ : stabilizer SL(2, R) (Q.toBinaryQuadraticForm e)) :
    (((specialOrthogonalGroupEquivStabilizer Q e).symm γ : M ≃ₗ[R] M) : M →ₗ[R] M) =
      Matrix.toLin e e ((γ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) :=
  SpecialLinearGroup.toLin_equiv.toLinearMap_eq e γ

end QuadraticMap
