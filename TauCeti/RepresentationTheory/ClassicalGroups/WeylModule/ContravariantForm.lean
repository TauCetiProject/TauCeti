/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# The contravariant Hermitian form on a rational Weyl module

The tensor power `(𝕜ⁿ)^{⊗d}` over `𝕜 = ℝ` or `ℂ` carries the positive definite Hermitian form
`TauCeti.tensorPowerForm` for which the monomial basis is orthonormal; on pure tensors it is the
product of the standard Hermitian forms of the factors. It is **contravariant**: the adjoint of the
action of `g : GL n 𝕜` is the action of the conjugate transpose `star g`. Restricting it to the Weyl
module of a shape gives the positive definite Hermitian form `TauCeti.weylForm`, which stays
contravariant for the determinant twists `TauCeti.rationalWeylRep`, because the determinant of the
conjugate transpose is the conjugate of the determinant.

Since `V_λ` is irreducible, over `ℂ` every contravariant form on `V_λ` is a scalar multiple of
`TauCeti.weylForm` (`Representation.exists_forall_apply_eq_mul_apply`). It is a Hermitian,
group-level counterpart of the Shapovalov form, and it is the form for which the Gelfand–Tsetlin
basis is orthonormal.

## Main definitions

* `TauCeti.tensorPowerForm`: the standard Hermitian form on `(𝕜ⁿ)^{⊗d}`.
* `TauCeti.weylForm`: its restriction to the Weyl module of a shape.

## Main results

* `TauCeti.tensorPowerForm_tprod_tprod`: its value on pure tensors.
* `TauCeti.tensorPowerForm_tensorPowerRep_apply` and `TauCeti.weylForm_rationalWeylRep_apply`:
  contravariance.
-/

public section

open Matrix Module
open scoped ComplexOrder TensorProduct

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] (n d : ℕ)

/-- **The standard Hermitian form on a tensor power**: the form on `(𝕜ⁿ)^{⊗d}` for which the
monomial basis `TauCeti.tensorPowerBasis` is orthonormal. By `TauCeti.tensorPowerForm_tprod_tprod`
it is the product of the standard Hermitian forms of the tensor factors, so it does not depend on
the basis. -/
noncomputable def tensorPowerForm :
    (⨂[𝕜]^d (Fin n → 𝕜)) →ₗ⋆[𝕜] (⨂[𝕜]^d (Fin n → 𝕜)) →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _
    (fun x y ↦ ∑ w, star ((tensorPowerBasis 𝕜 n d).repr x w) * (tensorPowerBasis 𝕜 n d).repr y w)
    (by simp [add_mul, Finset.sum_add_distrib])
    (by simp [Finset.mul_sum, mul_assoc])
    (by simp [mul_add, Finset.sum_add_distrib])
    (by simp [Finset.mul_sum, mul_left_comm])

variable {n d}

/-- The value of the standard Hermitian form in the coordinates of the monomial basis. -/
theorem tensorPowerForm_apply (x y : ⨂[𝕜]^d (Fin n → 𝕜)) :
    tensorPowerForm n d x y =
      ∑ w, star ((tensorPowerBasis 𝕜 n d).repr x w) * (tensorPowerBasis 𝕜 n d).repr y w :=
  (rfl)

/-- On pure tensors, the standard Hermitian form of a tensor power is the product of the standard
Hermitian forms of the factors. -/
@[simp]
theorem tensorPowerForm_tprod_tprod (x y : Fin d → Fin n → 𝕜) :
    tensorPowerForm n d (PiTensorProduct.tprod 𝕜 x) (PiTensorProduct.tprod 𝕜 y) =
      ∏ i, star (x i) ⬝ᵥ y i := by
  simp only [tensorPowerForm_apply, tensorPowerBasis_def, Basis.piTensorProduct_repr_tprod_apply,
    dotProduct, Finset.prod_univ_sum, Fintype.piFinset_univ, star_prod, ← Finset.prod_mul_distrib]
  simp

/-- The standard form of a tensor power is Hermitian. -/
theorem isSymm_tensorPowerForm : (tensorPowerForm (𝕜 := 𝕜) n d).IsSymm where
  eq x y := by
    simp [tensorPowerForm_apply, mul_comm]

/-- The standard form of a tensor power is positive definite. -/
theorem tensorPowerForm_apply_self_pos {x : ⨂[𝕜]^d (Fin n → 𝕜)} (hx : x ≠ 0) :
    0 < tensorPowerForm n d x x := by
  obtain ⟨w, hw⟩ : ∃ w, (tensorPowerBasis 𝕜 n d).repr x w ≠ 0 := by
    contrapose! hx
    exact (tensorPowerBasis 𝕜 n d).repr.map_eq_zero_iff.mp (Finsupp.ext hx)
  rw [tensorPowerForm_apply]
  exact Finset.sum_pos' (fun _ _ ↦ star_mul_self_nonneg _)
    ⟨w, Finset.mem_univ w, by
      rw [RCLike.star_def, RCLike.conj_mul]
      exact_mod_cast pow_pos (norm_pos_iff.mpr hw) 2⟩

/-- **Contravariance of the standard form.** The adjoint of the action of `g` on a tensor power is
the action of the conjugate transpose `star g`. -/
theorem tensorPowerForm_tensorPowerRep_apply (g : GL (Fin n) 𝕜) (x y : ⨂[𝕜]^d (Fin n → 𝕜)) :
    tensorPowerForm n d (tensorPowerRep 𝕜 n d g x) y =
      tensorPowerForm n d x (tensorPowerRep 𝕜 n d (star g) y) := by
  have h : (tensorPowerForm n d).comp (tensorPowerRep 𝕜 n d g) =
      (tensorPowerForm n d).compl₂ (tensorPowerRep 𝕜 n d (star g)) := by
    refine (tensorPowerBasis 𝕜 n d).ext fun u ↦ (tensorPowerBasis 𝕜 n d).ext fun v ↦ ?_
    simp [Representation.tensorPower_apply, PiTensorProduct.map_tprod, star_eq_conjTranspose,
      Units.coe_star]
  exact LinearMap.congr_fun₂ h x y

variable (n)

/-- **The contravariant Hermitian form on the Weyl module of a shape**: the restriction of the
standard Hermitian form `TauCeti.tensorPowerForm` of the ambient tensor power. -/
noncomputable def weylForm (μ : YoungDiagram) :
    (weylModuleOfShape 𝕜 n μ).toSubmodule →ₗ⋆[𝕜] (weylModuleOfShape 𝕜 n μ).toSubmodule →ₗ[𝕜] 𝕜 :=
  (tensorPowerForm n μ.card).domRestrict₁₂ _ _

variable {n}

/-- `TauCeti.weylForm` is computed in the ambient tensor power. -/
theorem weylForm_apply {μ : YoungDiagram} (x y : (weylModuleOfShape 𝕜 n μ).toSubmodule) :
    weylForm n μ x y = tensorPowerForm n μ.card (x : ⨂[𝕜]^μ.card (Fin n → 𝕜)) y :=
  (rfl)

/-- The form on a Weyl module is Hermitian. -/
theorem isSymm_weylForm (μ : YoungDiagram) : (weylForm (𝕜 := 𝕜) n μ).IsSymm :=
  isSymm_tensorPowerForm.domRestrict _

/-- The form on a Weyl module is positive definite. -/
theorem weylForm_apply_self_pos {μ : YoungDiagram} {x : (weylModuleOfShape 𝕜 n μ).toSubmodule}
    (hx : x ≠ 0) : 0 < weylForm n μ x x :=
  tensorPowerForm_apply_self_pos fun h ↦ hx (Subtype.ext h)

/-- **Contravariance of the form on a rational Weyl module.** The adjoint of the action of `g` on
`V_λ` is the action of the conjugate transpose `star g`. The determinant twist is compatible with
the form because the determinant of `star g` is the conjugate of the determinant of `g`. -/
theorem weylForm_rationalWeylRep_apply (l : DominantWeight n) (g : GL (Fin n) 𝕜)
    (x y : (weylModuleOfShape 𝕜 n l.detShiftShape).toSubmodule) :
    weylForm n _ (rationalWeylRep 𝕜 n l g x) y =
      weylForm n _ x (rationalWeylRep 𝕜 n l (star g) y) := by
  have hdet : Matrix.GeneralLinearGroup.det (star g) ^ l.detShift =
      star (Matrix.GeneralLinearGroup.det g ^ l.detShift) := by
    rw [star_zpow]
    congr 1
    exact Units.ext (by simp [Units.coe_star, star_eq_conjTranspose])
  simp only [rationalWeylRep_apply, map_smulₛₗ, LinearMap.smul_apply, hdet, weylForm_apply,
    weylRepOfShape_apply_coe, tensorPowerForm_tensorPowerRep_apply, Units.coe_star,
    RingHom.id_apply, RCLike.star_def]

end TauCeti
