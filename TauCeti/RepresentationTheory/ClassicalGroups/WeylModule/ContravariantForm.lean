/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower.Form
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# The contravariant Hermitian form on a rational Weyl module

Restricting the standard Hermitian form `TauCeti.tensorPowerForm` of the ambient tensor power to
the Weyl module of a shape gives the positive definite Hermitian form `TauCeti.weylForm`. It is
contravariant for the determinant twists `TauCeti.rationalWeylRep`, because the determinant of the
conjugate transpose is the conjugate of the determinant.

Since `V_λ` is irreducible, over `ℂ` every contravariant form on `V_λ` is a scalar multiple of
`TauCeti.weylForm` (`Representation.exists_forall_apply_eq_mul_apply`). It is a Hermitian,
group-level counterpart of the Shapovalov form, and it is the form for which the Gelfand–Tsetlin
basis is orthonormal.

## Main definitions

* `TauCeti.weylForm`: the restriction of the standard form to the Weyl module of a shape.

## Main results

* `TauCeti.isSymm_weylForm`, `TauCeti.weylForm_apply_self_pos`, `TauCeti.separatingRight_weylForm`:
  it is Hermitian, positive definite and separating.
* `TauCeti.weylForm_rationalWeylRep_apply`: contravariance.
-/

public section

open Matrix
open scoped ComplexOrder TensorProduct

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] (n : ℕ)

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

/-- The form on a Weyl module is separating: a vector pairing to zero with everything vanishes. -/
theorem separatingRight_weylForm (μ : YoungDiagram) : (weylForm (𝕜 := 𝕜) n μ).SeparatingRight :=
  fun y hy ↦ by_contra fun hy0 ↦ (weylForm_apply_self_pos hy0).ne' (hy y)

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
