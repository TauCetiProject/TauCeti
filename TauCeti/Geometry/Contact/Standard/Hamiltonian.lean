/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flow
import TauCeti.Geometry.Manifold.Flow.NormedSpace

/-!
# Contact Hamiltonian vector fields and flows of the standard contact form

On `ℝ³ = ℝ × ℝ × ℝ` with coordinates `p = (x, y, z)`, let `α = dz - x dy` be the standard contact
form (`TauCeti.standardContactForm`), with `dα = -dx ∧ dy` and Reeb vector field `R_α = ∂_z`. This
file computes its contact Hamiltonian vector fields `X_f`, defined by `α(X_f) = f` and
`ι_(X_f) dα = (R_α f) α - df`, and the flows of two of them.

Writing `f_x`, `f_y`, `f_z` for the partial derivatives of `f`,

`X_f = (x f_z + f_y) ∂_x - f_x ∂_y + (f - x f_x) ∂_z`

(`TauCeti.contactHamiltonianVectorField_standardContactForm`). Indeed the `∂_z`-component makes
`α(X_f) = f`, and for a tangent vector `v` the two sides of the contraction equation are
`ι_(X_f) dα (v) = -f_x v_x - (x f_z + f_y) v_y` and `f_z (v_z - x v_y) - df(v)`. The formula holds
for every function `f`, with the Fréchet derivative of `f` read as zero where `f` is not
differentiable, as in the definition of `X_f`. For the coordinate functions it gives

`X_x = -∂_y`,  `X_y = ∂_x + y ∂_z`,  `X_z = x ∂_x + z ∂_z`,

and for the constant `1` the Reeb field `∂_z`, as for every contact form
(`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_one`).

The flow of `X_z` is the dilation `φₜ(x, y, z) = (eᵗ x, y, eᵗ z)`: its orbits are the integral
curves of `X_z` (`TauCeti.isMIntegralCurve_contactHamiltonianVectorField_standardContactForm_z`),
so `X_z` is complete and `φₜ` is its maximal flow
(`TauCeti.flowOf_contactHamiltonianVectorField_standardContactForm_z`). It rescales the contact
form, `φₜ^* α = eᵗ α`
(`TauCeti.mpullback_flowOf_contactHamiltonianVectorField_standardContactForm_z`), which is the
factor `exp (∫₀ᵗ (R_α z)(φₛ p) ds) = eᵗ` of the general rescaling law
`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply`, as `R_α z = 1`. So
`φₜ` preserves the coorientation, and it is strict only for `t = 0`
(`TauCeti.mpullback_flowOf_contactHamiltonianVectorField_standardContactForm_z_eq_self_iff`).

The Reeb flow of `α` is the translation `(x, y, z) ↦ (x, y, z + t)`
(`TauCeti.flowOf_reebVectorField_standardContactForm`), which is complete and, as for every Reeb
flow, consists of strict contactomorphisms.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians and their flows).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

/-! ### Contact Hamiltonian vector fields -/

/-- **Contact Hamiltonian vector fields of `dz - x dy`.** For every function `f` on `ℝ³`, the
contact Hamiltonian vector field of `f` for the standard contact form is
`X_f = (x f_z + f_y) ∂_x - f_x ∂_y + (f - x f_x) ∂_z`, where `f_x = df(∂_x)`, `f_y = df(∂_y)` and
`f_z = df(∂_z)`. -/
theorem contactHamiltonianVectorField_standardContactForm (f : ℝ × ℝ × ℝ → ℝ)
    (p : ℝ × ℝ × ℝ) :
    (standardContactForm.contactHamiltonianVectorField f p : ℝ × ℝ × ℝ) =
      (p.1 * fderiv ℝ f p (0, 0, 1) + fderiv ℝ f p (0, 1, 0), -fderiv ℝ f p (1, 0, 0),
        f p - p.1 * fderiv ℝ f p (1, 0, 0)) := by
  -- The candidate field, which satisfies the defining equations of `X_f`.
  let X : (q : ℝ × ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q := fun q ↦
    ((q.1 * fderiv ℝ f q (0, 0, 1) + fderiv ℝ f q (0, 1, 0), -fderiv ℝ f q (1, 0, 0),
      f q - q.1 * fderiv ℝ f q (1, 0, 0)) : ℝ × ℝ × ℝ)
  have hX : standardContactForm.IsContactHamiltonianVectorField f X := by
    refine SmoothForm.isContactHamiltonianVectorField_iff.2 fun q ↦ ⟨?_, fun v ↦ ?_⟩
    · rw [standardContactForm_apply]
      simp only [X]
      ring
    · -- Expand `df_q(v)` in the coordinates of `v`.
      have hv : (v : ℝ × ℝ × ℝ) = v.1 • ((1, 0, 0) : ℝ × ℝ × ℝ) +
          v.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ) + v.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
      have hdf : fderiv ℝ f q v = v.1 * fderiv ℝ f q (1, 0, 0) +
          v.2.1 * fderiv ℝ f q (0, 1, 0) + v.2.2 * fderiv ℝ f q (0, 0, 1) := by
        conv_lhs => rw [hv]
        simp only [map_add, map_smul, smul_eq_mul]
      rw [mextDeriv_standardContactForm_apply, standardContactForm_apply,
        reebVectorField_standardContactForm, mvfderiv_eq_fderiv_apply, mvfderiv_eq_fderiv_apply,
        standardReebField_apply, hdf]
      simp only [X]
      ring
  exact congrFun ((isContactForm_standardContactForm.isContactHamiltonianVectorField_iff_eq).1
    hX).symm p

/-- The contact Hamiltonian vector field of the coordinate `x` for `dz - x dy` is `-∂_y`. -/
@[simp]
theorem contactHamiltonianVectorField_standardContactForm_x (p : ℝ × ℝ × ℝ) :
    (standardContactForm.contactHamiltonianVectorField (fun q ↦ q.1) p : ℝ × ℝ × ℝ) =
      (0, -1, 0) := by
  rw [contactHamiltonianVectorField_standardContactForm, fderiv_fst]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-- The contact Hamiltonian vector field of the coordinate `y` for `dz - x dy` is
`∂_x + y ∂_z`. -/
@[simp]
theorem contactHamiltonianVectorField_standardContactForm_y (p : ℝ × ℝ × ℝ) :
    (standardContactForm.contactHamiltonianVectorField (fun q ↦ q.2.1) p : ℝ × ℝ × ℝ) =
      (1, 0, p.2.1) := by
  have hd : HasFDerivAt (fun q : ℝ × ℝ × ℝ ↦ q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  rw [contactHamiltonianVectorField_standardContactForm, hd.fderiv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-- The contact Hamiltonian vector field of the coordinate `z` for `dz - x dy` is
`x ∂_x + z ∂_z`. -/
@[simp]
theorem contactHamiltonianVectorField_standardContactForm_z (p : ℝ × ℝ × ℝ) :
    (standardContactForm.contactHamiltonianVectorField (fun q ↦ q.2.2) p : ℝ × ℝ × ℝ) =
      (p.1, 0, p.2.2) := by
  have hd : HasFDerivAt (fun q : ℝ × ℝ × ℝ ↦ q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  rw [contactHamiltonianVectorField_standardContactForm, hd.fderiv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-! ### The flow of `X_z` -/

/-- The contact Hamiltonian vector field `X_z = x ∂_x + z ∂_z` of `dz - x dy` is `C¹`. -/
private theorem contMDiff_contactHamiltonianVectorField_standardContactForm_z :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ).tangent 1
      (fun q ↦ (⟨q, standardContactForm.contactHamiltonianVectorField (fun q ↦ q.2.2) q⟩ :
        TangentBundle 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ))) :=
  isContactForm_standardContactForm.contMDiff_contactHamiltonianVectorField (n := 1) (by simp)
    (contDiff_snd.snd).contMDiff

/-- The orbits `t ↦ (eᵗ x, y, eᵗ z)` of the dilation are the integral curves of the contact
Hamiltonian vector field `X_z = x ∂_x + z ∂_z` of `dz - x dy`. -/
theorem isMIntegralCurve_contactHamiltonianVectorField_standardContactForm_z
    (p : ℝ × ℝ × ℝ) :
    IsMIntegralCurve (fun t ↦ (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2))
      (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.2) := by
  intro t
  have hd : HasDerivAt (fun t ↦ (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2))
      (Real.exp t * p.1, 0, Real.exp t * p.2.2) t :=
    ((Real.hasDerivAt_exp t).mul_const p.1).prodMk
      ((hasDerivAt_const t p.2.1).prodMk ((Real.hasDerivAt_exp t).mul_const p.2.2))
  refine hasMFDerivAt_iff_hasFDerivAt.2 ?_
  rw [contactHamiltonianVectorField_standardContactForm_z]
  exact hd.hasFDerivAt

/-- The contact Hamiltonian vector field `X_z = x ∂_x + z ∂_z` of `dz - x dy` is complete. -/
theorem isCompleteVectorField_contactHamiltonianVectorField_standardContactForm_z :
    IsCompleteVectorField (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.2) :=
  isCompleteVectorField_of_forall_exists_isMIntegralCurve fun p ↦
    ⟨_, by simp, isMIntegralCurve_contactHamiltonianVectorField_standardContactForm_z p⟩

/-- **The flow of `X_z` is the dilation.** The maximal flow of the contact Hamiltonian vector field
`X_z = x ∂_x + z ∂_z` of `dz - x dy` is `φₜ(x, y, z) = (eᵗ x, y, eᵗ z)`. -/
theorem flowOf_contactHamiltonianVectorField_standardContactForm_z (t : ℝ) (p : ℝ × ℝ × ℝ) :
    flowOf (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.2) t p =
      (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2) := by
  have h := flowOf_eq_of_isMIntegralCurve
    contMDiff_contactHamiltonianVectorField_standardContactForm_z
    (isMIntegralCurve_contactHamiltonianVectorField_standardContactForm_z p) t
  simpa using h

/-- **The flow of `X_z` rescales the contact form by `eᵗ`.** The time-`t` map
`φₜ(x, y, z) = (eᵗ x, y, eᵗ z)` of the contact Hamiltonian vector field of `z` pulls `dz - x dy`
back to `eᵗ (dz - x dy)`. -/
theorem mpullback_flowOf_contactHamiltonianVectorField_standardContactForm_z (t : ℝ) :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
        (flowOf (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.2) t)
        standardContactForm.val =
      Real.exp t • standardContactForm.val := by
  -- In the coordinates `(q, p, z) = (y, x, z)` of `innerProductContactForm ℝ`, given by the
  -- involution `σ`, the time-`t` map is `(q, p, z) ↦ (q, eᵗ p, eᵗ z)`, which rescales that form
  -- by `eᵗ` (`mpullback_innerProductContactForm_smul`).
  let σ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦ (p.2.1, p.1, p.2.2)
  let S : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦ (p.1, Real.exp t • p.2)
  have hσ : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) σ :=
    (show ContDiff ℝ 1 σ by fun_prop).contMDiff.mdifferentiable one_ne_zero
  have hS : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) S :=
    (show ContDiff ℝ 1 S by fun_prop).contMDiff.mdifferentiable one_ne_zero
  have hφ : flowOf (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.2) t =
      fun p ↦ (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2) :=
    funext (flowOf_contactHamiltonianVectorField_standardContactForm_z t)
  have hφd : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
      (fun p : ℝ × ℝ × ℝ ↦ (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2)) :=
    (show ContDiff ℝ 1 fun p : ℝ × ℝ × ℝ ↦ (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2) by
      fun_prop).contMDiff.mdifferentiable one_ne_zero
  have hσφ : σ ∘ (fun p : ℝ × ℝ × ℝ ↦ (Real.exp t * p.1, p.2.1, Real.exp t * p.2.2)) = S ∘ σ := by
    funext p
    simp [σ, S]
  rw [hφ, ← mpullback_innerProductContactForm_real, ← mpullback_comp hφd hσ, hσφ,
    mpullback_comp hσ hS, mpullback_innerProductContactForm_smul, SmoothForm.smul_toRoughForm,
    mpullback_smul]

/-- The time-`t` map of the flow of `X_z` pulls `dz - x dy` back to itself only for `t = 0`. -/
theorem mpullback_flowOf_contactHamiltonianVectorField_standardContactForm_z_eq_self_iff (t : ℝ) :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
        (flowOf (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.2) t)
        standardContactForm.val = standardContactForm.val ↔ t = 0 := by
  rw [mpullback_flowOf_contactHamiltonianVectorField_standardContactForm_z]
  refine ⟨fun h ↦ ?_, fun ht ↦ by rw [ht, Real.exp_zero, one_smul]⟩
  have h₀ := congrFun h 0
  rw [Pi.smul_apply] at h₀
  have h₁ : Real.exp t = 1 := smul_left_injective ℝ
    (isContactForm_standardContactForm.apply_ne_zero 0) (h₀.trans (one_smul ℝ _).symm)
  rwa [Real.exp_eq_one_iff] at h₁

/-! ### The Reeb flow -/

/-- The orbits `t ↦ (x, y, z + t)` of the translation are the integral curves of the Reeb vector
field `∂_z` of `dz - x dy`. -/
theorem isMIntegralCurve_reebVectorField_standardContactForm (p : ℝ × ℝ × ℝ) :
    IsMIntegralCurve (fun t ↦ (p.1, p.2.1, p.2.2 + t)) standardContactForm.reebVectorField := by
  have h : (fun t : ℝ ↦ p + t • ((0, 0, 1) : ℝ × ℝ × ℝ)) = fun t ↦ (p.1, p.2.1, p.2.2 + t) := by
    funext t
    ext <;> simp
  rw [funext reebVectorField_standardContactForm, funext standardReebField_apply, ← h]
  exact isMIntegralCurve_translation _ p

/-- The Reeb vector field `∂_z` of `dz - x dy` is complete. -/
theorem isCompleteVectorField_reebVectorField_standardContactForm :
    IsCompleteVectorField standardContactForm.reebVectorField := by
  rw [funext reebVectorField_standardContactForm, funext standardReebField_apply]
  exact isCompleteVectorField_const _

/-- **The Reeb flow of `dz - x dy` is the translation** `(x, y, z) ↦ (x, y, z + t)`. Its time-`t`
maps are strict contactomorphisms
(`TauCeti.SmoothForm.IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField`
with `TauCeti.isCompleteVectorField_reebVectorField_standardContactForm`). -/
theorem flowOf_reebVectorField_standardContactForm (t : ℝ) (p : ℝ × ℝ × ℝ) :
    flowOf standardContactForm.reebVectorField t p = (p.1, p.2.1, p.2.2 + t) := by
  rw [funext reebVectorField_standardContactForm, funext standardReebField_apply, flowOf_const]
  ext <;> simp

end TauCeti
