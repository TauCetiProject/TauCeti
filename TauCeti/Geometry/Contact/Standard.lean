/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.Distribution
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The standard contact form on `ℝ³`

On `ℝ³ = ℝ × ℝ × ℝ` with coordinates `(x, y, z)`, the one-form `α = dz - x dy`
(`TauCeti.standardContactForm`) is a contact form (`TauCeti.isContactForm_standardContactForm`).
Its exterior derivative is `dα = -dx ∧ dy`, and its kernel is the standard contact distribution
`TauCeti.standardContactDistribution ℝ`, spanned at `(x, y, z)` by `(1, 0, 0)` and `(0, 1, x)`
(`TauCeti.kerDistribution_standardContactForm`). On this frame `dα` takes the value `-1`, which is
the nondegeneracy of `dα` on the kernel.

The constant vector field `∂_z` (`TauCeti.standardReebField`) satisfies the Reeb equations
`α(∂_z) = 1` and `ι_{∂_z} dα = 0`.

The form is assembled from the constant forms `dz` and `dy` and the coordinate function `x`, so its
exterior derivative is computed by the Leibniz rule `d(x dy) = dx ∧ dy`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Example 2.1.3.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

/-- The coordinate one-form `dy` on `ℝ × ℝ × ℝ`, reading the middle coordinate. -/
private def standardDy : (ℝ × ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ × ℝ) ℝ (0 : Fin 1)
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

/-- The coordinate one-form `dz` on `ℝ × ℝ × ℝ`, reading the last coordinate. -/
private def standardDz : (ℝ × ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ × ℝ) ℝ (0 : Fin 1)
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

private theorem standardDy_apply (u : Fin 1 → ℝ × ℝ × ℝ) : standardDy u = (u 0).2.1 :=
  ContinuousAlternatingMap.ofSubsingleton_apply_apply ..

private theorem standardDz_apply (u : Fin 1 → ℝ × ℝ × ℝ) : standardDz u = (u 0).2.2 :=
  ContinuousAlternatingMap.ofSubsingleton_apply_apply ..

/-- The one-form `-x dy` on `ℝ × ℝ × ℝ`. -/
private def standardNegXDy : SmoothForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1 :=
  ⟨fun p ↦ (-p.1) • (SmoothForm.const standardDy).1 p,
    ((SmoothForm.const standardDy).isSmoothForm.fun_smul
      contDiff_fst.neg.contMDiff).mem_smoothBundleForms⟩

private theorem standardNegXDy_toRoughForm :
    standardNegXDy.1 = fun p ↦ (-p.1) • (SmoothForm.const standardDy).1 p :=
  (rfl)

private theorem mvfderiv_neg_fst (p : ℝ × ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    mvfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) (fun q : ℝ × ℝ × ℝ ↦ -q.1) p v = -v.1 := by
  have h : HasFDerivAt (fun q : ℝ × ℝ × ℝ ↦ -q.1) (-ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst.neg
  simp [mvfderiv_eq_fderiv, h.fderiv, NormedSpace.fromTangentSpace_apply]

/-- The **standard contact form** `dz - x dy` on `ℝ³ = ℝ × ℝ × ℝ`, with coordinates
`p = (x, y, z)`. -/
def standardContactForm : SmoothForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1 :=
  SmoothForm.const standardDz + standardNegXDy

/-- The standard contact form evaluates a tangent vector `v = (a, b, c)` at `p = (x, y, z)` as
`c - x b`. -/
@[simp]
theorem standardContactForm_apply (p : ℝ × ℝ × ℝ)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    standardContactForm.1 p ![v] = v.2.2 - p.1 * v.2.1 := by
  simp only [standardContactForm, standardNegXDy, SmoothForm.add_toRoughForm, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, SmoothForm.const_apply]
  rw [standardDz_apply, standardDy_apply, smul_eq_mul, neg_mul, ← sub_eq_add_neg]
  simp only [Matrix.cons_val_zero, NormedSpace.fromTangentSpace_apply (𝕜 := ℝ)]

/-- The exterior derivative of the standard contact form is `-dx ∧ dy`. -/
theorem mextDeriv_standardContactForm_apply (p : ℝ × ℝ × ℝ)
    (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    mextDeriv standardContactForm.1 p ![v, w] = w.1 * v.2.1 - v.1 * w.2.1 := by
  have hdy := (SmoothForm.isClosed_def _).1 (SmoothForm.isClosed_const standardDy)
  have hdz := (SmoothForm.isClosed_def _).1 (SmoothForm.isClosed_const standardDz)
  have hsum : mextDeriv standardContactForm.1 =
      mextDeriv (SmoothForm.const standardDz).1 + mextDeriv standardNegXDy.1 := by
    rw [← mextDerivₗ_apply, standardContactForm, map_add, SmoothForm.add_toRoughForm,
      mextDerivₗ_apply, mextDerivₗ_apply]
  rw [hsum, hdz, zero_add, standardNegXDy_toRoughForm,
    mextDeriv_fun_smul_apply
      (contDiff_fst.neg.contMDiff.contMDiffAt.mdifferentiableAt one_ne_zero)
      ((SmoothForm.const standardDy).mdifferentiableAt p), hdy]
  simp only [SmoothForm.const_apply, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, mul_zero,
    add_zero]
  rw [standardDy_apply, standardDy_apply, mvfderiv_neg_fst, mvfderiv_neg_fst]
  simp only [Matrix.cons_val_zero]
  rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) p v,
    NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) p w]
  ring

/-- The kernel of the standard contact form is the standard contact distribution. -/
theorem kerDistribution_standardContactForm :
    standardContactForm.kerDistribution = standardContactDistribution ℝ := by
  ext p v
  rw [SmoothForm.mem_kerDistribution, standardContactForm_apply, sub_eq_zero]
  exact mem_standardContactDistribution.symm

/-- The standard form `dz - x dy` on `ℝ³` is a contact form. -/
theorem isContactForm_standardContactForm : standardContactForm.IsContactForm := by
  refine SmoothForm.isContactForm_iff.2 fun p ↦ ?_
  -- Name the tangent vectors used below, so that they keep their tangent-space type.
  obtain ⟨e₁, he₁⟩ : ∃ e : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p, e = (1, 0, 0) := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p, e = (0, 1, p.1) := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p, e = (0, 0, 1) := ⟨_, rfl⟩
  refine ⟨⟨e₃, by rw [standardContactForm_apply, he₃]; norm_num⟩, fun v hv hvw ↦ ?_⟩
  rw [standardContactForm_apply, sub_eq_zero] at hv
  -- Test against the frame `(1, 0, 0)` and `(0, 1, x)` of the kernel.
  have h₁ := hvw e₁ (by rw [standardContactForm_apply, he₁]; norm_num)
  have h₂ := hvw e₂ (by rw [standardContactForm_apply, he₂]; norm_num)
  rw [mextDeriv_standardContactForm_apply] at h₁ h₂
  simp only [he₁, he₂, one_mul, zero_mul, mul_zero, sub_zero, zero_sub, neg_eq_zero,
    mul_one] at h₁ h₂
  -- The last goal `0 = (0 : TangentSpace _ p).2.2` holds by `rfl`: the zero tangent vector is by
  -- definition the zero vector `(0, 0, 0)` of `ℝ × ℝ × ℝ`.
  exact Prod.ext h₂ (Prod.ext h₁ (by rw [hv, h₁, mul_zero]; rfl))

/-- The Reeb vector field `∂_z` of `dz - x dy`, characterized by
`TauCeti.standardContactForm_apply_standardReebField` and
`TauCeti.mextDeriv_standardContactForm_standardReebField`. -/
def standardReebField (p : ℝ × ℝ × ℝ) : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p :=
  ((0, 0, 1) : ℝ × ℝ × ℝ)

/-- In coordinates, the Reeb vector field of `dz - x dy` is the constant vector `(0, 0, 1)`. -/
theorem standardReebField_apply (p : ℝ × ℝ × ℝ) :
    standardReebField p = ((0, 0, 1) : ℝ × ℝ × ℝ) :=
  (rfl)

/-- The `x`-coordinate of the Reeb vector field of `dz - x dy` is `0`. -/
@[simp]
theorem standardReebField_fst (p : ℝ × ℝ × ℝ) : (standardReebField p).1 = 0 :=
  (rfl)

/-- The `y`-coordinate of the Reeb vector field of `dz - x dy` is `0`. -/
@[simp]
theorem standardReebField_snd_fst (p : ℝ × ℝ × ℝ) : (standardReebField p).2.1 = 0 :=
  (rfl)

/-- The `z`-coordinate of the Reeb vector field of `dz - x dy` is `1`. -/
@[simp]
theorem standardReebField_snd_snd (p : ℝ × ℝ × ℝ) : (standardReebField p).2.2 = 1 :=
  (rfl)

/-- The form `dz - x dy` takes the value `1` on its Reeb vector field `∂_z`. -/
theorem standardContactForm_apply_standardReebField (p : ℝ × ℝ × ℝ) :
    standardContactForm.1 p ![standardReebField p] = 1 := by
  simp

/-- The contraction of the Reeb vector field `∂_z` with the exterior derivative of `dz - x dy`
vanishes. -/
@[simp]
theorem mextDeriv_standardContactForm_standardReebField (p : ℝ × ℝ × ℝ)
    (w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    mextDeriv standardContactForm.1 p ![standardReebField p, w] = 0 := by
  rw [mextDeriv_standardContactForm_apply]
  simp [standardReebField]

end TauCeti
