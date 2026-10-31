/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The standard contact forms

On `ℝ³ = ℝ × ℝ × ℝ` with coordinates `(x, y, z)`, the one-form `α = dz - x dy`
(`TauCeti.standardContactForm`) is a contact form (`TauCeti.isContactForm_standardContactForm`).
Its exterior derivative is `dα = -dx ∧ dy`, and its kernel is the standard contact distribution
`TauCeti.standardContactDistribution ℝ`, spanned at `(x, y, z)` by `(1, 0, 0)` and `(0, 1, x)`
(`TauCeti.kerDistribution_standardContactForm`). On this frame `dα` takes the value `-1`, which is
the nondegeneracy of `dα` on the kernel.

The constant vector field `∂_z` (`TauCeti.standardReebField`) satisfies the Reeb equations
`α(∂_z) = 1` and `ι_{∂_z} dα = 0`, so it is the vector field corresponding to `α` itself under the
contact flat equivalence (`TauCeti.contactFlatEquiv_symm_standardContactForm`).

The form is assembled from the constant forms `dz` and `dy` and the coordinate function `x`, so its
exterior derivative is computed by the Leibniz rule `d(x dy) = dx ∧ dy`.

In every dimension, let `V` be a real inner product space and give `V × V × ℝ` the coordinates
`(q, p, z)`. The one-form `α = dz - ⟪p, dq⟫` (`TauCeti.innerProductContactForm`) is a contact form
(`TauCeti.isContactForm_innerProductContactForm`), and no finite-dimensionality is needed. For
`V = EuclideanSpace ℝ (Fin n)` it is the standard form `dz - Σᵢ pᵢ dqᵢ` on `ℝ^(2n+1)`
(`TauCeti.innerProductContactForm_euclideanSpace_apply`). Its exterior derivative
`Σᵢ dqᵢ ∧ dpᵢ` is the standard symplectic form `TauCeti.stdSymplecticForm` of the `(q, p)`
coordinates
(`TauCeti.mextDeriv_innerProductContactForm_apply`), and its kernel at `(q, p, z)` consists of
the vectors
`(u, v, w)` with `w = ⟪p, u⟫` (`TauCeti.mem_kerDistribution_innerProductContactForm`). The proof of
contactness tests a kernel vector `(u, v, w)` against the kernel vectors `(0, u, 0)` and
`(v, 0, ⟪p, v⟫)`, on which `dα` takes the values `‖u‖²` and `-‖v‖²`.

For `V = ℝ` this is the form `dz - x dy` above in the coordinates `(q, p, z) = (y, x, z)`
(`TauCeti.mpullback_innerProductContactForm_real`). The linear map
`(q, p, z) ↦ (q, -p, -z)` preserves the contact structure and reverses its coorientation,
pulling `α` back to `-α`
(`TauCeti.mpullback_innerProductContactForm_neg`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.1, in particular Example 2.1.3.
-/

public section

noncomputable section

open scoped Manifold InnerProductSpace ContDiff

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

/-- For the standard contact form `dz - x dy` on `ℝ³`, the vector field corresponding to the form
itself under the contact flat equivalence is its Reeb vector field `∂_z`. -/
theorem contactFlatEquiv_symm_standardContactForm :
    ⇑(isContactForm_standardContactForm.contactFlatEquiv.symm standardContactForm) =
      standardReebField :=
  funext fun p ↦ (isContactForm_standardContactForm.isInvertible_contactFlat p).injective <| by
    rw [SmoothForm.IsContactForm.contactFlat_contactFlatEquiv_symm,
      isContactForm_standardContactForm.contactFlat_apply_eq_iff.2
        ⟨standardContactForm_apply_standardReebField p,
          mextDeriv_standardContactForm_standardReebField p⟩]

section InnerProductSpace

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The family of covectors `(u, v, w) ↦ w - ⟪p, u⟫` at the points `(q, p, z)`. -/
private def innerProductContactFormFun (x : V × V × ℝ) : (V × V × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (V × V × ℝ) ℝ (0 : Fin 1)
    ((ContinuousLinearMap.snd ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ)) -
      (innerSL ℝ x.2.1).comp (ContinuousLinearMap.fst ℝ V (V × ℝ)))

private theorem innerProductContactFormFun_apply (x : V × V × ℝ) (v : Fin 1 → V × V × ℝ) :
    innerProductContactFormFun V x v = (v 0).2.2 - ⟪x.2.1, (v 0).1⟫_ℝ := by
  simp [innerProductContactFormFun]

private theorem contDiff_innerProductContactFormFun : ContDiff ℝ ∞ (innerProductContactFormFun V) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V × V × ℝ) (F := ℝ)
    (0 : Fin 1)).contDiff.comp <| contDiff_const.sub <|
      ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).contDiff.comp
        (contDiff_fst.comp contDiff_snd)).clm_comp contDiff_const

/-- The **standard contact form** `α = dz - ⟪p, dq⟫` on `V × V × ℝ`, with coordinates
`(q, p, z)`. For `V = EuclideanSpace ℝ (Fin n)` this is the form `dz - Σᵢ pᵢ dqᵢ` on `ℝ^(2n+1)`
(`TauCeti.innerProductContactForm_euclideanSpace_apply`). Its exterior derivative is the standard
symplectic form `TauCeti.stdSymplecticForm` of the `(q, p)` coordinates
(`TauCeti.mextDeriv_innerProductContactForm_apply`). -/
def innerProductContactForm : SmoothForm 𝓘(ℝ, V × V × ℝ) (V × V × ℝ) ℝ 1 :=
  ⟨innerProductContactFormFun V,
    (isSmoothForm_modelSpace_iff.mpr (contDiff_innerProductContactFormFun V)).mem_smoothBundleForms⟩

private theorem innerProductContactForm_toRoughForm :
    (innerProductContactForm V).1 = innerProductContactFormFun V :=
  (rfl)

/-- The standard contact form evaluates a tangent vector `(u, v, w)` at `(q, p, z)` as
`w - ⟪p, u⟫`. -/
@[simp]
theorem innerProductContactForm_apply (x : V × V × ℝ) (v : TangentSpace 𝓘(ℝ, V × V × ℝ) x) :
    (innerProductContactForm V).1 x ![v] = v.2.2 - ⟪x.2.1, v.1⟫_ℝ :=
  innerProductContactFormFun_apply V x ![v]

/-- The scalar function obtained by evaluating the standard contact form on a fixed vector has
derivative `δx ↦ -⟪δp, u⟫`: only the momentum coordinate of the base point varies. -/
private theorem hasFDerivAt_innerProductContactFormFun_apply
    (v : Fin 1 → V × V × ℝ) (x : V × V × ℝ) :
    HasFDerivAt (fun y ↦ innerProductContactFormFun V y v)
      (-((innerSL ℝ (v 0).1).comp ((ContinuousLinearMap.fst ℝ V ℝ).comp
        (ContinuousLinearMap.snd ℝ V (V × ℝ))))) x := by
  have h : (fun y ↦ innerProductContactFormFun V y v) = fun y ↦ (v 0).2.2 -
      (innerSL ℝ (v 0).1).comp ((ContinuousLinearMap.fst ℝ V ℝ).comp
        (ContinuousLinearMap.snd ℝ V (V × ℝ))) y := by
    funext y
    simp [innerProductContactFormFun_apply, real_inner_comm]
  rw [h]
  exact (hasFDerivAt_const _ x).sub (ContinuousLinearMap.hasFDerivAt _) |>.congr_fderiv
    (zero_sub _)

/-- The flat exterior derivative of the standard contact form. -/
private theorem extDeriv_innerProductContactFormFun_apply (x : V × V × ℝ) (v : Fin 2 → V × V × ℝ) :
    extDeriv (innerProductContactFormFun V) x v =
      stdSymplecticForm ((v 0).1, (v 0).2.1) ((v 1).1, (v 1).2.1) := by
  rw [extDeriv_apply ((contDiff_innerProductContactFormFun V).differentiable (by simp) x),
    Fin.sum_univ_two,
    (hasFDerivAt_innerProductContactFormFun_apply V _ x).fderiv,
    (hasFDerivAt_innerProductContactFormFun_apply V _ x).fderiv]
  simp [Fin.removeNth, stdSymplecticForm_apply, real_inner_comm (v 1).1, neg_add_eq_sub]

/-- The exterior derivative of the standard contact form is the standard symplectic form of the
`(q, p)` coordinates: `d(dz - ⟪p, dq⟫) = Σᵢ dqᵢ ∧ dpᵢ`. -/
theorem mextDeriv_innerProductContactForm_apply (x : V × V × ℝ)
    (v w : TangentSpace 𝓘(ℝ, V × V × ℝ) x) :
    mextDeriv (innerProductContactForm V).1 x ![v, w] =
      stdSymplecticForm (v.1, v.2.1) (w.1, w.2.1) :=
  (congrArg (fun A ↦ A ![v, w]) (mextDeriv_eq_extDeriv (innerProductContactForm V).1 x)).trans
    (extDeriv_innerProductContactFormFun_apply V x ![v, w])

/-- A tangent vector `(u, v, w)` lies in the kernel of the standard contact form at `(q, p, z)`
exactly when `w = ⟪p, u⟫`. -/
theorem mem_kerDistribution_innerProductContactForm {x : V × V × ℝ}
    {v : TangentSpace 𝓘(ℝ, V × V × ℝ) x} :
    v ∈ (innerProductContactForm V).kerDistribution x ↔ v.2.2 = ⟪x.2.1, v.1⟫_ℝ := by
  rw [SmoothForm.mem_kerDistribution, innerProductContactForm_apply, sub_eq_zero]

/-- The standard form `dz - ⟪p, dq⟫` on `V × V × ℝ` is a contact form. -/
theorem isContactForm_innerProductContactForm : (innerProductContactForm V).IsContactForm := by
  refine SmoothForm.isContactForm_iff.2 fun x ↦ ⟨?_, fun v hv hvw ↦ ?_⟩
  · -- The form takes the value `1` on `∂_z`.
    obtain ⟨e, he⟩ : ∃ e : TangentSpace 𝓘(ℝ, V × V × ℝ) x, e = ((0, 0, 1) : V × V × ℝ) :=
      ⟨_, rfl⟩
    exact ⟨e, by rw [innerProductContactForm_apply, he]; simp⟩
  -- Test `v = (u, v', w)` against the kernel vectors `(0, u, 0)` and `(v', 0, ⟪p, v'⟫)`.
  obtain ⟨e₁, he₁⟩ : ∃ e : TangentSpace 𝓘(ℝ, V × V × ℝ) x, e = ((0, v.1, 0) : V × V × ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : TangentSpace 𝓘(ℝ, V × V × ℝ) x,
      e = ((v.2.1, 0, ⟪x.2.1, v.2.1⟫_ℝ) : V × V × ℝ) := ⟨_, rfl⟩
  have h₁ := hvw e₁ (by rw [innerProductContactForm_apply, he₁]; simp)
  have h₂ := hvw e₂ (by rw [innerProductContactForm_apply, he₂]; simp)
  rw [mextDeriv_innerProductContactForm_apply, he₁] at h₁
  rw [mextDeriv_innerProductContactForm_apply, he₂] at h₂
  simp only [stdSymplecticForm_apply, inner_zero_right, sub_zero, zero_sub, neg_eq_zero,
    inner_self_eq_zero] at h₁ h₂
  rw [innerProductContactForm_apply, sub_eq_zero, h₁, inner_zero_right] at hv
  -- The zero tangent vector is by definition the zero of `V × V × ℝ`.
  exact Prod.ext h₁ (Prod.ext h₂ hv)

/-- On `ℝ^(2n+1) = ℝⁿ × ℝⁿ × ℝ`, the standard contact form is `dz - Σᵢ pᵢ dqᵢ`. -/
theorem innerProductContactForm_euclideanSpace_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) x) :
    (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 x ![v] =
      v.2.2 - ∑ i, x.2.1 i * v.1 i := by
  simp [PiLp.inner_apply, mul_comm]

/-- On `ℝ^(2n+1) = ℝⁿ × ℝⁿ × ℝ`, the exterior derivative of the standard contact form is
`Σᵢ dqᵢ ∧ dpᵢ`. -/
theorem mextDeriv_innerProductContactForm_euclideanSpace_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) x) :
    mextDeriv (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 x ![v, w] =
      ∑ i, (v.1 i * w.2.1 i - v.2.1 i * w.1 i) := by
  simp [mextDeriv_innerProductContactForm_apply, PiLp.inner_apply, Finset.sum_sub_distrib, mul_comm]

/-- A continuous linear map `L` pulls the inner product contact form back to any one-form `β`
taking the value `(L w).2.2 - ⟪(L x).2.1, (L w).1⟫` on each tangent vector `w` at `x`. -/
private theorem mpullback_innerProductContactForm_linear_eq {f : V × V × ℝ → V × V × ℝ}
    (L : (V × V × ℝ) →L[ℝ] V × V × ℝ) (hf : f = L)
    (β : RoughForm 𝓘(ℝ, V × V × ℝ) (V × V × ℝ) ℝ 1)
    (hβ : ∀ x (w : TangentSpace 𝓘(ℝ, V × V × ℝ) x),
      (L w).2.2 - ⟪(L x).2.1, (L w).1⟫_ℝ = β x ![w]) :
    mpullback 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) f (innerProductContactForm V).1 = β := by
  subst hf
  funext x
  ext v
  -- A one-form only sees the single entry `v 0` of `v`.
  have hv : v = ![v 0] := by
    ext i
    fin_cases i
    rfl
  rw [mpullback_apply, L.mfderiv_eq, innerProductContactForm_toRoughForm]
  refine (innerProductContactFormFun_apply V (L x) fun i ↦ L (v i)).trans ?_
  conv_rhs => rw [hv]
  exact hβ x (v 0)

/-- For `V = ℝ`, the standard contact form is the form `dz - x dy` of
`TauCeti.standardContactForm` in the coordinates `(q, p, z) = (y, x, z)`: pulling `dz - p dq` back
along `(x, y, z) ↦ (y, x, z)` gives `dz - x dy`. -/
theorem mpullback_innerProductContactForm_real :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun p : ℝ × ℝ × ℝ ↦ (p.2.1, p.1, p.2.2))
      (innerProductContactForm ℝ).1 = standardContactForm.1 := by
  let L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
  exact mpullback_innerProductContactForm_linear_eq ℝ L (by funext p; simp [L]) _
    fun p w ↦ by
      rw [standardContactForm_apply]
      obtain ⟨a, b, c⟩ := w
      simp [L, mul_comm]

/-- The linear map `(q, p, z) ↦ (q, -p, -z)` reverses the coorientation of the standard contact
structure: it pulls the standard contact form `α` back to `-α`. -/
theorem mpullback_innerProductContactForm_neg :
    mpullback 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (fun x : V × V × ℝ ↦ (x.1, -x.2.1, -x.2.2))
      (innerProductContactForm V).1 = (-innerProductContactForm V).1 := by
  let L : (V × V × ℝ) →L[ℝ] V × V × ℝ :=
    (ContinuousLinearMap.fst ℝ V (V × ℝ)).prod
      (-(ContinuousLinearMap.snd ℝ V (V × ℝ)))
  exact mpullback_innerProductContactForm_linear_eq V L (by funext x; simp [L, Prod.ext_iff]) _
    fun x w ↦ by
      rw [SmoothForm.neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
        innerProductContactForm_apply]
      obtain ⟨a, b, c⟩ := w
      simp [L, neg_add_eq_sub]

end InnerProductSpace

end TauCeti
