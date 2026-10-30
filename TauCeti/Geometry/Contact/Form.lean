/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.Distribution

/-!
# Contact forms

A one-form `α` on a manifold `M` satisfies the **contact condition** at a point `x` when
`α_x ≠ 0` and the two-form `dα_x` is nondegenerate on the hyperplane `ξ_x = ker α_x`. This
pointwise condition is purely algebraic and carries no regularity; a **contact form** is a smooth
one-form satisfying it at every point. Its kernel distribution `ξ` is then a contact
distribution, and `α` is a defining form of it. This kernel
formulation needs neither a dimension nor exterior powers of `dα`; in dimension `2n + 1` it is
classically equivalent to the pointwise nonvanishing of `α ∧ (dα)ⁿ`, a criterion not developed
here.

The kernel distribution and the contact condition depend on `α` only up to multiplication by a
nowhere-vanishing function. The kernel identity `ker (f α)_x = ker α_x` needs only `f x ≠ 0`. For
the contact condition, when both `f` and `α` are differentiable at `x` and `f x ≠ 0`, the Leibniz
rule gives `d(f α) = f dα` on `ker α_x`, so `f α` is contact at `x` exactly when `α` is. A
positive `f` preserves the coorientation of `ξ` defined by `α`, a negative one reverses it.

Through Cartan's formula, the contact condition is the nondegeneracy of the Levi form
`(V, W) ↦ -[V, W] mod ξ` of `ξ`. For vector fields `V` and `W` tangent to `ξ` near `x`, the
invariant formula for the exterior derivative of a one-form gives

`α_x ([V, W]_x) = -dα_x (V_x, W_x)`,

so `[V, W]_x ∈ ξ_x` exactly when `dα_x (V_x, W_x) = 0`. These identities hold for every
one-form and are `TauCeti.RoughForm.apply_mlieBracket_eq_neg_mextDeriv` and
`TauCeti.RoughForm.mlieBracket_mem_ker_iff`, alongside the invariant formula for the exterior
derivative; the kernel distribution `TauCeti.RoughForm.ker` is part of the basic form API.

The standard example is `dz - x dy` on `ℝ³`, whose kernel is
`TauCeti.standardContactDistribution ℝ`; its exterior derivative is `-dx ∧ dy`, and the
coordinate vector field `∂_z` satisfies the Reeb equations `α(∂_z) = 1` and `ι_{∂_z} dα = 0`.

## Main definitions

* `TauCeti.IsContactFormAt α x`: `α` satisfies the pointwise contact condition at `x`.
* `TauCeti.IsContactForm α`: `α` is smooth and satisfies the contact condition at every point.
* `TauCeti.standardContactForm`: the contact form `dz - x dy` on `ℝ³`.
* `TauCeti.standardReebField`: its Reeb vector field `∂_z`.

## Main results

* `TauCeti.isContactFormAt_fun_smul_iff`: for a one-form differentiable at `x`, rescaling by a
  function differentiable and nonvanishing at `x` preserves the contact condition at `x`, in both
  directions.
* `TauCeti.isContactForm_fun_smul_iff`: rescaling by a nowhere-vanishing smooth function preserves
  being a contact form, in both directions.
* `TauCeti.isContactFormAt_neg_iff`: so does the coorientation reversal `α ↦ -α`.
* `TauCeti.ker_standardContactForm`: the kernel of `dz - x dy` is the standard contact distribution.
* `TauCeti.mextDeriv_standardContactForm_apply`: `d(dz - x dy) = -dx ∧ dy`.
* `TauCeti.isContactForm_standardContactForm`: `dz - x dy` is a contact form.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109,
  Cambridge University Press, 2008, Sections 1.1 and 2.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A one-form `α` is a **contact form at `x`** when `α_x ≠ 0` and `dα_x` is nondegenerate on the
hyperplane `ker α_x`: the only vector of `ker α_x` that is `dα_x`-orthogonal to all of
`ker α_x` is zero. This is the pointwise algebraic condition only: it imposes no regularity on `α`,
and is meaningful when `α` is differentiable at `x`. The global notion `TauCeti.IsContactForm`
also requires smoothness. -/
structure IsContactFormAt (α : RoughForm I M ℝ 1) (x : M) : Prop where
  /-- A contact form does not vanish, so its kernel is a hyperplane. -/
  ne_zero : α x ≠ 0
  /-- The exterior derivative of a contact form is nondegenerate on its kernel. -/
  nondegenerate : ∀ v ∈ α.ker x, (∀ w ∈ α.ker x, mextDeriv α x ![v, w] = 0) → v = 0

open scoped ContDiff in
/-- A one-form is a **contact form** when it is smooth and a contact form at every point. -/
structure IsContactForm [IsManifold I 1 M] (α : RoughForm I M ℝ 1) : Prop where
  /-- A contact form is smooth. -/
  isSmoothForm : IsSmoothForm I ∞ α
  /-- A contact form satisfies the contact condition at every point. -/
  isContactFormAt : ∀ x, IsContactFormAt α x

/-- Reversing the coorientation, `α ↦ -α`, preserves the contact condition. -/
@[simp]
theorem isContactFormAt_neg_iff {α : RoughForm I M ℝ 1} {x : M} :
    IsContactFormAt (-α) x ↔ IsContactFormAt α x := by
  suffices ∀ α : RoughForm I M ℝ 1, IsContactFormAt α x → IsContactFormAt (-α) x from
    ⟨fun h ↦ neg_neg α ▸ this _ h, this α⟩
  intro α h
  refine ⟨by simpa using h.ne_zero, fun v hv hvw ↦ h.nondegenerate v (by simpa using hv)
    fun w hw ↦ ?_⟩
  have := hvw w (by simpa using hw)
  simpa [mextDeriv_neg] using this

/-- Reversing the coorientation, `α ↦ -α`, preserves being a contact form: `-α` is a smooth
contact form exactly when `α` is. -/
@[simp]
theorem isContactForm_neg_iff [IsManifold I 1 M] {α : RoughForm I M ℝ 1} :
    IsContactForm (-α) ↔ IsContactForm α :=
  ⟨fun h ↦ ⟨neg_neg α ▸ h.isSmoothForm.neg,
      fun x ↦ isContactFormAt_neg_iff.mp (h.isContactFormAt x)⟩,
    fun h ↦ ⟨h.isSmoothForm.neg, fun x ↦ isContactFormAt_neg_iff.mpr (h.isContactFormAt x)⟩⟩

section Rescaling

variable [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {f : M → ℝ} {x : M}

/-- **Rescaling a contact form**: for a one-form `α` differentiable at `x` and a function `f`
differentiable at `x` with `f x ≠ 0`, the one-form `f α` is a contact form at `x` exactly when
`α` is. On `ker α_x` the Leibniz rule reads `d(f α)_x = f x • dα_x`. -/
theorem isContactFormAt_fun_smul_iff (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x) (hfx : f x ≠ 0) :
    IsContactFormAt (fun y ↦ f y • α y) x ↔ IsContactFormAt α x := by
  have hd : ∀ v ∈ α.ker x, ∀ w ∈ α.ker x,
      mextDeriv (fun y ↦ f y • α y) x ![v, w] = f x * mextDeriv α x ![v, w] := by
    intro v hv w hw
    rw [RoughForm.mem_ker] at hv hw
    rw [mextDeriv_fun_smul_apply_one hf hα, hv, hw]
    ring
  constructor
  · intro h
    refine ⟨(smul_ne_zero_iff.mp h.ne_zero).2, fun v hv hvw ↦ ?_⟩
    refine h.nondegenerate v (by rwa [RoughForm.ker_fun_smul hfx]) fun w hw ↦ ?_
    rw [RoughForm.ker_fun_smul hfx] at hw
    rw [hd v hv w hw, hvw w hw, mul_zero]
  · intro h
    refine ⟨smul_ne_zero hfx h.ne_zero, fun v hv hvw ↦ ?_⟩
    rw [RoughForm.ker_fun_smul hfx] at hv hvw
    refine h.nondegenerate v hv fun w hw ↦ ?_
    have := hvw w hw
    rw [hd v hv w hw] at this
    exact (mul_eq_zero.mp this).resolve_left hfx

open scoped ContDiff in
/-- Rescaling by a nowhere-vanishing smooth function preserves being a contact form, in both
directions. -/
theorem isContactForm_fun_smul_iff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0) :
    IsContactForm (fun y ↦ f y • α y) ↔ IsContactForm α := by
  have key {α : RoughForm I M ℝ 1} (hα : IsSmoothForm I ∞ α) :
      (∀ x, IsContactFormAt (fun y ↦ f y • α y) x) ↔ ∀ x, IsContactFormAt α x :=
    forall_congr' fun x ↦ isContactFormAt_fun_smul_iff (hf.mdifferentiable (by simp) x)
      (hα.contMDiff.mdifferentiable (by simp) x) (hf₀ x)
  refine ⟨fun h ↦ ?_, fun h ↦
    ⟨h.isSmoothForm.fun_smul hf, (key h.isSmoothForm).mpr h.isContactFormAt⟩⟩
  have hα : IsSmoothForm I ∞ α := by
    have := h.isSmoothForm.fun_smul (hf.inv₀ hf₀)
    simpa [smul_smul, inv_mul_cancel₀ (hf₀ _)] using this
  exact ⟨hα, (key hα).mp h.isContactFormAt⟩

end Rescaling

section Standard

/-- The standard contact form `dz - x dy` on `ℝ³`, with coordinates `p = (x, y, z)`. -/
def standardContactForm : RoughForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1 := fun p ↦
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ × ℝ) ℝ (0 : Fin 1)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) -
    p.1 • ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ × ℝ) ℝ (0 : Fin 1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

@[simp]
theorem standardContactForm_apply (p : ℝ × ℝ × ℝ)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    standardContactForm p v = (v 0).2.2 - p.1 * (v 0).2.1 :=
  (rfl)

/-- The kernel of `dz - x dy` is the standard contact distribution. -/
theorem ker_standardContactForm :
    standardContactForm.ker = standardContactDistribution ℝ := by
  funext p
  ext v
  exact RoughForm.mem_ker.trans <| sub_eq_zero.trans mem_standardContactDistribution.symm

/-- The exterior derivative of `dz - x dy` is `-dx ∧ dy`. -/
theorem mextDeriv_standardContactForm_apply (p : ℝ × ℝ × ℝ)
    (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    mextDeriv standardContactForm p ![v, w] = w.1 * v.2.1 - v.1 * w.2.1 := by
  -- Over the model space, the form is the flat form `ω` and `mextDeriv` is `extDeriv`.
  let ω : ℝ × ℝ × ℝ → (ℝ × ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ := standardContactForm
  have hω : DifferentiableAt ℝ ω p := by
    unfold ω standardContactForm
    fun_prop
  have hev (u : Fin 1 → ℝ × ℝ × ℝ) :
      (fun q ↦ ω q u) = fun q ↦ (u 0).2.2 - q.1 * (u 0).2.1 :=
    funext fun q ↦ standardContactForm_apply q u
  have h := extDeriv_apply hω ![v, w]
  have hfd (c d : ℝ) (u : ℝ × ℝ × ℝ) :
      fderiv ℝ (fun q : ℝ × ℝ × ℝ ↦ c - q.1 * d) p u = -(u.1 * d) := by
    rw [fderiv_const_sub, fderiv_mul_const differentiableAt_fst, fderiv_fst]
    simp [mul_comm]
  rw [Fin.sum_univ_two, hev, hev, hfd, hfd] at h
  refine (DFunLike.congr_fun (mextDeriv_eq_extDeriv standardContactForm p) _).trans (h.trans ?_)
  simp [Fin.removeNth_apply]
  ring

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

/-- The form `dz - x dy` takes the value `1` on its Reeb vector field `∂_z`. `simp` proves this
from `TauCeti.standardContactForm_apply` and the coordinate lemmas of `standardReebField`. -/
theorem standardContactForm_apply_standardReebField (p : ℝ × ℝ × ℝ) :
    standardContactForm p ![standardReebField p] = 1 := by
  simp

/-- The contraction of the Reeb vector field `∂_z` with the exterior derivative of `dz - x dy`
vanishes. -/
@[simp]
theorem mextDeriv_standardContactForm_standardReebField (p : ℝ × ℝ × ℝ)
    (w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    mextDeriv standardContactForm p ![standardReebField p, w] = 0 := by
  rw [mextDeriv_standardContactForm_apply]
  simp [standardReebField]

/-- `dz - x dy` is a contact form on `ℝ³`. -/
theorem isContactForm_standardContactForm : IsContactForm standardContactForm := by
  refine ⟨isSmoothForm_modelSpace_iff.mpr (by unfold standardContactForm; fun_prop), fun p ↦ ?_⟩
  refine ⟨fun h ↦ ?_, fun v hv hvw ↦ ?_⟩
  · have := standardContactForm_apply_standardReebField p
    rw [h] at this
    simp at this
  · -- Test `v` against the frame `(0, 1, x)`, `(1, 0, 0)` of the kernel.
    let e₁ : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p := ((0, 1, p.1) : ℝ × ℝ × ℝ)
    let e₂ : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p := ((1, 0, 0) : ℝ × ℝ × ℝ)
    have h₁ := hvw e₁ (by
      simp only [RoughForm.mem_ker, standardContactForm_apply, Matrix.cons_val_zero]
      simp [e₁])
    have h₂ := hvw e₂ (by
      simp only [RoughForm.mem_ker, standardContactForm_apply, Matrix.cons_val_zero]
      simp [e₂])
    rw [RoughForm.mem_ker, standardContactForm_apply] at hv
    rw [mextDeriv_standardContactForm_apply] at h₁ h₂
    simp only [e₁, e₂] at h₁ h₂
    simp only [Matrix.cons_val_zero] at hv
    obtain ⟨a, b, c⟩ := v
    simp only at h₁ h₂ hv
    have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    have hc : c = 0 := by rw [hb, mul_zero, sub_zero] at hv; exact hv
    subst ha hb hc
    rfl

end Standard

end TauCeti
