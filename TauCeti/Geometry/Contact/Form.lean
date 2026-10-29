/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.Distribution

/-!
# Contact forms

A one-form `α` on a manifold `M` is a **contact form** at a point `x` when `α_x ≠ 0` and the
two-form `dα_x` is nondegenerate on the hyperplane `ξ_x = ker α_x`. Its kernel distribution `ξ`
satisfies the contact condition at `x`, and `α` is a defining form of it. This kernel
formulation needs neither a dimension nor exterior powers of `dα`; in dimension `2n + 1` it is
classically equivalent to the pointwise nonvanishing of `α ∧ (dα)ⁿ`, a criterion not developed
here.

The kernel distribution and the contact condition depend on `α` only up to multiplication by a
nowhere-vanishing function: for `f` differentiable at `x` with `f x ≠ 0`, the Leibniz rule gives
`d(f α) = f dα` on `ker α_x`, so `f α` is contact at `x` exactly when `α` is. A positive `f`
preserves the coorientation of `ξ` defined by `α`, a negative one reverses it.

Through Cartan's formula, the contact condition is the nondegeneracy of the Levi form
`(V, W) ↦ -[V, W] mod ξ` of `ξ`. For vector fields `V` and `W` tangent to `ξ` near `x`, the
invariant formula for the exterior derivative of a one-form gives

`α_x ([V, W]_x) = -dα_x (V_x, W_x)`,

so `[V, W]_x ∈ ξ_x` exactly when `dα_x (V_x, W_x) = 0`.

The standard example is `dz - x dy` on `ℝ³`, whose kernel is
`TauCeti.standardContactDistribution ℝ`; its exterior derivative is `-dx ∧ dy`, and the
coordinate vector field `∂_z` satisfies the Reeb equations `α(∂_z) = 1` and `ι_{∂_z} dα = 0`.

## Main definitions

* `TauCeti.RoughForm.ker α`: the kernel distribution `x ↦ ker α_x` of a one-form.
* `TauCeti.IsContactFormAt α x`: `α` is a contact form at `x`.
* `TauCeti.IsContactForm α`: `α` is a contact form at every point.
* `TauCeti.standardContactForm`: the contact form `dz - x dy` on `ℝ³`.
* `TauCeti.standardReebField`: its Reeb vector field `∂_z`.

## Main results

* `TauCeti.RoughForm.ker_fun_smul`: rescaling by a function nonvanishing at `x` does not change
  the kernel at `x`.
* `TauCeti.isContactFormAt_fun_smul_iff`, `TauCeti.isContactForm_fun_smul_iff`: rescaling by a
  nowhere-vanishing differentiable function preserves the contact condition, in both directions.
* `TauCeti.isContactFormAt_neg_iff`: so does the coorientation reversal `α ↦ -α`.
* `TauCeti.RoughForm.apply_mlieBracket_eq_neg_mextDeriv`: Cartan's formula for the Levi form,
  `α ([V, W]) = -dα (V, W)` for vector fields tangent to `ker α`.
* `TauCeti.RoughForm.mlieBracket_mem_ker_iff`: the bracket of two such fields lies in `ker α`
  exactly when `dα` vanishes on them.
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

open Set Filter Bundle VectorField
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

namespace RoughForm

/-- The kernel distribution of a one-form `α`: at each point `x`, the subspace of tangent vectors
`v` with `α_x (v) = 0`. -/
def ker (α : RoughForm I M ℝ 1) (x : M) : Submodule ℝ (TangentSpace I x) :=
  LinearMap.ker
    ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)).symm (α x) :
      TangentSpace I x →ₗ[ℝ] ℝ)

@[simp]
theorem mem_ker {α : RoughForm I M ℝ 1} {x : M} {v : TangentSpace I x} :
    v ∈ α.ker x ↔ α x ![v] = 0 := by
  rw [ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, Matrix.vec_single_eq_const]

/-- Rescaling a one-form by a function that does not vanish at `x` does not change its kernel
at `x`. -/
theorem ker_fun_smul {α : RoughForm I M ℝ 1} {f : M → ℝ} {x : M} (hfx : f x ≠ 0) :
    ker (fun y ↦ f y • α y) x = α.ker x := by
  ext v
  simp [hfx]

@[simp]
theorem ker_neg (α : RoughForm I M ℝ 1) (x : M) : (-α).ker x = α.ker x := by
  ext v
  simp

end RoughForm

/-- A one-form `α` is a **contact form at `x`** when `α_x ≠ 0` and `dα_x` is nondegenerate on the
hyperplane `ker α_x`: the only vector of `ker α_x` that is `dα_x`-orthogonal to all of
`ker α_x` is zero. -/
structure IsContactFormAt (α : RoughForm I M ℝ 1) (x : M) : Prop where
  /-- A contact form does not vanish, so its kernel is a hyperplane. -/
  ne_zero : α x ≠ 0
  /-- The exterior derivative of a contact form is nondegenerate on its kernel. -/
  nondegenerate : ∀ v ∈ α.ker x, (∀ w ∈ α.ker x, mextDeriv α x ![v, w] = 0) → v = 0

/-- A one-form is a **contact form** when it is a contact form at every point. -/
def IsContactForm (α : RoughForm I M ℝ 1) : Prop :=
  ∀ x, IsContactFormAt α x

theorem isContactForm_iff {α : RoughForm I M ℝ 1} :
    IsContactForm α ↔ ∀ x, IsContactFormAt α x :=
  Iff.rfl

theorem IsContactForm.isContactFormAt {α : RoughForm I M ℝ 1} (h : IsContactForm α) (x : M) :
    IsContactFormAt α x :=
  h x

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

@[simp]
theorem isContactForm_neg_iff {α : RoughForm I M ℝ 1} : IsContactForm (-α) ↔ IsContactForm α :=
  forall_congr' fun _ ↦ isContactFormAt_neg_iff

section Rescaling

variable [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {f : M → ℝ} {x : M}

/-- **Rescaling a contact form**: for a function `f` differentiable at `x` with `f x ≠ 0`, the
one-form `f α` is a contact form at `x` exactly when `α` is. On `ker α_x` the Leibniz rule reads
`d(f α)_x = f x • dα_x`. -/
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

/-- Rescaling by a nowhere-vanishing differentiable function preserves the contact condition, in
both directions. -/
theorem isContactForm_fun_smul_iff (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y))) (hf₀ : ∀ x, f x ≠ 0) :
    IsContactForm (fun y ↦ f y • α y) ↔ IsContactForm α :=
  forall_congr' fun x ↦ isContactFormAt_fun_smul_iff (hf x) (hα x) (hf₀ x)

end Rescaling

section Levi

variable [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {V W : (y : M) → TangentSpace I y} {x : M}

namespace RoughForm

/-- **Cartan's formula for the Levi form.** For vector fields `V` and `W` tangent to the kernel of
a one-form `α` near `x`, `α_x ([V, W]_x) = -dα_x (V_x, W_x)`. -/
theorem apply_mlieBracket_eq_neg_mextDeriv
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hVα : ∀ᶠ y in 𝓝 x, V y ∈ α.ker y) (hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.ker y) :
    α x ![mlieBracket I V W x] = -mextDeriv α x ![V x, W x] := by
  have hzero {U : (y : M) → TangentSpace I y} (hU : ∀ᶠ y in 𝓝 x, U y ∈ α.ker y) :
      mvfderiv I (fun y ↦ α y ![U y]) x = 0 := by
    have hU' : (fun y ↦ α y ![U y]) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hU] with y hy using mem_ker.mp hy
    ext v
    simp [mvfderiv, hU'.mfderiv_eq]
  rw [mextDeriv_apply_one hα hV hW, hzero hVα, hzero hWα]
  simp

/-- For vector fields `V` and `W` tangent to the kernel of a one-form `α` near `x`, the bracket
`[V, W]_x` lies in `ker α_x` exactly when `dα_x (V_x, W_x) = 0`. -/
theorem mlieBracket_mem_ker_iff
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x)
    (hVα : ∀ᶠ y in 𝓝 x, V y ∈ α.ker y) (hWα : ∀ᶠ y in 𝓝 x, W y ∈ α.ker y) :
    mlieBracket I V W x ∈ α.ker x ↔ mextDeriv α x ![V x, W x] = 0 := by
  rw [mem_ker, apply_mlieBracket_eq_neg_mextDeriv hα hV hW hVα hWα, neg_eq_zero]

end RoughForm

end Levi

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

/-- The form `dz - x dy` takes the value `1` on its Reeb vector field `∂_z`. -/
theorem standardContactForm_apply_standardReebField (p : ℝ × ℝ × ℝ) :
    standardContactForm p ![standardReebField p] = 1 := by
  simp [standardReebField]

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
  intro p
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
