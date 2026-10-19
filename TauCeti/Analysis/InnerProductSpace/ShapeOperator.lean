/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm
public import TauCeti.Analysis.InnerProductSpace.SquaredDistance

/-!
# The shape operator of a map into an inner product space

Let `i : V → E` be a map from a finite-dimensional real normed space into a real inner product
space, and let `A = Di(x)`. When `A` is injective, the **induced metric**
`g(v, w) = ⟪A v, A w⟫` is an inner product on `V`. For a vector `ν : E`, the **shape operator**
`S_ν = TauCeti.shapeOperator i x ν` is the endomorphism of `V` representing the second fundamental
form in the direction `ν` with respect to this metric:

`g(S_ν v, w) = ⟪ν, B(v, w)⟫`.

It depends linearly on `ν`, only through the normal component of `ν`, and is self-adjoint for
`g` when `i` is `C²`. For a holomorphic map into a complex inner product space, the complex
identities of the second fundamental form give

`S_ν (J v) = -J (S_ν v)` and `S_(J ν) = J S_ν`,

so every shape operator anticommutes with the complex structure `J = I •` of `V`.

The shape operator governs the squared-distance function `ρ_a(y) = ‖i y - a‖²`. At a critical
point `x` of `ρ_a`, the displacement `a - i x` is normal and the Hessian is

`D²ρ_a(x)(v, w) = 2 (g(v, w) - ⟪a - i x, B(v, w)⟫) = 2 g(v - S_(a - i x) v, w)`.

Hence, along an immersion, the Hessian kernel at `x` is the `1`-eigenspace of `S_(a - i x)`: the
point `a` is a focal point of `x` exactly when `1` is an eigenvalue of this shape operator, with
focal multiplicity the dimension of that eigenspace.

## Main definitions

* `TauCeti.shapeOperator i x`: the shape operator of `i` at `x`, as a linear map from `E` to the
  endomorphisms of `V`. It is zero when `Di(x)` is not injective.

## Main results

* `TauCeti.inner_fderiv_shapeOperator_apply`: the defining identity `g(S_ν v, w) = ⟪ν, B(v, w)⟫`.
* `TauCeti.shapeOperator_apply_eq_iff`: the shape operator is characterized by that identity.
* `ContDiffAt.inner_fderiv_shapeOperator_left`: the shape operator is self-adjoint for `g`.
* `ContDiffAt.shapeOperator_apply_I_smul`, `ContDiffAt.shapeOperator_I_smul_apply`: the complex
  identities `S_ν J = -J S_ν` and `S_(J ν) = J S_ν` for holomorphic maps.
* `TauCeti.fderiv_fderiv_norm_sq_sub_comp_apply_of_fderiv_eq_zero`: the critical squared-distance
  Hessian `2 (g - ⟪a - i x, B⟫)`.
* `TauCeti.ker_fderiv_fderiv_norm_sq_sub_comp_eq_eigenspace`: its kernel is the `1`-eigenspace of
  `S_(a - i x)`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Sections 6 and 7.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Chapter 8.
-/

public section

open Complex Function Module
open scoped RealInnerProductSpace

namespace TauCeti

section Real

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {i : V → E} {x : V}

omit [FiniteDimensional ℝ V] in
/-- Along an injective linear map into an inner product space, the pulled-back inner product
separates points. -/
private theorem eq_of_forall_inner_fderiv_eq (h : Injective (fderiv ℝ i x)) {u u' : V}
    (huu' : ∀ w, ⟪fderiv ℝ i x u, fderiv ℝ i x w⟫ = ⟪fderiv ℝ i x u', fderiv ℝ i x w⟫) :
    u = u' := by
  have h₀ := huu' (u - u')
  rw [← sub_eq_zero, ← inner_sub_left, ← map_sub, inner_self_eq_zero, map_eq_zero_iff _ h,
    sub_eq_zero] at h₀
  exact h₀

/-- The metric `g(v, w) = ⟪Di(x) v, Di(x) w⟫` induced by `i` at `x`, as a bilinear form. -/
private noncomputable def inducedMetric (i : V → E) (x : V) : LinearMap.BilinForm ℝ V :=
  (innerₗ E).compl₁₂ (fderiv ℝ i x : V →ₗ[ℝ] E) (fderiv ℝ i x : V →ₗ[ℝ] E)

omit [FiniteDimensional ℝ V] in
private theorem inducedMetric_apply (v w : V) :
    inducedMetric i x v w = ⟪fderiv ℝ i x v, fderiv ℝ i x w⟫ :=
  (rfl)

omit [FiniteDimensional ℝ V] in
private theorem nondegenerate_inducedMetric (h : Injective (fderiv ℝ i x)) :
    (inducedMetric i x).Nondegenerate := by
  refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
  · exact eq_of_forall_inner_fderiv_eq h fun w ↦ by simpa [inducedMetric_apply] using hv w
  · refine eq_of_forall_inner_fderiv_eq h fun v ↦ ?_
    rw [real_inner_comm, ← inducedMetric_apply, hw v]
    simp

/-- The **Weingarten form** `(ν, v, w) ↦ ⟪ν, B(v, w)⟫`, with values in the dual of `V`. -/
private noncomputable def weingartenForm (i : V → E) (x : V) : E →ₗ[ℝ] V →ₗ[ℝ] Dual ℝ V :=
  LinearMap.mk₂ ℝ
    (fun ν v ↦ innerₗ E ν ∘ₗ (secondFundamentalForm ℝ i x v : V →ₗ[ℝ] E))
    (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp [inner_add_right])
    (fun _ _ _ ↦ by ext; simp)

private theorem weingartenForm_apply (ν : E) (v w : V) :
    weingartenForm i x ν v w = ⟪ν, secondFundamentalForm ℝ i x v w⟫ :=
  (rfl)

/-- The **shape operator** of `i : V → E` at `x`. For `ν : E`, the endomorphism `S_ν` of `V`
represents the second fundamental form in the direction `ν` with respect to the induced metric:
`⟪Di(x) (S_ν v), Di(x) w⟫ = ⟪ν, B(v, w)⟫` (`TauCeti.inner_fderiv_shapeOperator_apply`). This
requires `Di(x)` to be injective; otherwise the shape operator is defined to be zero. -/
noncomputable def shapeOperator (i : V → E) (x : V) : E →ₗ[ℝ] End ℝ V :=
  open scoped Classical in
  if h : Injective (fderiv ℝ i x) then
    LinearMap.llcomp ℝ V (Dual ℝ V) V
        ((inducedMetric i x).toDual (nondegenerate_inducedMetric h)).symm.toLinearMap ∘ₗ
      weingartenForm i x
  else 0

/-- The shape operator of a map whose derivative is not injective is zero. -/
theorem shapeOperator_of_not_injective (h : ¬Injective (fderiv ℝ i x)) :
    shapeOperator i x = 0 :=
  dite_eq_right h

/-- **The defining identity of the shape operator**: `g(S_ν v, w) = ⟪ν, B(v, w)⟫`, where `g` is the
metric induced by the injective derivative `Di(x)`. -/
theorem inner_fderiv_shapeOperator_apply (h : Injective (fderiv ℝ i x)) (ν : E) (v w : V) :
    ⟪fderiv ℝ i x (shapeOperator i x ν v), fderiv ℝ i x w⟫ =
      ⟪ν, secondFundamentalForm ℝ i x v w⟫ := by
  rw [← inducedMetric_apply, ← weingartenForm_apply, shapeOperator, dite_eq_left h]
  simp [LinearMap.llcomp_apply]

/-- The shape operator is characterized by its defining identity: `S_ν v = u` exactly when
`g(u, w) = ⟪ν, B(v, w)⟫` for every `w`. -/
theorem shapeOperator_apply_eq_iff (h : Injective (fderiv ℝ i x)) {ν : E} {v u : V} :
    shapeOperator i x ν v = u ↔
      ∀ w, ⟪fderiv ℝ i x u, fderiv ℝ i x w⟫ = ⟪ν, secondFundamentalForm ℝ i x v w⟫ := by
  refine ⟨fun hu w ↦ hu ▸ inner_fderiv_shapeOperator_apply h ν v w, fun hu ↦ ?_⟩
  exact eq_of_forall_inner_fderiv_eq h fun w ↦ by
    rw [inner_fderiv_shapeOperator_apply h, hu]

/-- The shape operator only sees the normal component: it vanishes on tangent vectors. -/
theorem shapeOperator_eq_zero_of_mem_range {ν : E} (hν : ν ∈ (fderiv ℝ i x).range) :
    shapeOperator i x ν = 0 := by
  by_cases h : Injective (fderiv ℝ i x)
  · ext v
    rw [LinearMap.zero_apply, shapeOperator_apply_eq_iff h]
    intro w
    rw [map_zero, inner_zero_left, Submodule.inner_right_of_mem_orthogonal hν
      (secondFundamentalForm_apply_mem_orthogonal i x v w)]
  · simp [shapeOperator_of_not_injective h]

/-- The shape operator of a `C²` map is self-adjoint for the induced metric:
`g(S_ν v, w) = g(v, S_ν w)`. -/
theorem _root_.ContDiffAt.inner_fderiv_shapeOperator_left (hi : ContDiffAt ℝ 2 i x) (ν : E)
    (v w : V) :
    ⟪fderiv ℝ i x (shapeOperator i x ν v), fderiv ℝ i x w⟫ =
      ⟪fderiv ℝ i x v, fderiv ℝ i x (shapeOperator i x ν w)⟫ := by
  by_cases h : Injective (fderiv ℝ i x)
  · rw [real_inner_comm (fderiv ℝ i x (shapeOperator i x ν w)), inner_fderiv_shapeOperator_apply h,
      inner_fderiv_shapeOperator_apply h, hi.secondFundamentalForm_apply_comm]
  · simp [shapeOperator_of_not_injective h]

/-! ### Squared distance and focal points -/

variable {a : E}

/-- **The critical squared-distance Hessian.** At a critical point `x` of `y ↦ ‖i y - a‖²`, the
Hessian is `2 (g(v, w) - ⟪a - i x, B(v, w)⟫)`, where `g` is the induced metric and `B` the second
fundamental form. -/
theorem fderiv_fderiv_norm_sq_sub_comp_apply_of_fderiv_eq_zero (hi : ContDiffAt ℝ 2 i x)
    (hx : fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2) x = 0) (v w : V) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2)) x v w =
      2 * (⟪fderiv ℝ i x v, fderiv ℝ i x w⟫ - ⟪a - i x, secondFundamentalForm ℝ i x v w⟫) := by
  have hν : a - i x ∈ (fderiv ℝ i x).rangeᗮ := by
    rw [← neg_sub, Submodule.neg_mem_iff]
    exact (fderiv_norm_sq_sub_comp_eq_zero_iff (hi.differentiableAt (by norm_num))).1 hx
  rw [fderiv_fderiv_norm_sq_sub_comp_apply hi,
    inner_secondFundamentalForm_apply_of_mem_orthogonal hν, ← neg_sub a, inner_neg_left]
  ring

/-- At a critical point `x` of `y ↦ ‖i y - a‖²` along an immersion, the Hessian is
`2 g(v - S_(a - i x) v, w)`. -/
theorem fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_sub_shapeOperator
    (hi : ContDiffAt ℝ 2 i x) (h : Injective (fderiv ℝ i x))
    (hx : fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2) x = 0) (v w : V) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2)) x v w =
      2 * ⟪fderiv ℝ i x (v - shapeOperator i x (a - i x) v), fderiv ℝ i x w⟫ := by
  rw [fderiv_fderiv_norm_sq_sub_comp_apply_of_fderiv_eq_zero hi hx,
    ← inner_fderiv_shapeOperator_apply h, map_sub (fderiv ℝ i x), inner_sub_left]

/-- **Focal points.** At a critical point `x` of `y ↦ ‖i y - a‖²` along an immersion, the kernel
of the Hessian is the `1`-eigenspace of the shape operator `S_(a - i x)`. In particular the
Hessian is degenerate exactly when `1` is an eigenvalue of `S_(a - i x)`, and its nullity is the
multiplicity of that eigenvalue. -/
theorem ker_fderiv_fderiv_norm_sq_sub_comp_eq_eigenspace (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) (hx : fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2) x = 0) :
    (fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - a‖ ^ 2)) x).ker =
      End.eigenspace (shapeOperator i x (a - i x)) 1 := by
  ext v
  rw [LinearMap.mem_ker, End.mem_eigenspace_iff, one_smul, ContinuousLinearMap.ext_iff]
  simp only [ContinuousLinearMap.coe_coe, zero_apply, mul_eq_zero, two_ne_zero, false_or,
    fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_sub_shapeOperator hi h hx]
  refine ⟨fun hv ↦ ?_, fun hv w ↦ by rw [hv, sub_self, map_zero, inner_zero_left]⟩
  refine (sub_eq_zero.1 (eq_of_forall_inner_fderiv_eq h fun w ↦ ?_)).symm
  rw [hv w, map_zero, inner_zero_left]

/-- **Focal points along a normal line.** For a normal vector `ν` at `x` and `t ≠ 0`, the point `x`
is critical for the squared distance from `i x + t • ν`, and the kernel of the Hessian there is
the `t⁻¹`-eigenspace of `S_ν`. Thus the focal points of `x` on the normal line through `ν` are the
points `i x + κ⁻¹ • ν` for the nonzero eigenvalues `κ` of `S_ν`. -/
theorem ker_fderiv_fderiv_norm_sq_sub_comp_add_smul_eq_eigenspace (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) {ν : E} (hν : ν ∈ (fderiv ℝ i x).rangeᗮ) {t : ℝ} (ht : t ≠ 0) :
    (fderiv ℝ (fderiv ℝ (fun y ↦ ‖i y - (i x + t • ν)‖ ^ 2)) x).ker =
      End.eigenspace (shapeOperator i x ν) t⁻¹ := by
  have hx : fderiv ℝ (fun y ↦ ‖i y - (i x + t • ν)‖ ^ 2) x = 0 := by
    rw [fderiv_norm_sq_sub_comp_eq_zero_iff (hi.differentiableAt (by norm_num)),
      sub_add_cancel_left, Submodule.neg_mem_iff]
    exact Submodule.smul_mem _ t hν
  rw [ker_fderiv_fderiv_norm_sq_sub_comp_eq_eigenspace hi h hx, add_sub_cancel_left, map_smul]
  ext v
  simp only [End.mem_eigenspace_iff, LinearMap.smul_apply, one_smul]
  rw [← eq_inv_smul_iff₀ ht]

end Real

section Complex

/-! ### Holomorphic maps

The real inner product `re ⟪x, y⟫` on a complex inner product space is enabled locally; the shape
operator below is taken with respect to it. -/

attribute [local instance] InnerProductSpace.complexToReal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {i : V → E} {x : V}

/-- The shape operators of a holomorphic map anticommute with the complex structure:
`S_ν (J v) = -J (S_ν v)`. -/
theorem _root_.ContDiffAt.shapeOperator_apply_I_smul (hi : ContDiffAt ℂ 2 i x) (ν : E) (v : V) :
    shapeOperator i x ν (I • v) = -(I • shapeOperator i x ν v) := by
  by_cases h : Injective (fderiv ℝ i x)
  · have hD : fderiv ℝ i x = (fderiv ℂ i x).restrictScalars ℝ :=
      (hi.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ
    rw [shapeOperator_apply_eq_iff h]
    intro w
    rw [hi.secondFundamentalForm_I_smul_left, ← hi.secondFundamentalForm_I_smul_right,
      ← inner_fderiv_shapeOperator_apply h, hD]
    simp [real_inner_eq_re_inner, inner_smul_left, inner_smul_right]
  · simp [shapeOperator_of_not_injective h]

/-- The shape operators of a holomorphic map satisfy `S_(J ν) = J S_ν`. -/
theorem _root_.ContDiffAt.shapeOperator_I_smul_apply (hi : ContDiffAt ℂ 2 i x) (ν : E) (v : V) :
    shapeOperator i x (I • ν) v = I • shapeOperator i x ν v := by
  by_cases h : Injective (fderiv ℝ i x)
  · have hD : fderiv ℝ i x = (fderiv ℂ i x).restrictScalars ℝ :=
      (hi.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ
    rw [shapeOperator_apply_eq_iff h]
    intro w
    have key := inner_fderiv_shapeOperator_apply h ν v (I • w)
    rw [hi.secondFundamentalForm_I_smul_right, hD] at key
    rw [hD]
    simp only [real_inner_eq_re_inner, ContinuousLinearMap.coe_restrictScalars', map_smul,
      inner_smul_left, inner_smul_right, conj_I, neg_mul, map_neg] at key ⊢
    rw [key]
  · simp [shapeOperator_of_not_injective h]

end Complex

end TauCeti
