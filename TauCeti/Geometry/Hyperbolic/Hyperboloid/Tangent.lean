/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hyperbolic.Hyperboloid.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Lorentz form on hyperboloid tangent hyperplanes

On `ℝ × E` the Lorentz form is `L((t,x),(s,y)) = ⟪x,y⟫ - ts`, the negative of
`minkowskiNormSq` on the diagonal. At a point `p` of the upper unit hyperboloid,
the tangent hyperplane is `ker (L p)`. Spatial projection identifies this hyperplane
with `E`, with inverse `v ↦ (⟪p.2,v⟫ / p.1, v)`.

The restriction of `L` is positive definite. More precisely, its value on a tangent
vector `v` lies between `‖v.2‖² / p.1²` and `‖v.2‖²`. These estimates supply positivity
and compatibility with the subspace topology for the hyperboloid Riemannian metric.
The differential of the ambient level function and the differential of the global
graph parametrization both identify this same tangent hyperplane.

The Lorentz-normal projection `Hyperboloid.tangentProjection`, given by
`v ↦ v + L(p,v)p`, fixes tangent vectors, kills the position vector, and preserves
the Lorentz pairing with tangent vectors. It is used to differentiate tangent fields.

## References

* J. Ratcliffe, *Foundations of Hyperbolic Manifolds*, third edition, Sections 3.1–3.2
  (the Lorentz form and the hyperboloid model).
-/

public section

noncomputable section

open scoped InnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Lorentz form with negative time direction on `ℝ × E`. -/
def lorentzForm : (ℝ × E) →L⋆[ℝ] (ℝ × E) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ E)
      (ContinuousLinearMap.snd ℝ ℝ E) -
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ E)
      (ContinuousLinearMap.fst ℝ ℝ E)

/-- Evaluation of the Lorentz form. -/
@[simp] theorem lorentzForm_apply (p q : ℝ × E) :
    lorentzForm p q = ⟪p.2, q.2⟫_ℝ - p.1 * q.1 := by
  simp [lorentzForm, mul_comm]

/-- The Lorentz form is symmetric. -/
theorem lorentzForm_comm (p q : ℝ × E) : lorentzForm p q = lorentzForm q p := by
  simp [real_inner_comm, mul_comm]

/-- On the diagonal the Lorentz form is minus the Minkowski square norm. -/
theorem lorentzForm_self (p : ℝ × E) : lorentzForm p p = -minkowskiNormSq p := by
  simp [minkowskiNormSq_def, pow_two]

/-- The Lorentz square of any ambient vector is at most its spatial square norm. -/
theorem lorentzForm_self_le_norm_snd_sq (v : ℝ × E) :
    lorentzForm v v ≤ ‖v.2‖ ^ 2 := by
  simp only [lorentzForm_apply, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg v.1]

/-- The derivative of the Minkowski square norm is minus twice the Lorentz pairing. -/
theorem hasFDerivAt_minkowskiNormSq (p : ℝ × E) :
    HasFDerivAt minkowskiNormSq (-2 • lorentzForm p) p := by
  have htime := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2
  have hspace := (hasStrictFDerivAt_norm_sq p.2).hasFDerivAt.comp p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hf : minkowskiNormSq = (fun v : ℝ × E ↦ v.1 ^ 2 - ‖v.2‖ ^ 2) :=
    funext minkowskiNormSq_def
  rw [hf]
  exact (htime.sub hspace).congr_fderiv (by
    apply ContinuousLinearMap.ext
    intro v
    simp
    ring)

namespace Hyperboloid

variable (p : hyperboloid E)

/-- The position vector on the unit hyperboloid has Lorentz square `-1`. -/
theorem lorentzForm_self_eq_neg_one : lorentzForm (p : ℝ × E) p = -1 := by
  rw [lorentzForm_self, (mem_hyperboloid.mp p.property).2]

/-- The tangent hyperplane, Lorentz-orthogonal to the position vector. -/
def tangent : Submodule ℝ (ℝ × E) := (lorentzForm (p : ℝ × E)).ker

/-- A tangent vector is Lorentz-orthogonal to the position vector. -/
theorem lorentzForm_eq_zero_of_mem_tangent {v : ℝ × E} (hv : v ∈ tangent p) :
    lorentzForm (p : ℝ × E) v = 0 :=
  (LinearMap.mem_ker).mp hv

/-- The tangent equation in ambient coordinates. -/
@[simp] theorem mem_tangent (v : ℝ × E) :
    v ∈ tangent p ↔ ⟪(p : ℝ × E).2, v.2⟫_ℝ = (p : ℝ × E).1 * v.1 := by
  simp [tangent, sub_eq_zero]

/-- A tangent vector's time coordinate is determined by its spatial coordinate. -/
theorem time_eq (v : tangent p) :
    (v : ℝ × E).1 = ⟪(p : ℝ × E).2, (v : ℝ × E).2⟫_ℝ / (p : ℝ × E).1 := by
  apply (eq_div_iff (time_pos p).ne').2
  simpa [mul_comm] using ((mem_tangent p _).1 v.property).symm

/-- The inverse of spatial projection on the tangent hyperplane. -/
def tangentLift : E →L[ℝ] ℝ × E :=
  (((p : ℝ × E).1)⁻¹ • innerSL ℝ (p : ℝ × E).2).prod (ContinuousLinearMap.id ℝ E)

/-- The ambient formula for the tangent lift. -/
@[simp] theorem tangentLift_apply (v : E) :
    tangentLift p v = (⟪(p : ℝ × E).2, v⟫_ℝ / (p : ℝ × E).1, v) := by
  simp [tangentLift, div_eq_mul_inv, mul_comm]

/-- Every tangent lift belongs to the Lorentz-orthogonal hyperplane. -/
theorem tangentLift_mem (v : E) : tangentLift p v ∈ tangent p := by
  simp only [mem_tangent, tangentLift_apply]
  field_simp [(time_pos p).ne']

/-- Spatial projection identifies the tangent hyperplane continuously and linearly with `E`. -/
def tangentEquiv : tangent p ≃L[ℝ] E where
  toFun v := (v : ℝ × E).2
  invFun v := ⟨tangentLift p v, tangentLift_mem p v⟩
  left_inv v := by
    apply Subtype.ext
    simpa only [tangentLift_apply] using Prod.ext (time_eq p v).symm (by simp)
  right_inv v := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (tangentLift p).continuous.subtype_mk _

/-- The tangent equivalence is spatial projection. -/
@[simp] theorem tangentEquiv_apply (v : tangent p) : tangentEquiv p v = (v : ℝ × E).2 :=
  (rfl)

/-- The inverse tangent equivalence is the tangent lift. -/
@[simp] theorem coe_tangentEquiv_symm (v : E) :
    ((tangentEquiv p).symm v : ℝ × E) = tangentLift p v := (rfl)

/-- The Lorentz form on tangent lifts, in spatial coordinates. -/
theorem lorentzForm_tangentLift (u v : E) :
    lorentzForm (tangentLift p u) (tangentLift p v) =
      ⟪u, v⟫_ℝ - ⟪(p : ℝ × E).2, u⟫_ℝ * ⟪(p : ℝ × E).2, v⟫_ℝ /
        (p : ℝ × E).1 ^ 2 := by
  simp [div_mul_div_comm, pow_two]

/-- A quantitative lower bound for the Lorentz form on a tangent hyperplane. -/
theorem norm_snd_sq_div_le_lorentzForm_self (v : tangent p) :
    ‖(v : ℝ × E).2‖ ^ 2 / (p : ℝ × E).1 ^ 2 ≤ lorentzForm (v : ℝ × E) v := by
  have hcs := real_inner_mul_inner_self_le (p : ℝ × E).2 (v : ℝ × E).2
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    (mem_tangent p _).1 v.property] at hcs
  rw [lorentzForm_apply, real_inner_self_eq_norm_sq]
  apply (div_le_iff₀ (sq_pos_of_pos (time_pos p))).2
  nlinarith [time_sq p]

/-- The Lorentz form is positive definite on every hyperboloid tangent hyperplane. -/
theorem lorentzForm_self_pos (v : tangent p) (hv : v ≠ 0) :
    0 < lorentzForm (v : ℝ × E) v := by
  have hs : (v : ℝ × E).2 ≠ 0 := by
    intro h
    apply hv
    apply (tangentEquiv p).injective
    simpa using h
  exact (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hs)) (sq_pos_of_pos (time_pos p))).trans_le
    (norm_snd_sq_div_le_lorentzForm_self p v)

/-- The tangent hyperplane is precisely the kernel of the ambient level differential. -/
theorem ker_fderiv_minkowskiNormSq :
    (fderiv ℝ minkowskiNormSq (p : ℝ × E)).ker = tangent p := by
  rw [(hasFDerivAt_minkowskiNormSq _).fderiv]
  ext v
  simp [tangent]

/-- The differential of the graph parametrization is the tangent lift. -/
theorem hasFDerivAt_parametrization (x : E) :
    HasFDerivAt (fun y : E ↦ (parametrization y : ℝ × E))
      (tangentLift (parametrization x)) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1
  simpa only [coe_parametrization, id_eq] using
    ((hn.sqrt (by positivity)).prodMk (hasFDerivAt_id x)).congr_fderiv
      (g' := tangentLift (parametrization x)) (by
        ext v
        · simp [tangentLift_apply, div_eq_mul_inv]
          ring
        · simp [tangentLift_apply])

/-- The image of the parametrization differential is exactly the tangent hyperplane. -/
theorem range_fderiv_parametrization (x : E) :
    (fderiv ℝ (fun y : E ↦ (parametrization y : ℝ × E)) x).range =
      tangent (parametrization x) := by
  rw [(hasFDerivAt_parametrization x).fderiv]
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact tangentLift_mem _ u
  · intro hv
    refine ⟨v.2, ?_⟩
    simpa only [tangentEquiv_apply, coe_tangentEquiv_symm, ContinuousLinearMap.coe_coe] using
      congrArg Subtype.val ((tangentEquiv (parametrization x)).symm_apply_apply ⟨v, hv⟩)

/-- The Lorentz-orthogonal projection onto the tangent hyperplane. It kills the normal
position vector and fixes every tangent vector. -/
def tangentProjection : (ℝ × E) →L[ℝ] tangent p :=
  (ContinuousLinearMap.id ℝ (ℝ × E) + (lorentzForm (p : ℝ × E)).smulRight (p : ℝ × E)).codRestrict
    (tangent p) fun v ↦ by
      simp only [add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply]
      -- The normal has Lorentz square `-1`, so the normal component cancels.
      simp only [tangent, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_add, map_smul,
        lorentzForm_self_eq_neg_one, smul_eq_mul, mul_neg_one, add_neg_cancel]

/-- The projection adds the Lorentz pairing with the normal times the normal. -/
@[simp] theorem coe_tangentProjection (v : ℝ × E) :
    (tangentProjection p v : ℝ × E) = v + lorentzForm (p : ℝ × E) v • (p : ℝ × E) := (rfl)

/-- Tangent projection fixes tangent vectors. -/
@[simp] theorem tangentProjection_coe (v : tangent p) : tangentProjection p v = v := by
  apply Subtype.ext
  have hv := lorentzForm_eq_zero_of_mem_tangent p v.property
  simp [hv]

/-- Tangent projection kills the position vector. -/
@[simp] theorem tangentProjection_self : tangentProjection p p = 0 := by
  apply Subtype.ext
  rw [coe_tangentProjection, lorentzForm_self_eq_neg_one]
  simp

/-- Tangent projection preserves the Lorentz pairing with every tangent vector. -/
theorem lorentzForm_tangentProjection (u : ℝ × E) (v : tangent p) :
    lorentzForm (tangentProjection p u : ℝ × E) v = lorentzForm u v := by
  rw [coe_tangentProjection]
  have hv := lorentzForm_eq_zero_of_mem_tangent p v.property
  simp only [map_add, map_smulₛₗ, add_apply, smul_apply, hv, smul_zero,
    add_zero]

end Hyperboloid

end TauCeti
