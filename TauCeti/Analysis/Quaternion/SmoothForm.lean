/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import TauCeti.Analysis.Calculus.DifferentialForm.Flux
public import TauCeti.Analysis.Quaternion.Cauchy.Representation
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cube
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Smooth-form exterior derivatives and oriented facet comparisons for `Dq`

This file connects the quaternionic surface element `Dq` and the affine boundary functional
`ContinuousLinearMap.rawAffineBoundary` to Mathlib's coordinate exterior derivative `extDeriv` and
to manifold top-form integration `TauCeti.integralTopForm`.

1. **Exterior-derivative identities.** For a continuous real-linear coefficient family
   `B : (Fin 4 → ℝ) → ℍ →L[ℝ] E`, the weighted `3`-form `quatSurfaceForm B x = (B x) ∘ Dq` is the
   coordinate flux form `fluxForm (fun i x ↦ B x (dq (Pi.single i 1)))`. Whenever `g, f : ℍ → ℍ`
   are real differentiable at `dq x`, the exterior derivative of the ordered two-sided `3`-form
   `g * Dq * f` is `(fueterRight (dg) * f + g * fueterLeft (df))` tensored with
   `(Pi.basisFun ℝ (Fin 4)).continuousDet`. Taking `g = 1` or `f = 1` yields
   `d(Dq · f) = (fueterLeft df) dV` and `d(f · Dq) = (fueterRight df) dV`, as well as closedness
   for Fueter regular functions and the affine cofactor pullback identity via `extDeriv_pullback`.

2. **Individual oriented facets and `integralTopForm` comparison.** Each of the eight facets
   `(j : Fin 4, b : Bool)` of an invertible affine parallelepiped `(fun w ↦ p + L w) '' Icc 0 1`
   is an injective affine image of the unit `3`-cube `Icc (0 : Fin 3 → ℝ) 1`, carrying its own
   global chart (`ContinuousLinearEquiv.affineFacetChartedSpace`) and signed orientation
   `ContinuousLinearEquiv.affineFacetOrientation`. When `0 < det L`, a tangent basis on a facet is
   positively oriented for `affineFacetOrientation` if and only if prepending the outward vector
   `± L eⱼ` produces a positive `4 × 4` determinant in `Fin 4 → ℝ`. For every scalar functional
   `ℓ : E →L[ℝ] ℝ` (and in particular each of the four real quaternion coordinates `1, i, j, k`),
   `integralTopForm` of the pulled-back surface form on each facet agrees unconditionally with the
   signed scalar face integral, and when the face integrands are Bochner integrable the sum over
   all eight facets recovers `rawAffineBoundary` — including for the un-cutoff Cauchy–Fueter kernel
   away from an interior pole.

## Main declarations

* `TauCeti.quatSurfaceForm`: the `E`-valued `3`-form `x ↦ (B x).compContinuousAlternatingMap Dq`.
* `TauCeti.extDeriv_quatSurfaceForm_mulLeftRight`, `TauCeti.extDeriv_op_smul_Dq`,
  `TauCeti.extDeriv_smul_Dq`: two-sided, left, and right Fueter exterior-derivative identities.
* `ContinuousLinearEquiv.extDeriv_pullback_quatSurfaceForm_mulLeftRight`: affine-pulled-back
  two-sided exterior-derivative identity via `extDeriv_pullback`.
* `ContinuousLinearEquiv.affineFacetChartedSpace`, `ContinuousLinearEquiv.affineFacetOrientation`,
  `ContinuousLinearEquiv.orientation_eq_affineFacetOrientation_iff_det_pos`: smooth cube-chart
  structure, signed orientation, and outward-first characterization on each parallelepiped facet.
* `ContinuousLinearEquiv.integralTopForm_affineFacet`,
  `ContinuousLinearEquiv.sum_integralTopForm_affineFacet`,
  `ContinuousLinearEquiv.sum_smul_integralTopForm_affineFacet_eq_rawAffineBoundary`: facetwise and
  boundary-sum comparisons between `integralTopForm` and `rawAffineBoundary`.
* `TauCeti.left_cauchyFueter_affine_integralTopForm`,
  `TauCeti.right_cauchyFueter_affine_integralTopForm`: left and right Cauchy–Fueter representation
  formulas in terms of `integralTopForm` on the eight oriented facets.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 4, equation (18), and Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

noncomputable section

open MeasureTheory Set Function TauCeti.Quaternion
open scoped Quaternion Manifold Topology RealInnerProductSpace

namespace TauCeti

section ExteriorDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `E`-valued `3`-form `x ↦ (B x).compContinuousAlternatingMap Dq` on `Fin 4 → ℝ` obtained by
applying a real-linear coefficient `B x : ℍ →L[ℝ] E` to the quaternionic surface element `Dq`. -/
def quatSurfaceForm (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (x : Fin 4 → ℝ) :
    (Fin 4 → ℝ) [⋀^Fin 3]→L[ℝ] E :=
  (B x).compContinuousAlternatingMap Dq

theorem quatSurfaceForm_apply (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (x : Fin 4 → ℝ)
    (v : Fin 3 → Fin 4 → ℝ) :
    quatSurfaceForm B x v = B x (Dq v) :=
  (rfl)

/-- `quatSurfaceForm B` is the coordinate `fluxForm` of the four unit evaluations
`i ↦ B x (dq (Pi.single i 1))`. -/
theorem quatSurfaceForm_eq_fluxForm (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    quatSurfaceForm B = fluxForm fun i x ↦ B x (dq (Pi.single i 1)) := by
  ext x v
  rw [quatSurfaceForm_apply, Dq_eq_fluxForm x, fluxForm_apply, map_sum, fluxForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, dq_single, one_smul]

/-- Pulling `quatSurfaceForm B` back along an invertible affine map `u ↦ p + L u` gives the
coordinate `fluxForm` of `L.affineFluxPullback p (fun i x ↦ B x (dq (Pi.single i 1)))`. -/
theorem _root_.ContinuousLinearEquiv.quatSurfaceForm_comp_affine
    (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E)
    (u : Fin 4 → ℝ) :
    (quatSurfaceForm B (p + L u)).compContinuousLinearMap L.toContinuousLinearMap =
      fluxForm (L.affineFluxPullback p fun i x ↦ B x (dq (Pi.single i 1))) u := by
  rw [quatSurfaceForm_eq_fluxForm, L.fluxForm_comp_affine]

/-- The exterior derivative of `quatSurfaceForm B` at `x` is the coordinate divergence of
`i ↦ B x (dq (Pi.single i 1))` tensored with `(Pi.basisFun ℝ (Fin 4)).continuousDet`. -/
theorem extDeriv_quatSurfaceForm {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E} {x : Fin 4 → ℝ}
    (hB : ∀ i : Fin 4, DifferentiableAt ℝ (fun y ↦ B y (dq (Pi.single i 1))) x) :
    extDeriv (quatSurfaceForm B) x =
      (Pi.basisFun ℝ (Fin 4)).continuousDet.smulRight
        (∑ i : Fin 4, fderiv ℝ (fun y ↦ B y (dq (Pi.single i 1))) x (Pi.single i 1)) := by
  rw [quatSurfaceForm_eq_fluxForm, extDeriv_fluxForm hB]

/-- The coordinate divergence of the ordered two-sided field `g (dq y) * eᵢ * f (dq y)` at `x` is
`fueterRight (fderiv ℝ g (dq x)) * f (dq x) + g (dq x) * fueterLeft (fderiv ℝ f (dq x))`. -/
theorem sum_fderiv_mul_dq_single {f g : ℍ → ℍ} {x : Fin 4 → ℝ}
    (hg : DifferentiableAt ℝ g (dq x)) (hf : DifferentiableAt ℝ f (dq x)) :
    ∑ i : Fin 4,
      fderiv ℝ (fun y ↦ g (dq y) * dq (Pi.single i 1) * f (dq y)) x (Pi.single i 1) =
      fueterRight (fderiv ℝ g (dq x)) * f (dq x) +
        g (dq x) * fueterLeft (fderiv ℝ f (dq x)) := by
  have hd (i : Fin 4) :
      fderiv ℝ (fun y ↦ g (dq y) * dq (Pi.single i 1) * f (dq y)) x (Pi.single i 1) =
        (fderiv ℝ g (dq x) (dq (Pi.single i 1)) * dq (Pi.single i 1)) * f (dq x) +
          g (dq x) * (dq (Pi.single i 1) * fderiv ℝ f (dq x) (dq (Pi.single i 1))) := by
    have hq := (((hg.hasFDerivAt.mul_const' (dq (Pi.single i 1))).fun_mul'
      hf.hasFDerivAt).comp x dq.hasFDerivAt).fderiv
    have happ := congrArg (fun D : (Fin 4 → ℝ) →L[ℝ] ℍ ↦ D (Pi.single i 1)) hq
    simpa [Function.comp_def, mul_assoc, add_comm] using happ
  simp_rw [hd, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← fueterRight_eq_sum, ← fueterLeft_eq_sum]

/-- **Two-sided Fueter exterior-derivative identity.** Whenever `g` and `f` are real differentiable
at `dq x`, `d(g * Dq * f)` at `x` equals `(fueterRight (dg) * f + g * fueterLeft (df)) dV`. -/
theorem extDeriv_quatSurfaceForm_mulLeftRight {f g : ℍ → ℍ} {x : Fin 4 → ℝ}
    (hg : DifferentiableAt ℝ g (dq x)) (hf : DifferentiableAt ℝ f (dq x)) :
    extDeriv (quatSurfaceForm fun y ↦
      ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq y)) (f (dq y))) x =
      (Pi.basisFun ℝ (Fin 4)).continuousDet.smulRight
        (fueterRight (fderiv ℝ g (dq x)) * f (dq x) +
          g (dq x) * fueterLeft (fderiv ℝ f (dq x))) := by
  have hd (i : Fin 4) :
      DifferentiableAt ℝ (fun y ↦ g (dq y) * dq (Pi.single i 1) * f (dq y)) x :=
    (((hg.comp x dq.differentiableAt).mul_const _).mul (hf.comp x dq.differentiableAt))
  simpa only [ContinuousLinearMap.mulLeftRight_apply, sum_fderiv_mul_dq_single hg hf] using
    extDeriv_quatSurfaceForm (B := fun y ↦
      ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq y)) (f (dq y))) hd

private theorem dq_single_zero_one : dq (Pi.single 0 1) = 1 := by
  ext <;> simp [dq_apply]

/-- **Left Fueter exterior-derivative identity:** `d(Dq · f) = (fueterLeft (df)) dV` for every
`f : ℍ → ℍ` and `x : Fin 4 → ℝ` (for `f` non-differentiable at `dq x` both sides are `0`). -/
theorem extDeriv_op_smul_Dq (f : ℍ → ℍ) (x : Fin 4 → ℝ) :
    extDeriv (fun y ↦ MulOpposite.op (f (dq y)) • Dq) x =
      (Pi.basisFun ℝ (Fin 4)).continuousDet.smulRight (fueterLeft (fderiv ℝ f (dq x))) := by
  have heq : (fun y : Fin 4 → ℝ ↦ MulOpposite.op (f (dq y)) • Dq) =
      quatSurfaceForm fun y ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ 1 (f (dq y)) := by
    funext y; ext1 v; simp [quatSurfaceForm_apply]
  by_cases hf : DifferentiableAt ℝ f (dq x)
  · rw [heq, extDeriv_quatSurfaceForm_mulLeftRight (differentiableAt_const 1) hf]
    ext1 v; simp
  · have hnd : ¬ DifferentiableAt ℝ (fun y ↦ MulOpposite.op (f (dq y)) • Dq) x := by
      rw [heq, quatSurfaceForm_eq_fluxForm, differentiableAt_fluxForm_iff]
      let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
      have hdq : ⇑dq = ⇑e := coe_dq.trans (LinearEquiv.coe_toContinuousLinearEquiv' _).symm
      intro hall
      have hcomp : DifferentiableAt ℝ (f ∘ e) x := by
        simpa only [ContinuousLinearMap.mulLeftRight_apply, dq_single_zero_one, one_mul, hdq,
          Function.comp_def] using hall 0
      rw [e.comp_right_differentiableAt_iff, ← hdq] at hcomp
      exact hf hcomp
    rw [extDeriv_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hf, map_zero]
    ext1 v; simp

/-- **Right Fueter exterior-derivative identity:** `d(f · Dq) = (fueterRight (df)) dV` for every
`f : ℍ → ℍ` and `x : Fin 4 → ℝ` (for `f` non-differentiable at `dq x` both sides are `0`). -/
theorem extDeriv_smul_Dq (f : ℍ → ℍ) (x : Fin 4 → ℝ) :
    extDeriv (fun y ↦ f (dq y) • Dq) x =
      (Pi.basisFun ℝ (Fin 4)).continuousDet.smulRight (fueterRight (fderiv ℝ f (dq x))) := by
  have heq : (fun y : Fin 4 → ℝ ↦ f (dq y) • Dq) =
      quatSurfaceForm fun y ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ (f (dq y)) 1 := by
    funext y; ext1 v; simp [quatSurfaceForm_apply]
  by_cases hf : DifferentiableAt ℝ f (dq x)
  · rw [heq, extDeriv_quatSurfaceForm_mulLeftRight hf (differentiableAt_const 1)]
    ext1 v; simp
  · have hnd : ¬ DifferentiableAt ℝ (fun y ↦ f (dq y) • Dq) x := by
      rw [heq, quatSurfaceForm_eq_fluxForm, differentiableAt_fluxForm_iff]
      let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
      have hdq : ⇑dq = ⇑e := coe_dq.trans (LinearEquiv.coe_toContinuousLinearEquiv' _).symm
      intro hall
      have hcomp : DifferentiableAt ℝ (f ∘ e) x := by
        simpa only [ContinuousLinearMap.mulLeftRight_apply, dq_single_zero_one, mul_one, hdq,
          Function.comp_def] using hall 0
      rw [e.comp_right_differentiableAt_iff, ← hdq] at hcomp
      exact hf hcomp
    rw [extDeriv_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hf, map_zero]
    ext1 v; simp

/-- When `g` is right Fueter regular and `f` is left Fueter regular at `dq x`, the two-sided
weighted `3`-form `g * Dq * f` is closed at `x`. -/
theorem RightFueterAt.extDeriv_quatSurfaceForm_mulLeftRight_eq_zero {f g : ℍ → ℍ} {x : Fin 4 → ℝ}
    (hg : RightFueterAt g (dq x)) (hf : LeftFueterAt f (dq x)) :
    extDeriv (quatSurfaceForm fun y ↦
      ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq y)) (f (dq y))) x = 0 := by
  rw [extDeriv_quatSurfaceForm_mulLeftRight hg.differentiableAt hf.differentiableAt,
    hg.fueterRight_fderiv, hf.fueterLeft_fderiv]
  ext1 v; simp

/-- When `f` is left Fueter regular at `dq x`, `Dq · f` is closed at `x`. -/
theorem LeftFueterAt.extDeriv_op_smul_Dq_eq_zero {f : ℍ → ℍ} {x : Fin 4 → ℝ}
    (hf : LeftFueterAt f (dq x)) :
    extDeriv (fun y ↦ MulOpposite.op (f (dq y)) • Dq) x = 0 := by
  rw [extDeriv_op_smul_Dq f x, hf.fueterLeft_fderiv]; ext1 v; simp

/-- When `f` is right Fueter regular at `dq x`, `f · Dq` is closed at `x`. -/
theorem RightFueterAt.extDeriv_smul_Dq_eq_zero {f : ℍ → ℍ} {x : Fin 4 → ℝ}
    (hf : RightFueterAt f (dq x)) :
    extDeriv (fun y ↦ f (dq y) • Dq) x = 0 := by
  rw [extDeriv_smul_Dq f x, hf.fueterRight_fderiv]; ext1 v; simp

/-- Exterior derivative of the affine-pulled-back two-sided surface form `g * Dq * f` via
`extDeriv_pullback`: at any `u` where `g` and `f` are differentiable at `dq (p + L u)`, it equals
`det L` times the two-sided Fueter expression tensored with
`(Pi.basisFun ℝ (Fin 4)).continuousDet`. -/
theorem _root_.ContinuousLinearEquiv.extDeriv_pullback_quatSurfaceForm_mulLeftRight
    (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) {f g : ℍ → ℍ} {u : Fin 4 → ℝ}
    (hg : DifferentiableAt ℝ g (dq (p + L u))) (hf : DifferentiableAt ℝ f (dq (p + L u))) :
    extDeriv (fun w ↦ (quatSurfaceForm (fun y ↦
      ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq y)) (f (dq y))) (p + L w)).compContinuousLinearMap
        L.toContinuousLinearMap) u =
      (Pi.basisFun ℝ (Fin 4)).continuousDet.smulRight
        (LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) •
          (fueterRight (fderiv ℝ g (dq (p + L u))) * f (dq (p + L u)) +
            g (dq (p + L u)) * fueterLeft (fderiv ℝ f (dq (p + L u))))) := by
  have hpull : (fun w ↦ (quatSurfaceForm (fun y ↦
      ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq y)) (f (dq y))) (p + L w)).compContinuousLinearMap
        L.toContinuousLinearMap) =
      fluxForm (L.affineFluxPullback p fun i y ↦
        g (dq y) * dq (Pi.single i 1) * f (dq y)) :=
    funext fun w ↦ L.quatSurfaceForm_comp_affine p _ w
  have hd (i : Fin 4) :
      DifferentiableAt ℝ (fun y ↦ g (dq y) * dq (Pi.single i 1) * f (dq y)) (p + L u) :=
    (((hg.comp (p + L u) dq.differentiableAt).mul_const _).mul
      (hf.comp (p + L u) dq.differentiableAt))
  rw [hpull, L.extDeriv_fluxForm_affineFluxPullback p hd, sum_fderiv_mul_dq_single hg hf]

end ExteriorDerivative

/-- The orientation sign `± (-1)^j` of the `(j, b)`-facet of the unit `4`-cube: `b = true` is the
front facet `u j = 1` and `b = false` is the back facet `u j = 0`. -/
def affineFacetSign (j : Fin 4) (b : Bool) : ℤˣ :=
  (if b then 1 else -1) * (-1) ^ (j : ℕ)

theorem coe_affineFacetSign (j : Fin 4) (b : Bool) :
    ((affineFacetSign j b : ℤ) : ℝ) = (if b then (1 : ℝ) else -1) * (-1 : ℝ) ^ (j : ℕ) := by
  rcases b with _ | _ <;> simp [affineFacetSign]

/-- The scalar ambient rough `3`-form on `Fin 4 → ℝ` obtained by composing `quatSurfaceForm B`
with a continuous linear functional `ℓ : E →L[ℝ] ℝ`. -/
def ambientQuatSurfaceRoughForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    RoughForm 𝓘(ℝ, Fin 4 → ℝ) (Fin 4 → ℝ) ℝ 3 :=
  fun x ↦ ((ℓ.comp (B x)).compContinuousAlternatingMap Dq).compContinuousLinearMap
    (NormedSpace.fromTangentSpace x).toContinuousLinearMap

@[simp]
theorem ambientQuatSurfaceRoughForm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (x : Fin 4 → ℝ)
    (v : Fin 3 → TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x) :
    ambientQuatSurfaceRoughForm ℓ B x v =
      ℓ (B x (Dq fun r ↦ NormedSpace.fromTangentSpace x (v r))) := (rfl)

/-- Identifies the coordinate `fluxForm` of the scalar components `i ↦ ℓ (B x (dq eᵢ))` with the
ambient manifold rough `3`-form `ambientQuatSurfaceRoughForm ℓ B` on `Fin 4 → ℝ`. -/
theorem fluxForm_eq_ambientQuatSurfaceRoughForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    (fluxForm fun i x ↦ ℓ (B x (dq (Pi.single i 1)))) = ambientQuatSurfaceRoughForm ℓ B := by
  have hcomp : (fun i (x : Fin 4 → ℝ) ↦ ℓ (B x (dq (Pi.single i 1)))) =
      fun i x ↦ (ℓ.comp (B x)) (dq (Pi.single i 1)) := by
    funext i x
    simp only [ContinuousLinearMap.comp_apply]
  rw [hcomp, ← quatSurfaceForm_eq_fluxForm]
  ext x v
  simp only [quatSurfaceForm_apply, ContinuousLinearMap.comp_apply]
  exact congrArg (fun u ↦ ℓ (B x (Dq u)))
    (funext fun r ↦ (NormedSpace.fromTangentSpace_apply x (v r)).symm)

/-- The ambient rough `3`-form `ambientQuatSurfaceRoughForm ℓ B` is continuous on `s` whenever each
of the four quaternion-basis coefficient functions `x ↦ B x (dq eᵢ)` is continuous on `s`. -/
theorem continuousOn_ambientQuatSurfaceRoughForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℝ) {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E} {s : Set (Fin 4 → ℝ)}
    (hB : ∀ i : Fin 4, ContinuousOn (fun x ↦ B x (dq (Pi.single i 1))) s) :
    ContinuousOn (X := Fin 4 → ℝ) (Y := (Fin 4 → ℝ) [⋀^Fin 3]→L[ℝ] ℝ)
      (ambientQuatSurfaceRoughForm ℓ B) s := by
  rw [← fluxForm_eq_ambientQuatSurfaceRoughForm]
  exact continuousOn_fluxForm fun i ↦ ℓ.continuous.comp_continuousOn (hB i)

/-- The ambient rough `3`-form `ambientQuatSurfaceRoughForm ℓ B` is a `C^r` smooth form on the
model manifold `Fin 4 → ℝ` whenever each of the four quaternion-basis coefficient functions
`x ↦ B x (dq eᵢ)` is globally `C^r`. -/
theorem isSmoothForm_ambientQuatSurfaceRoughForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℝ) {r : WithTop ℕ∞} {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB : ∀ i : Fin 4, ContDiff ℝ r (fun x ↦ B x (dq (Pi.single i 1)))) :
    IsSmoothForm 𝓘(ℝ, Fin 4 → ℝ) r (ambientQuatSurfaceRoughForm ℓ B) := by
  rw [isSmoothForm_modelSpace_iff, ← fluxForm_eq_ambientQuatSurfaceRoughForm]
  exact contDiff_fluxForm fun i ↦ ℓ.contDiff.comp (hB i)

end TauCeti

namespace ContinuousLinearMap

open TauCeti

/-- The base corner `p + L (j.insertNth (if b then 1 else 0) 0)` of the `(j, b)`-facet of the
affine parallelepiped `w ↦ p + L w`. -/
def affineFacetBase (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) (j : Fin 4)
    (b : Bool) : Fin 4 → ℝ :=
  p + L (j.insertNth (if b then 1 else 0) 0)

/-- The continuous linear map `u ↦ L (j.insertNth 0 u)` parametrizing the tangent directions of the
`j`-th facet pair of `w ↦ p + L w`. -/
def affineFacetLinearMap (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ∑ r : Fin 3, (ContinuousLinearMap.proj r).smulRight (L (Pi.single (j.succAbove r) 1))

@[simp]
theorem affineFacetLinearMap_apply (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4)
    (u : Fin 3 → ℝ) :
    L.affineFacetLinearMap j u = L (j.insertNth 0 u) := by
  have hu : ∑ r : Fin 3, u r • (Pi.single (j.succAbove r) 1 : Fin 4 → ℝ) = j.insertNth 0 u := by
    ext k
    rcases eq_or_ne j k with rfl | hk
    · simp
    · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hk.symm
      simp [Pi.single_apply, (Fin.succAbove_right_injective (p := j)).eq_iff]
  simp only [affineFacetLinearMap, sum_apply, smulRight_apply, proj_apply, ← map_smul, ← map_sum,
    hu]

theorem affineFacetLinearMap_single (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) (r : Fin 3) :
    L.affineFacetLinearMap j (Pi.single r 1) = L (Pi.single (j.succAbove r) 1) := by
  rw [affineFacetLinearMap_apply]
  congr 1
  ext k
  rcases eq_or_ne j k with rfl | hk
  · simp
  · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hk.symm
    simp [Pi.single_apply, (Fin.succAbove_right_injective (p := j)).eq_iff]

theorem affineFacetBase_add_affineFacetLinearMap (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (j : Fin 4) (b : Bool) (u : Fin 3 → ℝ) :
    L.affineFacetBase p j b + L.affineFacetLinearMap j u =
      p + L (j.insertNth (if b then 1 else 0) u) := by
  rw [affineFacetBase, affineFacetLinearMap_apply, add_assoc, ← map_add]
  congr 2
  ext k
  rcases eq_or_ne j k with rfl | hk
  · simp
  · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hk.symm
    simp

theorem affineFacet_subset_image (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) (j : Fin 4)
    (b : Bool) :
    ((fun u : Fin 3 → ℝ ↦ L.affineFacetBase p j b + L.affineFacetLinearMap j u) '' Icc 0 1) ⊆
      (fun w : Fin 4 → ℝ ↦ p + L w) '' Icc 0 1 := by
  rintro _ ⟨u, hu, rfl⟩
  dsimp only
  rw [affineFacetBase_add_affineFacetLinearMap]
  refine mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨?_, hu⟩)
  rcases b with _ | _ <;> simp

/-- The outward-pointing edge vector `± L eⱼ` on the `(j, b)`-facet of `w ↦ p + L w`. -/
def affineFacetOutward (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) (b : Bool) :
    Fin 4 → ℝ :=
  (if b then (1 : ℝ) else -1) • L (Pi.single j 1)

/-- Prepending `affineFacetOutward L j b` to `w ↦ L.affineFacetLinearMap j (w r)` gives `4 × 4`
determinant `affineFacetSign j b * det L * det w`. -/
theorem det_cons_affineFacetOutward_affineFacetLinearMap (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (j : Fin 4) (b : Bool) (w : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of (Fin.cons (L.affineFacetOutward j b)
      (fun r ↦ L.affineFacetLinearMap j (w r)))).det =
      ((affineFacetSign j b : ℤ) : ℝ) * LinearMap.det L.toLinearMap * (Matrix.of w).det := by
  let u₀ : Fin 4 → ℝ := (if b then (1 : ℝ) else -1) • Pi.single j 1
  let u : Fin 3 → Fin 4 → ℝ := fun r ↦ j.insertNth 0 (w r)
  have hcons : Fin.cons (L.affineFacetOutward j b) (fun r ↦ L.affineFacetLinearMap j (w r)) =
      L.toLinearMap ∘ Fin.cons u₀ u := funext <| Fin.cases
    (by rcases b <;> simp [u₀, affineFacetOutward])
    (fun r ↦ by simp [u, affineFacetLinearMap_apply])
  have hdet := (Pi.basisFun ℝ (Fin 4)).det_comp L.toLinearMap (Fin.cons u₀ u)
  simp only [Pi.basisFun_det_apply] at hdet
  rw [hcons, hdet, ← sum_signed_mul_coordMinorForm]
  simp only [u₀, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hminor : coordMinorForm j u = (Matrix.of w).det := by
    simp [coordMinorForm_apply, u]
  rw [hminor, coe_affineFacetSign]
  rcases b with _ | _ <;> simp <;> ring

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open ContinuousLinearMap TauCeti

variable (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ))

theorem injective_affineFacetLinearMap (j : Fin 4) :
    Injective (L.toContinuousLinearMap.affineFacetLinearMap j) := by
  intro u₁ u₂ h
  simp only [affineFacetLinearMap_apply, ContinuousLinearEquiv.coe_coe] at h
  funext r; simpa using congrFun (L.injective h) (j.succAbove r)

variable (p : Fin 4 → ℝ)

/-- The single-chart `ChartedSpace` structure on the `(j, b)`-facet of `w ↦ p + L w`, modelled on
the closed unit `3`-cube `Icc (0 : Fin 3 → ℝ) 1`. -/
abbrev affineFacetChartedSpace (j : Fin 4) (b : Bool) :
    ChartedSpace (Icc (0 : Fin 3 → ℝ) 1)
      ↥((fun u : Fin 3 → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1) :=
  (L.toContinuousLinearMap.affineFacetLinearMap j).unitCubeImageChartedSpace
    (L.injective_affineFacetLinearMap j) (L.toContinuousLinearMap.affineFacetBase p j b)

/-- Each `(j, b)`-facet of an invertible affine parallelepiped is a `C^n` manifold with corners
modelled on the closed unit `3`-cube. -/
theorem isManifold_affineFacetChartedSpace (j : Fin 4) (b : Bool) (n : WithTop ℕ∞) :
    letI := L.affineFacetChartedSpace p j b
    IsManifold (modelWithCornersUnitCube (Fin 3)) n
      ↥((fun u : Fin 3 → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1) :=
  (L.toContinuousLinearMap.affineFacetLinearMap j).isManifold_unitCubeImageChartedSpace
    (L.injective_affineFacetLinearMap j) (L.toContinuousLinearMap.affineFacetBase p j b) n

/-- The outward-signed orientation on the `(j, b)`-facet of `w ↦ p + L w`. When `0 < det L`, this
is the geometric outward-first orientation (`orientation_eq_affineFacetOrientation_iff_det_pos`). -/
def affineFacetOrientation (j : Fin 4) (b : Bool) :
    letI := L.affineFacetChartedSpace p j b
    Manifold.Orientation (modelWithCornersUnitCube (Fin 3))
      ↥((fun u : Fin 3 → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1) (Fin 3) :=
  (L.toContinuousLinearMap.affineFacetLinearMap j).unitCubeImageOrientation
    (L.injective_affineFacetLinearMap j)
    (L.toContinuousLinearMap.affineFacetBase p j b) (affineFacetSign j b)

/-- **Outward-first geometric characterization of `affineFacetOrientation`.** When `0 < det L`, a
tangent basis `v` at any point `x` of the `(j, b)`-facet (including edges and vertices) has the
facet orientation if and only if prepending the outward vector `affineFacetOutward L j b` to the
pushforward tangent frame produces a positive `4 × 4` determinant. -/
theorem orientation_eq_affineFacetOrientation_iff_det_pos
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ)) (j : Fin 4) (b : Bool) :
    letI := L.affineFacetChartedSpace p j b
    letI := L.isManifold_affineFacetChartedSpace p j b 1
    ∀ (x : ↥((fun u : Fin 3 → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1))
      (v : Module.Basis (Fin 3) ℝ (TangentSpace (modelWithCornersUnitCube (Fin 3)) x)),
      v.orientation = (L.affineFacetOrientation p j b).orientationAt x ↔
        0 < (Matrix.of (Fin.cons (L.toContinuousLinearMap.affineFacetOutward j b)
          (fun r ↦ NormedSpace.fromTangentSpace x.val
            (mfderiv (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ)
              Subtype.val x (v r))))).det := by
  let M := L.toContinuousLinearMap.affineFacetLinearMap j
  let hM := L.injective_affineFacetLinearMap j
  let q₀ := L.toContinuousLinearMap.affineFacetBase p j b
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  intro x v
  let e := (tangentSpaceCastModel (modelWithCornersUnitCube (Fin 3)) x).toLinearEquiv
  let w : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) := v.map e
  let b₀ := Pi.basisFun ℝ (Fin 3)
  have hmf (r : Fin 3) : NormedSpace.fromTangentSpace x.val
      (mfderiv (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ) Subtype.val x (v r)) =
      M (w r) := by rw [M.mfderiv_subtypeVal_unitCubeImage hM q₀ x]; simp [w, e]
  simp_rw [hmf]
  rw [L.toContinuousLinearMap.det_cons_affineFacetOutward_affineFacetLinearMap j b w,
    ← Pi.basisFun_det_apply]
  have hor : (v.orientation = (L.affineFacetOrientation p j b).orientationAt x) ↔
      w.orientation =
        if affineFacetSign j b = 1 then b₀.orientation else -b₀.orientation := by
    rw [← (_root_.Orientation.map (Fin 3) e).injective.eq_iff, ← Module.Basis.orientation_map,
      affineFacetOrientation, M.map_orientationAt_unitCubeImageOrientation hM q₀]
  rw [hor]
  rcases Int.units_eq_one_or (affineFacetSign j b) with hs | hs <;> simp only [hs, ↓reduceIte]
  · rw [eq_comm, b₀.orientation_eq_iff_det_pos w]
    simp only [Units.val_one, Int.cast_one, one_mul]
    exact ⟨fun hw ↦ mul_pos hL hw, fun hpos ↦ pos_of_mul_pos_right hpos hL.le⟩
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hne, ↓reduceIte, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      neg_one_mul]
    rw [← b₀.orientation_ne_iff_eq_neg, ne_comm, w.orientation_ne_iff_eq_neg,
      b₀.orientation_eq_neg_iff_det_neg w, neg_mul, neg_pos]
    exact ⟨mul_neg_of_pos_of_neg hL, fun hneg ↦ neg_of_mul_neg_right hneg hL.le⟩

/-- **Facetwise `integralTopForm` comparison.** For any real normed space `E`, continuous linear
functional `ℓ : E →L[ℝ] ℝ`, and coefficient family `B : (Fin 4 → ℝ) → ℍ →L[ℝ] E`,
`integralTopForm` of the pulled-back surface form on the `(j, b)`-facet against
`affineFacetOrientation` equals `(if b then 1 else -1)` times the scalar Lebesgue face integral of
`ℓ (B · (affineFaceNormal L j))` (with both sides equal to `0` when non-integrable). -/
theorem integralTopForm_affineFacet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (j : Fin 4) (b : Bool) :
    letI := L.affineFacetChartedSpace p j b
    integralTopForm (L.affineFacetOrientation p j b)
      (mpullback (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ) Subtype.val
        (ambientQuatSurfaceRoughForm ℓ B)) =
      (if b then (1 : ℝ) else -1) *
        ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          ℓ (B (p + L (j.insertNth (if b then 1 else 0) u))
            (L.toContinuousLinearMap.affineFaceNormal j)) := by
  let M := L.toContinuousLinearMap.affineFacetLinearMap j
  let hM := L.injective_affineFacetLinearMap j
  let q₀ := L.toContinuousLinearMap.affineFacetBase p j b
  let := M.unitCubeImageChartedSpace hM q₀
  have hparam (u : Fin 3 → ℝ) : p + L (j.insertNth (if b then 1 else 0) u) = q₀ + M u := by
    simpa only [q₀, M, ContinuousLinearEquiv.coe_coe] using
      (L.toContinuousLinearMap.affineFacetBase_add_affineFacetLinearMap p j b u).symm
  simp_rw [hparam]
  rw [affineFacetOrientation,
    M.integralTopForm_mpullback_unitCubeImage hM q₀ (affineFacetSign j b)
      (ambientQuatSurfaceRoughForm ℓ B),
    coe_affineFacetSign, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine setIntegral_congr_fun isClosed_Icc.measurableSet fun u _ ↦ ?_
  simp only [ambientQuatSurfaceRoughForm_apply, affineFacetLinearMap_single,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, affineFaceNormal_eq,
    _root_.map_smul, smul_eq_mul, M]

/-- Summing `integralTopForm` of the pulled-back surface form over all eight oriented facets gives
`ℓ (rawAffineBoundary L p B)` whenever the `E`-valued face integrand is Bochner integrable on each
facet. -/
theorem sum_integralTopForm_affineFacet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ℓ : E →L[ℝ] ℝ) {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB : ∀ j (b : Bool), IntegrableOn
      (fun u : Fin 3 → ℝ ↦ B (p + L (j.insertNth (if b then 1 else 0) u))
        (L.toContinuousLinearMap.affineFaceNormal j))
      (Icc (0 : Fin 3 → ℝ) 1)) :
    (∑ j : Fin 4, ∑ b : Bool,
      letI := L.affineFacetChartedSpace p j b
      integralTopForm (L.affineFacetOrientation p j b)
        (mpullback (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ) Subtype.val
          (ambientQuatSurfaceRoughForm ℓ B))) =
      ℓ (L.toContinuousLinearMap.rawAffineBoundary p B) := by
  simp_rw [L.integralTopForm_affineFacet p ℓ B, fun j b ↦ ℓ.integral_comp_comm (hB j b)]
  rw [rawAffineBoundary_eq, _root_.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fintype.sum_bool, ℓ.map_sub]
  simp [ContinuousLinearEquiv.coe_coe, sub_eq_add_neg]

/-- **Componentwise `(1, i, j, k)` reconstruction of `rawAffineBoundary` from `integralTopForm`.**
Summing the `1, i, j, k` coordinate `integralTopForm` values across all eight oriented facets
recovers `rawAffineBoundary L.toContinuousLinearMap p B` in `ℍ` whenever each face integrand is
integrable. -/
theorem sum_smul_integralTopForm_affineFacet_eq_rawAffineBoundary
    {B : (Fin 4 → ℝ) → ℍ →L[ℝ] ℍ}
    (hB : ∀ j (b : Bool), IntegrableOn
      (fun u : Fin 3 → ℝ ↦ B (p + L (j.insertNth (if b then 1 else 0) u))
        (L.toContinuousLinearMap.affineFaceNormal j))
      (Icc (0 : Fin 3 → ℝ) 1)) :
    (∑ i : Fin 4,
      (∑ j : Fin 4, ∑ b : Bool,
        letI := L.affineFacetChartedSpace p j b
        integralTopForm (L.affineFacetOrientation p j b)
          (mpullback (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ) Subtype.val
            (ambientQuatSurfaceRoughForm (innerSLFlip ℝ (dq (Pi.single i 1))) B))) •
        dq (Pi.single i 1)) =
      L.toContinuousLinearMap.rawAffineBoundary p B := by
  rw [← _root_.Quaternion.sum_inner_dq_single_smul (L.toContinuousLinearMap.rawAffineBoundary p B)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [L.sum_integralTopForm_affineFacet p (innerSLFlip ℝ (dq (Pi.single i 1))) hB,
    innerSLFlip_apply_apply]

end ContinuousLinearEquiv

namespace TauCeti

private theorem integrableOn_affineFacet_mul_cauchyFueterKernel
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' ((fun w ↦ p + L w) '' Icc 0 1)))
    (hx₀ : L.symm (x₀ - p) ∈ univ.pi fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
    (j : Fin 4) (b : Bool) :
    IntegrableOn
      (fun u : Fin 3 → ℝ ↦
        cauchyFueterKernel (dq (p + L (j.insertNth (if b then 1 else 0) u))) (dq x₀) *
          L.toContinuousLinearMap.affineFaceNormal j *
          f (dq (p + L (j.insertNth (if b then 1 else 0) u))))
      (Icc (0 : Fin 3 → ℝ) 1) ∧
    IntegrableOn
      (fun u : Fin 3 → ℝ ↦
        f (dq (p + L (j.insertNth (if b then 1 else 0) u))) *
          L.toContinuousLinearMap.affineFaceNormal j *
          cauchyFueterKernel (dq (p + L (j.insertNth (if b then 1 else 0) u))) (dq x₀))
      (Icc (0 : Fin 3 → ℝ) 1) := by
  let S := (fun u : Fin 3 → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
    L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1
  have hsub : S ⊆ (fun w ↦ p + L w) '' Icc 0 1 :=
    L.toContinuousLinearMap.affineFacet_subset_image p j b
  have hnotMem : dq x₀ ∉ dq '' S := by
    rintro ⟨_, ⟨u, _, rfl⟩, hy⟩
    dsimp only at hy
    rw [ContinuousLinearMap.affineFacetBase_add_affineFacetLinearMap,
      ContinuousLinearEquiv.coe_coe] at hy
    have heq : p + L (j.insertNth (if b then 1 else 0) u) = x₀ :=
      (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.injective
        (by simpa only [coe_dq] using hy)
    have hj := mem_pi.mp hx₀ j (mem_univ j)
    have hinv : L.symm (x₀ - p) = j.insertNth (if b then 1 else 0) u :=
      L.injective (by simp [← heq])
    rw [hinv, Fin.insertNth_apply_same] at hj
    rcases b with _ | _ <;> simp at hj
  have hmap : MapsTo (fun u : Fin 3 → ℝ ↦ p + L (j.insertNth (if b then 1 else 0) u))
      (Icc 0 1) S := fun u hu ↦
    ⟨u, hu, by dsimp only; rw [ContinuousLinearMap.affineFacetBase_add_affineFacetLinearMap,
      ContinuousLinearEquiv.coe_coe]⟩
  have hparam :
      Continuous (fun u : Fin 3 → ℝ ↦ dq (p + L (j.insertNth (if b then 1 else 0) u))) :=
    dq.continuous.comp (continuous_const.add
      (L.continuous.comp (continuous_const.finInsertNth j continuous_id)))
  have hK : ContinuousOn
      (fun u : Fin 3 → ℝ ↦ cauchyFueterKernel
        (dq (p + L (j.insertNth (if b then 1 else 0) u))) (dq x₀))
      (Icc 0 1) :=
    (continuousOn_cauchyFueterKernel hnotMem).comp hparam.continuousOn (hmap.comp_left dq)
  have hfI : ContinuousOn
      (fun u : Fin 3 → ℝ ↦ f (dq (p + L (j.insertNth (if b then 1 else 0) u))))
      (Icc 0 1) :=
    (hc.mono (image_mono hsub)).comp hparam.continuousOn (hmap.comp_left dq)
  exact ⟨((hK.mul continuousOn_const).mul hfI).integrableOn_compact isCompact_Icc,
    ((hfI.mul continuousOn_const).mul hK).integrableOn_compact isCompact_Icc⟩

/-- **Left Cauchy–Fueter representation via `integralTopForm` on the eight oriented facets.**
When `0 < det L`, `f` is continuous on the closed affine parallelepiped and left Fueter regular in
its punctured interior, and `x₀` lies in the open parameter cube, `f (dq x₀)` is `(2π²)⁻¹` times
the componentwise `integralTopForm` sum of `G * Dq * f` over the eight outward-oriented facets. -/
theorem left_cauchyFueter_affine_integralTopForm
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : LeftFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)) \ {dq x₀}))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ∑ i : Fin 4,
        (∑ j : Fin 4, ∑ b : Bool,
          letI := L.affineFacetChartedSpace p j b
          integralTopForm (L.affineFacetOrientation p j b)
            (mpullback (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ) Subtype.val
              (ambientQuatSurfaceRoughForm (innerSLFlip ℝ (dq (Pi.single i 1)))
                (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
                  (cauchyFueterKernel (dq x) (dq x₀)) (f (dq x)))))) •
          dq (Pi.single i 1) := by
  rw [L.sum_smul_integralTopForm_affineFacet_eq_rawAffineBoundary p fun j b ↦
    (integrableOn_affineFacet_mul_cauchyFueterKernel hc hx₀ j b).left]
  exact left_cauchyFueter_affine hL hc hf hx₀

/-- **Right Cauchy–Fueter representation via `integralTopForm` on the eight oriented facets.**
When `0 < det L`, `f` is continuous on the closed affine parallelepiped and right Fueter regular in
its punctured interior, and `x₀` lies in the open parameter cube, `f (dq x₀)` is `(2π²)⁻¹` times
the componentwise `integralTopForm` sum of `f * Dq * G` over the eight outward-oriented facets. -/
theorem right_cauchyFueter_affine_integralTopForm
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : RightFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)) \ {dq x₀}))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ∑ i : Fin 4,
        (∑ j : Fin 4, ∑ b : Bool,
          letI := L.affineFacetChartedSpace p j b
          integralTopForm (L.affineFacetOrientation p j b)
            (mpullback (modelWithCornersUnitCube (Fin 3)) 𝓘(ℝ, Fin 4 → ℝ) Subtype.val
              (ambientQuatSurfaceRoughForm (innerSLFlip ℝ (dq (Pi.single i 1)))
                (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
                  (f (dq x)) (cauchyFueterKernel (dq x) (dq x₀)))))) •
          dq (Pi.single i 1) := by
  rw [L.sum_smul_integralTopForm_affineFacet_eq_rawAffineBoundary p fun j b ↦
    (integrableOn_affineFacet_mul_cauchyFueterKernel hc hx₀ j b).right]
  exact right_cauchyFueter_affine hL hc hf hx₀

end TauCeti

end
