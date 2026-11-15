/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Integrability
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
import TauCeti.Analysis.ODE.Frobenius
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Chart
import TauCeti.Geometry.Manifold.Riemannian.Isometry.ConformalCurvature
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Local solutions of the conformal flattening equation

Let `g` be a smooth Riemannian metric on a smooth manifold `M` modelled on a finite-dimensional real
normed space `E`. In dimension at least `3`, the metric `e^(2φ) g` has vanishing Schouten tensor
exactly when `φ` solves the *conformal flattening equation*

`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`,

with `P` the Schouten tensor of `g`
(`Bundle.ContMDiffRiemannianMetric.schoutenTensor_leviCivitaConnection_rescale_eq_zero_iff`).
This file proves that at an interior point `x₀` where the Weyl and Cotton tensors of `g` vanish
nearby, the equation is locally solvable through every initial jet `(φ x₀, grad φ x₀)` with smooth
joint dependence on the initial jet and the point: around every `(c₀, ξ₀)` there is a smooth family
`Φ : (ℝ × TangentSpace I x₀) × M → ℝ` whose slices `Φ (p, ·)` solve the equation on a fixed open
neighbourhood of `x₀` with `Φ (p, x₀) = p.1` and `mgradient I (Φ (p, ·)) x₀ = p.2` for all `p` near
`(c₀, ξ₀)`. In particular, for each prescribed `c` and `ξ` there is a smooth solution near `x₀` with
`φ x₀ = c` and `mgradient I φ x₀ = ξ`. This is a converse of
`TauCeti.Manifold.weylTensor_eq_zero_of_forall_exists_eventually_hessian_eq` and
`TauCeti.Manifold.cottonTensor_eq_zero_of_eventually_hessian_eq`, and the analytic step in the
proof that a metric with vanishing Weyl tensor (dimension at least `4`) or vanishing Cotton tensor
(dimension `3`) is locally conformally flat.

On the model space `E`, writing `α = dφ` in linear coordinates turns the equation into the
first-order total differential equation `D(φ, α)(u) = (α u, v ↦ α(Γ(u, v)) + Φ_α(u, v))` on
`E × (ℝ × E*)`, where `Γ` are the Christoffel symbols of `g`
(`TauCeti.Manifold.christoffelSecondKind`) and `Φ_α` is the right side of the equation. Its
Frobenius integrability condition is checked without computing curvature in coordinates: at a point
`(y, c, α)`, a quadratic function with this value, differential and prescribed second derivative
solves the equation at `y`, and along such a function the antisymmetrized derivative of the defect
of the equation is `-(C(X, Y, Z) + W(Z, Y, X, grad φ))`
(`TauCeti.Manifold.mvfderiv_hessian_sub_conformalFlatteningForm_sub_swap`), which vanishes. The
local Frobenius theorem `TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt`
produces the smooth solution family on `E`, and chartwise model-space metric realization
(`TauCeti.exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint`) together with naturality
of the Weyl tensor, Cotton tensor, gradient and conformal flattening equation under local isometries
(`TauCeti.IsLocalRiemannianIsometry`) transfers the family to any interior point of a manifold.

## Main results

* `TauCeti.Manifold.exists_contMDiff_hessian_eq_conformalFlatteningForm_model_space` and
  `TauCeti.Manifold.exists_eventually_hessian_eq_model_space`: smooth-family and single-jet local
  solvability on a model space `E`.
* `TauCeti.Manifold.exists_contMDiff_hessian_eq_conformalFlatteningForm_of_isInteriorPoint` and
  `TauCeti.Manifold.exists_eventually_hessian_eq_of_isInteriorPoint`: smooth-family and single-jet
  local solvability near an interior point of a Riemannian manifold.
* `TauCeti.Manifold.exists_contMDiff_hessian_eq_conformalFlatteningForm` and
  `TauCeti.Manifold.exists_eventually_hessian_eq`: specializations to boundaryless manifolds.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G (the Weyl–Schouten theorem).
* L. P. Eisenhart, *Riemannian Geometry*, Princeton Univ. Press (1926), Sections 28–29.
* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press (1969), Section 10.9 (the
  Frobenius theorem for total differential equations).
-/

public section

open Bundle Filter Set TopologicalSpace
open scoped ContDiff Manifold InnerProductSpace Topology TauCeti

noncomputable section

namespace TauCeti.Manifold

/-! ### The conformal flattening system on a model space -/

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]

local notation "lc" => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E

variable (E) in
/-- The Riemannian metric of the model space, read as a field of bilinear forms on `E`. -/
private def metricCoeff (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (RiemannianBundle.g (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)).inner y

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
private theorem inner_eq_metricCoeff (y : E) (v w : TangentSpace 𝓘(ℝ, E) y) :
    ⟪v, w⟫_ℝ = metricCoeff E y (tangentSpaceCastModel 𝓘(ℝ, E) y v)
      (tangentSpaceCastModel 𝓘(ℝ, E) y w) :=
  rfl

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
private theorem metricCoeff_comm (y u v : E) : metricCoeff E y u v = metricCoeff E y v u :=
  real_inner_comm ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm v)
    ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm u)

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
private theorem metricCoeff_self_pos (y : E) {v : E} (hv : v ≠ 0) : 0 < metricCoeff E y v v :=
  (real_inner_self_pos.2 (by simpa using hv)).trans_eq
    ((inner_eq_metricCoeff y ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm v) _).trans (by simp))

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
private theorem isInvertible_metricCoeff (y : E) : (metricCoeff E y).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_pos fun _ ↦ metricCoeff_self_pos y

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
private theorem nondegenerate_metricCoeff (y : E) :
    (metricCoeff E y).toBilinForm.Nondegenerate := by
  have hsep : (metricCoeff E y).toBilinForm.SeparatingLeft := fun a ha ↦ by
    by_contra h
    exact (metricCoeff_self_pos y h).ne' (ha a)
  exact LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (ContinuousLinearMap.isSymm_toBilinForm_iff.2 (metricCoeff_comm y)).isRefl |>.2 hsep

private theorem contDiff_metricCoeff : ContDiff ℝ ∞ (metricCoeff E) := by
  refine contDiff_clm_apply_iff.2 fun a ↦ contDiff_clm_apply_iff.2 fun b ↦ ?_
  let C (a : E) (y : E) : TangentSpace 𝓘(ℝ, E) y := (tangentSpaceCastModel 𝓘(ℝ, E) y).symm a
  have hC (a : E) : CMDiff ∞ (T% (C a)) :=
    (contMDiff_vectorSpace_iff_contDiff (n := ∞)).2 contDiff_const
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun y ↦ ⟪C a y, C b y⟫_ℝ) :=
    ContMDiff.inner_bundle (IB := 𝓘(ℝ, E)) (F := E) (E := fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)
      (b := id) (hC a) (hC b)
  exact contMDiff_iff_contDiff.1 h

variable (E) in
/-- The Schouten tensor of the model space, read as a field of bilinear forms on `E`. -/
private def schoutenCoeff (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((lc).schoutenTensor y : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).toContinuousBilinearMap

private theorem schoutenCoeff_apply (y u v : E) :
    schoutenCoeff E y u v = (lc).schoutenTensor y ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm u)
      ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm v) :=
  rfl

private theorem schoutenCoeff_comm (y u v : E) :
    schoutenCoeff E y u v = schoutenCoeff E y v u := by
  rw [schoutenCoeff_apply, schoutenCoeff_apply]
  simpa only [RingHom.id_apply] using
    ((CovariantDerivative.IsMetricCompatible.schoutenTensor_isSymm (cov := lc)
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := 𝓘(ℝ, E)) (M := E))
      (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, E)) y).eq
        ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm u) ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm v))

private theorem contDiff_schoutenCoeff : ContDiff ℝ ∞ (schoutenCoeff E) := by
  refine contDiff_clm_apply_iff.2 fun a ↦ contDiff_clm_apply_iff.2 fun b ↦ ?_
  let C (a : E) (y : E) : TangentSpace 𝓘(ℝ, E) y := (tangentSpaceCastModel 𝓘(ℝ, E) y).symm a
  have hC (a : E) : CMDiff ∞ (T% (C a)) :=
    (contMDiff_vectorSpace_iff_contDiff (n := ∞)).2 contDiff_const
  exact contMDiff_iff_contDiff.1 fun y ↦
    (lc).contMDiffAt_schoutenTensor_apply (hC a y) (hC b y)

local notation "Γ" => christoffelSecondKind (metricCoeff E)

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
private theorem christoffel_comm (y u v : E) : Γ y u v = Γ y v u :=
  christoffelSecondKind_comm (Eventually.of_forall fun z ↦
    ContinuousLinearMap.isSymm_toBilinForm_iff.2 (metricCoeff_comm z)) u v

private theorem contDiff_christoffel : ContDiff ℝ ∞ Γ :=
  contDiff_iff_contDiffAt.2 fun y ↦ contDiffAt_christoffelSecondKind
    contDiff_metricCoeff.contDiffAt (by simp) (nondegenerate_metricCoeff y)

variable (E) in
/-- The conformal flattening equation `Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` in linear coordinates,
as a first-order total differential equation for the value and the differential `α` of `φ`:
`D(φ, α)(u) = (α u, v ↦ α(Γ(u, v)) + P(u, v) + α u α v - (α(g⁻¹ α) / 2) g(u, v))`. -/
private def flatteningField (p : E × ℝ × (E →L[ℝ] ℝ)) : E →L[ℝ] ℝ × (E →L[ℝ] ℝ) :=
  p.2.2.prod (ContinuousLinearMap.compL ℝ E E ℝ p.2.2 ∘L Γ p.1 + schoutenCoeff E p.1 +
    p.2.2.smulRight p.2.2 - (p.2.2 ((metricCoeff E p.1).inverse p.2.2) / 2) • metricCoeff E p.1)

private theorem flatteningField_apply_fst (p : E × ℝ × (E →L[ℝ] ℝ)) (u : E) :
    (flatteningField E p u).1 = p.2.2 u :=
  rfl

private theorem flatteningField_apply_snd (p : E × ℝ × (E →L[ℝ] ℝ)) (u v : E) :
    (flatteningField E p u).2 v = p.2.2 (Γ p.1 u v) + schoutenCoeff E p.1 u v +
      p.2.2 u * p.2.2 v -
        p.2.2 ((metricCoeff E p.1).inverse p.2.2) / 2 * metricCoeff E p.1 u v := by
  simp [flatteningField]

private theorem flatteningField_apply_snd_comm (p : E × ℝ × (E →L[ℝ] ℝ)) (u v : E) :
    (flatteningField E p u).2 v = (flatteningField E p v).2 u := by
  rw [flatteningField_apply_snd, flatteningField_apply_snd, christoffel_comm, schoutenCoeff_comm,
    metricCoeff_comm p.1 u v]
  ring

private theorem contDiff_flatteningField : ContDiff ℝ ∞ (flatteningField E) := by
  have hα : ContDiff ℝ ∞ fun p : E × ℝ × (E →L[ℝ] ℝ) ↦ p.2.2 := contDiff_snd.snd
  have hg : ContDiff ℝ ∞ fun p : E × ℝ × (E →L[ℝ] ℝ) ↦ metricCoeff E p.1 :=
    contDiff_metricCoeff.comp contDiff_fst
  have hgα : ContDiff ℝ ∞ fun p : E × ℝ × (E →L[ℝ] ℝ) ↦ (metricCoeff E p.1).inverse p.2.2 :=
    ContDiff.clm_apply (f := fun p ↦ (metricCoeff E p.1).inverse) (contDiff_iff_contDiffAt.2 fun p ↦
      (isInvertible_metricCoeff p.1).contDiffAt_map_inverse.comp p hg.contDiffAt) hα
  have hsnd (u v : E) : ContDiff ℝ ∞ fun p ↦ (flatteningField E p u).2 v := by
    simp only [flatteningField_apply_snd]
    exact (((hα.clm_apply (((contDiff_christoffel.comp contDiff_fst).clm_apply
      contDiff_const).clm_apply contDiff_const)).add (((contDiff_schoutenCoeff.comp
        contDiff_fst).clm_apply contDiff_const).clm_apply contDiff_const)).add
      ((hα.clm_apply contDiff_const).mul (hα.clm_apply contDiff_const))).sub
      (((hα.clm_apply hgα).div_const 2).mul
        ((hg.clm_apply contDiff_const).clm_apply contDiff_const))
  refine contDiff_clm_apply_iff.2 fun u ↦ ?_
  exact (hα.clm_apply contDiff_const).prodMk (contDiff_clm_apply_iff.2 (hsnd u))

/-- In linear coordinates, the defect `Hess φ - Φ_(grad φ)` of the conformal flattening equation
is `D²φ - f(y, φ y, Dφ y)`, the defect of the coordinate system. -/
private theorem hessian_sub_conformalFlatteningForm_model_space {φ : E → ℝ} {y : E}
    (hφ : ContDiffAt ℝ 2 φ y) (u v : E) :
    hessian 𝓘(ℝ, E) φ y ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm u)
        ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm v) -
      (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y)
        ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm u) ((tangentSpaceCastModel 𝓘(ℝ, E) y).symm v) =
      fderiv ℝ (fderiv ℝ φ) y u v - (flatteningField E (y, φ y, fderiv ℝ φ y) u).2 v := by
  rw [hessian_model_space_eq_fderiv_sub_christoffelSecondKind inner_eq_metricCoeff hφ,
    CovariantDerivative.conformalFlatteningForm_apply, flatteningField_apply_snd,
    inner_mgradient_model_space, inner_mgradient_model_space,
    norm_mgradient_sq_model_space (inner_eq_metricCoeff y),
    ← schoutenCoeff_apply, inner_eq_metricCoeff]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  ring

/-- Where the Weyl and Cotton tensors vanish, the coordinate conformal flattening system satisfies
the Frobenius integrability condition at every value and differential. -/
private theorem isFrobeniusIntegrableAt_flatteningField {y : E} (hW : (lc).weylTensor y = 0)
    (hC : (lc).cottonTensor y = 0) (q : ℝ × (E →L[ℝ] ℝ)) :
    IsFrobeniusIntegrableAt (flatteningField E) (y, q) := by
  set p : E × ℝ × (E →L[ℝ] ℝ) := (y, q)
  -- Test the condition along a quadratic function solving the equation at `y`.
  let B : E →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ (E →L[ℝ] ℝ) ∘L flatteningField E p
  obtain ⟨φ, hφ, hφy, hDφ, hD2φ⟩ :=
    exists_contDiff_apply_eq_fderiv_eq_fderiv_fderiv_eq y q.1 q.2 B
      (flatteningField_apply_snd_comm p)
  have hφ2 (z : E) : ContDiffAt ℝ 2 φ z := hφ.contDiffAt.of_le (by simp)
  refine isFrobeniusIntegrableAt_of_fderiv_apply_snd_comm flatteningField_apply_fst
    flatteningField_apply_snd_comm (hφ2 y) hφy hDφ (fun u v ↦ by simp [hD2φ, B, p]) fun u v w ↦ ?_
  -- Along `φ`, the coordinate system is `B` minus the defect of the equation.
  let C (a : E) (z : E) : TangentSpace 𝓘(ℝ, E) z := (tangentSpaceCastModel 𝓘(ℝ, E) z).symm a
  have hCs (a : E) : CMDiff ∞ (T% (C a)) :=
    (contMDiff_vectorSpace_iff_contDiff (n := ∞)).2 contDiff_const
  have hdefect (a b : E) : (fun z ↦ (flatteningField E (z, φ z, fderiv ℝ φ z) a).2 b) =
      fun z ↦ B a b - (hessian 𝓘(ℝ, E) φ z (C a z) (C b z) -
        (lc).conformalFlatteningForm z (mgradient 𝓘(ℝ, E) φ z) (C a z) (C b z)) := by
    funext z
    rw [hessian_sub_conformalFlatteningForm_model_space (hφ2 z), hD2φ]
    ring
  have hHy (a b : TangentSpace 𝓘(ℝ, E) y) : hessian 𝓘(ℝ, E) φ y a b =
      (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y) a b := by
    have h := hessian_sub_conformalFlatteningForm_model_space (hφ2 y)
      (tangentSpaceCastModel 𝓘(ℝ, E) y a) (tangentSpaceCastModel 𝓘(ℝ, E) y b)
    rw [hφy, hDφ, hD2φ] at h
    -- The second derivative of `φ` at `y` is the coordinate system at `(y, q) = p`.
    have h0 : B (tangentSpaceCastModel 𝓘(ℝ, E) y a) (tangentSpaceCastModel 𝓘(ℝ, E) y b) -
        (flatteningField E (y, q.1, q.2) (tangentSpaceCastModel 𝓘(ℝ, E) y a)).2
          (tangentSpaceCastModel 𝓘(ℝ, E) y b) = 0 :=
      sub_eq_zero.2 (by simp [B, p])
    rw [h0] at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, sub_eq_zero] using h
  -- The invariant integrability identity, on the constant fields `C u`, `C v` and `C w`.
  have h := mvfderiv_hessian_sub_conformalFlatteningForm_sub_swap
    (contMDiff_iff_contDiff.2 hφ) hHy (hCs u) (hCs v) (hCs w)
  rw [hW, hC] at h
  simp only [mvfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_coe, C,
    ContinuousLinearEquiv.apply_symm_apply, LinearMap.zero_apply, add_zero, neg_zero] at h
  rw [hdefect, hdefect, fderiv_const_sub, fderiv_const_sub]
  simp only [neg_apply, neg_inj]
  exact sub_eq_zero.1 h

/-- **A smooth solution family of the flattening system around a prescribed jet.** Where the Weyl
and Cotton tensors vanish near `x₀`, the coordinate conformal flattening system admits, around every
initial value `q₀`, an open product neighbourhood `V ×ˢ Q` of `(x₀, q₀)` and a smooth family `s`
satisfying `s (x₀, q) = q` for `q ∈ Q` and solving the total differential equation in `x ∈ V`. -/
private theorem exists_contDiffOn_hasFDerivAt_flatteningField_family {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (q₀ : ℝ × (E →L[ℝ] ℝ)) :
    ∃ (s : E × (ℝ × (E →L[ℝ] ℝ)) → ℝ × (E →L[ℝ] ℝ)) (V : Set E)
      (Q : Set (ℝ × (E →L[ℝ] ℝ))),
      IsOpen V ∧ x₀ ∈ V ∧ IsOpen Q ∧ q₀ ∈ Q ∧ ContDiffOn ℝ ∞ s (V ×ˢ Q) ∧
      (∀ q ∈ Q, s (x₀, q) = q) ∧
      ∀ x ∈ V, ∀ q ∈ Q, HasFDerivAt (fun z ↦ s (z, q)) (flatteningField E (x, s (x, q))) x := by
  have hint : ∀ᶠ p in 𝓝 (x₀, q₀), IsFrobeniusIntegrableAt (flatteningField E) p :=
    ((continuous_fst.tendsto (x₀, q₀)).eventually (hW.and hC)).mono fun p hp ↦
      isFrobeniusIntegrableAt_flatteningField hp.1 hp.2 p.2
  obtain ⟨s, U, hU, hx₀U, hs, -, hsinit, hsol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt (n := ⊤)
      (contDiff_flatteningField.contDiffOn (s := univ) |>.of_le (by simp)) univ_mem hint
  obtain ⟨V, Q, hV, hQ, hx₀V, hq₀Q, hVQ⟩ := isOpen_prod_iff.1 hU x₀ q₀ hx₀U
  exact ⟨s, V, Q, hV, hx₀V, hQ, hq₀Q, (hs.mono hVQ).of_le (by simp),
    fun q hq ↦ hsinit q (hVQ ⟨hx₀V, hq⟩), fun x hx q hq ↦ hsol (x, q) (hVQ ⟨hx, hq⟩)⟩

/-- Any smooth function `φ` locally agreeing with the first component of a solution `σ` of
`flatteningField E` on an open set `V` has differential `σ.2` and solves the conformal flattening
equation on `V`. -/
private theorem hessian_eq_of_eventuallyEq_flatteningField {V : Set E} (hV : IsOpen V)
    {σ : E → ℝ × (E →L[ℝ] ℝ)}
    (hσsol : ∀ x ∈ V, HasFDerivAt σ (flatteningField E (x, σ x)) x)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {y : E} (hyV : y ∈ V)
    (hφσ : ∀ z ∈ V, φ z = (σ z).1) :
    fderiv ℝ φ y = (σ y).2 ∧
      ∀ u v : TangentSpace 𝓘(ℝ, E) y, hessian 𝓘(ℝ, E) φ y u v =
        (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y) u v := by
  have hDφ (x : E) (hx : x ∈ V) : fderiv ℝ φ x = (σ x).2 := by
    have heq : (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)).comp (flatteningField E (x, σ x)) =
        (σ x).2 :=
      ContinuousLinearMap.ext fun u ↦ flatteningField_apply_fst (x, σ x) u
    have h := (hσsol x hx).fst
    rw [heq] at h
    exact (EventuallyEq.fderiv_eq (eventually_of_mem (hV.mem_nhds hx) hφσ)).trans h.fderiv
  refine ⟨hDφ y hyV, fun u v ↦ ?_⟩
  have hD2φ (a b : E) : fderiv ℝ (fderiv ℝ φ) y a b = (flatteningField E (y, σ y) a).2 b := by
    rw [EventuallyEq.fderiv_eq (eventually_of_mem (hV.mem_nhds hyV) hDφ),
      (hσsol y hyV).snd.fderiv]
    simp
  have h := hessian_sub_conformalFlatteningForm_model_space
    (hφ.contDiffAt.of_le (by simp) : ContDiffAt ℝ 2 φ y)
    (tangentSpaceCastModel 𝓘(ℝ, E) y u) (tangentSpaceCastModel 𝓘(ℝ, E) y v)
  have hjet : (y, φ y, fderiv ℝ φ y) = (y, σ y) := by rw [hφσ y hyV, hDφ y hyV]
  rw [hD2φ, hjet, sub_self] at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply, sub_eq_zero] using h

/-- **Smooth-family local solutions of the conformal flattening equation on a model space.** Let `g`
be a smooth Riemannian metric on a finite-dimensional real normed space `E` whose Weyl and Cotton
tensors vanish near `x₀`. Around every initial jet `(c₀, ξ₀) : ℝ × TangentSpace 𝓘(ℝ, E) x₀`, there
exist open neighbourhoods `Ω` of `(c₀, ξ₀)` and `V` of `x₀` and a jointly smooth function
`Φ : (ℝ × TangentSpace 𝓘(ℝ, E) x₀) × E → ℝ` such that for every `(c, ξ) ∈ Ω`, the slice
`x ↦ Φ ((c, ξ), x)` has value `c` and gradient `ξ` at `x₀` and solves the conformal flattening
equation on `V`. -/
theorem exists_contMDiff_hessian_eq_conformalFlatteningForm_model_space {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace 𝓘(ℝ, E) x₀) :
    ∃ (Φ : (ℝ × TangentSpace 𝓘(ℝ, E) x₀) × E → ℝ)
      (Ω : Set (ℝ × TangentSpace 𝓘(ℝ, E) x₀)) (V : Set E),
      IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧ IsOpen V ∧ x₀ ∈ V ∧
      ContMDiff (𝓘(ℝ, ℝ × TangentSpace 𝓘(ℝ, E) x₀).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞ Φ ∧
      ∀ p ∈ Ω, Φ (p, x₀) = p.1 ∧
        mgradient 𝓘(ℝ, E) (fun x ↦ Φ (p, x)) x₀ = p.2 ∧
        ∀ y ∈ V, ∀ u v : TangentSpace 𝓘(ℝ, E) y,
          hessian 𝓘(ℝ, E) (fun x ↦ Φ (p, x)) y u v =
            (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) (fun x ↦ Φ (p, x)) y) u v := by
  let J₀ : (ℝ × TangentSpace 𝓘(ℝ, E) x₀) →L[ℝ] ℝ × (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap
      ((metricCoeff E x₀).comp (tangentSpaceCastModel 𝓘(ℝ, E) x₀).toContinuousLinearMap)
  obtain ⟨s, V₀, Q, hV₀, hx₀V₀, hQ, hq₀Q, hs, hsinit, hsol⟩ :=
    exists_contDiffOn_hasFDerivAt_flatteningField_family hW hC (J₀ (c₀, ξ₀))
  have hΩ₀ : IsOpen (J₀ ⁻¹' Q) := hQ.preimage J₀.continuous
  let ψ₀ : (ℝ × TangentSpace 𝓘(ℝ, E) x₀) × E → ℝ := fun z ↦ (s (z.2, J₀ z.1)).1
  have hψ₀ : ContDiffOn ℝ ∞ ψ₀ ((J₀ ⁻¹' Q) ×ˢ V₀) :=
    contDiff_fst.contDiffOn.comp
      (hs.comp (contDiffOn_snd.prodMk (J₀.contDiff.contDiffOn.comp contDiffOn_fst
        (mapsTo_univ _ _))) fun _ hz ↦ ⟨hz.2, hz.1⟩) (mapsTo_univ _ _)
  obtain ⟨χ, hχ, -, hχ₁, -, hχsub⟩ :=
    (isCompact_singleton (x := ((c₀, ξ₀), x₀))).exists_contDiff_cutoff_eventuallyEq_one
      (hΩ₀.prod hV₀) (singleton_subset_iff.2 ⟨hq₀Q, hx₀V₀⟩)
  let Φ : (ℝ × TangentSpace 𝓘(ℝ, E) x₀) × E → ℝ := fun z ↦ χ z • ψ₀ z
  have hΦ : ContDiff ℝ ∞ Φ := hψ₀.contDiff_smul_of_tsupport_subset (hΩ₀.prod hV₀) hχ.contDiffOn
    hχsub
  have hΦm : ContMDiff (𝓘(ℝ, ℝ × TangentSpace 𝓘(ℝ, E) x₀).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞ Φ := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiff_iff_contDiff.2 hΦ
  obtain ⟨Ω, V, hΩ, hV, hp₀Ω, hx₀V, hΩV⟩ := isOpen_prod_iff.1
    (isOpen_interior.inter (hΩ₀.prod hV₀)) (c₀, ξ₀) x₀
    ⟨mem_interior_iff_mem_nhds.2 (hχ₁ _ rfl), hq₀Q, hx₀V₀⟩
  refine ⟨Φ, Ω, V, hΩ, hp₀Ω, hV, hx₀V, hΦm, fun p hp ↦ ?_⟩
  have hpQ : J₀ p ∈ Q := (hΩV (mk_mem_prod hp hx₀V)).2.1
  have hV_sub : V ⊆ V₀ := fun y hy ↦ (hΩV (mk_mem_prod hp hy)).2.2
  have hΦ_eq (y : E) (hy : y ∈ V) : Φ (p, y) = (s (y, J₀ p)).1 := by
    have h1 : χ (p, y) = 1 := interior_subset (hΩV (mk_mem_prod hp hy)).1
    simp [Φ, ψ₀, h1]
  have hφp : ContDiff ℝ ∞ (fun x ↦ Φ (p, x)) := hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hx₀sol := hessian_eq_of_eventuallyEq_flatteningField hV
    (fun x hx ↦ hsol x (hV_sub hx) (J₀ p) hpQ) hφp hx₀V hΦ_eq
  refine ⟨by rw [hΦ_eq x₀ hx₀V, hsinit (J₀ p) hpQ]; rfl, ?_, fun y hy ↦
    (hessian_eq_of_eventuallyEq_flatteningField hV (fun x hx ↦ hsol x (hV_sub hx) (J₀ p) hpQ)
      hφp hy hΦ_eq).2⟩
  refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
  rw [mvfderiv_eq_fderiv, hx₀sol.1, hsinit (J₀ p) hpQ]
  simp [J₀, inner_eq_metricCoeff, NormedSpace.fromTangentSpace]

/-- **Local solutions of the conformal flattening equation on a model space.** Let `g` be a smooth
Riemannian metric on a finite-dimensional real normed space `E` whose Weyl and Cotton tensors vanish
near `x₀`. Then for every `c : ℝ` and every tangent vector `ξ` at `x₀` there is a smooth function
`φ` with `φ x₀ = c` and `grad φ x₀ = ξ` solving the conformal flattening equation
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` near `x₀`, where `P` is the Schouten tensor. -/
theorem exists_eventually_hessian_eq_model_space {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace 𝓘(ℝ, E) x₀) :
    ∃ φ : E → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient 𝓘(ℝ, E) φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace 𝓘(ℝ, E) y, hessian 𝓘(ℝ, E) φ y u v =
        (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y) u v := by
  obtain ⟨Φ, Ω, V, -, hpΩ, hV, hx₀V, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_conformalFlatteningForm_model_space hW hC c ξ
  obtain ⟨hval, hgrad, hhess⟩ := hsol (c, ξ) hpΩ
  exact ⟨fun x ↦ Φ ((c, ξ), x), hΦ.comp (contMDiff_const.prodMk contMDiff_id), hval, hgrad,
    eventually_of_mem (hV.mem_nhds hx₀V) hhess⟩

end ModelSpace

/-! ### Local solutions of the conformal flattening equation on a manifold -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Realize `M` near an interior point `x₀` where `W = 0` and `C = 0` as an open chart
neighbourhood `W` with a local Riemannian isometry `f : W → (E, gE)` realizing `extChartAt I x₀`
such that `gE` also has vanishing Weyl and Cotton tensors near `extChartAt I x₀ x₀`. -/
private theorem exists_model_space_isometry_weyl_cotton_zero {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0) :
    ∃ (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z))
      (W : Opens M) (_ : x₀ ∈ W),
      (W : Set M) ⊆ (extChartAt I x₀).source ∧
      letI : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
      ∃ f : W → E, IsLocalRiemannianIsometry I 𝓘(ℝ, E) f ∧
        (∀ y : W, f y = extChartAt I x₀ y.1) ∧
        (∀ᶠ z in 𝓝 (extChartAt I x₀ x₀),
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).weylTensor z = 0) ∧
        ∀ᶠ z in 𝓝 (extChartAt I x₀ x₀),
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).cottonTensor z = 0 := by
  obtain ⟨U_WC, hU_WC, hU_open, hx₀U⟩ := eventually_nhds_iff.1 (hW.and hC)
  obtain ⟨gE, r, hr, W, hx₀W, hWU, -, hW_eq, Ψ, hΨ, -⟩ :=
    TauCeti.exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint hx₀
      (hU_open.mem_nhds hx₀U)
  let B : Opens E := ⟨Metric.ball (extChartAt I x₀ x₀) r, Metric.isOpen_ball⟩
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : B ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨(gE.restrictOpenTangentSpace B).toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : B ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨(gE.restrictOpenTangentSpace B).inner, (gE.restrictOpenTangentSpace B).contMDiff,
      fun _ _ _ ↦ rfl⟩
  have hιW := IsLocalRiemannianIsometry.subtype_val (I := I) W
  have hιB := gE.isLocalRiemannianIsometry_restrictOpenTangentSpace B
  have hf : IsLocalRiemannianIsometry I 𝓘(ℝ, E) ((Subtype.val : B → E) ∘ Ψ) :=
    hιB.comp Ψ.isLocalRiemannianIsometry
  have hfinv : IsLocalRiemannianIsometry 𝓘(ℝ, E) I ((Subtype.val : W → M) ∘ Ψ.symm) :=
    hιW.comp Ψ.symm.isLocalRiemannianIsometry
  refine ⟨gE, W, hx₀W, hW_eq.trans_subset Set.inter_subset_left, (Subtype.val : B → E) ∘ Ψ, hf,
    hΨ, ?_, ?_⟩
  · refine eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz ↦ ?_
    let zb : B := ⟨z, hz⟩
    exact (hιB.weylTensor_eq_zero_iff zb).2 <| (hfinv.weylTensor_eq_zero_iff zb).1 <|
      (hU_WC _ (hWU (Ψ.symm zb).2)).1
  · refine eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz ↦ ?_
    let zb : B := ⟨z, hz⟩
    exact (hιB.cottonTensor_eq_zero_iff zb).2 <| (hfinv.cottonTensor_eq_zero_iff zb).1 <|
      (hU_WC _ (hWU (Ψ.symm zb).2)).2

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Extend a smooth model-space family `ΦE` pulled back by `extChartAt I x₀` to all of `P × M`
using a smooth bump function `χ` supported inside `(extChartAt I x₀).source`. -/
private theorem contMDiff_bump_mul_comp_extChartAt
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {x₀ : M} (χ : SmoothBumpFunction I x₀)
    (hχ_src : tsupport χ ⊆ (extChartAt I x₀).source) (J : P →L[ℝ] Q)
    {ΦE : Q × E → ℝ} (hΦE : ContMDiff (𝓘(ℝ, Q).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞ ΦE) :
    ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ) ∞
      (fun q : P × M ↦ χ q.2 * ΦE (J q.1, extChartAt I x₀ q.2)) := by
  intro q
  by_cases hq : q.2 ∈ tsupport χ
  · have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x₀) q.2 :=
      contMDiffAt_extChartAt' (extChartAt_source I x₀ ▸ hχ_src hq)
    have harg : ContMDiffAt (𝓘(ℝ, P).prod I) (𝓘(ℝ, Q).prod 𝓘(ℝ, E)) ∞
        (fun q' : P × M ↦ (J q'.1, extChartAt I x₀ q'.2)) q :=
      (J.contDiff.contMDiff.comp contMDiff_fst).contMDiffAt.prodMk
        (hchart.comp q contMDiff_snd.contMDiffAt)
    exact (χ.contMDiff.comp contMDiff_snd).contMDiffAt.mul (hΦE.contMDiffAt.comp q harg)
  · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds univ_mem ((isClosed_tsupport χ).isOpen_compl.mem_nhds hq)]
      with q' hq'
    rw [image_eq_zero_of_notMem_tsupport hq'.2, zero_mul]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Transport the basepoint gradient along an open-submanifold chart isometry `f : W → E`. -/
private theorem mgradient_eq_of_comp_subtype_eq {W W' : Opens M} (hW'_W : (W' : Set M) ⊆ W)
    {x₀ : M} (hx₀W : x₀ ∈ W) (hx₀W' : x₀ ∈ W')
    {gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)}
    {f : W → E}
    (hf : letI : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩;
      IsLocalRiemannianIsometry I 𝓘(ℝ, E) f)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {φE : E → ℝ} (hφE : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φE)
    (hcomp_eq : φ ∘ (Subtype.val : W' → M) = φE ∘ (f ∘ fun y : W' ↦ ⟨y.1, hW'_W y.2⟩))
    {ξ : TangentSpace I x₀}
    (hgradE : (letI : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) :=
        ⟨gE.toRiemannianMetric⟩;
      mgradient 𝓘(ℝ, E) φE (f ⟨x₀, hx₀W⟩)) =
      (mfderiv I 𝓘(ℝ, E) f ⟨x₀, hx₀W⟩) ((tangentSpaceOpenEquiv (I := I) ⟨x₀, hx₀W⟩).symm ξ)) :
    mgradient I φ x₀ = ξ := by
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  let w₀ : W := ⟨x₀, hx₀W⟩
  let y₀ : W' := ⟨x₀, hx₀W'⟩
  have hιW' := IsLocalRiemannianIsometry.subtype_val (I := I) W'
  have hinc := IsLocalRiemannianIsometry.inclusion (I := I) hW'_W
  have hf' : IsLocalRiemannianIsometry I 𝓘(ℝ, E) (f ∘ fun y : W' ↦ (⟨y.1, hW'_W y.2⟩ : W)) :=
    hf.comp hinc
  have h1 := hιW'.mfderiv_mgradient_comp (x := y₀) (hφ.contMDiffAt.mdifferentiableAt (by simp))
  have h2 := hf'.mfderiv_mgradient_comp (x := y₀) (hφE.contMDiffAt.mdifferentiableAt (by simp))
  rw [hcomp_eq] at h1
  have hsub (v : TangentSpace I y₀) :
      mfderiv I I (fun y : W' ↦ (⟨y.1, hW'_W y.2⟩ : W)) y₀ v =
        (tangentSpaceOpenEquiv (I := I) w₀).symm (mfderiv I I (Subtype.val : W' → M) y₀ v) := by
    apply (tangentSpaceOpenEquiv (I := I) w₀).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ← ContinuousLinearEquiv.coe_coe,
      ← mfderiv_subtype_val,
      ← mfderiv_comp_apply y₀ ((IsLocalRiemannianIsometry.subtype_val W).mdifferentiableAt w₀)
        (hinc.mdifferentiableAt y₀)]
    rfl
  rw [mfderiv_comp_apply y₀ (hf.mdifferentiableAt w₀) (hinc.mdifferentiableAt y₀), hsub, h1] at h2
  exact (hf.mfderiv_injective w₀).comp (ContinuousLinearEquiv.injective _) (h2.trans hgradE)

/-- Transport the conformal flattening equation from `E` to `M` along an open-submanifold chart
isometry `f : W → E`. -/
private theorem hessian_eq_conformalFlatteningForm_of_comp_subtype_eq
    [RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)]
    {W W' : Opens M} (hW'_W : (W' : Set M) ⊆ W) {f : W → E}
    (hf : IsLocalRiemannianIsometry I 𝓘(ℝ, E) f)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {φE : E → ℝ} (hφE : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φE)
    (hcomp_eq : φ ∘ (Subtype.val : W' → M) = φE ∘ (f ∘ fun y : W' ↦ ⟨y.1, hW'_W y.2⟩))
    {y : M} (hy : y ∈ W')
    (hhessE : ∀ u v : TangentSpace 𝓘(ℝ, E) (f ⟨y, hW'_W hy⟩),
      hessian 𝓘(ℝ, E) φE (f ⟨y, hW'_W hy⟩) u v =
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).conformalFlatteningForm
          (f ⟨y, hW'_W hy⟩) (mgradient 𝓘(ℝ, E) φE (f ⟨y, hW'_W hy⟩)) u v) :
    ∀ u v : TangentSpace I y, hessian I φ y u v =
      (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
        (mgradient I φ y) u v := by
  let y' : W' := ⟨y, hy⟩
  have hιW' := IsLocalRiemannianIsometry.subtype_val (I := I) W'
  have hf' : IsLocalRiemannianIsometry I 𝓘(ℝ, E) (f ∘ fun z : W' ↦ (⟨z.1, hW'_W z.2⟩ : W)) :=
    hf.comp (IsLocalRiemannianIsometry.inclusion (I := I) hW'_W)
  refine (hιW'.hessian_comp_eq_conformalFlatteningForm_iff (x := y')
    (hφ.contMDiffAt.of_le (by simp))).1 ?_
  rw [hcomp_eq]
  exact (hf'.hessian_comp_eq_conformalFlatteningForm_iff (x := y')
    (hφE.contMDiffAt.of_le (by simp))).2 hhessE

/-- **Smooth-family local solutions of the conformal flattening equation near an interior point.**
Let `M` be a smooth Riemannian manifold and `x₀` an interior point of `M` near which the Weyl and
Cotton tensors vanish. Around every initial jet `(c₀, ξ₀) : ℝ × TangentSpace I x₀`, there exist open
neighbourhoods `Ω` of `(c₀, ξ₀)` and `V` of `x₀` and a jointly smooth function
`Φ : (ℝ × TangentSpace I x₀) × M → ℝ` such that for every `(c, ξ) ∈ Ω`, the slice
`y ↦ Φ ((c, ξ), y)` has value `c` and gradient `ξ` at `x₀` and solves the conformal flattening
equation on `V`. -/
theorem exists_contMDiff_hessian_eq_conformalFlatteningForm_of_isInteriorPoint {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (Φ : (ℝ × TangentSpace I x₀) × M → ℝ)
      (Ω : Set (ℝ × TangentSpace I x₀)) (V : Set M),
      IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧ IsOpen V ∧ x₀ ∈ V ∧
      ContMDiff (𝓘(ℝ, ℝ × TangentSpace I x₀).prod I) 𝓘(ℝ) ∞ Φ ∧
      ∀ p ∈ Ω, Φ (p, x₀) = p.1 ∧
        mgradient I (fun y ↦ Φ (p, y)) x₀ = p.2 ∧
        ∀ y ∈ V, ∀ u v : TangentSpace I y,
          hessian I (fun z ↦ Φ (p, z)) y u v =
            (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
              (mgradient I (fun z ↦ Φ (p, z)) y) u v := by
  obtain ⟨gE, W, hx₀W, hW_src, hex⟩ := exists_model_space_isometry_weyl_cotton_zero hx₀ hW hC
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨gE.inner, gE.contMDiff, fun _ _ _ ↦ rfl⟩
  rcases hex with ⟨f, hf, hf_eq, hWE, hCE⟩
  let w₀ : W := ⟨x₀, hx₀W⟩
  have hz₀ : f w₀ = extChartAt I x₀ x₀ := hf_eq w₀
  let L₀ : TangentSpace I x₀ →L[ℝ] TangentSpace 𝓘(ℝ, E) (f w₀) :=
    (mfderiv I 𝓘(ℝ, E) f w₀).comp (tangentSpaceOpenEquiv (I := I) w₀).symm.toContinuousLinearMap
  obtain ⟨ΦE, ΩE, VE, hΩE, hpΩE, hVE, hz₀VE, hΦE, hsolE⟩ :=
    exists_contMDiff_hessian_eq_conformalFlatteningForm_model_space (hz₀ ▸ hWE) (hz₀ ▸ hCE)
      c₀ (L₀ ξ₀)
  let J : (ℝ × TangentSpace I x₀) →L[ℝ] ℝ × TangentSpace 𝓘(ℝ, E) (f w₀) :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap L₀
  have hS_nhds : ((W : Set M) ∩ ((extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' VE)) ∈ 𝓝 x₀ :=
    (W.2.inter (isOpen_extChartAt_preimage' (I := I) x₀ hVE)).mem_nhds
      ⟨hx₀W, mem_extChartAt_source x₀, by simpa only [mem_preimage, ← hz₀] using hz₀VE⟩
  obtain ⟨χ, -, hχsub⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1 hS_nhds
  let Φ : (ℝ × TangentSpace I x₀) × M → ℝ := fun q ↦ χ q.2 * ΦE (J q.1, extChartAt I x₀ q.2)
  have hΦ : ContMDiff (𝓘(ℝ, ℝ × TangentSpace I x₀).prod I) 𝓘(ℝ) ∞ Φ :=
    contMDiff_bump_mul_comp_extChartAt χ (hχsub.trans (inter_subset_left.trans hW_src)) J hΦE
  let V : Set M := interior {y : M | χ y = 1}
  have hx₀V : x₀ ∈ V := mem_interior_iff_mem_nhds.2 χ.eventuallyEq_one
  have hV_sub : V ⊆ (W : Set M) ∩ ((extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' VE) :=
    (interior_subset.trans fun _ hy ↦
      subset_tsupport _ (Function.mem_support.2 (by rw [mem_ofPred.1 hy]; exact one_ne_zero))).trans
      hχsub
  let W' : Opens M := ⟨V, isOpen_interior⟩
  have hW'_W : (W' : Set M) ⊆ W := fun _ hy ↦ (hV_sub hy).1
  refine ⟨Φ, J ⁻¹' ΩE, V, hΩE.preimage J.continuous, hpΩE, isOpen_interior, hx₀V, hΦ, fun p hp ↦ ?_⟩
  obtain ⟨hvalE, hgradE, hhessE⟩ := hsolE (J p) hp
  let φ : M → ℝ := fun y ↦ Φ (p, y)
  let φE : E → ℝ := fun z ↦ ΦE (J p, z)
  have hφ : ContMDiff I 𝓘(ℝ) ∞ φ := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
  have hφE : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φE := hΦE.comp (contMDiff_const.prodMk contMDiff_id)
  have hcomp_eq : φ ∘ (Subtype.val : W' → M) = φE ∘ (f ∘ fun y : W' ↦ ⟨y.1, hW'_W y.2⟩) := by
    funext y
    have hχy : χ y.1 = 1 := interior_subset y.2
    simp [φ, φE, Φ, hχy, hf_eq]
  refine ⟨?_, mgradient_eq_of_comp_subtype_eq hW'_W hx₀W hx₀V hf hφ hφE hcomp_eq hgradE,
    fun y hy ↦ hessian_eq_conformalFlatteningForm_of_comp_subtype_eq hW'_W hf hφ hφE hcomp_eq hy
      (hhessE _ (by rw [hf_eq]; exact (hV_sub hy).2.2))⟩
  change χ x₀ * ΦE (J p, extChartAt I x₀ x₀) = p.1
  rw [interior_subset hx₀V, one_mul, ← hz₀, hvalE]
  rfl

/-- **Local solutions of the conformal flattening equation near an interior point.** Let `M` be a
smooth Riemannian manifold and `x₀` an interior point of `M` near which the Weyl and Cotton tensors
vanish. For every `c : ℝ` and every `ξ : TangentSpace I x₀` there is a smooth function `φ : M → ℝ`
with `φ x₀ = c` and `mgradient I φ x₀ = ξ` solving the conformal flattening equation near `x₀`. -/
theorem exists_eventually_hessian_eq_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v := by
  obtain ⟨Φ, Ω, V, -, hpΩ, hV, hx₀V, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_conformalFlatteningForm_of_isInteriorPoint hx₀ hW hC c ξ
  obtain ⟨hval, hgrad, hhess⟩ := hsol (c, ξ) hpΩ
  exact ⟨fun y ↦ Φ ((c, ξ), y), hΦ.comp (contMDiff_const.prodMk contMDiff_id), hval, hgrad,
    eventually_of_mem (hV.mem_nhds hx₀V) hhess⟩

/-- **Smooth-family local solutions of the conformal flattening equation on a boundaryless
manifold.** -/
theorem exists_contMDiff_hessian_eq_conformalFlatteningForm [BoundarylessManifold I M] {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (Φ : (ℝ × TangentSpace I x₀) × M → ℝ)
      (Ω : Set (ℝ × TangentSpace I x₀)) (V : Set M),
      IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧ IsOpen V ∧ x₀ ∈ V ∧
      ContMDiff (𝓘(ℝ, ℝ × TangentSpace I x₀).prod I) 𝓘(ℝ) ∞ Φ ∧
      ∀ p ∈ Ω, Φ (p, x₀) = p.1 ∧
        mgradient I (fun y ↦ Φ (p, y)) x₀ = p.2 ∧
        ∀ y ∈ V, ∀ u v : TangentSpace I y,
          hessian I (fun z ↦ Φ (p, z)) y u v =
            (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
              (mgradient I (fun z ↦ Φ (p, z)) y) u v :=
  exists_contMDiff_hessian_eq_conformalFlatteningForm_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hW hC c₀ ξ₀

/-- **Local solutions of the conformal flattening equation on a boundaryless manifold.** -/
theorem exists_eventually_hessian_eq [BoundarylessManifold I M] {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v :=
  exists_eventually_hessian_eq_of_isInteriorPoint BoundarylessManifold.isInteriorPoint hW hC c ξ

end Manifold

end TauCeti.Manifold
