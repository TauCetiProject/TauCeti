/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Integrability
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
import TauCeti.Analysis.ODE.Frobenius
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.Instances.OpenBall.Diffeomorph
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Isometry.ConformalCurvature
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Local solutions of the conformal flattening equation

Let `g` be a smooth Riemannian metric on a smooth manifold `M`. In dimension at least `3`, the
metric `e^(2φ) g` has vanishing Schouten tensor exactly when `φ` solves the *conformal flattening
equation*

`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`,

with `P` the Schouten tensor of `g`
(`Bundle.ContMDiffRiemannianMetric.schoutenTensor_leviCivitaConnection_rescale_eq_zero_iff`).
This file proves that at every interior point `x₀` near which the Weyl and Cotton tensors of `g`
vanish (hence at every point of a boundaryless manifold where `W = 0` and `C = 0` nearby), the
equation is locally solvable through any initial value `φ x₀ = c` and initial gradient
`grad φ x₀ = ξ`, with smooth joint dependence on the point and the initial data `(c, ξ)`. This is a
converse of `TauCeti.Manifold.weylTensor_eq_zero_of_forall_exists_eventually_hessian_eq` and
`TauCeti.Manifold.cottonTensor_eq_zero_of_eventually_hessian_eq`, and the analytic step in the
proof that a metric with vanishing Weyl tensor (dimension at least `4`) or vanishing Cotton tensor
(dimension `3`) is locally conformally flat.

On a model vector space `E`, writing `α = dφ` in linear coordinates turns the equation into the
first-order total differential equation `D(φ, α)(u) = (α u, v ↦ α(Γ(u, v)) + Φ_α(u, v))` on
`E × (ℝ × E*)`, where `Γ` are the Christoffel symbols of `g`
(`TauCeti.Manifold.christoffelSecondKind`) and `Φ_α` is the right side of the equation. Its
Frobenius integrability condition is checked without computing curvature in coordinates: at a point
`(y, c, α)`, a quadratic function with this value, differential and prescribed second derivative
solves the equation at `y`, and along such a function the antisymmetrized derivative of the defect
of the equation is `-(C(X, Y, Z) + W(Z, Y, X, grad φ))`
(`TauCeti.Manifold.mvfderiv_hessian_sub_conformalFlatteningForm_sub_swap`), which vanishes. The
local Frobenius theorem `TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt`
produces a smooth two-variable solution family, and smooth cutoffs make it globally smooth.

On a general smooth Riemannian manifold `M`, an interior point `x₀` has an open coordinate
neighbourhood inside `{W = 0 ∧ C = 0}` diffeomorphic to the whole model space `E`
(`TauCeti.exists_diffeomorph_opens_of_isInteriorPoint`). Pulling the restricted metric back to `E`
turns that diffeomorphism into a Riemannian isometry onto `(E, g_E)` whose Weyl and Cotton tensors
vanish everywhere, and naturality of the conformal flattening equation under local Riemannian
isometries (`TauCeti.IsLocalRiemannianIsometry.hessian_comp_eq_conformalFlatteningForm_iff`) carries
the model-space solution family back to `M`.

## Main results

* `TauCeti.Manifold.exists_contMDiff_hessian_eq_family_model_space` and
  `TauCeti.Manifold.exists_eventually_hessian_eq_model_space`: smooth initial-value families and
  individual solutions of the conformal flattening equation on a model vector space.
* `TauCeti.Manifold.exists_contMDiff_hessian_eq_family_of_isInteriorPoint` and
  `TauCeti.Manifold.exists_contMDiff_hessian_eq_family`: smooth initial-value families on a smooth
  Riemannian manifold (at an interior point, and on a boundaryless manifold).
* `TauCeti.Manifold.exists_eventually_hessian_eq_of_isInteriorPoint` and
  `TauCeti.Manifold.exists_eventually_hessian_eq`: local solutions with prescribed value and
  gradient on a smooth Riemannian manifold.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G (the Weyl–Schouten theorem).
* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press (1969), Section 10.9 (the
  Frobenius theorem for total differential equations).
-/

public section

open Filter Set TopologicalSpace
open scoped ContDiff Manifold InnerProductSpace Topology TauCeti

noncomputable section

namespace TauCeti.Manifold

open Bundle

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

/-- **A smooth solution family of the flattening system near an initial jet.** Where the Weyl and
Cotton tensors vanish near `x₀`, the coordinate conformal flattening system has, near any initial
jet `q₀`, a smooth two-variable solution `s` on an open product neighbourhood `V ×ˢ Q'` of
`(x₀, q₀)` with `s (x₀, q) = q`. -/
private theorem exists_contDiffOn_hasFDerivAt_flatteningField_family {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (q₀ : ℝ × (E →L[ℝ] ℝ)) :
    ∃ (s : (E × ℝ × (E →L[ℝ] ℝ)) → ℝ × (E →L[ℝ] ℝ)) (V : Set E)
      (Q' : Set (ℝ × (E →L[ℝ] ℝ))),
      IsOpen V ∧ x₀ ∈ V ∧ IsOpen Q' ∧ q₀ ∈ Q' ∧ ContDiffOn ℝ ∞ s (V ×ˢ Q') ∧
      (∀ q ∈ Q', s (x₀, q) = q) ∧
      ∀ x ∈ V, ∀ q ∈ Q', HasFDerivAt (fun y ↦ s (y, q)) (flatteningField E (x, s (x, q))) x := by
  have hint : ∀ᶠ p in 𝓝 (x₀, q₀), IsFrobeniusIntegrableAt (flatteningField E) p :=
    ((continuous_fst.tendsto (x₀, q₀)).eventually (hW.and hC)).mono fun p hp ↦
      isFrobeniusIntegrableAt_flatteningField hp.1 hp.2 p.2
  obtain ⟨s, U, hU, hx₀U, hs, -, hs₀, hsol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt (n := ⊤)
      (contDiff_flatteningField.contDiffOn (s := univ) |>.of_le (by simp)) univ_mem hint
  obtain ⟨V, Q', hV, hQ', hx₀V, hq₀Q', hsub⟩ := isOpen_prod_iff.1 hU x₀ q₀ hx₀U
  exact ⟨s, V, Q', hV, hx₀V, hQ', hq₀Q', (hs.mono hsub).of_le (by simp),
    fun q hq ↦ hs₀ q (hsub ⟨hx₀V, hq⟩), fun x hx q hq ↦ hsol (x, q) (hsub ⟨hx, hq⟩)⟩

/-- If a smooth scalar function `φ` agrees on an open set `W ⊆ V` containing `x₀` with the first
component of a coordinate flattening-system solution `σ` initialized at `(c, g(ξ, ·))`, then `φ`
has value `c` and gradient `ξ` at `x₀` and solves the conformal flattening equation on `W`. -/
private theorem hessian_eq_of_hasFDerivAt_flatteningField {x₀ : E} {V W : Set E}
    (hV : IsOpen V) (hW : IsOpen W) (hx₀W : x₀ ∈ W) (hWV : W ⊆ V)
    {σ : E → ℝ × (E →L[ℝ] ℝ)} (hσsol : ∀ x ∈ V, HasFDerivAt σ (flatteningField E (x, σ x)) x)
    {c : ℝ} {ξ : TangentSpace 𝓘(ℝ, E) x₀}
    (hσ₀ : σ x₀ = (c, metricCoeff E x₀ (tangentSpaceCastModel 𝓘(ℝ, E) x₀ ξ)))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφσ : ∀ y ∈ W, φ y = (σ y).1) :
    φ x₀ = c ∧ mgradient 𝓘(ℝ, E) φ x₀ = ξ ∧
      ∀ y ∈ W, ∀ u v : TangentSpace 𝓘(ℝ, E) y, hessian 𝓘(ℝ, E) φ y u v =
        (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y) u v := by
  set φ₀ : E → ℝ := fun x ↦ (σ x).1
  have hDφ₀ (x : E) (hx : x ∈ V) : fderiv ℝ φ₀ x = (σ x).2 := by
    have heq : (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)).comp (flatteningField E (x, σ x)) =
        (σ x).2 :=
      ContinuousLinearMap.ext fun u ↦ flatteningField_apply_fst (x, σ x) u
    have h := (hσsol x hx).fst
    rw [heq] at h
    exact h.fderiv
  have hD2φ₀ (x : E) (hx : x ∈ V) (u v : E) :
      fderiv ℝ (fderiv ℝ φ₀) x u v = (flatteningField E (x, σ x) u).2 v := by
    have hEq : fderiv ℝ φ₀ =ᶠ[𝓝 x] fun x ↦ (σ x).2 := eventually_of_mem (hV.mem_nhds hx) hDφ₀
    rw [hEq.fderiv_eq, (hσsol x hx).snd.fderiv]
    simp
  have hEqW (y : E) (hy : y ∈ W) : φ =ᶠ[𝓝 y] φ₀ := eventually_of_mem (hW.mem_nhds hy) hφσ
  refine ⟨(hφσ x₀ hx₀W).trans (by simp [hσ₀]), ?_, fun y hy u v ↦ ?_⟩
  · refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
    rw [mvfderiv_eq_fderiv, (hEqW x₀ hx₀W).fderiv_eq, hDφ₀ x₀ (hWV hx₀W)]
    simp [hσ₀, inner_eq_metricCoeff, NormedSpace.fromTangentSpace]
  · have h := hessian_sub_conformalFlatteningForm_model_space
      (hφ.contDiffAt.of_le (by simp) : ContDiffAt ℝ 2 φ y)
      (tangentSpaceCastModel 𝓘(ℝ, E) y u) (tangentSpaceCastModel 𝓘(ℝ, E) y v)
    have hjet : (y, φ y, fderiv ℝ φ y) = (y, σ y) := by
      rw [hφσ y hy, (hEqW y hy).fderiv_eq, hDφ₀ y (hWV hy)]
    rw [(hEqW y hy).fderiv.fderiv_eq, hD2φ₀ y (hWV hy), hjet, sub_self] at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, sub_eq_zero] using h

/-- **Smooth initial-value dependence for the conformal flattening equation on a model space.**
Where the Weyl and Cotton tensors of a smooth Riemannian metric on `E` vanish near `x₀`, around any
initial value `c₀ : ℝ` and initial gradient `ξ₀ : TangentSpace 𝓘(ℝ, E) x₀` there exist open
neighbourhoods `W` of `x₀` and `Q` of `(c₀, ξ₀)` and a globally smooth family
`Φ : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) → ℝ` such that for every `q ∈ Q`, the slice `y ↦ Φ (y, q)`
has value `q.1` and gradient `q.2` at `x₀` and solves the conformal flattening equation on `W`. -/
theorem exists_contMDiff_hessian_eq_family_model_space {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace 𝓘(ℝ, E) x₀) :
    ∃ (W : Set E) (Q : Set (ℝ × TangentSpace 𝓘(ℝ, E) x₀))
      (Φ : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) → ℝ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ × TangentSpace 𝓘(ℝ, E) x₀)) 𝓘(ℝ) ∞ Φ ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient 𝓘(ℝ, E) (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W, ∀ u v : TangentSpace 𝓘(ℝ, E) y,
          hessian 𝓘(ℝ, E) (fun z ↦ Φ (z, q)) y u v =
            (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) (fun z ↦ Φ (z, q)) y) u v := by
  let Lξ : TangentSpace 𝓘(ℝ, E) x₀ →L[ℝ] (E →L[ℝ] ℝ) :=
    (metricCoeff E x₀).comp (tangentSpaceCastModel 𝓘(ℝ, E) x₀).toContinuousLinearMap
  let J₀ : (ℝ × TangentSpace 𝓘(ℝ, E) x₀) →L[ℝ] (ℝ × (E →L[ℝ] ℝ)) :=
    ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) Lξ
  obtain ⟨s, V, Q', hV, hx₀V, hQ', hq₀Q', hs, hs₀, hsol⟩ :=
    exists_contDiffOn_hasFDerivAt_flatteningField_family hW hC (J₀ (c₀, ξ₀))
  let Q₀ : Set (ℝ × TangentSpace 𝓘(ℝ, E) x₀) := J₀ ⁻¹' Q'
  have hQ₀ : IsOpen Q₀ := hQ'.preimage J₀.continuous
  -- Cut off the local Frobenius family in both space and initial-value coordinates.
  obtain ⟨χE, hχE, -, hχE₁, -, hχEV⟩ :=
    (isCompact_singleton (x := x₀)).exists_contDiff_cutoff_eventuallyEq_one hV
      (singleton_subset_iff.2 hx₀V)
  obtain ⟨χQ, hχQ, -, hχQ₁, -, hχQQ₀⟩ :=
    (isCompact_singleton (x := (c₀, ξ₀))).exists_contDiff_cutoff_eventuallyEq_one hQ₀
      (singleton_subset_iff.2 hq₀Q')
  obtain ⟨W₁, hW₁_sub, hW₁_open, hx₀W₁⟩ := eventually_nhds_iff.1 (hχE₁ x₀ rfl)
  obtain ⟨Q₁, hQ₁_sub, hQ₁_open, hq₀Q₁⟩ := eventually_nhds_iff.1 (hχQ₁ (c₀, ξ₀) rfl)
  let χ (p : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀)) : ℝ := χE p.1 * χQ p.2
  have hχ : ContDiff ℝ ∞ χ := (hχE.comp contDiff_fst).mul (hχQ.comp contDiff_snd)
  have hχ_supp : tsupport χ ⊆ V ×ˢ Q₀ :=
    (closure_minimal (t := tsupport χE ×ˢ tsupport χQ)
      (fun p hp ↦ ⟨subset_tsupport _ (left_ne_zero_of_mul hp),
        subset_tsupport _ (right_ne_zero_of_mul hp)⟩)
      ((isClosed_tsupport _).prod (isClosed_tsupport _))).trans (prod_mono hχEV hχQQ₀)
  let Φ (p : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀)) : ℝ := χ p • (s (p.1, J₀ p.2)).1
  have hΦ_diff : ContDiff ℝ ∞ Φ :=
    (contDiffOn_fst.comp (hs.comp (contDiffOn_id.prodMap J₀.contDiff.contDiffOn)
      (MapsTo.prodMap (mapsTo_id V) (mapsTo_preimage J₀ Q')))
      (mapsTo_univ _ _)).contDiff_smul_of_tsupport_subset (hV.prod hQ₀) hχ.contDiffOn hχ_supp
  have hΦ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ × TangentSpace 𝓘(ℝ, E) x₀)) 𝓘(ℝ) ∞ Φ := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiff_iff_contDiff.2 hΦ_diff
  refine ⟨W₁ ∩ V, Q₁ ∩ Q₀, Φ, hW₁_open.inter hV, ⟨hx₀W₁, hx₀V⟩, hQ₁_open.inter hQ₀,
    ⟨hq₀Q₁, hq₀Q'⟩, hΦ, fun q hq ↦ ?_⟩
  exact hessian_eq_of_hasFDerivAt_flatteningField hV (hW₁_open.inter hV) ⟨hx₀W₁, hx₀V⟩
    inter_subset_right (fun x hx ↦ hsol x hx (J₀ q) hq.2) (hs₀ (J₀ q) hq.2)
    (hΦ_diff.comp (contDiff_id.prodMk contDiff_const))
    fun y hy ↦ by simp [Φ, χ, hW₁_sub y hy.1, hQ₁_sub q hq.1]

/-- **Local solutions of the conformal flattening equation.** Let `g` be a smooth Riemannian
metric on a finite-dimensional real normed space `E` whose Weyl and Cotton tensors vanish near
`x₀`. Then for every `c : ℝ` and every tangent vector `ξ` at `x₀` there is a smooth function `φ`
with `φ x₀ = c` and `grad φ x₀ = ξ` solving the conformal flattening equation
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` near `x₀`, where `P` is the Schouten tensor. When `E` has
dimension at least `3`, this says equivalently that `e^(2φ) g` has vanishing Schouten tensor near
`x₀`. -/
theorem exists_eventually_hessian_eq_model_space {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace 𝓘(ℝ, E) x₀) :
    ∃ φ : E → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient 𝓘(ℝ, E) φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace 𝓘(ℝ, E) y, hessian 𝓘(ℝ, E) φ y u v =
        (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y) u v := by
  obtain ⟨W, Q, Φ, hW_open, hx₀W, -, hqQ, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_family_model_space hW hC c ξ
  obtain ⟨hval, hgrad, hhess⟩ := hsol (c, ξ) hqQ
  exact ⟨fun y ↦ Φ (y, (c, ξ)), hΦ.comp (contMDiff_id.prodMk contMDiff_const), hval, hgrad,
    eventually_of_mem (hW_open.mem_nhds hx₀W) hhess⟩

end ModelSpace

/-! ### The conformal flattening system on a smooth Riemannian manifold -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The inclusion `Opens.inclusion hsub` between nested open submanifolds equipped with the
restricted Riemannian bundle is a local Riemannian isometry, and its differential commutes with
`tangentSpaceOpenEquiv`. -/
private theorem isLocalRiemannianIsometry_opens_inclusion
    {W W₀ : Opens M} (hsub : W ≤ W₀) :
    IsLocalRiemannianIsometry I I (Opens.inclusion hsub) ∧
      ∀ (y : W) (v : TangentSpace I y),
        tangentSpaceOpenEquiv (I := I) (Opens.inclusion hsub y)
            (mfderiv I I (Opens.inclusion hsub) y v) =
          tangentSpaceOpenEquiv (I := I) y v := by
  have hmf (y : W) (v : TangentSpace I y) :
      tangentSpaceOpenEquiv (I := I) (Opens.inclusion hsub y)
          (mfderiv I I (Opens.inclusion hsub) y v) =
        tangentSpaceOpenEquiv (I := I) y v := by
    simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using
      tangentSpaceOpenEquiv_mfderiv_apply (A := id)
        ((contMDiff_inclusion hsub).mdifferentiableAt one_ne_zero) rfl v
  refine ⟨{ contMDiff := contMDiff_inclusion hsub
            isInvertible_mfderiv := fun y ↦
              ⟨ContinuousLinearEquiv.refl ℝ (TangentSpace I y), by
                ext v
                exact (mfderiv_inclusion_apply hsub y v).symm⟩
            inner_mfderiv := fun y v w ↦ by
              rw [inner_tangentSpace_open, inner_tangentSpace_open, hmf, hmf] }, hmf⟩

/-- Around an interior point `x₀` near which the Weyl and Cotton tensors vanish, there is an open
neighbourhood `W₀` diffeomorphic to `E` and a smooth Riemannian metric `gE` on `E` with everywhere
vanishing Weyl and Cotton tensors such that the coordinate diffeomorphism `W₀ ≃ₘ E` is a local
Riemannian isometry. -/
private theorem exists_isLocalRiemannianIsometry_model_space_of_isInteriorPoint {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0) :
    ∃ (W₀ : Opens M) (_ : x₀ ∈ W₀) (Ψ : W₀ ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E)
      (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)),
      letI : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
      haveI : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) :=
        ⟨gE.inner, gE.contMDiff, fun _ _ _ ↦ rfl⟩
      IsLocalRiemannianIsometry I 𝓘(ℝ, E) Ψ ∧
        ∀ z : E, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).weylTensor z = 0 ∧
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).cottonTensor z = 0 := by
  obtain ⟨W₀, hx₀W₀, Ψ, hW₀_sub, -⟩ := exists_diffeomorph_opens_of_isInteriorPoint hx₀ (hW.and hC)
  let gW₀ := contMDiffRiemannianMetricOpen (I := I) (n := ∞) W₀
  have hinj : ∀ z : E, Function.Injective (mfderiv 𝓘(ℝ, E) I Ψ.symm z) := fun _ ↦
    (Ψ.symm.isInvertible_mfderiv (by simp)).injective
  let gE := gW₀.pullback Ψ.symm (by simpa using Ψ.symm.contMDiff) hinj
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨gE.inner, gE.contMDiff, fun _ _ _ ↦ rfl⟩
  have hΨ_iso : IsLocalRiemannianIsometry I 𝓘(ℝ, E) Ψ :=
    { contMDiff := Ψ.contMDiff
      isInvertible_mfderiv := fun _ ↦ Ψ.isInvertible_mfderiv (by simp)
      inner_mfderiv := fun y v w ↦ by
        rw [ContMDiffRiemannianMetric.inner_riemannianBundle gE, gW₀.pullback_inner,
          Ψ.mfderiv_symm_apply_mfderiv_apply (by simp),
          Ψ.mfderiv_symm_apply_mfderiv_apply (by simp), Ψ.symm_apply_apply,
          contMDiffRiemannianMetricOpen_inner, inner_tangentSpace_open] }
  have hι₀ := IsLocalRiemannianIsometry.subtype_val (I := I) W₀
  refine ⟨W₀, hx₀W₀, Ψ, gE, hΨ_iso, fun z ↦ ?_⟩
  have hWC := hW₀_sub (Ψ.symm z).2
  rw [← Ψ.apply_symm_apply z]
  exact ⟨(hΨ_iso.weylTensor_eq_zero_iff _).2 ((hι₀.weylTensor_eq_zero_iff _).1 hWC.1),
    (hΨ_iso.cottonTensor_eq_zero_iff _).2 ((hι₀.cottonTensor_eq_zero_iff _).1 hWC.2)⟩

/-- Transport gradient and conformal-flattening solution properties from `(E, gE)` to `M` across a
nested open submanifold `W_op ≤ W₀` where `φM` agrees with `φE ∘ Ψ`. -/
private theorem mgradient_and_hessian_eq_of_comp_opens
    [RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)]
    {W_op W₀ : Opens M} (hW_W₀ : W_op ≤ W₀) {x₀ : M} (hx₀W : x₀ ∈ W_op)
    {Ψ : W₀ ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E} (hΨ_iso : IsLocalRiemannianIsometry I 𝓘(ℝ, E) Ψ)
    {W_E : Set E} {φM : M → ℝ} {φE : E → ℝ} (hφM : ContMDiff I 𝓘(ℝ) ∞ φM)
    (hφE : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φE)
    (hcomp : φM ∘ (Subtype.val : W_op → M) = φE ∘ (Ψ ∘ Opens.inclusion hW_W₀))
    (hsub : ∀ y : W_op, Ψ (Opens.inclusion hW_W₀ y) ∈ W_E)
    {ξ : TangentSpace I x₀}
    (hgrad_E : mgradient 𝓘(ℝ, E) φE (Ψ ⟨x₀, hW_W₀ hx₀W⟩) =
      ((tangentSpaceOpenEquiv (I := I) ⟨x₀, hW_W₀ hx₀W⟩).symm.trans
        (Ψ.mfderivToContinuousLinearEquiv (by simp) ⟨x₀, hW_W₀ hx₀W⟩)) ξ)
    (hhess_E : ∀ z ∈ W_E, ∀ u v : TangentSpace 𝓘(ℝ, E) z,
      hessian 𝓘(ℝ, E) φE z u v =
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).conformalFlatteningForm z
          (mgradient 𝓘(ℝ, E) φE z) u v) :
    mgradient I φM x₀ = ξ ∧
      ∀ y ∈ W_op, ∀ u v : TangentSpace I y,
        hessian I φM y u v =
          (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
            (mgradient I φM y) u v := by
  obtain ⟨hι_sub, hmf_sub⟩ := isLocalRiemannianIsometry_opens_inclusion (I := I) hW_W₀
  have hΨW : IsLocalRiemannianIsometry I 𝓘(ℝ, E) (Ψ ∘ Opens.inclusion hW_W₀) := hΨ_iso.comp hι_sub
  have hιW := IsLocalRiemannianIsometry.subtype_val (I := I) W_op
  refine ⟨?_, fun y hy u v ↦ ?_⟩
  · let e₀ := (tangentSpaceOpenEquiv (I := I) ⟨x₀, hW_W₀ hx₀W⟩).symm.trans
      (Ψ.mfderivToContinuousLinearEquiv (by simp) ⟨x₀, hW_W₀ hx₀W⟩)
    apply e₀.injective
    have hm₁ := hιW.mfderiv_mgradient_comp (x := ⟨x₀, hx₀W⟩) (hφM.mdifferentiableAt (by simp))
    have hm₂ := hΨW.mfderiv_mgradient_comp (x := ⟨x₀, hx₀W⟩) (hφE.mdifferentiableAt (by simp))
    have he₀ (w : TangentSpace I (⟨x₀, hW_W₀ hx₀W⟩ : W₀)) :
        e₀ (tangentSpaceOpenEquiv (I := I) ⟨x₀, hW_W₀ hx₀W⟩ w) =
          mfderiv I 𝓘(ℝ, E) Ψ ⟨x₀, hW_W₀ hx₀W⟩ w := by
      simpa [e₀] using DFunLike.congr_fun (Ψ.mfderivToContinuousLinearEquiv_coe (by simp)) w
    rw [← hm₁, mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, ← hmf_sub ⟨x₀, hx₀W⟩, he₀,
      ← mfderiv_comp_apply (⟨x₀, hx₀W⟩ : W_op)
        (hΨ_iso.mdifferentiableAt ⟨x₀, hW_W₀ hx₀W⟩) (hι_sub.mdifferentiableAt ⟨x₀, hx₀W⟩),
      hcomp, hm₂]
    exact hgrad_E
  · have h₁ := (hΨW.hessian_comp_eq_conformalFlatteningForm_iff (x := ⟨y, hy⟩)
      (hφE.contMDiffAt.of_le (by simp))).2 (hhess_E _ (hsub ⟨y, hy⟩))
    rw [← hcomp] at h₁
    exact (hιW.hessian_comp_eq_conformalFlatteningForm_iff (x := ⟨y, hy⟩)
      (hφM.contMDiffAt.of_le (by simp))).1 h₁ u v

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Extending a smooth model-space family `Φ_E : E × P' → ℝ` to `M × P` via `Function.extend` and a
smooth bump function supported inside an open coordinate domain `W₀`. -/
private theorem contMDiff_mul_extend_family
    {P P' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup P'] [NormedSpace ℝ P']
    {W₀ : Opens M} (Ψ : W₀ ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E) {x₀ : M} (β : SmoothBumpFunction I x₀)
    (hβ : ∀ x ∈ tsupport β, x ∈ (W₀ : Set M)) (eQ : P →L[ℝ] P')
    {Φ_E : E × P' → ℝ} (hΦ_E : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, P')) 𝓘(ℝ) ∞ Φ_E) :
    ContMDiff (I.prod 𝓘(ℝ, P)) 𝓘(ℝ) ∞
      (fun p : M × P ↦ β p.1 * Φ_E (Function.extend Subtype.val Ψ 0 p.1, eQ p.2)) := by
  refine contMDiff_of_tsupport fun p hp ↦ ?_
  have hp_supp : p.1 ∈ tsupport β :=
    (continuous_fst.closure_preimage_subset (Function.support β))
      (closure_mono (fun r hr ↦ left_ne_zero_of_mul hr) hp)
  have hψ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (Function.extend Subtype.val Ψ 0) p.1 :=
    (ContMDiffMap.contMDiffOn_extend W₀ ⟨Ψ, Ψ.contMDiff⟩ 0).contMDiffAt
      (W₀.isOpen.mem_nhds (hβ p.1 hp_supp))
  exact (β.contMDiff.comp contMDiff_fst).contMDiffAt.mul
    (hΦ_E.contMDiffAt.comp p
      ((hψ_at.comp p contMDiff_fst.contMDiffAt).prodMk
        (eQ.contDiff.contMDiff.comp contMDiff_snd).contMDiffAt))

/-- **Smooth initial-value dependence for the conformal flattening equation at an interior point.**
Let `x₀` be an interior point of a smooth Riemannian manifold `M` near which the Weyl and Cotton
tensors vanish. Then around any `(c₀, ξ₀) : ℝ × TangentSpace I x₀` there exist open neighbourhoods
`W` of `x₀` and `Q` of `(c₀, ξ₀)` and a globally smooth family `Φ : M × (ℝ × TangentSpace I x₀) → ℝ`
such that for every `q ∈ Q`, the slice `y ↦ Φ (y, q)` has value `q.1` and gradient `q.2` at `x₀`
and solves the conformal flattening equation on `W`. -/
theorem exists_contMDiff_hessian_eq_family_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (W : Set M) (Q : Set (ℝ × TangentSpace I x₀)) (Φ : M × (ℝ × TangentSpace I x₀) → ℝ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient I (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W, ∀ u v : TangentSpace I y,
          hessian I (fun z ↦ Φ (z, q)) y u v =
            (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
              (mgradient I (fun z ↦ Φ (z, q)) y) u v := by
  obtain ⟨W₀, hx₀W₀, Ψ, gE, hΨ_iso, hWE_zero⟩ :=
    exists_isLocalRiemannianIsometry_model_space_of_isInteriorPoint hx₀ hW hC
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨gE.inner, gE.contMDiff, fun _ _ _ ↦ rfl⟩
  let z₀ : E := Ψ ⟨x₀, hx₀W₀⟩
  let e₀ : TangentSpace I x₀ ≃L[ℝ] TangentSpace 𝓘(ℝ, E) z₀ :=
    (tangentSpaceOpenEquiv (I := I) ⟨x₀, hx₀W₀⟩).symm.trans
      (Ψ.mfderivToContinuousLinearEquiv (by simp) ⟨x₀, hx₀W₀⟩)
  let eQ : (ℝ × TangentSpace I x₀) →L[ℝ] (ℝ × TangentSpace 𝓘(ℝ, E) z₀) :=
    ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) e₀.toContinuousLinearMap
  obtain ⟨W_E, Q_E, Φ_E, hWE_open, hz₀WE, hQE_open, hq₀QE, hΦ_E, hsol_E⟩ :=
    exists_contMDiff_hessian_eq_family_model_space (x₀ := z₀)
      (Eventually.of_forall fun z ↦ (hWE_zero z).1)
      (Eventually.of_forall fun z ↦ (hWE_zero z).2) c₀ (e₀ ξ₀)
  have hW₁_nhds : Subtype.val '' (Ψ ⁻¹' W_E) ∈ 𝓝 x₀ :=
    (W₀.isOpen.isOpenMap_subtype_val _ (hWE_open.preimage Ψ.continuous)).mem_nhds
      ⟨⟨x₀, hx₀W₀⟩, hz₀WE, rfl⟩
  obtain ⟨β, hβ_sub, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) hW₁_nhds).mem_iff.mp hW₁_nhds
  obtain ⟨W, hW_sub, hW_open, hx₀W⟩ := eventually_nhds_iff.1 (β.eventuallyEq_one.and hW₁_nhds)
  let ψM : M → E := Function.extend Subtype.val Ψ 0
  have hψ (y : W₀) : ψM y.1 = Ψ y := congrFun (Function.extend_comp Subtype.val_injective Ψ 0) y
  let Φ (p : M × (ℝ × TangentSpace I x₀)) : ℝ := β p.1 * Φ_E (ψM p.1, eQ p.2)
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ :=
    contMDiff_mul_extend_family Ψ β (fun x hx ↦ by
      obtain ⟨⟨_, hyW₀⟩, -, rfl⟩ := hβ_sub hx; exact hyW₀) eQ hΦ_E
  have hW_W₀ : (⟨W, hW_open⟩ : Opens M) ≤ W₀ := fun y hy ↦ by
    obtain ⟨⟨_, hy₀⟩, -, rfl⟩ := (hW_sub y hy).2; exact hy₀
  refine ⟨W, eQ ⁻¹' Q_E, Φ, hW_open, hx₀W, hQE_open.preimage eQ.continuous, hq₀QE, hΦ,
    fun q hq ↦ ?_⟩
  obtain ⟨hval_E, hgrad_E, hhess_E⟩ := hsol_E (eQ q) hq
  refine ⟨by simpa [Φ, eQ, (hW_sub x₀ hx₀W).1, hψ ⟨x₀, hx₀W₀⟩, z₀] using hval_E, ?_⟩
  exact mgradient_and_hessian_eq_of_comp_opens (φM := fun y ↦ Φ (y, q))
    (φE := fun z ↦ Φ_E (z, eQ q)) hW_W₀ hx₀W hΨ_iso
    (hΦ.comp (contMDiff_id.prodMk contMDiff_const))
    (hΦ_E.comp (contMDiff_id.prodMk contMDiff_const))
    (by ext y; simp [Φ, (hW_sub y.1 y.2).1, hψ (Opens.inclusion hW_W₀ y)])
    (fun y ↦ by
      obtain ⟨y', hy'WE, hy'eq⟩ := (hW_sub y.1 y.2).2
      exact (Subtype.ext hy'eq : y' = Opens.inclusion hW_W₀ y) ▸ hy'WE)
    (by simpa [eQ, e₀] using hgrad_E) hhess_E

/-- **Local solutions of the conformal flattening equation at an interior point.** Let `x₀` be an
interior point of a smooth Riemannian manifold `M` near which the Weyl and Cotton tensors vanish.
Then for every `c : ℝ` and every tangent vector `ξ` at `x₀` there is a globally smooth function `φ`
with `φ x₀ = c` and `grad φ x₀ = ξ` solving the conformal flattening equation near `x₀`. -/
theorem exists_eventually_hessian_eq_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v := by
  obtain ⟨W, Q, Φ, hW_open, hx₀W, -, hqQ, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_family_of_isInteriorPoint hx₀ hW hC c ξ
  obtain ⟨hval, hgrad, hhess⟩ := hsol (c, ξ) hqQ
  exact ⟨fun y ↦ Φ (y, (c, ξ)), hΦ.comp (contMDiff_id.prodMk contMDiff_const), hval, hgrad,
    eventually_of_mem (hW_open.mem_nhds hx₀W) hhess⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Smooth initial-value dependence for the conformal flattening equation on a boundaryless
manifold.** -/
theorem exists_contMDiff_hessian_eq_family {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (W : Set M) (Q : Set (ℝ × TangentSpace I x₀)) (Φ : M × (ℝ × TangentSpace I x₀) → ℝ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient I (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W, ∀ u v : TangentSpace I y,
          hessian I (fun z ↦ Φ (z, q)) y u v =
            (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
              (mgradient I (fun z ↦ Φ (z, q)) y) u v :=
  exists_contMDiff_hessian_eq_family_of_isInteriorPoint BoundarylessManifold.isInteriorPoint
    hW hC c₀ ξ₀

/-- **Local solutions of the conformal flattening equation on a boundaryless manifold.** -/
theorem exists_eventually_hessian_eq {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v :=
  exists_eventually_hessian_eq_of_isInteriorPoint BoundarylessManifold.isInteriorPoint hW hC c ξ

end Boundaryless

end Manifold

end TauCeti.Manifold
