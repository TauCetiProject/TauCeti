/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Integrability
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
import TauCeti.Analysis.ODE.Frobenius
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Local solutions of the conformal flattening equation

Let `g` be a smooth Riemannian metric on a finite-dimensional real normed space `E`. In dimension
at least `3`, the metric `e^(2φ) g` has vanishing Schouten tensor exactly when `φ` solves the
*conformal flattening equation*

`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`,

with `P` the Schouten tensor of `g`
(`Bundle.ContMDiffRiemannianMetric.schoutenTensor_leviCivitaConnection_rescale_eq_zero_iff`).
This file proves that the equation is locally solvable with arbitrary initial data wherever the
Weyl and Cotton tensors of `g` vanish: if `W = 0` and `C = 0` near `x₀`, then for every number `c`
and tangent vector `ξ` at `x₀` there is a smooth `φ` solving the equation near `x₀` with
`φ x₀ = c` and `grad φ x₀ = ξ`. This is a converse of
`TauCeti.Manifold.weylTensor_eq_zero_of_forall_exists_eventually_hessian_eq` and
`TauCeti.Manifold.cottonTensor_eq_zero_of_eventually_hessian_eq`, and the analytic step in the
proof that a metric with vanishing Weyl tensor (dimension at least `4`) or vanishing Cotton tensor
(dimension `3`) is locally conformally flat.

In linear coordinates, writing `α = dφ`, the equation is the first-order total differential
equation `D(φ, α)(u) = (α u, v ↦ α(Γ(u, v)) + Φ_α(u, v))` on `E × (ℝ × E*)`, where `Γ` are the
Christoffel symbols of `g` (`TauCeti.Manifold.christoffelSecondKind`) and `Φ_α` is the right side
of the equation. Its Frobenius integrability condition is checked without computing curvature in
coordinates: at a point `(y, c, α)`, a quadratic function with this value, differential and
prescribed second derivative solves the equation at `y`, and along such a function the
antisymmetrized derivative of the defect of the equation is
`-(C(X, Y, Z) + W(Z, Y, X, grad φ))`
(`TauCeti.Manifold.mvfderiv_hessian_sub_conformalFlatteningForm_sub_swap`), which vanishes. The
local Frobenius theorem `TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt`
then produces the solution, and a cutoff makes it globally smooth.

## Main results

* `TauCeti.Manifold.exists_contMDiff_hessian_eq_family_model_space`: on a normed space with a
  smooth Riemannian metric whose Weyl and Cotton tensors vanish near `x₀`, nearby initial data
  `(c, ξ)` around `(c₀, ξ₀)` admit a jointly smooth family of solutions of the conformal flattening
  equation on a common open neighbourhood of `x₀`, vanishing outside a compact subset of `E`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G (the Weyl–Schouten theorem).
* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press (1969), Section 10.9 (the
  Frobenius theorem for total differential equations).
-/

public section

open Filter Set
open scoped ContDiff Manifold InnerProductSpace Topology

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

/-- If `σ` solves the coordinate flattening total differential equation on an open set `V₀` and a
`C²` function `φp` locally agrees with `(σ ·).1` around every point of `V ⊆ V₀`, then `φp` inherits
the initial value and gradient encoded by `σ x₀` and solves the conformal flattening equation at
every point of `V`. -/
private theorem hessian_eq_of_hasFDerivAt_flatteningField
    {V₀ V : Set E} (hV₀ : IsOpen V₀) (hVV₀ : V ⊆ V₀) {x₀ : E} (hx₀V : x₀ ∈ V)
    {σ : E → ℝ × (E →L[ℝ] ℝ)}
    (hσsol : ∀ z ∈ V₀, HasFDerivAt σ (flatteningField E (z, σ z)) z)
    {c : ℝ} {ξ : TangentSpace 𝓘(ℝ, E) x₀}
    (hσx₀ : σ x₀ = (c, (metricCoeff E x₀).comp
      (tangentSpaceCastModel 𝓘(ℝ, E) x₀).toContinuousLinearMap ξ))
    {φp : E → ℝ} (hφp : ContDiff ℝ 2 φp)
    (hφp_eq : ∀ {y}, y ∈ V → φp =ᶠ[𝓝 y] fun z ↦ (σ z).1) :
    φp x₀ = c ∧ mgradient 𝓘(ℝ, E) φp x₀ = ξ ∧
      ∀ y ∈ V, ∀ u v : TangentSpace 𝓘(ℝ, E) y,
        hessian 𝓘(ℝ, E) φp y u v =
          (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φp y) u v := by
  have hDσ₁ (z : E) (hz : z ∈ V₀) : fderiv ℝ (fun w ↦ (σ w).1) z = (σ z).2 := by
    have heq : (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)).comp (flatteningField E (z, σ z)) =
        (σ z).2 :=
      ContinuousLinearMap.ext fun u ↦ flatteningField_apply_fst (z, σ z) u
    have h := (hσsol z hz).fst
    rw [heq] at h
    exact h.fderiv
  have hD2σ₁ (z : E) (hz : z ∈ V₀) (u v : E) :
      fderiv ℝ (fderiv ℝ fun w ↦ (σ w).1) z u v = (flatteningField E (z, σ z) u).2 v := by
    have hEq : (fderiv ℝ fun w ↦ (σ w).1) =ᶠ[𝓝 z] fun w ↦ (σ w).2 :=
      eventually_of_mem (hV₀.mem_nhds hz) hDσ₁
    rw [hEq.fderiv_eq, (hσsol z hz).snd.fderiv]
    simp
  refine ⟨(hφp_eq hx₀V).eq_of_nhds.trans (by simp [hσx₀]),
    (eq_mgradient_iff.2 fun v ↦ ?_).symm, fun y hy u v ↦ ?_⟩
  · rw [mvfderiv_eq_fderiv, (hφp_eq hx₀V).fderiv_eq, hDσ₁ x₀ (hVV₀ hx₀V), hσx₀,
      inner_eq_metricCoeff]
    simp [NormedSpace.fromTangentSpace]
  · have hyEq := hφp_eq hy
    have h := hessian_sub_conformalFlatteningForm_model_space (hφp.contDiffAt (x := y))
      (tangentSpaceCastModel 𝓘(ℝ, E) y u) (tangentSpaceCastModel 𝓘(ℝ, E) y v)
    have hjet : (y, φp y, fderiv ℝ φp y) = (y, σ y) := by
      rw [hyEq.eq_of_nhds, hyEq.fderiv_eq, hDσ₁ y (hVV₀ hy)]
    rw [hyEq.fderiv.fderiv_eq, hD2σ₁ y (hVV₀ hy), hjet, sub_self] at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, sub_eq_zero] using h

/-- **Smooth family of local solutions of the conformal flattening equation.** Let `g` be a smooth
Riemannian metric on a finite-dimensional real normed space `E` whose Weyl and Cotton tensors
vanish near `x₀`. Around any initial data `(c₀, ξ₀) : ℝ × TangentSpace 𝓘(ℝ, E) x₀`, there exist a
jointly smooth function `φ : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) → ℝ`, open neighbourhoods `V` of
`x₀` and `Q` of `(c₀, ξ₀)`, and a compact set `K ⊆ E` outside which `φ` vanishes, such that for
every `(c, ξ) ∈ Q` the slice `x ↦ φ (x, (c, ξ))` satisfies `φ (x₀, (c, ξ)) = c`,
`grad (φ (·, (c, ξ))) x₀ = ξ`, and solves the conformal flattening equation on all of `V`. -/
theorem exists_contMDiff_hessian_eq_family_model_space {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace 𝓘(ℝ, E) x₀) :
    ∃ (φ : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) → ℝ)
      (V : Set E) (Q : Set (ℝ × TangentSpace 𝓘(ℝ, E) x₀)) (K : Set E),
      IsOpen V ∧ IsOpen Q ∧ IsCompact K ∧ x₀ ∈ V ∧ (c₀, ξ₀) ∈ Q ∧
      ContMDiff (𝓘(ℝ, E).prod (𝓘(ℝ).prod 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x₀))) 𝓘(ℝ) ∞ φ ∧
      (∀ x ∉ K, ∀ p, φ (x, p) = 0) ∧
      ∀ p ∈ Q, φ (x₀, p) = p.1 ∧
        mgradient 𝓘(ℝ, E) (fun x ↦ φ (x, p)) x₀ = p.2 ∧
        ∀ y ∈ V, ∀ u v : TangentSpace 𝓘(ℝ, E) y,
          hessian 𝓘(ℝ, E) (fun x ↦ φ (x, p)) y u v =
            (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) (fun x ↦ φ (x, p)) y) u v := by
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x₀) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace 𝓘(ℝ, E)) x₀
  let G := ℝ × TangentSpace 𝓘(ℝ, E) x₀
  let L : TangentSpace 𝓘(ℝ, E) x₀ →L[ℝ] E →L[ℝ] ℝ :=
    (metricCoeff E x₀).comp (tangentSpaceCastModel 𝓘(ℝ, E) x₀).toContinuousLinearMap
  let ι : G →L[ℝ] ℝ × (E →L[ℝ] ℝ) := ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) L
  let κ : E × G →L[ℝ] E × (ℝ × (E →L[ℝ] ℝ)) :=
    ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ E) ι
  set p₀ : G := (c₀, ξ₀)
  set q₀ : ℝ × (E →L[ℝ] ℝ) := ι p₀
  -- The Frobenius condition holds near `(x₀, q₀)`, giving a smooth local solution family `s`.
  have hint : ∀ᶠ r in 𝓝 (x₀, q₀), IsFrobeniusIntegrableAt (flatteningField E) r :=
    ((continuous_fst.tendsto (x₀, q₀)).eventually (hW.and hC)).mono fun r hr ↦
      isFrobeniusIntegrableAt_flatteningField hr.1 hr.2 r.2
  obtain ⟨s, U, hU, hx₀q₀U, hs, -, hs_init, hsol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt (n := ⊤)
      (contDiff_flatteningField.contDiffOn (s := univ) |>.of_le (by simp)) univ_mem hint
  obtain ⟨V₀, Q₀, hV₀, hQ₀, hx₀V₀, hp₀Q₀, hVQ⟩ :=
    isOpen_prod_iff.1 (hU.preimage κ.continuous) x₀ p₀ hx₀q₀U
  -- Cut off smoothly in both base point and initial data so the family is globally smooth on
  -- `E × G` and vanishes outside the compact set `tsupport χ ⊆ E`.
  obtain ⟨χ, hχ, -, hx₀χ, hχ_cpt, hχV₀⟩ :=
    (isCompact_singleton (x := x₀)).exists_contDiff_cutoff hV₀ (singleton_subset_iff.2 hx₀V₀)
  obtain ⟨η, hη, -, hp₀η, -, hηQ₀⟩ :=
    (isCompact_singleton (x := p₀)).exists_contDiff_cutoff hQ₀ (singleton_subset_iff.2 hp₀Q₀)
  set ψ : E × G → ℝ := fun r ↦ χ r.1 * η r.2
  set φ₀ : E × G → ℝ := fun r ↦ (s (κ r)).1
  set φ : E × G → ℝ := fun r ↦ ψ r • φ₀ r
  have htsupp : tsupport ψ ⊆ V₀ ×ˢ Q₀ := by
    refine (closure_minimal (t := tsupport χ ×ˢ tsupport η) ?_
      ((isClosed_tsupport χ).prod (isClosed_tsupport η))).trans (prod_mono hχV₀ hηQ₀)
    exact fun r hr ↦ ⟨subset_tsupport χ (left_ne_zero_of_mul hr),
      subset_tsupport η (right_ne_zero_of_mul hr)⟩
  have hφ₀ : ContDiffOn ℝ ∞ φ₀ (V₀ ×ˢ Q₀) :=
    contDiffOn_fst.comp ((hs.of_le (by simp)).comp κ.contDiff.contDiffOn hVQ) (mapsTo_univ _ _)
  have hφ_diff : ContDiff ℝ ∞ φ :=
    hφ₀.contDiff_smul_of_tsupport_subset (hV₀.prod hQ₀)
      ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd)).contDiffOn htsupp
  have hφ : ContMDiff (𝓘(ℝ, E).prod (𝓘(ℝ).prod 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x₀))) 𝓘(ℝ) ∞ φ :=
    hφ_diff.comp_contMDiff (contMDiff_fst.prodMk_space
      ((contMDiff_fst.comp contMDiff_snd).prodMk_space (contMDiff_snd.comp contMDiff_snd)))
  set V : Set E := interior (χ ⁻¹' {1}) ∩ V₀
  set Q : Set G := interior (η ⁻¹' {1}) ∩ Q₀
  have hV : IsOpen V := isOpen_interior.inter hV₀
  have hQ : IsOpen Q := isOpen_interior.inter hQ₀
  have hx₀V : x₀ ∈ V := ⟨hx₀χ rfl, hx₀V₀⟩
  have hp₀Q : p₀ ∈ Q := ⟨hp₀η rfl, hp₀Q₀⟩
  refine ⟨φ, V, Q, tsupport χ, hV, hQ, hχ_cpt, hx₀V, hp₀Q, hφ, fun x hx p ↦ ?_, fun p hp ↦ ?_⟩
  · simp [φ, ψ, image_eq_zero_of_notMem_tsupport hx]
  · -- On `V`, `χ` and `η p` equal `1`, so `φ (·, p)` agrees with `(s (·, ι p)).1`.
    set σ : E → ℝ × (E →L[ℝ] ℝ) := fun z ↦ s (z, ι p)
    have hηp : η p = 1 := interior_subset hp.1
    have hσU (z : E) (hz : z ∈ V₀) : (z, ι p) ∈ U := by simpa [κ] using hVQ (mk_mem_prod hz hp.2)
    have hφp_diff : ContDiff ℝ 2 (fun x ↦ φ (x, p)) :=
      (hφ_diff.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
    exact hessian_eq_of_hasFDerivAt_flatteningField (σ := σ) hV₀ inter_subset_right hx₀V
      (fun z hz ↦ hsol (z, ι p) (hσU z hz)) (hs_init (ι p) (hσU x₀ hx₀V₀)) hφp_diff
      fun {y} hy ↦ eventually_of_mem (hV.mem_nhds hy) fun z hz ↦ by
        have hχz : χ z = 1 := interior_subset hz.1
        simp [φ, ψ, φ₀, σ, κ, hχz, hηp]

end ModelSpace

end TauCeti.Manifold
