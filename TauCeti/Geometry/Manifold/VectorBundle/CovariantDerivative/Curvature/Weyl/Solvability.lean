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

* `TauCeti.Manifold.exists_eventually_hessian_eq_model_space`: on a normed space with a smooth
  Riemannian metric whose Weyl and Cotton tensors vanish near `x₀`, the conformal flattening
  equation has a smooth solution near `x₀` with any prescribed value and gradient at `x₀`.

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
  rw [hessian_model_space_eq_fderiv_sub_christoffelSecondKind inner_eq_metricCoeff
      (contDiff_metricCoeff.differentiable (by simp) y) hφ,
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
    flatteningField_apply_snd_comm (contDiff_flatteningField.differentiable (by simp) p) (hφ2 y)
    hφy hDφ (fun u v ↦ by simp [hD2φ, B, p]) fun u v w ↦ ?_
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

/-- **A smooth solution of the flattening system through a prescribed jet.** Where the Weyl and
Cotton tensors vanish near `x₀`, the coordinate conformal flattening system has, for every initial
value `q₀`, a solution `σ` which is smooth on an open neighbourhood `V` of `x₀` and takes the value
`q₀` at `x₀`. -/
private theorem exists_contDiffOn_hasFDerivAt_flatteningField {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (q₀ : ℝ × (E →L[ℝ] ℝ)) :
    ∃ (σ : E → ℝ × (E →L[ℝ] ℝ)) (V : Set E), IsOpen V ∧ x₀ ∈ V ∧ ContDiffOn ℝ ∞ σ V ∧
      σ x₀ = q₀ ∧ ∀ x ∈ V, HasFDerivAt σ (flatteningField E (x, σ x)) x := by
  -- The Frobenius condition holds near `(x₀, q₀)`, so the system has a smooth solution family.
  have hint : ∀ᶠ p in 𝓝 (x₀, q₀), IsFrobeniusIntegrableAt (flatteningField E) p :=
    ((continuous_fst.tendsto (x₀, q₀)).eventually (hW.and hC)).mono fun p hp ↦
      isFrobeniusIntegrableAt_flatteningField hp.1 hp.2 p.2
  obtain ⟨s, U, hU, hx₀U, hs, hs₀, -, hsol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt (n := ⊤)
      (contDiff_flatteningField.contDiffOn (s := univ) |>.of_le (by simp)) univ_mem hint
  -- The slice through `q₀` is smooth on the open set `V` and solves the system there.
  exact ⟨fun x ↦ s (x, q₀), (fun x ↦ (x, q₀)) ⁻¹' U,
    hU.preimage (continuous_id.prodMk continuous_const), hx₀U,
    (hs.comp (contDiffOn_id.prodMk contDiffOn_const) fun _ hx ↦ hx).of_le (by simp), hs₀,
    fun x hx ↦ hsol (x, q₀) hx⟩

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
  set q₀ : ℝ × (E →L[ℝ] ℝ) := (c, metricCoeff E x₀ (tangentSpaceCastModel 𝓘(ℝ, E) x₀ ξ))
  obtain ⟨σ, V, hV, hx₀V, hσ, hσ₀, hσsol⟩ :=
    exists_contDiffOn_hasFDerivAt_flatteningField hW hC q₀
  -- Its first component `φ₀` has differential the second component and second derivative `f`.
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
    have hEq : fderiv ℝ φ₀ =ᶠ[𝓝 x] fun x ↦ (σ x).2 :=
      eventually_of_mem (hV.mem_nhds hx) hDφ₀
    rw [hEq.fderiv_eq, (hσsol x hx).snd.fderiv]
    simp
  -- Cut `φ₀` off to a globally smooth function, equal to it near `x₀`.
  obtain ⟨χ, hχ, -, hχ₁, -, hχV⟩ :=
    (isCompact_singleton (x := x₀)).exists_contDiff_cutoff hV (singleton_subset_iff.2 hx₀V)
  set φ : E → ℝ := fun x ↦ χ x • φ₀ x
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiffOn_fst.comp hσ (mapsTo_univ _ _)).contDiff_smul_of_tsupport_subset hV
      hχ.contDiffOn hχV
  have hφφ₀ : ∀ᶠ y in 𝓝 x₀, φ =ᶠ[𝓝 y] φ₀ := by
    filter_upwards [isOpen_interior.eventually_mem (singleton_subset_iff.1 hχ₁)] with y hy
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    have hz₁ : χ z = 1 := interior_subset hz
    simp [φ, hz₁]
  have hVx₀ : ∀ᶠ y in 𝓝 x₀, y ∈ V := hV.mem_nhds hx₀V
  have hDφx₀ : fderiv ℝ φ x₀ = (σ x₀).2 := by
    rw [hφφ₀.self_of_nhds.fderiv_eq, hDφ₀ x₀ hx₀V]
  refine ⟨φ, contMDiff_iff_contDiff.2 hφ, ?_, ?_, ?_⟩
  · rw [hφφ₀.self_of_nhds.eq_of_nhds]
    simp [φ₀, hσ₀, q₀]
  · refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
    rw [mvfderiv_eq_fderiv, hDφx₀]
    simp [hσ₀, q₀, inner_eq_metricCoeff, NormedSpace.fromTangentSpace]
  · filter_upwards [hφφ₀, hVx₀] with y hy hyV u v
    have h := hessian_sub_conformalFlatteningForm_model_space (hφ.contDiffAt.of_le (by simp) :
      ContDiffAt ℝ 2 φ y) (tangentSpaceCastModel 𝓘(ℝ, E) y u) (tangentSpaceCastModel 𝓘(ℝ, E) y v)
    have hjet : (y, φ y, fderiv ℝ φ y) = (y, σ y) := by
      rw [hy.eq_of_nhds, hy.fderiv_eq, hDφ₀ y hyV]
    rw [hy.fderiv.fderiv_eq, hD2φ₀ y hyV, hjet, sub_self] at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, sub_eq_zero] using h

end ModelSpace

end TauCeti.Manifold
