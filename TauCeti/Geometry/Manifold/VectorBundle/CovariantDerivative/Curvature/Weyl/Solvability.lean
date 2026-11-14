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

* `TauCeti.Manifold.exists_contDiff_hessian_eq_family_model_space`: on a normed space with a smooth
  Riemannian metric whose Weyl and Cotton tensors vanish near `x₀`, the conformal flattening
  equation admits near any initial jet `(c₀, ξ₀)` a jointly smooth family of solutions `Φ (x, c, ξ)`
  taking the value `c` and gradient `ξ` at `x₀` and solving the equation on a common open
  neighbourhood of `x₀`.
* `TauCeti.Manifold.exists_eventually_hessian_eq_model_space`: specialization at a single initial
  jet `(c, ξ)`.

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

/-- **A smooth solution family of the flattening system around a prescribed jet.** Where the Weyl
and Cotton tensors vanish near `x₀`, the coordinate conformal flattening system has, near every
initial value `q₀`, a smooth solution family `s` on an open product `V ×ˢ Q` around `(x₀, q₀)`
satisfying `s (x₀, q) = q` on `Q`. -/
private theorem exists_contDiffOn_hasFDerivAt_flatteningField_family {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (q₀ : ℝ × (E →L[ℝ] ℝ)) :
    ∃ (s : E × (ℝ × (E →L[ℝ] ℝ)) → ℝ × (E →L[ℝ] ℝ)) (V : Set E) (Q : Set (ℝ × (E →L[ℝ] ℝ))),
      IsOpen V ∧ x₀ ∈ V ∧ IsOpen Q ∧ q₀ ∈ Q ∧ ContDiffOn ℝ ∞ s (V ×ˢ Q) ∧
      (∀ q ∈ Q, s (x₀, q) = q) ∧
      ∀ x ∈ V, ∀ q ∈ Q, HasFDerivAt (fun z ↦ s (z, q)) (flatteningField E (x, s (x, q))) x := by
  have hint : ∀ᶠ p in 𝓝 (x₀, q₀), IsFrobeniusIntegrableAt (flatteningField E) p :=
    ((continuous_fst.tendsto (x₀, q₀)).eventually (hW.and hC)).mono fun p hp ↦
      isFrobeniusIntegrableAt_flatteningField hp.1 hp.2 p.2
  obtain ⟨s, U, hU, hp₀U, hs, -, hsinit, hsol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt (n := ⊤)
      (contDiff_flatteningField.contDiffOn (s := univ) |>.of_le (by simp)) univ_mem hint
  obtain ⟨V, Q, hV, hQ, hx₀V, hq₀Q, hVQ⟩ := isOpen_prod_iff.1 hU x₀ q₀ hp₀U
  exact ⟨s, V, Q, hV, hx₀V, hQ, hq₀Q, (hs.mono hVQ).of_le (by simp),
    fun q hq ↦ hsinit q (hVQ ⟨hx₀V, hq⟩), fun x hx q hq ↦ hsol (x, q) (hVQ ⟨hx, hq⟩)⟩

omit [RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)] in
/-- Cut off a function smooth on an open product `V ×ˢ Ω` around `(x₀, p₀)` to a globally smooth
function agreeing with it on a smaller open product `V' ×ˢ Ω'` around `(x₀, p₀)`. -/
private theorem exists_contDiff_cutoff_prod {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {V : Set E} {Ω : Set P} {x₀ : E} {p₀ : P} {Φ₀ : E × P → ℝ}
    (hV : IsOpen V) (hx₀V : x₀ ∈ V) (hΩ : IsOpen Ω) (hp₀Ω : p₀ ∈ Ω)
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (V ×ˢ Ω)) :
    ∃ (Φ : E × P → ℝ) (V' : Set E) (Ω' : Set P), IsOpen V' ∧ x₀ ∈ V' ∧ V' ⊆ V ∧
      IsOpen Ω' ∧ p₀ ∈ Ω' ∧ Ω' ⊆ Ω ∧ ContDiff ℝ ∞ Φ ∧
      ∀ x ∈ V', ∀ p ∈ Ω', Φ (x, p) = Φ₀ (x, p) := by
  obtain ⟨χ₁, hχ₁, -, hχ₁₁, -, hχ₁V⟩ :=
    (isCompact_singleton (x := x₀)).exists_contDiff_cutoff_eventuallyEq_one hV
      (singleton_subset_iff.2 hx₀V)
  obtain ⟨χ₂, hχ₂, -, hχ₂₁, -, hχ₂Ω⟩ :=
    (isCompact_singleton (x := p₀)).exists_contDiff_cutoff_eventuallyEq_one hΩ
      (singleton_subset_iff.2 hp₀Ω)
  let χ : E × P → ℝ := fun z ↦ χ₁ z.1 * χ₂ z.2
  have hχ : ContDiff ℝ ∞ χ := (hχ₁.comp contDiff_fst).mul (hχ₂.comp contDiff_snd)
  have htsupp : tsupport χ ⊆ V ×ˢ Ω :=
    (closure_minimal (fun z hz ↦ Set.mem_prod.2 ⟨subset_tsupport _ (left_ne_zero_of_mul hz),
      subset_tsupport _ (right_ne_zero_of_mul hz)⟩)
      ((isClosed_tsupport χ₁).prod (isClosed_tsupport χ₂))).trans (prod_mono hχ₁V hχ₂Ω)
  let V' : Set E := interior {x ∈ V | χ₁ x = 1}
  let Ω' : Set P := interior {p ∈ Ω | χ₂ p = 1}
  refine ⟨fun z ↦ χ z • Φ₀ z, V', Ω', isOpen_interior,
    mem_interior_iff_mem_nhds.2 (inter_mem (hV.mem_nhds hx₀V) (hχ₁₁ x₀ rfl)),
    fun _ hx ↦ (interior_subset hx).1, isOpen_interior,
    mem_interior_iff_mem_nhds.2 (inter_mem (hΩ.mem_nhds hp₀Ω) (hχ₂₁ p₀ rfl)),
    fun _ hp ↦ (interior_subset hp).1,
    hΦ₀.contDiff_smul_of_tsupport_subset (hV.prod hΩ) hχ.contDiffOn htsupp, fun x hx p hp ↦ ?_⟩
  simp [χ, (interior_subset hx).2, (interior_subset hp).2]

/-- A smooth function `φ` agreeing on an open neighbourhood `V` of `x₀` with the first component of
a solution `σ` of `flatteningField` takes the prescribed initial jet at `x₀` and solves the
conformal flattening equation on `V`. -/
private theorem hessian_eq_of_eqOn_flatteningField {x₀ : E} {V : Set E} (hV : IsOpen V)
    (hx₀V : x₀ ∈ V) {σ : E → ℝ × (E →L[ℝ] ℝ)} {c : ℝ} {ξ : TangentSpace 𝓘(ℝ, E) x₀}
    (hσ₀ : σ x₀ = (c, metricCoeff E x₀ (tangentSpaceCastModel 𝓘(ℝ, E) x₀ ξ)))
    (hσsol : ∀ x ∈ V, HasFDerivAt σ (flatteningField E (x, σ x)) x)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφeq : ∀ x ∈ V, φ x = (σ x).1) :
    φ x₀ = c ∧ mgradient 𝓘(ℝ, E) φ x₀ = ξ ∧ ∀ y ∈ V, ∀ u v : TangentSpace 𝓘(ℝ, E) y,
      hessian 𝓘(ℝ, E) φ y u v = (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) φ y) u v := by
  have hDφ (x : E) (hx : x ∈ V) : fderiv ℝ φ x = (σ x).2 := by
    have heq : (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)).comp (flatteningField E (x, σ x)) =
        (σ x).2 :=
      ContinuousLinearMap.ext fun u ↦ flatteningField_apply_fst (x, σ x) u
    have h := ((hσsol x hx).fst.congr_of_eventuallyEq
      (eventually_of_mem (hV.mem_nhds hx) hφeq))
    rw [heq] at h
    exact h.fderiv
  have hD2φ (x : E) (hx : x ∈ V) (u v : E) :
      fderiv ℝ (fderiv ℝ φ) x u v = (flatteningField E (x, σ x) u).2 v := by
    have hEq : fderiv ℝ φ =ᶠ[𝓝 x] fun z ↦ (σ z).2 :=
      eventually_of_mem (hV.mem_nhds hx) hDφ
    rw [hEq.fderiv_eq, (hσsol x hx).snd.fderiv]
    simp
  refine ⟨by rw [hφeq x₀ hx₀V, hσ₀], (eq_mgradient_iff.2 fun v ↦ ?_).symm, fun y hy u v ↦ ?_⟩
  · rw [mvfderiv_eq_fderiv, hDφ x₀ hx₀V]
    simp [hσ₀, inner_eq_metricCoeff, NormedSpace.fromTangentSpace]
  · have h := hessian_sub_conformalFlatteningForm_model_space (hφ.contDiffAt.of_le (by simp) :
      ContDiffAt ℝ 2 φ y) (tangentSpaceCastModel 𝓘(ℝ, E) y u) (tangentSpaceCastModel 𝓘(ℝ, E) y v)
    have hjet : (y, φ y, fderiv ℝ φ y) = (y, σ y) := by
      rw [hφeq y hy, hDφ y hy]
    rw [hD2φ y hy, hjet, sub_self] at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, sub_eq_zero] using h

/-- **Smooth dependence on the initial jet for the conformal flattening equation.** Let `g` be a
smooth Riemannian metric on a finite-dimensional real normed space `E` whose Weyl and Cotton
tensors vanish near `x₀`. Around every initial jet `(c₀, ξ₀)` at `x₀`, there exist open
neighbourhoods `V` of `x₀` and `Ω` of `(c₀, ξ₀)` and a jointly smooth function
`Φ : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) → ℝ` such that for every `(c, ξ) ∈ Ω` the slice
`x ↦ Φ (x, c, ξ)` takes the value `c` and gradient `ξ` at `x₀` and solves the conformal flattening
equation on `V`. -/
theorem exists_contDiff_hessian_eq_family_model_space {x₀ : E}
    (hW : ∀ᶠ y in 𝓝 x₀, (lc).weylTensor y = 0) (hC : ∀ᶠ y in 𝓝 x₀, (lc).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace 𝓘(ℝ, E) x₀) :
    ∃ (Φ : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) → ℝ) (V : Set E)
      (Ω : Set (ℝ × TangentSpace 𝓘(ℝ, E) x₀)),
      IsOpen V ∧ x₀ ∈ V ∧ IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧ ContDiff ℝ ∞ Φ ∧
      (∀ c ξ, (c, ξ) ∈ Ω → Φ (x₀, c, ξ) = c) ∧
      (∀ c ξ, (c, ξ) ∈ Ω → mgradient 𝓘(ℝ, E) (fun x ↦ Φ (x, c, ξ)) x₀ = ξ) ∧
      ∀ y ∈ V, ∀ c ξ, (c, ξ) ∈ Ω → ∀ u v : TangentSpace 𝓘(ℝ, E) y,
        hessian 𝓘(ℝ, E) (fun x ↦ Φ (x, c, ξ)) y u v =
          (lc).conformalFlatteningForm y (mgradient 𝓘(ℝ, E) (fun x ↦ Φ (x, c, ξ)) y) u v := by
  let qMap (p : ℝ × TangentSpace 𝓘(ℝ, E) x₀) : ℝ × (E →L[ℝ] ℝ) :=
    (p.1, metricCoeff E x₀ (tangentSpaceCastModel 𝓘(ℝ, E) x₀ p.2))
  have hqMap : ContDiff ℝ ∞ qMap :=
    contDiff_fst.prodMk ((metricCoeff E x₀).contDiff.comp
      ((tangentSpaceCastModel 𝓘(ℝ, E) x₀).contDiff.comp contDiff_snd))
  obtain ⟨s, V₀, Q, hV₀, hx₀V₀, hQ, hq₀Q, hs, hsinit, hsol⟩ :=
    exists_contDiffOn_hasFDerivAt_flatteningField_family hW hC (qMap (c₀, ξ₀))
  let Ω₀ : Set (ℝ × TangentSpace 𝓘(ℝ, E) x₀) := qMap ⁻¹' Q
  have hΦ₀ : ContDiffOn ℝ ∞ (fun z : E × (ℝ × TangentSpace 𝓘(ℝ, E) x₀) ↦ (s (z.1, qMap z.2)).1)
      (V₀ ×ˢ Ω₀) :=
    contDiff_fst.comp_contDiffOn (hs.comp (contDiffOn_fst.prodMk
      (hqMap.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _)))
      (fun _ hz ↦ ⟨hz.1, hz.2⟩))
  obtain ⟨Φ, V, Ω, hV, hx₀V, hVV₀, hΩ, hp₀Ω, hΩΩ₀, hΦ, hΦeq⟩ :=
    exists_contDiff_cutoff_prod hV₀ hx₀V₀ (hQ.preimage hqMap.continuous) hq₀Q hΦ₀
  have hslice (c : ℝ) (ξ : TangentSpace 𝓘(ℝ, E) x₀) (hp : (c, ξ) ∈ Ω) :=
    hessian_eq_of_eqOn_flatteningField hV hx₀V (hsinit (qMap (c, ξ)) (hΩΩ₀ hp))
      (fun x hx ↦ hsol x (hVV₀ hx) (qMap (c, ξ)) (hΩΩ₀ hp))
      (hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun x hx ↦ hΦeq x hx (c, ξ) hp)
  exact ⟨Φ, V, Ω, hV, hx₀V, hΩ, hp₀Ω, hΦ, fun c ξ hp ↦ (hslice c ξ hp).1,
    fun c ξ hp ↦ (hslice c ξ hp).2.1, fun y hy c ξ hp ↦ (hslice c ξ hp).2.2 y hy⟩

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
  obtain ⟨Φ, V, _, hV, hx₀V, _, hp₀Ω, hΦ, hval, hgrad, hsol⟩ :=
    exists_contDiff_hessian_eq_family_model_space hW hC c ξ
  exact ⟨fun x ↦ Φ (x, c, ξ),
    contMDiff_iff_contDiff.2 (hΦ.comp (contDiff_id.prodMk contDiff_const)),
    hval c ξ hp₀Ω, hgrad c ξ hp₀Ω,
    eventually_of_mem (hV.mem_nhds hx₀V) fun y hy ↦ hsol y hy c ξ hp₀Ω⟩

end ModelSpace

end TauCeti.Manifold
