/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.WarpedProd
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Mixed curvature of warped products

For the warped metric `g_M + f² g_N`, horizontal vectors `X, Y` and a vertical vector `V`
satisfy `R(X,V)Y = (Hess f(X,Y) / f) V`. Consequently a mixed tangent plane has sectional
curvature `-Hess f(X,X) / (f |X|²)`, independently of its nonzero vertical spanning vector.
The Hessian and the horizontal norm are those of the base metric.

These identities use the installed warped metric, characterized by
`TauCeti.Manifold.IsWarpedProduct`, and the existing Levi-Civita connection formula.
They hold at each point where the warping function is nonzero, without a sign assumption.

The tensor identity allows zero vectors and zero-dimensional factors. The sectional formula
requires nonzero horizontal and vertical vectors, so that they span a genuine tangent plane.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Proposition 42.
-/

public section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  [IsContMDiffRiemannianBundle (I.prod J) ∞ (E × F)
    (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  {f : M → ℝ}

private theorem IsWarpedProduct.curvatureOperator_horizontal_vertical_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x} {V : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hV : CMDiff ∞ (T% V))
    (p : M × N) (hf₀ : f p.1 ≠ 0) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureOperator
        (prodVectorField X 0) (prodVectorField 0 V) (prodVectorField Y 0) p =
      (hessian I f p.1 (X p.1) (Y p.1) / f p.1) • prodVectorField 0 V p := by
  have h0M : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) :=
    contMDiff_zeroSection ℝ (TangentSpace I)
  have h0N : CMDiff ∞ (T% (0 : Π y : N, TangentSpace J y)) :=
    contMDiff_zeroSection ℝ (TangentSpace J)
  let cov := leviCivitaConnection (I.prod J) (M × N)
  let D := leviCivitaConnection I M
  let a : M → ℝ := fun x ↦ mvfderiv I f x (Y x) / f x
  have hdY : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ mvfderiv I f x (Y x)) :=
    (hf.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hY
  have ha : ContMDiffAt I 𝓘(ℝ) ∞ a p.1 := hdY.contMDiffAt.div₀ hf.contMDiffAt hf₀
  have hXY := D.contMDiff_apply hX hY
  -- On horizontal sections the connection has no horizontal/vertical correction except
  -- `∇_V Y = (Y f / f) V`.
  have hh {W : Π x : M, TangentSpace I x} (hW : CMDiff ∞ (T% W)) (q : M × N)
      (u : TangentSpace (I.prod J) q) :
      tangentSpaceProdEquiv q (cov (prodVectorField W 0) q u) =
        (D W q.1 (tangentSpaceProdEquiv q u).1,
          (mvfderiv I f q.1 (W q.1) / f q.1) • (tangentSpaceProdEquiv q u).2) := by
    simpa [cov, D, (leviCivitaConnection J N).isCovariantDerivativeOnUniv.zero] using
      h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField
        (hf.mdifferentiableAt (by simp)) (hW.mdifferentiableAt (by simp))
        (h0N.mdifferentiableAt (by simp)) u
  have hv (q : M × N) : cov (prodVectorField 0 V) q (prodVectorField X 0 q) =
      (mvfderiv I f q.1 (X q.1) / f q.1) • prodVectorField 0 V q := by
    apply (tangentSpaceProdEquiv q).injective
    rw [map_smul, tangentSpaceProdEquiv_prodVectorField]
    simpa [cov, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.zero,
      tangentSpaceProdEquiv_prodVectorField] using
      h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField
        (hf.mdifferentiableAt (by simp)) (h0M.mdifferentiableAt (by simp))
        (hV.mdifferentiableAt (by simp)) (prodVectorField X 0 q)
  have hVY : (fun q ↦ cov (prodVectorField Y 0) q (prodVectorField 0 V q)) =
      (a ∘ (Prod.fst : M × N → M)) • prodVectorField (I := I) (M := M) 0 V := by
    funext q
    apply (tangentSpaceProdEquiv q).injective
    simp only [Pi.smul_apply', Function.comp_apply, map_smul,
      tangentSpaceProdEquiv_prodVectorField]
    simpa [a] using hh hY q (prodVectorField 0 V q)
  have hXYeq : (fun q ↦ cov (prodVectorField Y 0) q (prodVectorField X 0 q)) =
      prodVectorField (fun x ↦ D Y x (X x)) 0 := by
    funext q
    apply (tangentSpaceProdEquiv q).injective
    rw [tangentSpaceProdEquiv_prodVectorField]
    simpa using hh hY q (prodVectorField X 0 q)
  -- Horizontal and vertical lifts commute.
  have hbracket : mlieBracket (I.prod J) (prodVectorField X 0) (prodVectorField 0 V) p = 0 := by
    have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
    have : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
    apply (tangentSpaceProdEquiv p).injective
    rw [mlieBracket_prodVectorField (hX.mdifferentiableAt (by simp))
      (h0M.mdifferentiableAt (by simp)) (h0N.mdifferentiableAt (by simp))
      (hV.mdifferentiableAt (by simp))]
    simp only [map_zero, tangentSpaceProdEquiv_prodVectorField, mlieBracket_zero_right,
      mlieBracket_zero_left, Pi.zero_apply, Prod.mk_zero_zero]
  -- The derivative of `Y f / f` and the two connection corrections combine into `Hess f / f`.
  have hcoeff :
      a p.1 * (mvfderiv I f p.1 (X p.1) / f p.1) +
          mvfderiv I a p.1 (X p.1) -
          mvfderiv I f p.1 (D Y p.1 (X p.1)) / f p.1 =
        hessian I f p.1 (X p.1) (Y p.1) / f p.1 := by
    rw [hessian_apply_eq_mvfderiv_sub p.1 (hf.of_le (by simp)).contMDiffAt X Y
      (hY.mdifferentiableAt (by simp))]
    have hinv : mvfderiv I (fun x ↦ (f x)⁻¹) p.1 (X p.1) =
        -(f p.1 ^ 2)⁻¹ * mvfderiv I f p.1 (X p.1) := by
      simpa only [Function.comp_def, fderiv_inv, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, mul_comm] using
        (mvfderiv_comp_apply_of_differentiableAt
          (differentiableAt_inv hf₀) (hf.mdifferentiableAt (by simp)) (X p.1))
    dsimp only [a]
    simp only [div_eq_mul_inv]
    rw [mvfderiv_fun_mul (g := fun x ↦ (f x)⁻¹) (hdY.mdifferentiableAt (by simp))
      ((hf.mdifferentiableAt (by simp)).inv hf₀)]
    simp only [add_apply, smul_apply, smul_eq_mul, hinv]
    dsimp only [D]
    field_simp [hf₀]
    ring
  -- Substitute these three derivatives in the definition of curvature.
  rw [curvatureOperator_apply, hVY, hXYeq, hbracket, map_zero, sub_zero,
    cov.isCovariantDerivativeOnUniv.leibniz
      ((contMDiff_prodVectorField h0M hV).mdifferentiableAt (by simp))
      ((ha.comp p contMDiffAt_fst).mdifferentiableAt (by simp))]
  apply (tangentSpaceProdEquiv p).injective
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    mvfderiv_comp_fst_apply, prodVectorField_fst, Function.comp_apply, map_add, map_sub,
    map_smul, hv, smul_smul]
  rw [hh hXY]
  simp only [tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply, map_zero, Prod.smul_mk,
    smul_zero, Prod.mk_add_mk, Prod.mk_sub_mk, zero_add, sub_zero]
  rw [← add_smul, ← sub_smul, hcoeff]

variable [T2Space M] [T2Space N]

/-- In a warped product, `R(X,V)Y = (Hess f(X,Y) / f) V` for horizontal vectors `X, Y`
and a vertical vector `V`. The Hessian is computed on the base. -/
theorem IsWarpedProduct.tangentSpaceProdEquiv_curvatureTensor_horizontal_vertical_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hf₀ : f p.1 ≠ 0) (u w : TangentSpace I p.1) (v : TangentSpace J p.2) :
    tangentSpaceProdEquiv p
        ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
          ((tangentSpaceProdEquiv p).symm (u, 0))
          ((tangentSpaceProdEquiv p).symm (0, v))
          ((tangentSpaceProdEquiv p).symm (w, 0))) =
      (0, (hessian I f p.1 u w / f p.1) • v) := by
  obtain ⟨X, hX, hXp⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, hYp⟩ := exists_contMDiff_section_eq I E ∞ w
  obtain ⟨V, hV, hVp⟩ := exists_contMDiff_section_eq J F ∞ v
  have h0M : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) :=
    contMDiff_zeroSection ℝ (TangentSpace I)
  have h0N : CMDiff ∞ (T% (0 : Π y : N, TangentSpace J y)) :=
    contMDiff_zeroSection ℝ (TangentSpace J)
  have hR := h.curvatureOperator_horizontal_vertical_horizontal hf hX hY hV p hf₀
  rw [← curvatureTensor_apply _ p (contMDiff_prodVectorField hX h0N)
    (contMDiff_prodVectorField h0M hV)
    (contMDiff_prodVectorField hY h0N)] at hR
  have hvalue (A : Π x : M, TangentSpace I x) (B : Π y : N, TangentSpace J y) :
      prodVectorField A B p = (tangentSpaceProdEquiv p).symm (A p.1, B p.2) := by
    apply (tangentSpaceProdEquiv p).injective
    rw [tangentSpaceProdEquiv_prodVectorField, ContinuousLinearEquiv.apply_symm_apply]
  have := congrArg (tangentSpaceProdEquiv p) hR
  simpa only [map_smul, tangentSpaceProdEquiv_prodVectorField, hvalue, hXp, hYp, hVp,
    Pi.zero_apply, ContinuousLinearEquiv.apply_symm_apply, Prod.smul_mk, smul_zero] using this

/-- The mixed metric curvature component of a warped product is minus the base Hessian
paired with the vertical metric: `⟨R(X,V)W,Y⟩ = -f Hess f(X,Y) ⟨V,W⟩_N`. -/
theorem IsWarpedProduct.inner_curvatureTensor_horizontal_vertical_vertical_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hf₀ : f p.1 ≠ 0) (u w : TangentSpace I p.1) (v z : TangentSpace J p.2) :
    ⟪(leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (0, v))
        ((tangentSpaceProdEquiv p).symm (0, z)),
      (tangentSpaceProdEquiv p).symm (w, 0)⟫_ℝ =
      -f p.1 * hessian I f p.1 u w * ⟪v, z⟫_ℝ := by
  rw [(isMetricCompatible_leviCivitaConnection (I.prod J)).inner_curvatureTensor_eq_neg,
    h.inner_eq, ContinuousLinearEquiv.apply_symm_apply,
    h.tangentSpaceProdEquiv_curvatureTensor_horizontal_vertical_horizontal hf p hf₀]
  simp only [inner_zero_left, zero_add, inner_smul_right]
  rw [real_inner_comm z v]
  field_simp [hf₀]

/-- A mixed plane in a warped product has sectional curvature
`-Hess f(X,X) / (f |X|²)`. Both spanning vectors are nonzero; no normalization is required. -/
theorem IsWarpedProduct.sectionalCurvature_horizontal_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hf₀ : f p.1 ≠ 0) (u : TangentSpace I p.1) (v : TangentSpace J p.2)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (I.prod J)) p
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (0, v)) =
      -hessian I f p.1 u u / (f p.1 * ‖u‖ ^ 2) := by
  rw [sectionalCurvature_apply,
    h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p hf₀,
    Matrix.real_det_gram_fin_two]
  simp only [h.inner_eq, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
    inner_zero_right, zero_add, add_zero, mul_zero, real_inner_self_eq_norm_sq]
  field_simp [hf₀, norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hv]
  ring

end TauCeti.Manifold
