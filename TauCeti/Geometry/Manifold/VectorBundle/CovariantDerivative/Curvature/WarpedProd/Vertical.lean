/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.WarpedProd
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Vertical curvature of warped products

For the warped metric `g_M + f² g_N`, the curvature on three vertical vectors is vertical:

`R(U,V)W = R_N(U,V)W - |grad f|² (⟪V,W⟫_N U - ⟪U,W⟫_N V)`.

Consequently a vertical two-plane has sectional curvature
`(K_N - |grad f|²) / f²`. The vectors on the right are measured in the original fibre metric,
not its rescaling by `f²`. These formulas supply the vertical components needed when tracing
warped-product curvature. No completeness or curvature assumption on either factor is needed.
The tensor formula includes dependent and zero vectors; the sectional formula requires an
independent pair. The warping function need only be nonzero at the point evaluated.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Proposition 42.
  We use `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`.
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold

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

private theorem IsWarpedProduct.leviCivitaConnection_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {V W : Π y : N, TangentSpace J y} (hW : CMDiff ∞ (T% W)) :
    (fun p ↦ leviCivitaConnection (I.prod J) (M × N) (prodVectorField 0 W) p
      (prodVectorField 0 V p)) =
      prodVectorField 0 (fun y ↦ leviCivitaConnection J N W y (V y)) -
        (fun p : M × N ↦ f p.1 * inner ℝ (V p.2) (W p.2)) •
          prodVectorField (mgradient I f) 0 := by
  funext p
  apply (tangentSpaceProdEquiv (I := I) (J := J) p).injective
  rw [h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := 0) (Y₂ := W)
    (hf.mdifferentiable (by simp) p.1) (mdifferentiableAt_zeroSection ℝ (TangentSpace I))
    (hW.mdifferentiable (by simp) p.2)]
  simp only [Pi.sub_apply, Pi.smul_apply', map_sub, map_smul,
    tangentSpaceProdEquiv_prodVectorField]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Pi.zero_apply, map_zero, zero_sub, smul_zero, sub_zero, zero_div, zero_smul, add_zero]

private theorem IsWarpedProduct.leviCivitaConnection_vertical_sub
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {p : M × N} (hf₀ : f p.1 ≠ 0)
    {U Z : Π y : N, TangentSpace J y} {b : N → ℝ}
    (hZ : CMDiff ∞ (T% Z)) (hb : ContMDiff J 𝓘(ℝ) ∞ b) :
    tangentSpaceProdEquiv (I := I) (J := J) p
      (leviCivitaConnection (I.prod J) (M × N)
        (prodVectorField 0 Z - (fun q : M × N ↦ f q.1 * b q.2) •
          prodVectorField (mgradient I f) 0) p (prodVectorField 0 U p)) =
      (-(f p.1 * (inner ℝ (U p.2) (Z p.2) + mvfderiv J b p.2 (U p.2))) •
          mgradient I f p.1,
        leviCivitaConnection J N Z p.2 (U p.2) -
          (‖mgradient I f p.1‖ ^ 2 * b p.2) • U p.2) := by
  let cov := leviCivitaConnection (I.prod J) (M × N)
  have hgrad := mdifferentiable_mgradient (I := I) (hf.of_le (by simp))
  have hz := (contMDiff_prodVectorField
    (contMDiff_zeroSection ℝ (TangentSpace I)) hZ).mdifferentiable (by simp) p
  have hg := mdifferentiableAt_prodVectorField (hgrad p.1)
    (mdifferentiableAt_zeroSection ℝ (TangentSpace J))
  have hc : MDifferentiableAt (I.prod J) 𝓘(ℝ) (fun q : M × N ↦ f q.1 * b q.2) p :=
    ((hf.mdifferentiable (by simp) p.1).comp p mdifferentiableAt_fst).mul
      ((hb.mdifferentiable (by simp) p.2).comp p mdifferentiableAt_snd)
  have hdb : mvfderiv (I.prod J) (fun q : M × N ↦ f q.1 * b q.2) p
      (prodVectorField 0 U p) = f p.1 * mvfderiv J b p.2 (U p.2) := by
    rw [mvfderiv_fun_mul (I := I.prod J) (f := fun q : M × N ↦ f q.1)
      (g := fun q : M × N ↦ b q.2)
      ((hf.mdifferentiable (by simp) p.1).comp p mdifferentiableAt_fst)
      ((hb.mdifferentiable (by simp) p.2).comp p mdifferentiableAt_snd)]
    simp only [smul_apply, add_apply]
    have hfst := mvfderiv_comp_fst_apply (I := I) (J := J) f p (prodVectorField 0 U p)
    have hsnd := mvfderiv_comp_snd_apply (I := I) (J := J) b p (prodVectorField 0 U p)
    simp only [Function.comp_def] at hfst hsnd
    rw [hfst, hsnd]
    simp only [prodVectorField_fst, prodVectorField_snd, Pi.zero_apply, map_zero,
      smul_eq_mul, mul_zero, add_zero]
  -- Differentiate the vertical field and its horizontal gradient correction separately.
  rw [cov.isCovariantDerivativeOnUniv.sub (σ := prodVectorField 0 Z)
      (σ' := (fun q : M × N ↦ f q.1 * b q.2) • prodVectorField (mgradient I f) 0)
      hz (hc.smul_section hg),
    cov.isCovariantDerivativeOnUniv.leibniz (σ := prodVectorField (mgradient I f) 0)
      (g := fun q : M × N ↦ f q.1 * b q.2) hg hc]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_sub, map_add, map_smul, hdb]
  rw [h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := 0) (Y₂ := Z)
      (hf.mdifferentiable (by simp) p.1) (mdifferentiableAt_zeroSection ℝ (TangentSpace I))
      (hZ.mdifferentiable (by simp) p.2),
    h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField
      (Y₁ := mgradient I f) (Y₂ := 0) (hf.mdifferentiable (by simp) p.1) (hgrad p.1)
      (mdifferentiableAt_zeroSection ℝ (TangentSpace J))]
  simp only [tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply, map_zero,
    inner_zero_right, mul_zero, zero_smul, sub_zero, zero_div, add_zero]
  have hdf : mvfderiv I f p.1 (mgradient I f p.1) = ‖mgradient I f p.1‖ ^ 2 := by
    rw [← inner_mgradient, real_inner_self_eq_norm_sq]
  rw [hdf]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_zero, zero_sub]
  · module
  · simp only [CovariantDerivative.zero, Pi.zero_apply, zero_apply, add_zero, zero_add, smul_smul]
    congr 1
    field_simp [hf₀]

private theorem IsWarpedProduct.curvatureOperator_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {p : M × N} (hf₀ : f p.1 ≠ 0)
    {U V W : Π y : N, TangentSpace J y}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W)) :
    tangentSpaceProdEquiv (I := I) (J := J) p
      ((leviCivitaConnection (I.prod J) (M × N)).curvatureOperator
        (prodVectorField 0 U) (prodVectorField 0 V) (prodVectorField 0 W) p) =
      (0, (leviCivitaConnection J N).curvatureOperator U V W p.2 -
        ‖mgradient I f p.1‖ ^ 2 •
          (inner ℝ (V p.2) (W p.2) • U p.2 - inner ℝ (U p.2) (W p.2) • V p.2)) := by
  have hzero : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) :=
    contMDiff_zeroSection ℝ (TangentSpace I)
  have hVW := (leviCivitaConnection J N).contMDiff_apply hV hW
  have hUW := (leviCivitaConnection J N).contMDiff_apply hU hW
  have hiVW := ContMDiff.inner_bundle (IB := J) (F := F)
    (E := fun y : N ↦ TangentSpace J y) (b := id) hV hW
  have hiUW := ContMDiff.inner_bundle (IB := J) (F := F)
    (E := fun y : N ↦ TangentSpace J y) (b := id) hU hW
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have : IsManifold J (minSmoothness ℝ 2) N := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hdU := hU.mdifferentiable (by simp) p.2
  have hdV := hV.mdifferentiable (by simp) p.2
  have hdW := hW.mdifferentiable (by simp) p.2
  have hm := isMetricCompatible_leviCivitaConnection (I := J) (M := N)
  -- Metric compatibility and torsion-freeness cancel the horizontal curvature component.
  have h₁ := hm.mvfderiv_inner_eq U hdV hdW
  have h₂ := hm.mvfderiv_inner_eq V hdU hdW
  have ht := (torsion_eq_zero_iff (leviCivitaConnection J N)).1
    (torsion_leviCivitaConnection_eq_zero J) hdU hdV
  rw [curvatureOperator_apply, h.leviCivitaConnection_vertical hf hW,
    h.leviCivitaConnection_vertical hf hW,
    mlieBracket_prodVectorField (hzero.mdifferentiable (by simp) p.1)
      (hzero.mdifferentiable (by simp) p.1) hdU hdV,
    mlieBracket_self]
  simp only [map_sub]
  rw [h.leviCivitaConnection_vertical_sub hf hf₀ hVW hiVW,
    h.leviCivitaConnection_vertical_sub hf hf₀ hUW hiUW,
    h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := 0) (Y₂ := W)
      (hf.mdifferentiable (by simp) p.1) (hzero.mdifferentiable (by simp) p.1) hdW]
  simp only [tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply, map_zero, zero_div,
    zero_smul, add_zero]
  apply Prod.ext
  · simp only [Prod.fst_sub]
    rw [h₁, h₂, ← ht, inner_sub_left]
    simp only [real_inner_comm (W p.2)]
    module
  · simp only [Prod.snd_sub, curvatureOperator_apply]
    module

variable [T2Space M] [T2Space N]

/-- On three vertical vectors, warped-product curvature is the fibre curvature minus the
constant-curvature tensor with coefficient `|grad f|²`, and has no horizontal component.
All inner products on the right use the original metric of `N`. -/
theorem IsWarpedProduct.tangentSpaceProdEquiv_curvatureTensor_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hf₀ : f p.1 ≠ 0) (u v w : TangentSpace J p.2) :
    tangentSpaceProdEquiv (I := I) (J := J) p
      ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
        ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, u))
        ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, v))
        ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, w))) =
      (0, (leviCivitaConnection J N).curvatureTensor p.2 u v w -
        ‖mgradient I f p.1‖ ^ 2 • (inner ℝ v w • u - inner ℝ u w • v)) := by
  -- Smooth fibre fields realize arbitrary vectors without choosing product coordinates.
  obtain ⟨U, hU, rfl⟩ := exists_contMDiff_section_eq J F ∞ u
  obtain ⟨V, hV, rfl⟩ := exists_contMDiff_section_eq J F ∞ v
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq J F ∞ w
  have hzero : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) :=
    contMDiff_zeroSection ℝ (TangentSpace I)
  have hp (Y : Π y : N, TangentSpace J y) :
      (tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, Y p.2) = prodVectorField 0 Y p := by
    apply (tangentSpaceProdEquiv (I := I) (J := J) p).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, tangentSpaceProdEquiv_prodVectorField]
    rfl
  rw [hp, hp, hp, curvatureTensor_apply _ p (contMDiff_prodVectorField hzero hU)
    (contMDiff_prodVectorField hzero hV) (contMDiff_prodVectorField hzero hW),
    h.curvatureOperator_vertical hf hf₀ hU hV hW, curvatureTensor_apply _ _ hU hV hW]

/-- A vertical two-plane in `g_M + f² g_N` has sectional curvature
`(K_N - |grad f|²) / f²`. The spanning vectors and `K_N` on the right use the unscaled
fibre metric. Independence is essential: the totalized sectional quotient is zero on
dependent pairs, whereas the displayed correction need not be. -/
theorem IsWarpedProduct.sectionalCurvature_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (hf₀ : f p.1 ≠ 0) (u v : TangentSpace J p.2)
    (huv : LinearIndependent ℝ ![u, v]) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (I.prod J)) p
        ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, u))
        ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, v)) =
      ((leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) p.2 u v - ‖mgradient I f p.1‖ ^ 2) /
          f p.1 ^ 2 := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  have hi (a b : TangentSpace J p.2) :
      inner ℝ (e.symm (0, a)) (e.symm (0, b)) = f p.1 ^ 2 * inner ℝ a b := by
    rw [h.inner_eq]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add]
  have hgram : (Matrix.gram ℝ ![e.symm (0, u), e.symm (0, v)]).det =
      f p.1 ^ 4 * (Matrix.gram ℝ ![u, v]).det := by
    simp only [Matrix.real_det_gram_fin_two, hi]
    ring
  have hD := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr huv
  rw [sectionalCurvature_apply, sectionalCurvature_apply, hgram,
    h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p hf₀]
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add,
    inner_sub_left, real_inner_smul_left]
  have hdet : inner ℝ v v * inner ℝ u u - inner ℝ u v * inner ℝ v u =
      (Matrix.gram ℝ ![u, v]).det := by
    rw [Matrix.real_det_gram_fin_two, real_inner_comm v u]
    ring
  rw [hdet]
  field_simp [hf₀, hD]

end TauCeti.Manifold
