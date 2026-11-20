/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Chart
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability

/-!
# The Weyl–Schouten theorem on Riemannian manifolds

This file proves the Weyl–Schouten theorem characterizing locally conformally flat metrics on smooth
Riemannian manifolds:

* In dimension `n ≥ 4`, a smooth Riemannian metric `g` on a boundaryless manifold is locally
  conformally flat if and only if its Weyl tensor vanishes identically.
* In dimension `n = 3`, a smooth Riemannian metric `g` on a boundaryless manifold is locally
  conformally flat if and only if its Cotton tensor vanishes identically.
* Uniformly away from dimension `2` (`n ≠ 2`), `g` is locally conformally flat if and only if both
  its Weyl and Cotton tensors vanish identically.

Each theorem is first proved as a germ equivalence around an arbitrary interior point `x₀` of a
manifold (allowing nonempty boundary): away from dimension `2`, existence of a smooth positive
conformal factor flattening `g` near `x₀` is equivalent to vanishing of the Weyl and Cotton tensors
in a neighbourhood of `x₀` (hence to vanishing of Weyl alone for `n ≥ 4`, by the divergence
identity `div W = (n - 3) C`, and to vanishing of Cotton alone for `n = 3`, where `W` vanishes
identically). Dimension `2` is excluded from the Weyl–Schouten equivalences because the
`(2 - 2)⁻¹ = 0` convention in `CovariantDerivative.schoutenTensor` sets `P = 0` and `C = 0`, so
`CovariantDerivative.weylTensor` equals the full Riemann curvature tensor rather than vanishing on
curved surfaces.

Moreover, in every dimension (`n ≥ 0`), if `W` and `C` vanish near an interior point `x₀` (which in
dimension `2` means `g` is already flat near `x₀`, since `P = 0` and `W = Rm` by `(2 - 2)⁻¹ = 0`),
for any prescribed value `c : ℝ` and tangent vector `ξ` at `x₀` there is a smooth function
`φ : M → ℝ` with `φ x₀ = c` and `grad φ x₀ = ξ` making `e^(2φ) g` flat near `x₀` (via Frobenius
integration of `Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` for `n ≥ 3`, harmonicity of affine functions
in flat coordinates for `n = 2`, and automatic flatness for `n ≤ 1`). Consequently, any metric that
is conformally flat near an interior point `x₀` admits a smooth positive flattening conformal factor
`f` normalized simultaneously to first order (`f x₀ = 1` and `grad f x₀ = 0`), with no dimension
bound.

## Main declarations

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero`: local conformal flattening `e^(2φ) g`
  with prescribed value and gradient of `φ` at an interior point when `W` and `C` vanish nearby, in
  all dimensions (in dimension `2`, `W = Rm` by `(2 - 2)⁻¹ = 0`, so `W = 0` assumes `g` is already
  flat near `x₀`).
* `isLocallyConformallyFlatAt_iff_eventually_weylTensor_and_cottonTensor_eq_zero_of_isInteriorPoint`
  (`n ≠ 2`), `isLocallyConformallyFlatAt_iff_eventually_weylTensor_eq_zero_of_isInteriorPoint`
  (`n ≥ 4`), and `isLocallyConformallyFlatAt_iff_eventually_cottonTensor_eq_zero_of_isInteriorPoint`
  (`n = 3`): pointwise Weyl–Schouten equivalences at an interior point.
* `exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero_of_isInteriorPoint` and
  `exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero` (in both
  `IsLocallyConformallyFlatAt` and `IsLocallyConformallyFlat`): existence of a positive flattening
  conformal factor with `f x₀ = 1` and `mgradient I f x₀ = 0`, in all dimensions.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero` (`n ≠ 2`),
  `isLocallyConformallyFlat_iff_weylTensor_eq_zero` (`n ≥ 4`), and
  `isLocallyConformallyFlat_iff_cottonTensor_eq_zero` (`n = 3`): the global Weyl–Schouten theorem on
  boundaryless manifolds, together with negated existential forms
  `not_isLocallyConformallyFlat_iff_exists_weylTensor_ne_zero` and
  `not_isLocallyConformallyFlat_iff_exists_cottonTensor_ne_zero`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Filter Set TopologicalSpace TauCeti.Manifold
open scoped ContDiff Manifold Topology TauCeti

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

section ModelSurface

/-- On a `2`-dimensional real inner-product space `F`, rescaling the Euclidean metric by
`e^(2 (c + ⟪v₀, ·⟫))` yields a flat metric, since `z ↦ c + ⟪v₀, z⟫` is harmonic. -/
private theorem curvatureTensor_rescale_exp_inner_model_space_eq_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ F = 2) (c : ℝ) (v₀ : F) (z : F) :
    (let gF := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
     let hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun y : F ↦ c + Inner.inner ℝ v₀ y) :=
       contMDiff_const.add ((innerSL ℝ v₀).contDiff.contMDiff)
     let hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun y : F ↦ Real.exp (2 * (c + Inner.inner ℝ v₀ y))) :=
       Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hψ)
     letI : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) :=
       ⟨(gF.rescale _ hf (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩
     (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor z) = 0 := by
  let gF := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
  let ψ : F → ℝ := fun y ↦ c + Inner.inner ℝ v₀ y
  have hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ ψ :=
    contMDiff_const.add ((innerSL ℝ v₀).contDiff.contMDiff)
  have hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun y ↦ Real.exp (2 * ψ y)) :=
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hψ)
  have hgrad_diff : DifferentiableAt ℝ (gradient ψ) z := by
    have hgrad_eq : gradient ψ = fun _ ↦ v₀ := funext fun y ↦ by
      simp [ψ]
    rw [hgrad_eq]
    exact differentiableAt_const v₀
  have hm := toRiemannianMetric_ofLE (riemannianMetricVectorSpace F) (le_top : (∞ : ℕ∞ω) ≤ ω)
  have hscalF : gF.scalarCurvature z = 0 := by
    rw [gF.scalarCurvature_eq_scalarCurvature_leviCivitaConnection hm.symm,
      scalarCurvature_leviCivitaConnection_model_space]
  have hΔ : (letI : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) := ⟨gF.toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ, F) ψ z) = 0 := by
    let _ : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) := ⟨gF.toRiemannianMetric⟩
    let _ := Bundle.instIsContMDiffRiemannianBundle (gF.ofLE (by simp : (1 : ℕ∞ω) ≤ ∞))
    rw [laplaceBeltrami_eq_laplacian_of_eq (inst := ⟨gF.toRiemannianMetric⟩) hm hgrad_diff,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    have hfd : fderiv ℝ ψ = fun _ ↦ innerSL ℝ v₀ :=
      funext fun y ↦ (((innerSL ℝ v₀).hasFDerivAt).const_add c).fderiv
    simp [iteratedFDeriv_two_apply, hfd]
  have hscal : (gF.rescale (fun y ↦ Real.exp (2 * ψ y)) hf
      (fun _ ↦ Real.exp_pos _)).scalarCurvature z = 0 := by
    rw [gF.scalarCurvature_rescale_of_finrank_eq_two hF hf (fun _ ↦ Real.exp_pos _)
      (fun _ ↦ rfl) z, hscalF, hΔ]
    simp
  let gRes := gF.rescale (fun y ↦ Real.exp (2 * ψ y)) hf (fun _ ↦ Real.exp_pos _)
  let _ : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) := ⟨gRes.toRiemannianMetric⟩
  ext w u v
  rw [CovariantDerivative.curvatureTensor_eq_scalarCurvature_div_two_smul _
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection 𝓘(ℝ, F))
    (by rw [TauCeti.finrank_tangentSpace, hF]), ← gRes.scalarCurvature_def z, hscal]
  simp

end ModelSurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-! ### Interior-point solvability and germ Weyl–Schouten equivalences -/

/-- If `fW : W → F` is a local Riemannian isometry from `(W, g|_W)` into a `2`-dimensional real
inner-product space `F` and `G : M → ℝ` agrees near `xW : W` with `z ↦ c + ⟪v₀, fW z⟫`, then
`e^(2G) g` has vanishing curvature tensor near `(xW : M)`. -/
private theorem eventually_curvatureTensor_rescale_exp_eq_zero_of_isLocalRiemannianIsometry_two
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ F = 2)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} (xW : W) {fW : W → F}
    (hfW : letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
        ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩;
      TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) fW)
    (c : ℝ) (v₀ : F) {G : M → ℝ} (hG : ContMDiff I 𝓘(ℝ) ∞ G)
    (hG_sub : (G ∘ (Subtype.val : W → M)) =ᶠ[𝓝 xW]
      (fun z ↦ c + Inner.inner ℝ v₀ z) ∘ fW) :
    ∀ᶠ y in 𝓝 (xW : M),
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun z ↦ Real.exp (2 * G z))
            (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hG))
            (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
    ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
  let ψ : F → ℝ := fun z ↦ c + Inner.inner ℝ v₀ z
  have hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ ψ :=
    contMDiff_const.add ((innerSL ℝ v₀).contDiff.contMDiff)
  let gF := (riemannianMetricVectorSpace F).ofLE (m := ∞) le_top
  have hfF : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun z ↦ Real.exp (2 * ψ z)) :=
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hψ)
  have hfW_smooth := hfW.contMDiff
  have hfW_inv := hfW.isInvertible_mfderiv
  have hfW_inner := hfW.inner_mfderiv
  let gWRes := (g.restrictOpenTangentSpace W).rescale (fun y : W ↦ Real.exp (2 * ψ (fW y)))
    (hfF.comp hfW_smooth) (fun _ ↦ Real.exp_pos _)
  have hWRes_flat (y : W) : (letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
        ⟨gWRes.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I W).curvatureTensor y) = 0 := by
    let gFRes := gF.rescale (fun z ↦ Real.exp (2 * ψ z)) hfF (fun _ ↦ Real.exp_pos _)
    let _ : RiemannianBundle (fun z : W ↦ TangentSpace I z) := ⟨gWRes.toRiemannianMetric⟩
    let _ : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) := ⟨gFRes.toRiemannianMetric⟩
    let _ := Bundle.instIsContMDiffRiemannianBundle gFRes
    have hfW_res : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) fW :=
      { contMDiff := hfW_smooth
        isInvertible_mfderiv := hfW_inv
        inner_mfderiv := fun q u v ↦ by
          have hq := hfW_inner q u v
          rw [inner_riemannianBundle (g.restrictOpenTangentSpace W) q u v] at hq
          rw [inner_riemannianBundle gFRes, inner_riemannianBundle gWRes,
            rescale_inner, rescale_inner, ofLE_inner]
          exact congrArg (Real.exp (2 * ψ (fW q)) * ·) hq }
    exact (hfW_res.curvatureTensor_eq_zero_iff y).1
      (curvatureTensor_rescale_exp_inner_model_space_eq_zero hF c v₀ _)
  have hGexp : ContMDiff I 𝓘(ℝ) ∞ (fun z ↦ Real.exp (2 * G z)) :=
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hG)
  exact (g.eventually_curvatureTensor_rescale_eq_zero_iff_of_eventuallyEq_opens xW
    hGexp (fun _ ↦ Real.exp_pos _) (hfF.comp hfW_smooth) (fun _ ↦ Real.exp_pos _)
    (hG_sub.fun_comp (fun t ↦ Real.exp (2 * t)))).2
    (Eventually.of_forall hWRes_flat)

/-- Surface case (`dim = 2`) of
`exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint`: when `W = 0` near an
interior point `x₀`, `g` is already flat near `x₀` (since `P = 0` in dimension `2`), and pulling
back an affine function along a local Euclidean isometry produces `φ` with prescribed value and
gradient making `e^(2φ) g` flat near `x₀`. -/
private theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_finrank_eq_two
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 2) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x₀ = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x₀ = ξ) ∧
      ∀ᶠ y in 𝓝 x₀,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
              (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  have hflat : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
    hW.mono fun y hyW ↦
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (CovariantDerivative.curvatureTensor_eq_zero_iff_weylTensor_eq_zero_and_schoutenTensor_eq_zero
        _ y).2 ⟨hyW, by
          ext; simp [CovariantDerivative.schoutenTensor_apply, TauCeti.finrank_tangentSpace, hn]⟩
  obtain ⟨W, hx₀W, r, _, Ψ, hΨ₀⟩ :=
    (g.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hx₀).1 hflat
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let B : Opens F := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  let xW : W := ⟨x₀, hx₀W⟩
  let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
    ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
  have hfW : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) ((Subtype.val : B → F) ∘ Ψ) :=
    (TauCeti.IsLocalRiemannianIsometry.subtype_val B).comp Ψ.isLocalRiemannianIsometry
  obtain ⟨e₀, he₀⟩ := hfW.exists_linearIsometryEquiv_eq_mfderiv xW
  let v₀ : F := NormedSpace.fromTangentSpace ((Subtype.val : B → F) (Ψ xW))
    (e₀ ((tangentSpaceOpenEquiv (I := I) xW).symm ξ))
  let ψ : F → ℝ := fun z ↦ c + Inner.inner ℝ v₀ z
  have hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ ψ :=
    contMDiff_const.add ((innerSL ℝ v₀).contDiff.contMDiff)
  obtain ⟨G, hG_sub⟩ := ((hψ.comp hfW.contMDiff).of_le
    (by simp : (⊤ : ℕ∞) ≤ ∞)).exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := xW)
  refine ⟨G, G.contMDiff,
    by simpa [Function.comp_apply, ψ, xW, hΨ₀] using hG_sub.self_of_nhds, ?_,
    eventually_curvatureTensor_rescale_exp_eq_zero_of_isLocalRiemannianIsometry_two
      (by simp [F, hn]) g xW hfW c v₀ G.contMDiff hG_sub⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hgrad_ψ0 : mgradient 𝓘(ℝ, F) ψ (((Subtype.val : B → F) ∘ Ψ) xW) =
      e₀ ((tangentSpaceOpenEquiv (I := I) xW).symm ξ) := by
    rw [mgradient_eq_gradient]
    simp only [ψ, TauCeti.gradient_const_add, TauCeti.gradient_inner_const_left]
    exact NormedSpace.fromTangentSpace_apply (E := F) _ _
  have hιW := g.isLocalRiemannianIsometry_restrictOpenTangentSpace W
  have h2 : mgradient I ((G : M → ℝ) ∘ Subtype.val) xW =
      mgradient I (ψ ∘ ((Subtype.val : B → F) ∘ Ψ)) xW := by
    simp only [mgradient_def, hG_sub.mvfderiv_eq]
  refine (hιW.mfderiv_mgradient_comp (x := xW) (G.contMDiff.mdifferentiableAt (by simp))).symm.trans
    ?_
  rw [h2, TauCeti.Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    ← (tangentSpaceOpenEquiv (I := I) xW).apply_symm_apply ξ]
  congr 1
  apply (hfW.mfderiv_injective xW)
  rw [hfW.mfderiv_mgradient_comp (hψ.mdifferentiableAt (by simp)), hgrad_ψ0, he₀]

/-- **Local conformal flattening with prescribed first jet at an interior point.** In every
dimension, near an interior point `x₀` where the Weyl and Cotton tensors vanish in a neighbourhood
(note that in dimension `2` the `(2 - 2)⁻¹ = 0` convention in `CovariantDerivative.schoutenTensor`
gives `P = 0` and `W = Rm`, so the hypothesis `W = 0` means `g` is already flat near `x₀`), for
every `c : ℝ` and `ξ : TangentSpace I x₀` there is a smooth function `φ : M → ℝ` with `φ x₀ = c`
and `grad φ x₀ = ξ` such that `e^(2φ) g` is flat near `x₀`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x₀ = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x₀ = ξ) ∧
      ∀ᶠ y in 𝓝 x₀,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
              (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  by_cases hn2 : Module.finrank ℝ E = 2
  · exact g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_finrank_eq_two hn2 hx₀ hW c ξ
  · obtain ⟨φ, hφ, hval, hgrad, hsol⟩ :=
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI := Bundle.instIsContMDiffRiemannianBundle g
        exists_eventually_hessian_eq_of_isInteriorPoint hx₀ hW hC c ξ)
    refine ⟨φ, hφ, hval, hgrad, ?_⟩
    rcases lt_or_gt_of_ne hn2 with hn1 | hn3
    · refine Eventually.of_forall fun y ↦ ?_
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
          (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
          (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩
      exact (CovariantDerivative.leviCivitaConnection I M).curvatureTensor_eq_zero_of_finrank_le_one
        y (by rw [TauCeti.finrank_tangentSpace]; omega)
    · filter_upwards [hW, hsol] with y hyW hy
      exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
        (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)) (fun _ ↦ Real.exp_pos _)
        (fun _ ↦ rfl) hn3 y).2 ⟨hyW, hy⟩

/-- **Pointwise Weyl–Schouten equivalence away from dimension two.** At an interior point `x₀` of
dimension `n ≠ 2`, `g` is locally conformally flat at `x₀` if and only if both its Weyl and Cotton
tensors vanish near `x₀`. -/
theorem
    isLocallyConformallyFlatAt_iff_eventually_weylTensor_and_cottonTensor_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E ≠ 2) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    g.IsLocallyConformallyFlatAt x₀ ↔
      (∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0) ∧
      (∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0) := by
  constructor
  · intro hg
    exact ⟨hg.eventually.mono fun _ hy ↦ hy.weylTensor_eq_zero hn,
      hg.eventually.mono fun _ hy ↦ hy.cottonTensor_eq_zero⟩
  · rintro ⟨hW, hC⟩
    obtain ⟨φ, hφ, -, -, hflat⟩ :=
      g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hx₀ hW hC 0 0
    exact g.isLocallyConformallyFlatAt_iff.2 ⟨fun z ↦ Real.exp (2 * φ z),
      Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ), fun _ ↦ Real.exp_pos _, hflat⟩

/-- **Pointwise Weyl–Schouten equivalence in dimension at least four.** At an interior point `x₀` of
dimension `n ≥ 4`, `g` is locally conformally flat at `x₀` if and only if its Weyl tensor vanishes
near `x₀`. -/
theorem isLocallyConformallyFlatAt_iff_eventually_weylTensor_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    g.IsLocallyConformallyFlatAt x₀ ↔
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0 := by
  rw [
    isLocallyConformallyFlatAt_iff_eventually_weylTensor_and_cottonTensor_eq_zero_of_isInteriorPoint
      g (by omega) hx₀]
  refine and_iff_left_of_imp fun hW ↦ hW.eventually_nhds.mono fun y hyW ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ := Bundle.instIsContMDiffRiemannianBundle g
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact hcov.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) (by omega) (by omega) hyW

/-- **Pointwise Weyl–Schouten equivalence in dimension three.** At an interior point `x₀` of
dimension `3`, `g` is locally conformally flat at `x₀` if and only if its Cotton tensor vanishes
near `x₀`. -/
theorem isLocallyConformallyFlatAt_iff_eventually_cottonTensor_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    g.IsLocallyConformallyFlatAt x₀ ↔
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0 := by
  rw [
    isLocallyConformallyFlatAt_iff_eventually_weylTensor_and_cottonTensor_eq_zero_of_isInteriorPoint
      g (by omega) hx₀]
  refine and_iff_right (Eventually.of_forall fun y ↦ ?_)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ := Bundle.instIsContMDiffRiemannianBundle g
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
    (cov := CovariantDerivative.leviCivitaConnection I M) hcov y
    (by rw [TauCeti.finrank_tangentSpace, hn])

namespace IsLocallyConformallyFlatAt

/-- **First-order normalized flattening conformal factor at an interior point.** In every dimension,
if `g` is locally conformally flat at an interior point `x₀`, then there is a smooth positive
function `f : M → ℝ` with `f x₀ = 1` and `grad f x₀ = 0` such that `f g` is flat near `x₀`. -/
theorem exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero_of_isInteriorPoint
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x₀ : M}
    (hg : g.IsLocallyConformallyFlatAt x₀) (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      f x₀ = 1 ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I f x₀ = 0) ∧
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  obtain ⟨f₁, hf₁, hf₁_pos, hf₁_one, hflat₁⟩ :=
    hg.exists_apply_eq_one_and_eventually_curvatureTensor_rescale_eq_zero
  let g₁ := g.rescale f₁ hf₁ hf₁_pos
  let ξ₀ : TangentSpace I x₀ :=
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩;
      -(2⁻¹ : ℝ) • mgradient I f₁ x₀)
  obtain ⟨φ, hφ, hφ₀, hgrad₀, hflat⟩ :=
    g₁.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hx₀
      (hflat₁.mono fun y hy ↦
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩;
          CovariantDerivative.weylTensor_eq_zero_of_curvatureTensor_eq_zero _ y hy))
      (hflat₁.eventually_nhds.mono fun y hy ↦
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩;
          CovariantDerivative.cottonTensor_eq_zero_of_eventually_curvatureTensor_eq_zero _ hy))
      0 ξ₀
  have hexp : ContMDiff I 𝓘(ℝ) ∞ (fun z ↦ Real.exp (2 * φ z)) :=
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)
  have hf : ContMDiff I 𝓘(ℝ) ∞ (fun z ↦ Real.exp (2 * φ z) * f₁ z) := hexp.mul hf₁
  have hf_pos (z : M) : 0 < Real.exp (2 * φ z) * f₁ z := mul_pos (Real.exp_pos _) (hf₁_pos z)
  have hEq : g.rescale (fun z ↦ Real.exp (2 * φ z) * f₁ z) hf hf_pos =
      g₁.rescale (fun z ↦ Real.exp (2 * φ z)) hexp (fun _ ↦ Real.exp_pos _) :=
    (g.rescale_rescale (hf := hf₁) (hf_pos := hf₁_pos) _ hexp (fun _ ↦ Real.exp_pos _)).symm
  refine ⟨fun z ↦ Real.exp (2 * φ z) * f₁ z, hf, hf_pos, by simp [hφ₀, hf₁_one], ?_, ?_⟩
  · have hmvφ (v : TangentSpace I x₀) :
        mvfderiv I φ x₀ v = -(2⁻¹ : ℝ) * mvfderiv I f₁ x₀ v := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
      rw [← inner_mgradient, hgrad₀]
      simp only [ξ₀, neg_smul, inner_neg_left, real_inner_smul_left, inner_mgradient, neg_mul]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
    have hd : HasDerivAt (fun t : ℝ ↦ Real.exp (2 * t)) (Real.exp (2 * φ x₀) * (2 * 1)) (φ x₀) :=
      (Real.hasDerivAt_exp (2 * φ x₀)).comp (φ x₀) ((hasDerivAt_id (φ x₀)).const_mul 2)
    have hexp_mv : mvfderiv I (fun z ↦ Real.exp (2 * φ z)) x₀ v = 2 * mvfderiv I φ x₀ v := by
      rw [← Function.comp_def (fun t : ℝ ↦ Real.exp (2 * t)) φ,
        TauCeti.mvfderiv_scalar_comp (hφ.mdifferentiableAt (by simp)) hd.differentiableAt, hd.deriv]
      simp only [hφ₀, mul_zero, Real.exp_zero, one_mul, mul_one, smul_apply, smul_eq_mul]
    rw [inner_zero_left,
      mvfderiv_fun_mul (hexp.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul,
      hφ₀, hf₁_one, mul_zero, Real.exp_zero, one_mul, hexp_mv, hmvφ v]
    ring
  · refine hflat.mono fun y hy ↦ ?_
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g₁.rescale (fun z ↦ Real.exp (2 * φ z)) hexp
        (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩
    rw [curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
      (congrArg ContMDiffRiemannianMetric.toRiemannianMetric hEq.symm) y]
    exact hy

end IsLocallyConformallyFlatAt

namespace IsLocallyConformallyFlat

/-- **First-order normalized flattening conformal factor at an interior point.** In every dimension,
if `g` is locally conformally flat and `x₀` is an interior point, then there is a smooth positive
function `f : M → ℝ` with `f x₀ = 1` and `grad f x₀ = 0` such that `f g` is flat near `x₀`. -/
theorem exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero_of_isInteriorPoint
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      f x₀ = 1 ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I f x₀ = 0) ∧
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  (hg.isLocallyConformallyFlatAt x₀)
    |>.exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero_of_isInteriorPoint hx₀

end IsLocallyConformallyFlat

/-! ### Global Weyl–Schouten theorem on boundaryless manifolds -/

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Local conformal flattening with prescribed first jet on a boundaryless manifold.** In every
dimension, near a point `x₀` where the Weyl and Cotton tensors vanish in a neighbourhood (note that
in dimension `2` the `(2 - 2)⁻¹ = 0` convention in `CovariantDerivative.schoutenTensor` gives
`P = 0` and `W = Rm`, so the hypothesis `W = 0` means `g` is already flat near `x₀`), for every
`c : ℝ` and `ξ : TangentSpace I x₀` there is a smooth function `φ : M → ℝ` with `φ x₀ = c` and
`grad φ x₀ = ξ` such that `e^(2φ) g` is flat near `x₀`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x₀ = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x₀ = ξ) ∧
      ∀ᶠ y in 𝓝 x₀,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
              (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hW hC c ξ

namespace IsLocallyConformallyFlatAt

/-- **First-order normalized flattening conformal factor at a point of a boundaryless manifold.** In
every dimension, if `g` is locally conformally flat at `x₀`, then there is a smooth positive
function `f : M → ℝ` with `f x₀ = 1` and `grad f x₀ = 0` such that `f g` is flat near `x₀`. -/
theorem exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x₀ : M}
    (hg : g.IsLocallyConformallyFlatAt x₀) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      f x₀ = 1 ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I f x₀ = 0) ∧
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  hg.exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

end IsLocallyConformallyFlatAt

namespace IsLocallyConformallyFlat

/-- **First-order normalized flattening conformal factor on a boundaryless manifold.** In every
dimension, if `g` is locally conformally flat, then around every point `x₀` there is a smooth
positive function `f : M → ℝ` with `f x₀ = 1` and `grad f x₀ = 0` such that `f g` is flat near
`x₀`. -/
theorem exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (x₀ : M) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      f x₀ = 1 ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I f x₀ = 0) ∧
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  hg.exists_apply_eq_one_and_mgradient_eq_zero_and_curvatureTensor_eq_zero_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

end IsLocallyConformallyFlat

/-- **Uniform Weyl–Schouten theorem away from dimension two.** On a boundaryless smooth manifold of
dimension `n ≠ 2`, a smooth Riemannian metric is locally conformally flat if and only if both its
Weyl tensor and its Cotton tensor vanish identically. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E ≠ 2) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  refine ⟨fun hg ↦ ⟨hg.weylTensor_eq_zero hn, hg.cottonTensor_eq_zero⟩, ?_⟩
  rintro ⟨hW, hC⟩
  exact g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.2 fun _ ↦ (
    isLocallyConformallyFlatAt_iff_eventually_weylTensor_and_cottonTensor_eq_zero_of_isInteriorPoint
      g hn BoundarylessManifold.isInteriorPoint).2
      ⟨Eventually.of_forall hW, Eventually.of_forall hC⟩

/-- **Weyl–Schouten theorem in dimension at least four.** On a boundaryless smooth manifold of
dimension at least `4`, a smooth Riemannian metric is locally conformally flat if and only if its
Weyl tensor vanishes identically. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) := by
  refine ⟨fun hg ↦ hg.weylTensor_eq_zero (by omega),
    fun hW ↦ g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.2 fun _ ↦ ?_⟩
  exact (g.isLocallyConformallyFlatAt_iff_eventually_weylTensor_eq_zero_of_isInteriorPoint
    hn BoundarylessManifold.isInteriorPoint).2 (Eventually.of_forall hW)

/-- **Weyl–Schouten theorem in dimension three.** On a boundaryless smooth `3`-manifold, a smooth
Riemannian metric is locally conformally flat if and only if its Cotton tensor vanishes
identically. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  refine ⟨fun hg ↦ hg.cottonTensor_eq_zero,
    fun hC ↦ g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.2 fun _ ↦ ?_⟩
  exact (g.isLocallyConformallyFlatAt_iff_eventually_cottonTensor_eq_zero_of_isInteriorPoint
    hn BoundarylessManifold.isInteriorPoint).2 (Eventually.of_forall hC)

/-- **Characterization of non-locally-conformally-flat metrics in dimension at least four.** On a
boundaryless smooth manifold of dimension at least `4`, a smooth Riemannian metric fails to be
locally conformally flat if and only if its Weyl tensor is nonzero at some point. -/
theorem not_isLocallyConformallyFlat_iff_exists_weylTensor_ne_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    ¬ g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∃ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x ≠ 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn, not_forall]

/-- **Characterization of non-locally-conformally-flat metrics in dimension three.** On a
boundaryless smooth `3`-manifold, a smooth Riemannian metric fails to be locally conformally flat if
and only if its Cotton tensor is nonzero at some point. -/
theorem not_isLocallyConformallyFlat_iff_exists_cottonTensor_ne_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    ¬ g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∃ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x ≠ 0) := by
  rw [g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn, not_forall]

end Boundaryless

end Bundle.ContMDiffRiemannianMetric

/-! ### Further results -/

public section

open Bundle Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **Smooth initial-value family of conformal flattenings around an interior point.** Let `x₀` be
an interior point of `M` near which the Weyl and Cotton tensors of `g` vanish, in dimension at least
`3`. Around any `(c₀, ξ₀) : ℝ × TangentSpace I x₀` there exist open neighbourhoods `W` of `x₀` and
`Q` of `(c₀, ξ₀)` and a smooth family `Φ : M × (ℝ × TangentSpace I x₀) → ℝ` such that for every
`q ∈ Q`, the slice `y ↦ Φ (y, q)` has value `q.1` and `g`-gradient `q.2` at `x₀`, and the rescaled
metric `e^(2 Φ(·, q)) g` has vanishing curvature tensor at every point of `W`. -/
theorem exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (W : Set M) (Q : Set (ℝ × TangentSpace I x₀))
      (Φ : M × (ℝ × TangentSpace I x₀) → ℝ)
      (hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient I (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W,
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * Φ (z, q)))
              (Real.contDiff_exp.comp_contMDiff
                (contMDiff_const.mul (hΦ.comp (contMDiff_id.prodMk contMDiff_const))))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨W₀, Q, Φ, hW₀_open, hx₀W₀, hQ_open, hq₀Q, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_family_of_isInteriorPoint hx₀ hW hC c₀ ξ₀
  obtain ⟨W₁, hW₁_zero, hW₁_open, hx₀W₁⟩ := eventually_nhds_iff.1 hW
  refine ⟨W₀ ∩ W₁, Q, Φ, hΦ, hW₀_open.inter hW₁_open, ⟨hx₀W₀, hx₀W₁⟩, hQ_open, hq₀Q,
    fun q hq ↦ ?_⟩
  obtain ⟨hval, hgrad, hhess⟩ := hsol q hq
  refine ⟨hval, hgrad, fun y hy ↦ ?_⟩
  exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (Real.contDiff_exp.comp_contMDiff
      (contMDiff_const.mul (hΦ.comp (contMDiff_id.prodMk contMDiff_const))))
    (fun _ ↦ Real.exp_pos _) (fun _ ↦ rfl) hn y).2 ⟨hW₁_zero y hy.2, hhess y hy.1⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Smooth initial-value family of conformal flattenings on a boundaryless manifold.** -/
theorem exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (W : Set M) (Q : Set (ℝ × TangentSpace I x₀))
      (Φ : M × (ℝ × TangentSpace I x₀) → ℝ)
      (hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient I (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W,
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * Φ (z, q)))
              (Real.contDiff_exp.comp_contMDiff
                (contMDiff_const.mul (hΦ.comp (contMDiff_id.prodMk contMDiff_const))))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint hW hC c₀ ξ₀

/-- **Converse of the Weyl–Schouten theorem in dimension at least `4`.** On a boundaryless smooth
manifold of dimension `n ≥ 4`, a smooth Riemannian metric whose Weyl tensor vanishes everywhere is
locally conformally flat (Eisenhart 1926, §28; Lee–Parker 1987, p. 43). -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E)
    (hW : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn).2 hW

/-- **Converse of the Cotton–Schouten theorem in dimension `3`.** On a boundaryless smooth
`3`-manifold, a smooth Riemannian metric whose Cotton tensor vanishes everywhere is locally
conformally flat (Cotton 1899, Chapter III, n° 18, p. 412). -/
theorem isLocallyConformallyFlat_of_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3)
    (hC : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn).2 hC

/-- **Weyl–Schouten in dimension at least `4` for an installed `RiemannianBundle`.** -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn

/-- **Cotton–Schouten in dimension `3` for an installed `RiemannianBundle`.** -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
