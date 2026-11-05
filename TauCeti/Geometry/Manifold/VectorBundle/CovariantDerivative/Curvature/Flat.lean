/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Analysis.ODE.Frobenius
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Flat connections and local parallel frames

A smooth connection `∇` on a finite-rank real vector bundle `V → M` is *locally flat* near `x₀`
when its curvature tensor vanishes on a neighbourhood of `x₀`. Reading `∇` in a vector-bundle
trivialization and a chart around an interior point `x₀` turns the parallel-section equation
`∇ σ = 0` into a first-order total differential equation `D u z = -Γ z (u z)` whose Frobenius
integrability condition (`TauCeti.IsFrobeniusIntegrableAt`) is precisely the vanishing of the
curvature tensor.

Applying the local Frobenius theorem
(`TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt`) produces smooth local
parallel sections with arbitrary prescribed value in `V x₀`, and applying this to a basis of `V x₀`
produces a smooth local parallel frame (`IsLocalFrameOn`) around `x₀`. Conversely, any local
parallel frame forces `R(X, Y) σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X, Y] σ` to vanish on its domain
without any boundaryless assumption.

When `V` carries a smooth Riemannian bundle metric and `∇` is metric-compatible, parallel sections
have locally constant pairwise inner products
(`CovariantDerivative.IsMetricCompatible.eventuallyEq_inner_const_of_cov_eq_zero`), so propagating
an orthonormal basis of `V x₀` yields a smooth *orthonormal* local parallel frame.

## Main results

* `CovariantDerivative.curvatureTensor_eq_zero_of_isLocalFrameOn`: a smooth local parallel frame on
  an open set forces the curvature tensor to vanish there.
* `CovariantDerivative.exists_contMDiff_apply_eq_and_eventually_cov_eq_zero_of_isInteriorPoint` and
  `CovariantDerivative.exists_contMDiff_apply_eq_and_eventually_cov_eq_zero`: if the curvature
  tensor vanishes near an interior point `x₀`, every vector in `V x₀` extends to a smooth section
  that is parallel near `x₀`.
* `CovariantDerivative.eventually_curvatureTensor_eq_zero_iff_forall_exists_parallel` (and its
  `of_isInteriorPoint` form):
  vanishing of the curvature tensor near `x₀` is equivalent to the existence of local parallel
  sections through every vector of `V x₀`.
* `CovariantDerivative.exists_isLocalFrameOn_parallel_of_isInteriorPoint`,
  `CovariantDerivative.exists_isLocalFrameOn_parallel`, and
  `CovariantDerivative.forall_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn_parallel`:
  characterization of flat connections on open sets by smooth local parallel frames.
* `CovariantDerivative.IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel` (and its
  `of_isInteriorPoint` form):
  existence of smooth orthonormal local parallel frames for flat metric-compatible connections.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Chapter II, §9 (Theorem 9.1).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 7.10 and Proposition 7.11.
* M. Spivak, *A Comprehensive Introduction to Differential Geometry*, Vol. II, 3rd ed.,
  Publish or Perish (1999), Chapter 6.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Module Set Topology TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

namespace CovariantDerivative

section VanishingFromParallel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- If a section `σ` is parallel near `x`, then `R(X, Y) σ` vanishes at `x` for any vector fields
`X` and `Y`. -/
theorem curvatureOperator_eq_zero_of_eventually_cov_eq_zero
    (cov : CovariantDerivative I F V) {X Y : Π y : M, TangentSpace I y} {σ : Π y : M, V y}
    {x : M} (hσ : ∀ᶠ y in 𝓝 x, cov σ y = 0) :
    cov.curvatureOperator X Y σ x = 0 := by
  have hYσ : ∀ᶠ y in 𝓝 x, cov σ y (Y y) = 0 :=
    hσ.mono fun y hy ↦ by rw [hy, zero_apply]
  have hXσ : ∀ᶠ y in 𝓝 x, cov σ y (X y) = 0 :=
    hσ.mono fun y hy ↦ by rw [hy, zero_apply]
  have hd0 : MDiffAt (T% (0 : Π y : M, V y)) x := mdifferentiableAt_zeroSection ℝ V
  have hdY : MDiffAt (T% (fun y ↦ cov σ y (Y y))) x :=
    hd0.congr_of_eventuallyEq (hYσ.mono fun y hy ↦ by simp only [hy, Pi.zero_apply])
  have hdX : MDiffAt (T% (fun y ↦ cov σ y (X y))) x :=
    hd0.congr_of_eventuallyEq (hXσ.mono fun y hy ↦ by simp only [hy, Pi.zero_apply])
  rw [curvatureOperator_apply, hσ.self_of_nhds, zero_apply, sub_zero,
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hdY hd0 univ_mem hYσ,
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hdX hd0 univ_mem hXσ,
    cov.isCovariantDerivativeOnUniv.zero]
  simp

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle ∞ F V I] (cov : CovariantDerivative I F V)
  [ContMDiffCovariantDerivative cov ∞]

/-- Evaluating the curvature tensor at `x` on a vector `w : V x` gives `0` whenever `w` extends
to a smooth section on an open neighbourhood of `x` that is parallel there. -/
theorem curvatureTensor_apply_eq_zero_of_cov_eq_zero {U : Set M} (hU : IsOpen U) {x : M}
    (hx : x ∈ U) {σ : Π y : M, V y} (hσ : CMDiff[U] ∞ (T% σ))
    (hpar : ∀ y ∈ U, cov σ y = 0) (u v : TangentSpace I x) :
    cov.curvatureTensor x u v (σ x) = 0 := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  rw [cov.curvatureTensor_apply_of_contMDiffOn x hU hx hX.contMDiffOn hY.contMDiffOn hσ]
  exact cov.curvatureOperator_eq_zero_of_eventually_cov_eq_zero
    (eventually_of_mem (hU.mem_nhds hx) hpar)

/-- If every vector in the fibre `V x` extends to a smooth section parallel near `x`, then the
curvature tensor of `cov` vanishes at `x`. -/
theorem curvatureTensor_eq_zero_of_forall_exists_parallel {x : M}
    (h : ∀ w : V x, ∃ σ : Π y : M, V y, CMDiff ∞ (T% σ) ∧ σ x = w ∧ ∀ᶠ y in 𝓝 x, cov σ y = 0) :
    cov.curvatureTensor x = 0 := by
  ext u v w
  obtain ⟨σ, hσ, rfl, hpar⟩ := h w
  obtain ⟨U, hUsub, hUopen, hxU⟩ := eventually_nhds_iff.1 hpar
  simpa using cov.curvatureTensor_apply_eq_zero_of_cov_eq_zero hUopen hxU hσ.contMDiffOn hUsub u v

/-- **A local parallel frame forces the curvature tensor to vanish.** If `s` is a smooth local
frame of `V` on an open set `U` and each frame section is parallel on `U`, then
`cov.curvatureTensor` vanishes at every point of `U`. No boundaryless assumption is needed. -/
theorem curvatureTensor_eq_zero_of_isLocalFrameOn {ι : Type*} {s : ι → Π y : M, V y} {U : Set M}
    (hU : IsOpen U) (hs : IsLocalFrameOn I F ∞ s U) (hpar : ∀ i, ∀ y ∈ U, cov (s i) y = 0)
    {x : M} (hx : x ∈ U) :
    cov.curvatureTensor x = 0 := by
  have : FiniteDimensional ℝ (V x) :=
    ((trivializationAt F V x).linearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).symm.finiteDimensional
  let b := hs.toBasisAt hx
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  ext u v w
  rw [← b.sum_repr w, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_smul, hs.toBasisAt_coe hx i,
    cov.curvatureTensor_apply_eq_zero_of_cov_eq_zero hU hx (hs.contMDiffOn i) (hpar i) u v,
    smul_zero]

end VanishingFromParallel

/-! ### Frobenius integrability and local parallel sections -/

/-- For a differentiable bilinear-map-valued field `ΓE : E → F →L[ℝ] E →L[ℝ] F`, vanishing of the
coordinate curvature expression `dΓE(a)(w, c) - dΓE(c)(w, a) + ΓE(ΓE(w, c), a) - ΓE(ΓE(w, a), c)`
at `(z, w)` implies Frobenius integrability of `p ↦ -ΓE p.1 p.2` at `(z, w)`. -/
private theorem isFrobeniusIntegrableAt_neg_clm_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ΓE : E → F →L[ℝ] E →L[ℝ] F} {z : E} (w : F)
    (hΓE_diff : DifferentiableAt ℝ ΓE z)
    (hcurv : ∀ a c : E,
      fderiv ℝ ΓE z a w c - fderiv ℝ ΓE z c w a +
        ΓE z (ΓE z w c) a - ΓE z (ΓE z w a) c = 0) :
    IsFrobeniusIntegrableAt (fun p : E × F ↦ -ΓE p.1 p.2) (z, w) := by
  let f : E × F → E →L[ℝ] F := fun p ↦ -ΓE p.1 p.2
  have hf_deriv : HasFDerivAt f
      (-((ΓE z).comp (ContinuousLinearMap.snd ℝ E F) +
        ((fderiv ℝ ΓE z).comp (ContinuousLinearMap.fst ℝ E F)).flip w)) (z, w) :=
    ((hΓE_diff.hasFDerivAt.comp (z, w) hasFDerivAt_fst).clm_apply hasFDerivAt_snd).neg
  change IsFrobeniusIntegrableAt f (z, w)
  rw [isFrobeniusIntegrableAt_iff, hf_deriv.fderiv]
  intro a c
  have heval (ξ η : E) :
      ((-((ΓE z).comp (ContinuousLinearMap.snd ℝ E F) +
        ((fderiv ℝ ΓE z).comp (ContinuousLinearMap.fst ℝ E F)).flip w)) (ξ, f (z, w) ξ)) η =
        -fderiv ℝ ΓE z ξ w η + ΓE z (ΓE z w ξ) η := by
    simp only [f, neg_apply, add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      map_neg]
    abel
  rw [heval a c, heval c a, ← sub_eq_zero]
  convert neg_eq_zero.2 (hcurv a c) using 1
  abel

section FrobeniusCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

omit [FiniteDimensional ℝ E] [T2Space M] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ (x : M), AddCommGroup (V x)] [∀ (x : M), Module ℝ (V x)]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] cov
  [ContMDiffCovariantDerivative cov ∞] in
private theorem isOpen_inter_preimage_baseSet_extChartAt_symm (x₀ : M) :
    IsOpen (interior (extChartAt I x₀).target ∩
      (extChartAt I x₀).symm ⁻¹' (trivializationAt F V x₀).baseSet) :=
  ((contMDiffOn_extChartAt_symm (n := ∞) x₀).mono
    interior_subset).continuousOn.isOpen_inter_preimage isOpen_interior
    (trivializationAt F V x₀).open_baseSet

private theorem contMDiffOn_bundleChristoffelMap_comp_extChartAt_symm (x₀ : M) :
    letI eV := trivializationAt F V x₀
    letI eT := trivializationAt E (TangentSpace I) x₀
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) ∞
      (fun ζ ↦ bundleChristoffelMap (Module.finBasis ℝ F) eT
        (cov.isCovariantDerivativeOn (s := eV.baseSet)) ((extChartAt I x₀).symm ζ))
      (interior (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' eV.baseSet) := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun eV.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov eV.open_baseSet
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact (contMDiffOn_bundleChristoffelMap (n := ∞) (Module.finBasis ℝ F) eT
      (cov.isCovariantDerivativeOn (s := eV.baseSet))).comp
    ((contMDiffOn_extChartAt_symm (n := ∞) x₀).mono (inter_subset_left.trans interior_subset))
    fun ζ hζ ↦ ⟨hζ.2, by simpa [eT] using (extChartAt I x₀).map_target (interior_subset hζ.1)⟩

/-- Chain rule for `bundleChristoffelMap` composed with `(extChartAt I x₀).symm` at an interior
target point `z`. -/
private theorem fderiv_bundleChristoffelMap_comp_extChartAt_symm (x₀ : M) {z : E}
    (hz : z ∈ interior (extChartAt I x₀).target)
    (hzV : (extChartAt I x₀).symm z ∈ (trivializationAt F V x₀).baseSet) (a : E) :
    letI eV := trivializationAt F V x₀
    letI eT := trivializationAt E (TangentSpace I) x₀
    letI Γ := bundleChristoffelMap (Module.finBasis ℝ F) eT
      (cov.isCovariantDerivativeOn (s := eV.baseSet))
    fderiv ℝ (fun ζ ↦ Γ ((extChartAt I x₀).symm ζ)) z a =
      mvfderiv I Γ ((extChartAt I x₀).symm z) (eT.symm ((extChartAt I x₀).symm z) a) := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  set y := (extChartAt I x₀).symm z with hy_def
  have hzt : z ∈ (extChartAt I x₀).target := interior_subset hz
  have hysrc : y ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hzt
  have hyT : y ∈ eT.baseSet := by simpa [eT] using hysrc
  have hyz : extChartAt I x₀ y = z := (extChartAt I x₀).right_inv hzt
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun eV.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov eV.open_baseSet
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let Γ := bundleChristoffelMap (Module.finBasis ℝ F) eT
    (cov.isCovariantDerivativeOn (s := eV.baseSet))
  have hΓ_mdiff : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ y :=
    ((contMDiffOn_bundleChristoffelMap (n := ∞) (Module.finBasis ℝ F) eT
        (cov.isCovariantDerivativeOn (s := eV.baseSet))).contMDiffAt
      ((eV.open_baseSet.inter eT.open_baseSet).mem_nhds ⟨hzV, hyT⟩)).mdifferentiableAt (by simp)
  have hsymm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm z :=
    (((contMDiffOn_extChartAt_symm (n := ∞) x₀).mono interior_subset).contMDiffAt
      (isOpen_interior.mem_nhds hz)).mdifferentiableAt (by simp)
  have hcomp := mvfderiv_comp_apply_of_eq z hΓ_mdiff hsymm_mdiff hy_def.symm
    ((NormedSpace.fromTangentSpace z).symm a)
  have hsymmL : eT.symm y a =
      mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z ((NormedSpace.fromTangentSpace z).symm a) := by
    have hchart : y ∈ (chartAt H x₀).source := by simpa using hysrc
    rw [← eT.symmL_apply (R := ℝ) hyT, TangentBundle.symmL_trivializationAt hchart, hyz,
      mfderivWithin_of_mem_nhds
        (mem_of_superset (isOpen_interior.mem_nhds hz)
          (interior_subset.trans (extChartAt_target_subset_range x₀)))]
    -- `y` is definitionally `(extChartAt I x₀).symm z`, and `NormedSpace.fromTangentSpace z`
    -- is the identity on `TangentSpace 𝓘(ℝ, E) z = E`.
    rfl
  rw [Function.comp_def, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, ← hsymmL] at hcomp
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hcomp

/-- Vanishing of `cov.curvatureTensor` at `(extChartAt I x₀).symm z` implies Frobenius
integrability of the total differential equation `D u z = -Γ((extChartAt I x₀).symm z)(u z)` at
every fibre point `(z, w)`. -/
private theorem isFrobeniusIntegrableAt_neg_bundleChristoffelMap (x₀ : M) {z : E}
    (hz : z ∈ interior (extChartAt I x₀).target)
    (hzV : (extChartAt I x₀).symm z ∈ (trivializationAt F V x₀).baseSet)
    (hflat : cov.curvatureTensor ((extChartAt I x₀).symm z) = 0) (w : F) :
    letI eV := trivializationAt F V x₀
    letI eT := trivializationAt E (TangentSpace I) x₀
    IsFrobeniusIntegrableAt
      (fun p : E × F ↦ -bundleChristoffelMap (Module.finBasis ℝ F) eT
        (cov.isCovariantDerivativeOn (s := eV.baseSet)) ((extChartAt I x₀).symm p.1) p.2)
      (z, w) := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  have hysrc : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target (interior_subset hz)
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  have hΓE_diff : DifferentiableAt ℝ
      (fun ζ ↦ bundleChristoffelMap (Module.finBasis ℝ F) eT
        (cov.isCovariantDerivativeOn (s := eV.baseSet)) ((extChartAt I x₀).symm ζ)) z :=
    (((contMDiffOn_iff_contDiffOn.1
      (contMDiffOn_bundleChristoffelMap_comp_extChartAt_symm cov x₀)).contDiffAt
        ((isOpen_inter_preimage_baseSet_extChartAt_symm (F := F) (V := V) x₀).mem_nhds
          ⟨hz, hzV⟩)).differentiableAt (by simp))
  refine isFrobeniusIntegrableAt_neg_clm_apply w hΓE_diff fun a c ↦ ?_
  rw [fderiv_bundleChristoffelMap_comp_extChartAt_symm cov x₀ hz hzV a,
    fderiv_bundleChristoffelMap_comp_extChartAt_symm cov x₀ hz hzV c]
  have hcurv := cov.curvatureTensor_symm_trivializationAt_bundle (Module.finBasis ℝ F) x₀
    hzV hysrc a c w
  simp only [hflat, LinearMap.zero_apply] at hcurv
  have h0 := congrArg (eV.continuousLinearMapAt ℝ ((extChartAt I x₀).symm z)) hcurv.symm
  rwa [map_zero, Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hzV,
    eV.apply_mk_symm hzV] at h0

omit [FiniteDimensional ℝ E] [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
/-- Pull back a local coordinate solution `u₀` of `D u₀ z = -Γ((extChartAt I x₀).symm z)(u₀ z)`
around an interior point `x₀` to a local smooth section of `V` parallel on an open neighbourhood of
`x₀`. -/
private theorem exists_contMDiffOn_parallel_of_fderiv_solution {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) {WE : Set E} (hWE : IsOpen WE) (hz₀WE : extChartAt I x₀ x₀ ∈ WE)
    {u₀ : E → F} (hu₀_smooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u₀ WE) (w₀ : V x₀)
    (hu₀_x₀ : u₀ (extChartAt I x₀ x₀) = (trivializationAt F V x₀).continuousLinearMapAt ℝ x₀ w₀)
    (husol : ∀ z ∈ WE,
      letI eV := trivializationAt F V x₀
      letI eT := trivializationAt E (TangentSpace I) x₀
      HasFDerivAt u₀
        (-bundleChristoffelMap (Module.finBasis ℝ F) eT
          (cov.isCovariantDerivativeOn (s := eV.baseSet)) ((extChartAt I x₀).symm z) (u₀ z)) z) :
    ∃ (WM : Set M) (σloc : Π y : M, V y),
      IsOpen WM ∧ x₀ ∈ WM ∧ CMDiff[WM] ∞ (T% σloc) ∧ σloc x₀ = w₀ ∧
      ∀ y ∈ WM, cov σloc y = 0 := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  let φ := extChartPartialDiffeomorph I ∞ x₀
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
  have hx₀φ : x₀ ∈ φ.source := (mem_extChartPartialDiffeomorph_source I ∞ x₀).2 hx₀
  have hφto : CMDiff[φ.source] ∞ (extChartAt I x₀) := by
    simpa only [φ, coe_extChartPartialDiffeomorph] using φ.contMDiffOn_toFun
  let WM : Set M := eV.baseSet ∩ (φ.source ∩ extChartAt I x₀ ⁻¹' WE)
  have hWM : IsOpen WM :=
    eV.open_baseSet.inter (hφto.continuousOn.isOpen_inter_preimage φ.open_source hWE)
  have hx₀WM : x₀ ∈ WM := ⟨hx₀V, hx₀φ, hz₀WE⟩
  set g : M → F := fun y ↦ u₀ (extChartAt I x₀ y) with hg_def
  have hg_smooth : CMDiff[WM] ∞ g :=
    hu₀_smooth.comp (hφto.mono fun _ hy ↦ hy.2.1) fun _ hy ↦ hy.2.2
  let σloc : Π y : M, V y := fun y ↦ eV.symm y (g y)
  have hσloc_smooth : CMDiff[WM] ∞ (T% σloc) :=
    (eV.contMDiffOn_section_iff hWM inter_subset_left).2 <|
      hg_smooth.congr fun y hy ↦ congrArg Prod.snd (eV.apply_mk_symm hy.1 (g y))
  have hσloc_x₀ : σloc x₀ = w₀ := by
    simp only [σloc, g, hu₀_x₀]
    rw [← eV.symmL_apply (R := ℝ) hx₀V, eV.symmL_continuousLinearMapAt hx₀V]
  refine ⟨WM, σloc, hWM, hx₀WM, hσloc_smooth, hσloc_x₀, fun y hy ↦ ?_⟩
  have hysrc : y ∈ (extChartAt I x₀).source :=
    ((extChartPartialDiffeomorph_source I ∞ x₀) ▸ hy.2.1).1
  have hyT : y ∈ eT.baseSet := by simpa [eT] using hysrc
  have hychart : y ∈ (chartAt H x₀).source := by simpa using hysrc
  have hg_diff : MDifferentiableAt I 𝓘(ℝ, F) g y :=
    (hg_smooth.contMDiffAt (hWM.mem_nhds hy)).mdifferentiableAt (by simp)
  ext w
  rw [← eT.symmL_continuousLinearMapAt (R := ℝ) hyT w, eT.symmL_apply (R := ℝ) hyT]
  set a := eT.continuousLinearMapAt ℝ y w
  rw [covariantDerivative_symm_comp_apply_symm_bundle (Module.finBasis ℝ F) eT
    (cov.isCovariantDerivativeOn (s := eV.baseSet)) hy.1 hyT hg_diff a]
  have hsol_y := husol (extChartAt I x₀ y) hy.2.2
  have hclm : mvfderiv I (extChartAt I x₀) y (eT.symm y a) = a := by
    have h : eT.continuousLinearMapAt ℝ y (eT.symm y a) = a := by
      rw [← eT.symmL_apply (R := ℝ) hyT, eT.continuousLinearMapAt_symmL (R := ℝ) hyT]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hychart] at h
    exact (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans h
  have hmv : mvfderiv I g y (eT.symm y a) =
      -bundleChristoffelMap (Module.finBasis ℝ F) eT
        (cov.isCovariantDerivativeOn (s := eV.baseSet)) y (g y) a := by
    have hchain := mvfderiv_comp_apply_of_differentiableAt hsol_y.differentiableAt
      (mdifferentiableAt_extChartAt hychart) (eT.symm y a)
    rw [Function.comp_def, ← hg_def, hclm, hsol_y.fderiv] at hchain
    dsimp only [eV, eT, g] at hchain ⊢
    rwa [(extChartAt I x₀).left_inv hysrc, neg_apply] at hchain
  rw [hmv, neg_add_cancel, ← eV.symmL_apply (R := ℝ) hy.1, map_zero, zero_apply]

/-- **Existence of local smooth parallel sections at an interior point.** If the curvature tensor
of `cov` vanishes on a neighbourhood of an interior point `x₀`, then every fibre vector `w₀ : V x₀`
extends to a globally smooth section of `V` that agrees with `w₀` at `x₀` and is parallel near
`x₀`. -/
theorem exists_contMDiff_apply_eq_and_eventually_cov_eq_zero_of_isInteriorPoint
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0)
    (w₀ : V x₀) :
    ∃ σ : Π y : M, V y, CMDiff ∞ (T% σ) ∧ σ x₀ = w₀ ∧ ∀ᶠ y in 𝓝 x₀, cov σ y = 0 := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  let z₀ : E := extChartAt I x₀ x₀
  let y₀ : F := eV.continuousLinearMapAt ℝ x₀ w₀
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
  have hz₀ : z₀ ∈ interior (extChartAt I x₀).target := I.isInteriorPoint_iff.1 hx₀
  let OE : Set E := interior (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' eV.baseSet
  have hOE : IsOpen OE := isOpen_inter_preimage_baseSet_extChartAt_symm (F := F) (V := V) x₀
  have hz₀OE : z₀ ∈ OE := ⟨hz₀, by simpa [z₀] using hx₀V⟩
  let ΓE : E → F →L[ℝ] E →L[ℝ] F := fun ζ ↦ bundleChristoffelMap (Module.finBasis ℝ F) eT
    (cov.isCovariantDerivativeOn (s := eV.baseSet)) ((extChartAt I x₀).symm ζ)
  have hΓE : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) ΓE OE :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_bundleChristoffelMap_comp_extChartAt_symm cov x₀)
  let f : E × F → E →L[ℝ] F := fun p ↦ -ΓE p.1 p.2
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) f (OE ×ˢ univ) :=
    ((hΓE.comp (contDiffOn_fst (s := OE ×ˢ univ)) fun _ hp ↦ hp.1).clm_apply contDiffOn_snd).neg
  have hint : ∀ᶠ p in 𝓝 (z₀, y₀), IsFrobeniusIntegrableAt f p := by
    have hcont : ContinuousAt ((extChartAt I x₀).symm ∘ Prod.fst) (z₀, y₀) :=
      ContinuousAt.comp (g := (extChartAt I x₀).symm) (f := Prod.fst)
        (((contMDiffOn_extChartAt_symm (n := ∞) x₀).mono interior_subset).continuousOn.continuousAt
          (isOpen_interior.mem_nhds hz₀)) continuousAt_fst
    have hflat' : ∀ᶠ p in 𝓝 (z₀, y₀), cov.curvatureTensor ((extChartAt I x₀).symm p.1) = 0 :=
      hcont.eventually (by simpa [z₀] using hflat)
    filter_upwards [(hOE.prod isOpen_univ).mem_nhds ⟨hz₀OE, mem_univ _⟩, hflat']
      with ⟨z, w⟩ ⟨hzE, _⟩ hzf
    exact isFrobeniusIntegrableAt_neg_bundleChristoffelMap cov x₀ hzE.1 hzE.2 hzf w
  obtain ⟨u, U, hU, hp₀U, husmooth, hu₀, -, husol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt hf
      ((hOE.prod isOpen_univ).mem_nhds ⟨hz₀OE, mem_univ _⟩) hint
  let WE : Set E := (fun z ↦ (z, y₀)) ⁻¹' U ∩ OE
  have hWE : IsOpen WE := (hU.preimage (continuous_id.prodMk continuous_const)).inter hOE
  have hu₀_smooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun z ↦ u (z, y₀)) WE :=
    contMDiffOn_iff_contDiffOn.2 <|
      husmooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hz ↦ hz.1
  obtain ⟨WM, σloc, hWM, hx₀WM, hσloc_smooth, hσloc_x₀, hσloc_par⟩ :=
    exists_contMDiffOn_parallel_of_fderiv_solution cov hx₀ hWE ⟨hp₀U, hz₀OE⟩ hu₀_smooth w₀ hu₀
      fun z hz ↦ husol (z, y₀) hz.1
  -- Cut `σloc` off by a smooth bump function supported in `WM`.
  obtain ⟨χ, -, hχsub⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp (hWM.mem_nhds hx₀WM)
  let σ : Π y : M, V y := fun y ↦ χ y • σloc y
  have hσ_smooth : CMDiff ∞ (T% σ) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hWM hχsub hσloc_smooth
  refine ⟨σ, hσ_smooth, by simp [σ, hσloc_x₀], ?_⟩
  have heq : ∀ᶠ y in 𝓝 x₀, σ y = σloc y :=
    χ.eventuallyEq_one.mono fun y hy ↦ by simp [σ, hy]
  filter_upwards [hWM.mem_nhds hx₀WM, heq.eventually_nhds] with y hyWM hy_eq
  have hd₁ : MDiffAt (T% σ) y := hσ_smooth.mdifferentiable (by simp) y
  have hd₂ : MDiffAt (T% σloc) y :=
    (hσloc_smooth.contMDiffAt (hWM.mem_nhds hyWM)).mdifferentiableAt (by simp)
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hd₁ hd₂ univ_mem hy_eq]
  exact hσloc_par y hyWM

/-- **Existence of local smooth parallel sections.** On a boundaryless manifold, if the curvature
tensor of `cov` vanishes near `x₀`, every fibre vector `w₀ : V x₀` extends to a smooth section
agreeing with `w₀` at `x₀` and parallel near `x₀`. -/
theorem exists_contMDiff_apply_eq_and_eventually_cov_eq_zero [BoundarylessManifold I M]
    {x₀ : M} (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) (w₀ : V x₀) :
    ∃ σ : Π y : M, V y, CMDiff ∞ (T% σ) ∧ σ x₀ = w₀ ∧ ∀ᶠ y in 𝓝 x₀, cov σ y = 0 :=
  cov.exists_contMDiff_apply_eq_and_eventually_cov_eq_zero_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hflat w₀

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [cov.ContMDiffCovariantDerivative ∞] in
/-- If every vector of a basis `b₀` of `V x₀` extends to a smooth section parallel near `x₀`,
those sections form a smooth local parallel frame on an open neighbourhood of `x₀`. -/
theorem exists_isLocalFrameOn_parallel_of_forall_exists {ι : Type*}
    {x₀ : M} {U : Set M} (hU : U ∈ 𝓝 x₀) (b₀ : Basis ι ℝ (V x₀))
    (hsec : ∀ i : ι, ∃ σ : Π y : M, V y,
      CMDiff ∞ (T% σ) ∧ σ x₀ = b₀ i ∧ ∀ᶠ y in 𝓝 x₀, cov σ y = 0) :
    ∃ (s : ι → Π y : M, V y) (W : Set M),
      (∀ i, CMDiff ∞ (T% (s i))) ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b₀ i) ∧ ∀ i, ∀ y ∈ W, cov (s i) y = 0 := by
  let eV := trivializationAt F V x₀
  have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
  have : FiniteDimensional ℝ (V x₀) :=
    (eV.linearEquivAt ℝ x₀ hx₀V).symm.finiteDimensional
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b₀
  choose s hs_smooth hs_x₀ hs_par using hsec
  -- Read `s` in `eV` to see that linear independence of `s · y` is an open condition near `x₀`.
  let coords : M → ι → F := fun y i ↦ (eV ⟨y, s i y⟩).2
  have hcoords_cont : ContinuousOn coords eV.baseSet :=
    continuousOn_pi.2 fun i ↦
      ((eV.contMDiffOn_section_baseSet_iff.1 (hs_smooth i).contMDiffOn).continuousOn)
  have hli_open : IsOpen (eV.baseSet ∩ coords ⁻¹' {f : ι → F | LinearIndependent ℝ f}) :=
    hcoords_cont.isOpen_inter_preimage eV.open_baseSet isOpen_setOfPred_linearIndependent
  have hx₀_li : x₀ ∈ eV.baseSet ∩ coords ⁻¹' {f : ι → F | LinearIndependent ℝ f} := by
    refine ⟨hx₀V, ?_⟩
    rw [mem_preimage, mem_ofPred_eq]
    have hfun : coords x₀ = (eV.linearEquivAt ℝ x₀ hx₀V) ∘ b₀ := by
      funext i
      simp [coords, hs_x₀ i]
    rw [hfun]
    exact b₀.linearIndependent.map' (eV.linearEquivAt ℝ x₀ hx₀V).toLinearMap (LinearEquiv.ker _)
  have hpar_all : ∀ᶠ y in 𝓝 x₀, ∀ i, cov (s i) y = 0 := eventually_all.2 hs_par
  obtain ⟨U₀, hU₀sub, hU₀open, hx₀U₀⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hpar_all)
  let W : Set M := (eV.baseSet ∩ coords ⁻¹' {f : ι → F | LinearIndependent ℝ f}) ∩ U₀
  have hWopen : IsOpen W := hli_open.inter hU₀open
  have hx₀W : x₀ ∈ W := ⟨hx₀_li, hx₀U₀⟩
  have hli_at {y : M} (hy : y ∈ W) : LinearIndependent ℝ (fun i ↦ s i y) := by
    have hliF : LinearIndependent ℝ (coords y) := hy.1.2
    have hfun : (fun i ↦ s i y) = (eV.linearEquivAt ℝ y hy.1.1).symm ∘ coords y := by
      funext i
      simpa [coords] using (eV.symm_apply_apply_mk hy.1.1 (s i y)).symm
    rw [hfun]
    exact hliF.map' (eV.linearEquivAt ℝ y hy.1.1).symm.toLinearMap (LinearEquiv.ker _)
  have hframe : IsLocalFrameOn I F ∞ s W := by
    refine ⟨fun hy ↦ hli_at hy, fun {y} hy ↦ ?_, fun i ↦ (hs_smooth i).contMDiffOn⟩
    have : FiniteDimensional ℝ (V y) :=
      (eV.linearEquivAt ℝ y hy.1.1).symm.finiteDimensional
    have hcard : Fintype.card ι = Module.finrank ℝ (V y) := by
      rw [← Module.finrank_eq_card_basis b₀,
        (eV.linearEquivAt ℝ x₀ hx₀V).finrank_eq,
        (eV.linearEquivAt ℝ y hy.1.1).finrank_eq]
    exact ((hli_at hy).span_eq_top_of_card_eq_finrank' hcard).ge
  exact ⟨s, W, hs_smooth, hWopen, hx₀W, fun y hy ↦ (hU₀sub hy.2).1, hframe, hs_x₀,
    fun i y hy ↦ (hU₀sub hy.2).2 i⟩

/-- **Existence of a smooth local parallel frame at an interior point.** If `cov.curvatureTensor`
vanishes near an interior point `x₀`, any basis `b₀` of `V x₀` extends to a smooth local parallel
frame on an open neighbourhood `W ⊆ U` of `x₀`. -/
theorem exists_isLocalFrameOn_parallel_of_isInteriorPoint {ι : Type*}
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0)
    {U : Set M} (hU : U ∈ 𝓝 x₀) (b₀ : Basis ι ℝ (V x₀)) :
    ∃ (s : ι → Π y : M, V y) (W : Set M),
      (∀ i, CMDiff ∞ (T% (s i))) ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b₀ i) ∧ ∀ i, ∀ y ∈ W, cov (s i) y = 0 :=
  cov.exists_isLocalFrameOn_parallel_of_forall_exists hU b₀ fun i ↦
    cov.exists_contMDiff_apply_eq_and_eventually_cov_eq_zero_of_isInteriorPoint hx₀ hflat (b₀ i)

/-- **Existence of a smooth local parallel frame.** On a boundaryless manifold, if
`cov.curvatureTensor` vanishes near `x₀`, any basis `b₀` of `V x₀` extends to a smooth local
parallel frame on an open neighbourhood `W ⊆ U` of `x₀`. -/
theorem exists_isLocalFrameOn_parallel [BoundarylessManifold I M] {ι : Type*}
    {x₀ : M} (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0)
    {U : Set M} (hU : U ∈ 𝓝 x₀) (b₀ : Basis ι ℝ (V x₀)) :
    ∃ (s : ι → Π y : M, V y) (W : Set M),
      (∀ i, CMDiff ∞ (T% (s i))) ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b₀ i) ∧ ∀ i, ∀ y ∈ W, cov (s i) y = 0 :=
  cov.exists_isLocalFrameOn_parallel_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hflat hU b₀

/-- **Pointwise germ characterization of flat connections at an interior point.** The curvature
tensor of `cov` vanishes near an interior point `x₀` if and only if every vector in `V x₀`
extends to a smooth section parallel near `x₀`. -/
theorem eventually_curvatureTensor_eq_zero_iff_forall_exists_parallel_of_isInteriorPoint
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    (∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) ↔
      ∀ w₀ : V x₀, ∃ σ : Π y : M, V y,
        CMDiff ∞ (T% σ) ∧ σ x₀ = w₀ ∧ ∀ᶠ y in 𝓝 x₀, cov σ y = 0 := by
  refine ⟨cov.exists_contMDiff_apply_eq_and_eventually_cov_eq_zero_of_isInteriorPoint hx₀,
    fun h ↦ ?_⟩
  let eV := trivializationAt F V x₀
  have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
  let b₀ : Basis (Fin (Module.finrank ℝ F)) ℝ (V x₀) :=
    eV.basisAt (Module.finBasis ℝ F) hx₀V
  obtain ⟨s, W, -, hWopen, hx₀W, -, hframe, -, hpar⟩ :=
    cov.exists_isLocalFrameOn_parallel_of_forall_exists univ_mem b₀ fun i ↦ h (b₀ i)
  exact eventually_of_mem (hWopen.mem_nhds hx₀W) fun y hy ↦
    cov.curvatureTensor_eq_zero_of_isLocalFrameOn hWopen hframe hpar hy

/-- **Pointwise germ characterization of flat connections.** On a boundaryless manifold, the
curvature tensor of `cov` vanishes near `x₀` if and only if every vector in `V x₀` extends to a
smooth section parallel near `x₀`. -/
theorem eventually_curvatureTensor_eq_zero_iff_forall_exists_parallel [BoundarylessManifold I M]
    (x₀ : M) :
    (∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) ↔
      ∀ w₀ : V x₀, ∃ σ : Π y : M, V y,
        CMDiff ∞ (T% σ) ∧ σ x₀ = w₀ ∧ ∀ᶠ y in 𝓝 x₀, cov σ y = 0 :=
  cov.eventually_curvatureTensor_eq_zero_iff_forall_exists_parallel_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

/-- **Open-set characterization of flat connections by local parallel frames.** On an open set `U`
consisting of interior points (in particular, any open set on a boundaryless manifold), the
curvature tensor of `cov` vanishes on `U` if and only if every point of `U` admits a smooth local
parallel frame on an open neighbourhood inside `U`. -/
theorem forall_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn_parallel_of_isInteriorPoint
    {U : Set M} (hU : IsOpen U) (hUint : ∀ x ∈ U, I.IsInteriorPoint x) :
    (∀ x ∈ U, cov.curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (W : Set M) (s : Fin (Module.finrank ℝ F) → Π y : M, V y),
        IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsLocalFrameOn I F ∞ s W ∧ ∀ i, ∀ y ∈ W, cov (s i) y = 0 := by
  refine ⟨fun hflat x hx ↦ ?_, fun hframe x hx ↦ ?_⟩
  · let eV := trivializationAt F V x
    have hxV : x ∈ eV.baseSet := mem_baseSet_trivializationAt F V x
    let b₀ := eV.basisAt (Module.finBasis ℝ F) hxV
    obtain ⟨s, W, -, hWopen, hxW, hWU, hsW, -, hpar⟩ :=
      cov.exists_isLocalFrameOn_parallel_of_isInteriorPoint (hUint x hx)
        (eventually_of_mem (hU.mem_nhds hx) hflat) (hU.mem_nhds hx) b₀
    exact ⟨W, s, hWopen, hxW, hWU, hsW, hpar⟩
  · obtain ⟨W, s, hWopen, hxW, -, hsW, hpar⟩ := hframe x hx
    exact cov.curvatureTensor_eq_zero_of_isLocalFrameOn hWopen hsW hpar hxW

/-- **Open-set characterization of flat connections by local parallel frames.** On a boundaryless
manifold, the curvature tensor of `cov` vanishes on an open set `U` if and only if every point of
`U` admits a smooth local parallel frame on an open neighbourhood inside `U`. -/
theorem forall_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn_parallel
    [BoundarylessManifold I M] {U : Set M} (hU : IsOpen U) :
    (∀ x ∈ U, cov.curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (W : Set M) (s : Fin (Module.finrank ℝ F) → Π y : M, V y),
        IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsLocalFrameOn I F ∞ s W ∧ ∀ i, ∀ y ∈ W, cov (s i) y = 0 :=
  cov.forall_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn_parallel_of_isInteriorPoint hU
    fun _ _ ↦ BoundarylessManifold.isInteriorPoint

end FrobeniusCoordinates

/-! ### Metric-compatible flat connections and orthonormal local parallel frames -/

section MetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V}

section OrthonormalFrame

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative cov ∞]

/-- **Existence of a smooth orthonormal local parallel frame at an interior point.** For a smooth
metric-compatible connection whose curvature tensor vanishes near an interior point `x₀`, any
orthonormal basis `b₀` of `V x₀` extends to a smooth local parallel frame on an open
neighbourhood `W ⊆ U` of `x₀` whose vectors are orthonormal at every point of `W`. -/
theorem IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel_of_isInteriorPoint
    (hcov : cov.IsMetricCompatible) {ι : Type*} [Fintype ι]
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0)
    {U : Set M} (hU : U ∈ 𝓝 x₀) (b₀ : OrthonormalBasis ι ℝ (V x₀)) :
    ∃ (s : ι → Π y : M, V y) (W : Set M),
      (∀ i, CMDiff ∞ (T% (s i))) ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b₀ i) ∧
      (∀ i, ∀ y ∈ W, cov (s i) y = 0) ∧ ∀ y ∈ W, Orthonormal ℝ (s · y) := by
  classical
  obtain ⟨s, W₁, hs_smooth, hW₁open, hx₀W₁, hW₁U, hframe₁, hs_x₀, hpar₁⟩ :=
    cov.exists_isLocalFrameOn_parallel_of_isInteriorPoint hx₀ hflat hU b₀.toBasis
  have hinner_ev : ∀ᶠ y in 𝓝 x₀, ∀ i j : ι,
      inner ℝ (s i y) (s j y) = inner ℝ (b₀ i) (b₀ j) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    filter_upwards [hcov.eventuallyEq_inner_const_of_cov_eq_zero hW₁open
      ((hs_smooth i).mdifferentiable (by simp)).mdifferentiableOn
      ((hs_smooth j).mdifferentiable (by simp)).mdifferentiableOn
      (hpar₁ i) (hpar₁ j) hx₀W₁] with y hy
    simpa [hs_x₀] using hy
  obtain ⟨W₂, hW₂sub, hW₂open, hx₀W₂⟩ := mem_nhds_iff.1 hinner_ev
  let W := W₁ ∩ W₂
  refine ⟨s, W, hs_smooth, hW₁open.inter hW₂open, ⟨hx₀W₁, hx₀W₂⟩,
    fun y hy ↦ hW₁U hy.1, hframe₁.mono inter_subset_left, hs_x₀,
    fun i y hy ↦ hpar₁ i y hy.1, fun y hy ↦ ?_⟩
  rw [orthonormal_iff_ite]
  intro i j
  rw [hW₂sub hy.2 i j]
  exact orthonormal_iff_ite.1 b₀.orthonormal i j

/-- **Existence of a smooth orthonormal local parallel frame.** On a boundaryless manifold, for a
smooth metric-compatible connection whose curvature tensor vanishes near `x₀`, any orthonormal
basis `b₀` of `V x₀` extends to a smooth orthonormal local parallel frame on an open
neighbourhood `W ⊆ U` of `x₀`. -/
theorem IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel
    [BoundarylessManifold I M] (hcov : cov.IsMetricCompatible) {ι : Type*} [Fintype ι]
    {x₀ : M} (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0)
    {U : Set M} (hU : U ∈ 𝓝 x₀) (b₀ : OrthonormalBasis ι ℝ (V x₀)) :
    ∃ (s : ι → Π y : M, V y) (W : Set M),
      (∀ i, CMDiff ∞ (T% (s i))) ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b₀ i) ∧
      (∀ i, ∀ y ∈ W, cov (s i) y = 0) ∧ ∀ y ∈ W, Orthonormal ℝ (s · y) :=
  hcov.exists_orthonormal_isLocalFrameOn_parallel_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hflat hU b₀

end OrthonormalFrame

end MetricCompatible

end CovariantDerivative
