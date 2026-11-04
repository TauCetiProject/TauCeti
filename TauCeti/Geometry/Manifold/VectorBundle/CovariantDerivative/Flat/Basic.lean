/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Analysis.ODE.Frobenius
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-!
# Flat connections, local parallel sections, and local parallel frames

Let `V → M` be a finite-rank smooth real vector bundle equipped with a smooth covariant derivative
`∇`. Evaluating the curvature operator on sections that are parallel near a point `x` gives zero, so
if `V` admits a smooth local parallel frame near `x`, then the curvature tensor of `∇` vanishes at
`x`.

On a boundaryless smooth manifold, the converse holds by the local Frobenius theorem. Reading a
section `σ(y) = e_V⁻¹(y, g(y))` in the canonical bundle trivializations `e_V` of `V` and `e_T` of
`TM` centred at `x₀`, the parallel equation `∇ σ = 0` becomes the total differential equation

`d g(z) = -Γ(z)(g(z), ·)`

in the preferred chart `φ = extChartAt I x₀`, where `Γ` is the model-space Christoffel map of `∇`.
The Frobenius integrability condition for `f(z, w) = -Γ(z)(w, ·)` at `(z, w)` is the symmetry of
`(a, c) ↦ dΓ(z)(a)(w, c) - Γ(z)(Γ(z)(w, a), c)`, whose antisymmetric part is precisely the chart
reading of the curvature `R(e_T⁻¹ a, e_T⁻¹ c)(e_V⁻¹ w)`. When `R = 0` near `x₀`,
`TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt` produces a smooth local
solution with any prescribed initial value at `x₀`, cut off by a smooth bump function to a global
smooth section that is parallel near `x₀`. Extending a basis of `V x₀` in this way gives a smooth
local parallel frame on an open neighbourhood of `x₀`.

Consequently:
* a smooth connection on `V` is flat near `x₀` (or on an open set `U`) if and only if `V` admits a
  smooth local parallel frame near `x₀` (or around every point of `U`);
* two differentiable parallel sections on a preconnected open set where `∇` is flat agree everywhere
  once they agree at one point;
* if `∇` is metric-compatible, the inner product of parallel sections is locally constant (and
  constant on preconnected open sets), so extending an orthonormal basis of `V x₀` produces a smooth
  local *orthonormal* parallel frame near `x₀`.

## Main results

* `CovariantDerivative.curvatureTensor_eq_zero_of_isLocalFrameOn_eventually_eq_zero` and
  `CovariantDerivative.curvatureTensor_eq_zero_of_isLocalFrameOn_parallel`: a smooth local parallel
  frame forces the curvature tensor to vanish, including on manifolds with boundary or corners.
* `CovariantDerivative.exists_contMDiff_section_eventually_eq_zero`: on a boundaryless manifold, a
  connection with `curvatureTensor = 0` near `x₀` admits a smooth section with prescribed value at
  `x₀` that is parallel near `x₀`.
* `CovariantDerivative.exists_isLocalFrameOn_parallel_of_basis`: extending any basis of `V x₀` gives
  a smooth local parallel frame near `x₀`.
* `CovariantDerivative.eventually_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn` and
  `CovariantDerivative.forall_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn`: flat curvature
  near a point or on an open set is equivalent to the existence of smooth local parallel frames.
* `CovariantDerivative.eqOn_of_parallel`: parallel sections on a preconnected flat open set are
  uniquely determined by their value at one point.
* `CovariantDerivative.IsMetricCompatible.inner_eq_of_parallel` and
  `CovariantDerivative.IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel`: constancy of
  inner products of parallel sections, and existence of smooth local orthonormal parallel frames for
  flat metric-compatible connections.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Theorem 7.8
  and Proposition 7.9.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Chapter II, §9.
* M. Spivak, *A Comprehensive Introduction to Differential Geometry*, Vol. II, 3rd ed., Publish or
  Perish (1999), Chapter 4D.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Module Set Topology
open scoped ContDiff Manifold

namespace CovariantDerivative

open TauCeti.Manifold

section WithBoundary

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

/-- **A local parallel frame forces the curvature tensor to vanish.** If `{s i}` is a smooth local
frame of `V` on an open neighbourhood `U` of `x` and each frame section satisfies `∇ (s i) = 0` near
`x`, then `cov.curvatureTensor x = 0`. Neither a metric nor boundarylessness is required. -/
theorem curvatureTensor_eq_zero_of_isLocalFrameOn_eventually_eq_zero {ι : Type*}
    {s : ι → Π x : M, V x} {U : Set M} (hs : IsLocalFrameOn I F ∞ s U) (hU : IsOpen U)
    {x : M} (hx : x ∈ U) (hpar : ∀ i, ∀ᶠ y in 𝓝 x, cov (s i) y = 0) :
    cov.curvatureTensor x = 0 := by
  classical
  ext u v w
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  have hbasis (i : ι) : cov.curvatureTensor x (X x) (Y x) (s i x) = 0 := by
    rw [cov.curvatureTensor_apply_of_contMDiffOn x hU hx hX.contMDiffOn hY.contMDiffOn
      (hs.contMDiffOn i), curvatureOperator_apply, (hpar i).self_of_nhds, zero_apply, sub_zero]
    have hd0 : MDiffAt (T% (0 : Π y : M, V y)) x := Bundle.mdifferentiableAt_zeroSection ℝ V
    have hcov_zero {Z : Π y : M, TangentSpace I y} (hZ : CMDiff ∞ (T% Z)) :
        cov (fun y ↦ cov (s i) y (Z y)) x = 0 := by
      have hsmooth : CMDiff[U] ∞ (T% (fun y ↦ cov (s i) y (Z y))) := by
        have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun U :=
          contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov hU
        have : ContMDiffVectorBundle (∞ + 1) F V I := by
          simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
        exact ContMDiffOn.clm_bundle_apply
          (ContMDiffCovariantDerivativeOn.contMDiff (hs.contMDiffOn i)) hZ.contMDiffOn
      have hd : MDiffAt (T% (fun y ↦ cov (s i) y (Z y))) x :=
        (hsmooth.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
      have hev : ∀ᶠ y in 𝓝 x, cov (s i) y (Z y) = (0 : Π y : M, V y) y :=
        (hpar i).mono fun y hy ↦ by simp [hy]
      rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hd hd0 univ_mem hev,
        cov.isCovariantDerivativeOnUniv.zero]
    rw [hcov_zero hY, hcov_zero hX]
    simp
  have : Fintype ι := hs.fintypeOfFiniteDimensional hx
  have hw : w = ∑ i, hs.coeff i x w • s i x := by
    simpa using hs.coeff_sum_eq (fun y : M ↦ if h : y = x then h ▸ w else 0) hx
  rw [hw]
  simp [hbasis]

/-- If `{s i}` is a smooth local frame of `V` on an open set `U` and `∇ (s i) = 0` everywhere on
`U`, then `cov.curvatureTensor` vanishes at every point of `U`. -/
theorem curvatureTensor_eq_zero_of_isLocalFrameOn_parallel {ι : Type*}
    {s : ι → Π x : M, V x} {U : Set M} (hs : IsLocalFrameOn I F ∞ s U) (hU : IsOpen U)
    (hpar : ∀ y ∈ U, ∀ i, cov (s i) y = 0) {x : M} (hx : x ∈ U) :
    cov.curvatureTensor x = 0 :=
  cov.curvatureTensor_eq_zero_of_isLocalFrameOn_eventually_eq_zero hs hU hx fun i ↦
    eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ hpar y hy i

end WithBoundary

/-! ### Bundle Christoffel map and Frobenius integrability in a chart -/

section NormedSpaceHelpers

private theorem hasMFDerivAt_clm_apply₂
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Γ : M → F →L[ℝ] E →L[ℝ] F} {x : M}
    (hΓ : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ x) (w : F) (v' : E) :
    HasMFDerivAt I 𝓘(ℝ, F) (fun y ↦ Γ y w v') x
      (((ContinuousLinearMap.apply ℝ F v').comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) w)).comp
          (mfderiv I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ x)) := by
  let _ : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup (F →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (F →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  exact (((ContinuousLinearMap.apply ℝ F v').comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) w)).hasFDerivAt (x := Γ x)).hasMFDerivAt.comp x
      hΓ.hasMFDerivAt

private theorem fderiv_neg_clm_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : E → F →L[ℝ] E →L[ℝ] F} {z : E}
    (hG : DifferentiableAt ℝ G z) (w : F) (a c : E) :
    fderiv ℝ (fun p : E × F ↦ -(G p.1 p.2)) (z, w) (a, -(G z w a)) c =
      -(fderiv ℝ G z a w c) + G z (G z w a) c := by
  let _ : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup (F →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (F →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hp1 := hG.hasFDerivAt.comp (z, w) (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := F))
  have hp2 : HasFDerivAt (Prod.snd : E × F → F) (ContinuousLinearMap.snd ℝ E F) (z, w) :=
    hasFDerivAt_snd
  have hneg : HasFDerivAt (fun p : E × F ↦ -(G p.1 p.2)) _ (z, w) := (hp1.clm_apply hp2).neg
  rw [hneg.fderiv]
  simp

/-- On a boundaryless manifold, reading a differentiable function in `extChartAt I x₀` identifies
`mvfderiv` along `(trivializationAt E (TangentSpace I) x₀).symm` with `fderiv` in `E`. -/
private theorem mvfderiv_symm_trivializationAt_eq_fderiv_comp_extChartAt_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {h : M → W} {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hh : MDifferentiableAt I 𝓘(ℝ, W) h ((extChartAt I x₀).symm z)) (a : E) :
    mvfderiv I h ((extChartAt I x₀).symm z)
        ((trivializationAt E (TangentSpace I) x₀).symm ((extChartAt I x₀).symm z) a) =
      fderiv ℝ (h ∘ (extChartAt I x₀).symm) z a := by
  set φ := extChartAt I x₀
  have hx : φ.symm z ∈ φ.source := φ.map_target hz
  have hx_chart : φ.symm z ∈ (chartAt H x₀).source := by
    simpa [φ, extChartAt_source] using hx
  have hxT : φ.symm z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hx_chart
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I φ.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt
      (by rw [I.range_eq_univ]; exact univ_mem)
  have hvec : (trivializationAt E (TangentSpace I) x₀).symm (φ.symm z) a =
      mfderiv 𝓘(ℝ, E) I φ.symm z a := by
    rw [← (trivializationAt E (TangentSpace I) x₀).symmL_apply (R := ℝ) hxT,
      TangentBundle.symmL_trivializationAt hx_chart,
      φ.right_inv hz, I.range_eq_univ, mfderivWithin_univ]
    rfl
  rw [hvec, mvfderiv_apply_eq_mfderiv_apply, ← mfderiv_comp_apply z hh hsymm a,
    mfderiv_eq_fderiv]
  rfl

/-- Universe-polymorphic wrapper around
`TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt`, transporting `E` and `F`
to `Fin (finrank ℝ _) → ℝ` in `Type 0` so `E` and `F` need not share a universe. -/
private theorem exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × F → E →L[ℝ] F} {s : Set (E × F)} {z₀ : E} {w₀ : F}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) f s) (hs : s ∈ 𝓝 (z₀, w₀))
    (hint : ∀ᶠ p in 𝓝 (z₀, w₀), TauCeti.IsFrobeniusIntegrableAt f p) :
    ∃ (u : E × F → F) (U : Set (E × F)),
      IsOpen U ∧ (z₀, w₀) ∈ U ∧ ContDiffOn ℝ ∞ u U ∧ u (z₀, w₀) = w₀ ∧
      ∀ p ∈ U, HasFDerivAt (fun z ↦ u (z, p.2)) (f (p.1, u p)) p.1 := by
  let E₀ := Fin (finrank ℝ E) → ℝ
  let F₀ := Fin (finrank ℝ F) → ℝ
  let eE : E ≃L[ℝ] E₀ := (finBasis ℝ E).equivFunL
  let eF : F ≃L[ℝ] F₀ := (finBasis ℝ F).equivFunL
  let eP : (E × F) ≃L[ℝ] (E₀ × F₀) := eE.prodCongr eF
  let eL : (E →L[ℝ] F) ≃L[ℝ] (E₀ →L[ℝ] F₀) := eE.arrowCongr eF
  let f₀ : E₀ × F₀ → E₀ →L[ℝ] F₀ := eL ∘ f ∘ eP.symm
  let s₀ : Set (E₀ × F₀) := eP.symm ⁻¹' s
  have hf₀ : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) f₀ s₀ :=
    eL.contDiff.comp_contDiffOn (hf.comp eP.symm.contDiff.contDiffOn fun _ h ↦ h)
  have hs₀ : s₀ ∈ 𝓝 (eE z₀, eF w₀) :=
    eP.symm.continuousAt.preimage_mem_nhds (by simpa [eP] using hs)
  have hint₀ : ∀ᶠ q in 𝓝 (eE z₀, eF w₀), TauCeti.IsFrobeniusIntegrableAt f₀ q := by
    filter_upwards [eP.symm.continuousAt.eventually (by simpa [eP] using hint),
      eP.symm.continuousAt.eventually (eventually_mem_nhds_iff.2 (by simpa [eP] using hs))]
      with q hq hqs
    have hfd : DifferentiableAt ℝ f (eP.symm q) :=
      (hf.contDiffAt hqs).differentiableAt (by simp)
    have hf₀d : HasFDerivAt f₀
        (eL.toContinuousLinearMap.comp
          ((fderiv ℝ f (eP.symm q)).comp eP.symm.toContinuousLinearMap)) q :=
      eL.hasFDerivAt.comp q (hfd.hasFDerivAt.comp q eP.symm.hasFDerivAt)
    rw [TauCeti.isFrobeniusIntegrableAt_iff] at hq ⊢
    intro v₀ u₀
    rw [hf₀d.fderiv]
    have hdir (x : E₀) : eP.symm (x, f₀ q x) = (eE.symm x, f (eP.symm q) (eE.symm x)) := by
      ext <;> simp [eP, f₀, eL, ContinuousLinearEquiv.arrowCongr]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hdir]
    simp only [eL, ContinuousLinearEquiv.arrowCongr_apply,
      hq (eE.symm v₀) (eE.symm u₀)]
  obtain ⟨u₀, U₀, hU₀, hp₀U₀, husmooth₀, hu₀_init, -, husol₀⟩ :=
    TauCeti.exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt hf₀ hs₀ hint₀
  refine ⟨fun p ↦ eF.symm (u₀ (eP p)), eP ⁻¹' U₀, hU₀.preimage eP.continuous, hp₀U₀,
    eF.symm.contDiff.comp_contDiffOn ((husmooth₀.of_le (by simp)).comp eP.contDiff.contDiffOn
      fun _ h ↦ h),
    by simp [eP, hu₀_init], fun p hp ↦ ?_⟩
  have hslice := eF.symm.hasFDerivAt.comp p.1 ((husol₀ (eP p) hp).comp p.1 eE.hasFDerivAt)
  refine hslice.congr_fderiv ?_
  ext v
  simp [eP, f₀, eL, ContinuousLinearEquiv.arrowCongr]

end NormedSpaceHelpers

section ChartFrobenius

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

/-- The Christoffel form of `cov` at `x₀`, read through the canonical trivializations of `V` and
`TM` at `x₀` as a continuous bilinear map `F →L[ℝ] E →L[ℝ] F`. -/
private def bundleChristoffelMap {ι : Type*} [Fintype ι] (bF : Basis ι ℝ F) (x₀ x : M) :
    F →L[ℝ] E →L[ℝ] F :=
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  ((eV.continuousLinearMap (RingHom.id ℝ) (eT.continuousLinearMap (RingHom.id ℝ) eV))
    ⟨x, christoffelForm bF (cov.isCovariantDerivativeOn (s := eV.baseSet)) x⟩).2

omit [FiniteDimensional ℝ E] [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
private theorem bundleChristoffelMap_apply {ι : Type*} [Fintype ι] (bF : Basis ι ℝ F)
    {x₀ x : M} (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hxT : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (w : F) (u : E) :
    bundleChristoffelMap cov bF x₀ x w u =
      (trivializationAt F V x₀).continuousLinearMapAt ℝ x
        (christoffelForm bF (cov.isCovariantDerivativeOn (s := (trivializationAt F V x₀).baseSet))
          x ((trivializationAt F V x₀).symmL ℝ x w)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x u)) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  have hxe : x ∈ (eT.continuousLinearMap (RingHom.id ℝ) eV).baseSet := ⟨hxT, hxV⟩
  simp only [bundleChristoffelMap, Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (eT.continuousLinearMap (RingHom.id ℝ) eV) hxe]
  simp only [Bundle.Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    eV, eT]

private theorem contMDiffOn_bundleChristoffelMap {ι : Type*} [Fintype ι] (bF : Basis ι ℝ F)
    (x₀ : M) :
    CMDiff[(trivializationAt F V x₀).baseSet ∩ (trivializationAt E (TangentSpace I) x₀).baseSet] ∞
      (bundleChristoffelMap cov bF x₀) := by
  classical
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  let bE := Basis.ofVectorSpace ℝ E
  have := FiniteDimensional.fintypeBasisIndex bE
  let U := eV.baseSet ∩ eT.baseSet
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun eV.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov eV.open_baseSet
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  have hterm (j : ι) (i : Basis.ofVectorSpaceIndex ℝ E) :
      CMDiff[U] ∞ (fun y ↦ (eV ⟨y, cov (eV.localFrame bF j) y (eT.localFrame bE i y)⟩).2) := by
    have hj : CMDiff[eV.baseSet] (∞ + 1) (T% (eV.localFrame bF j)) :=
      eV.contMDiffOn_localFrame_baseSet (∞ + 1) bF j
    have hi : CMDiff[eT.baseSet] ∞ (T% (eT.localFrame bE i)) :=
      eT.contMDiffOn_localFrame_baseSet ∞ bE i
    have hcovj : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) y
          (cov (eV.localFrame bF j) y)) eV.baseSet :=
      ContMDiffCovariantDerivativeOn.contMDiff hj
    have happ : CMDiff[U] ∞
        (T% (fun y ↦ cov (eV.localFrame bF j) y (eT.localFrame bE i y))) :=
      ContMDiffOn.clm_bundle_apply (hcovj.mono inter_subset_left) (hi.mono inter_subset_right)
    exact ((eV.contMDiffOn_iff fun y (hy : y ∈ U) ↦ eV.mem_source.mpr hy.1).1 happ).2
  have hsum : CMDiff[U] ∞ (fun y : M ↦ ∑ j', ∑ i', ∑ k',
      bF.coord k' (eV ⟨y, cov (eV.localFrame bF j') y (eT.localFrame bE i' y)⟩).2 •
        (bF.coord j').toContinuousLinearMap.smulRight
          ((bE.coord i').toContinuousLinearMap.smulRight (bF k'))) := by
    refine contMDiffOn_finsetSum fun j' _ ↦ contMDiffOn_finsetSum fun i' _ ↦
      contMDiffOn_finsetSum fun k' _ ↦ ?_
    exact (((bF.coord k').toContinuousLinearMap.contDiff.contMDiff).comp_contMDiffOn
      (hterm j' i')).smul contMDiffOn_const
  refine hsum.congr fun y hy ↦ ?_
  refine ContinuousLinearMap.coe_injective (bF.ext fun j ↦ ?_)
  simp only [ContinuousLinearMap.coe_coe]
  refine ContinuousLinearMap.coe_injective (bE.ext fun i ↦ ?_)
  simp only [ContinuousLinearMap.coe_coe]
  rw [bundleChristoffelMap_apply cov bF hy.1 hy.2, symmL_basis_eq_localFrame bF hy.1 j,
    symmL_basis_eq_localFrame bE hy.2 i, christoffelForm_apply bF _ hy.1]
  have hcollapse : ∑ l, eV.localFrameCoeff I bF l y (eV.localFrame bF j y) •
      cov (eV.localFrame bF l) y = cov (eV.localFrame bF j) y := by
    simp [localFrameCoeff_localFrame bF hy.1]
  rw [hcollapse, Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hy.1]
  simp [Basis.coord_apply, Finsupp.single_apply, bF.sum_repr]

omit [FiniteDimensional ℝ E] [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
/-- Coordinate formula for `cov` on a section `y ↦ eV.symm y (g y)` in the canonical
trivializations at `x₀`. -/
private theorem covariantDerivative_symm_comp_apply_symm_bundle {ι : Type*} [Fintype ι]
    (bF : Basis ι ℝ F) {x₀ x : M} (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hxT : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) {g : M → F}
    (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) (u : E) :
    cov (fun y ↦ (trivializationAt F V x₀).symm y (g y)) x
        ((trivializationAt E (TangentSpace I) x₀).symm x u) =
      (trivializationAt F V x₀).symm x
        (mvfderiv I g x ((trivializationAt E (TangentSpace I) x₀).symm x u) +
          bundleChristoffelMap cov bF x₀ x (g x) u) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  let hcov := cov.isCovariantDerivativeOn (s := eV.baseSet)
  have hread : ∀ᶠ y in 𝓝 x, (eV ⟨y, eV.symm y (g y)⟩).2 = g y :=
    eventually_of_mem (eV.open_baseSet.mem_nhds hxV) fun y hy ↦ by rw [eV.apply_mk_symm hy]
  have hσ : MDiffAt (T% (fun y ↦ eV.symm y (g y))) x :=
    (eV.mdifferentiableAt_section_iff I _ hxV).2 (hg.congr_of_eventuallyEq hread)
  rw [covariantDerivative_eq_add_christoffelForm bF hcov hxV hσ, add_apply,
    ← eV.symmL_apply (R := ℝ) hxV (_ + _), map_add,
    bundleChristoffelMap_apply cov bF hxV hxT, eV.symmL_continuousLinearMapAt (R := ℝ) hxV,
    eV.symmL_apply (R := ℝ) hxV, eT.symmL_apply (R := ℝ) hxT, eV.symmL_apply (R := ℝ) hxV]
  congr 1
  rw [frameCovariantDerivative_apply]
  have hcoeff (i : ι) : mvfderiv I ((LinearMap.piApply (eV.localFrameCoeff I bF i))
      (fun y ↦ eV.symm y (g y))) x (eT.symm x u) =
      bF.coord i (mvfderiv I g x (eT.symm x u)) := by
    have heq : (LinearMap.piApply (eV.localFrameCoeff I bF i)) (fun y ↦ eV.symm y (g y)) =ᶠ[𝓝 x]
        fun y ↦ bF.coord i (g y) := by
      filter_upwards [hread, eV.open_baseSet.mem_nhds hxV] with y hy hyb
      rw [LinearMap.piApply_apply_apply,
        eV.localFrameCoeff_eq_coeff (I := I) (b := bF) (s := fun y ↦ eV.symm y (g y)) hyb, hy,
        Basis.coord_apply]
    have hL : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y ↦ bF.coord i (g y)) x
        ((LinearMap.toContinuousLinearMap (bF.coord i)).comp (mfderiv I 𝓘(ℝ, F) g x)) :=
      (LinearMap.toContinuousLinearMap (bF.coord i)).hasMFDerivAt.comp x hg.hasMFDerivAt
    rw [mvfderiv, (hL.congr_of_eventuallyEq heq).mfderiv]
    rfl
  simp_rw [hcoeff, ← symmL_basis_eq_localFrame bF hxV, ← map_smul, ← map_sum]
  simp only [Basis.coord_apply, bF.sum_repr, eV.symmL_apply (R := ℝ) hxV]

/-- Coordinate formula for `cov.curvatureTensor` on a general vector bundle `V` in terms of
`bundleChristoffelMap`. -/
private theorem curvatureTensor_symm_trivializationAt_bundle {ι : Type*} [Fintype ι]
    (bF : Basis ι ℝ F) {x₀ x : M} (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hx : x ∈ (extChartAt I x₀).source) (a c : E) (w : F) :
    let Γ := bundleChristoffelMap cov bF x₀
    cov.curvatureTensor x ((trivializationAt E (TangentSpace I) x₀).symm x a)
        ((trivializationAt E (TangentSpace I) x₀).symm x c)
        ((trivializationAt F V x₀).symm x w) =
      (trivializationAt F V x₀).symm x
        (mvfderiv I Γ x ((trivializationAt E (TangentSpace I) x₀).symm x a) w c -
          mvfderiv I Γ x ((trivializationAt E (TangentSpace I) x₀).symm x c) w a +
          Γ x (Γ x w c) a - Γ x (Γ x w a) c) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  have hxT : x ∈ eT.baseSet := by simpa [eT] using hx
  let U := eV.baseSet ∩ eT.baseSet
  have hU : IsOpen U := eV.open_baseSet.inter eT.open_baseSet
  have hxU : x ∈ U := ⟨hxV, hxT⟩
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun U :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov hU
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  set Γ := bundleChristoffelMap cov bF x₀
  have hΓ : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ x :=
    ((contMDiffOn_bundleChristoffelMap cov bF x₀).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt
      (by simp)
  have hX (u : E) : CMDiff[U] ∞ (T% (fun y ↦ eT.symm y u)) :=
    (contMDiffOn_symm_baseSet u).mono inter_subset_right
  have hW : CMDiff[U] ∞ (T% (fun y ↦ eV.symm y w)) :=
    (contMDiffOn_symm_baseSet w).mono inter_subset_left
  have h := cov.curvatureTensor_apply_of_contMDiffOn x hU hxU (hX a) (hX c) hW
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  rw [h, curvatureOperator_apply, mlieBracket_symm_trivializationAt x₀ hx a c, map_zero, sub_zero]
  have hinner (v v' : E) :
      cov (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v')) x (eT.symm x v) =
        eV.symm x (mvfderiv I Γ x (eT.symm x v) w v' + Γ x (Γ x w v') v) := by
    have hL := hasMFDerivAt_clm_apply₂ hΓ w v'
    have hg : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ Γ y w v') x := hL.mdifferentiableAt
    have hsmooth : CMDiff[U] ∞ (T% (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v'))) :=
      ContMDiffOn.clm_bundle_apply (ContMDiffCovariantDerivativeOn.contMDiff hW) (hX v')
    have heq : ∀ᶠ y in 𝓝 x,
        cov (fun z ↦ eV.symm z w) y (eT.symm y v') = eV.symm y (Γ y w v') := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      have hconst := covariantDerivative_symm_comp_apply_symm_bundle cov bF hy.1 hy.2
        (mdifferentiableAt_const (c := w)) v'
      simpa [mvfderiv_const] using hconst
    have hd₁ : MDiffAt (T% (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v'))) x :=
      (hsmooth.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hd₂ : MDiffAt (T% (fun y ↦ eV.symm y (Γ y w v'))) x :=
      hd₁.congr_of_eventuallyEq (heq.mono fun y hy ↦ by dsimp only; rw [hy])
    rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hd₁ hd₂ univ_mem heq,
      covariantDerivative_symm_comp_apply_symm_bundle cov bF hxV hxT hg v]
    rw [mvfderiv, mvfderiv, hL.mfderiv]
    rfl
  have hsub (A B : F) : eV.symm x A - eV.symm x B = eV.symm x (A - B) := by
    simp only [← eV.symmL_apply (R := ℝ) hxV, map_sub]
  rw [hinner a c, hinner c a, hsub]
  congr 1
  abel

section Boundaryless

variable [I.Boundaryless]

/-- Vanishing of `cov.curvatureTensor` at `(extChartAt I x₀).symm z` gives Frobenius integrability
of `(z, w) ↦ -(Γ (φ.symm z) w)` at `(z, w)`. -/
private theorem isFrobeniusIntegrableAt_neg_bundleChristoffelMap {ι : Type*} [Fintype ι]
    (bF : Basis ι ℝ F) {x₀ : M} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hxV : (extChartAt I x₀).symm z ∈ (trivializationAt F V x₀).baseSet)
    (hcurv : cov.curvatureTensor ((extChartAt I x₀).symm z) = 0) (w : F) :
    TauCeti.IsFrobeniusIntegrableAt
      (fun p : E × F ↦ -(bundleChristoffelMap cov bF x₀ ((extChartAt I x₀).symm p.1) p.2))
      (z, w) := by
  let φ := extChartAt I x₀
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  let Γ := bundleChristoffelMap cov bF x₀
  let G : E → F →L[ℝ] E →L[ℝ] F := Γ ∘ φ.symm
  have hx : φ.symm z ∈ φ.source := φ.map_target hz
  have hxT : φ.symm z ∈ eT.baseSet := by simpa [eT, φ, extChartAt_source] using hx
  have hΓdiff : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ (φ.symm z) :=
    ((contMDiffOn_bundleChristoffelMap cov bF x₀).contMDiffAt
      ((eV.open_baseSet.inter eT.open_baseSet).mem_nhds ⟨hxV, hxT⟩)).mdifferentiableAt (by simp)
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I φ.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt
      (by rw [I.range_eq_univ]; exact univ_mem)
  have hGdiff : DifferentiableAt ℝ G z :=
    (hΓdiff.comp z hsymm).differentiableAt
  rw [TauCeti.isFrobeniusIntegrableAt_iff]
  intro a c
  -- Fold `bundleChristoffelMap cov bF x₀ ∘ φ.symm` into `G` so `fderiv_neg_clm_comp` applies.
  change fderiv ℝ (fun p : E × F ↦ -(G p.1 p.2)) (z, w) (a, -(G z w a)) c =
    fderiv ℝ (fun p : E × F ↦ -(G p.1 p.2)) (z, w) (c, -(G z w c)) a
  rw [fderiv_neg_clm_comp hGdiff w a c, fderiv_neg_clm_comp hGdiff w c a]
  have hcurv_coord := curvatureTensor_symm_trivializationAt_bundle cov bF hxV hx c a w
  rw [hcurv] at hcurv_coord
  simp only [LinearMap.zero_apply] at hcurv_coord
  have hinj : mvfderiv I Γ (φ.symm z) (eT.symm (φ.symm z) c) w a -
      mvfderiv I Γ (φ.symm z) (eT.symm (φ.symm z) a) w c +
      Γ (φ.symm z) (Γ (φ.symm z) w a) c - Γ (φ.symm z) (Γ (φ.symm z) w c) a = 0 :=
    (eV.linearEquivAt ℝ (φ.symm z) hxV).symm.map_eq_zero_iff.mp
      (by rw [Bundle.Trivialization.linearEquivAt_symm_apply]; exact hcurv_coord.symm)
  rw [mvfderiv_symm_trivializationAt_eq_fderiv_comp_extChartAt_symm (I := I) hz hΓdiff c,
    mvfderiv_symm_trivializationAt_eq_fderiv_comp_extChartAt_symm (I := I) hz hΓdiff a] at hinj
  have hzero : -(fderiv ℝ G z a w c) + G z (G z w a) c -
      (-(fderiv ℝ G z c w a) + G z (G z w c) a) = 0 := by
    simpa [G, Γ, φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hinj
  exact sub_eq_zero.mp hzero

/-- **Existence of local parallel sections of a flat connection.** On a boundaryless smooth
manifold, if `cov.curvatureTensor` vanishes near `x₀`, then every fibre vector `v₀ ∈ V x₀` extends
to a globally smooth section `σ` of `V` with `σ x₀ = v₀` and `cov σ = 0` near `x₀`. -/
theorem exists_contMDiff_section_eventually_eq_zero {x₀ : M}
    (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) (v₀ : V x₀) :
    ∃ σ : Π x : M, V x, CMDiff ∞ (T% σ) ∧ σ x₀ = v₀ ∧ ∀ᶠ y in 𝓝 x₀, cov σ y = 0 := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  let φ := extChartAt I x₀
  let bF := Basis.ofVectorSpace ℝ F
  have := FiniteDimensional.fintypeBasisIndex bF
  let z₀ : E := φ x₀
  let w₀ : F := (eV ⟨x₀, v₀⟩).2
  let Γ := bundleChristoffelMap cov bF x₀
  let W_E : Set E := φ.target ∩ φ.symm ⁻¹' eV.baseSet
  have hW_E : IsOpen W_E :=
    (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
      eV.open_baseSet
  have hz₀ : z₀ ∈ W_E := ⟨mem_extChartAt_target x₀, by
    simpa [z₀, φ, extChartAt_to_inv] using mem_baseSet_trivializationAt F V x₀⟩
  let f : E × F → E →L[ℝ] F := fun p ↦ -(Γ (φ.symm p.1) p.2)
  -- `f` is `C^∞` on `W_E ×ˢ univ` because `Γ` is smooth on `eV.baseSet ∩ eT.baseSet`.
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) f (W_E ×ˢ univ) := by
    have hΓc : ContDiffOn ℝ ∞ (Γ ∘ φ.symm) W_E := by
      have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm W_E :=
        (contMDiffOn_extChartAt_symm x₀).mono inter_subset_left
      have hmaps : MapsTo φ.symm W_E (eV.baseSet ∩ eT.baseSet) := fun z hz ↦
        ⟨hz.2, by simpa [eT, φ, extChartAt_source] using φ.map_target hz.1⟩
      exact contMDiffOn_iff_contDiffOn.1
        ((contMDiffOn_bundleChristoffelMap cov bF x₀).comp hsymm hmaps)
    have hfst : ContDiffOn ℝ ∞ (fun p : E × F ↦ (Γ ∘ φ.symm) p.1) (W_E ×ˢ univ) :=
      hΓc.comp contDiff_fst.contDiffOn fun p hp ↦ hp.1
    exact (hfst.clm_apply contDiff_snd.contDiffOn).neg
  have hs_nhds : W_E ×ˢ (univ : Set F) ∈ 𝓝 (z₀, w₀) :=
    (hW_E.prod isOpen_univ).mem_nhds ⟨hz₀, trivial⟩
  have hflat_E : ∀ᶠ z in 𝓝 z₀, cov.curvatureTensor (φ.symm z) = 0 := by
    have hcont : ContinuousAt φ.symm z₀ :=
      (continuousAt_extChartAt_symm x₀).congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
    exact hcont.eventually (by simpa [z₀, φ, extChartAt_to_inv] using hflat)
  have hint : ∀ᶠ p in 𝓝 (z₀, w₀), TauCeti.IsFrobeniusIntegrableAt f p := by
    filter_upwards [(continuousAt_fst (X := E) (Y := F)).eventually
      (Filter.inter_mem (hW_E.mem_nhds hz₀) hflat_E)] with p ⟨hpW, hp0⟩
    exact isFrobeniusIntegrableAt_neg_bundleChristoffelMap cov bF hpW.1 hpW.2 hp0 p.2
  -- Solve the total differential equation in `E` and pull the solution slice back to `M`.
  obtain ⟨u, U_EF, hU_EF, hp₀U, husmooth, hu₀, husol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt_univ hf hs_nhds hint
  let S_E : Set E := {z | (z, w₀) ∈ U_EF}
  have hS_E : IsOpen S_E := hU_EF.preimage (continuous_id.prodMk continuous_const)
  let O : Set M := (φ.source ∩ eV.baseSet) ∩ φ ⁻¹' S_E
  have hO : IsOpen O :=
    (continuousOn_extChartAt x₀ |>.mono inter_subset_left).isOpen_inter_preimage
      ((isOpen_extChartAt_source x₀).inter eV.open_baseSet) hS_E
  have hx₀O : x₀ ∈ O :=
    ⟨⟨mem_extChartAt_source x₀, mem_baseSet_trivializationAt F V x₀⟩, hp₀U⟩
  let g : M → F := fun y ↦ u (φ y, w₀)
  have hgO : CMDiff[O] ∞ g := by
    have huS : ContDiffOn ℝ ∞ (fun z : E ↦ u (z, w₀)) S_E :=
      husmooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun z hz ↦ hz
    exact (contMDiffOn_iff_contDiffOn.2 huS).comp
      ((contMDiffOn_extChartAt (I := I) (x := x₀)).mono
        fun y hy ↦ by simpa [φ, extChartAt_source] using hy.1.1) fun y hy ↦ hy.2
  have hsecO : CMDiff[O] ∞ (T% (fun y ↦ eV.symm y (g y))) := by
    refine (eV.contMDiffOn_iff fun y (hy : y ∈ O) ↦ eV.mem_source.mpr hy.1.2).2
      ⟨contMDiffOn_id, ?_⟩
    exact hgO.congr fun y hy ↦ congrArg Prod.snd (eV.apply_mk_symm hy.1.2 (g y))
  -- Cut the local parallel section off by a smooth bump function supported in `O`.
  obtain ⟨χ, -, hχO⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp (hO.mem_nhds hx₀O)
  let σ : Π y : M, V y := fun y ↦ χ y • eV.symm y (g y)
  have hσsmooth : CMDiff ∞ (T% σ) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hO hχO hsecO
  have hσ₀ : σ x₀ = v₀ := by
    simp only [σ, χ.eq_one, one_smul, g, z₀, hu₀, w₀]
    exact eV.symm_apply_apply_mk (mem_baseSet_trivializationAt F V x₀) v₀
  refine ⟨σ, hσsmooth, hσ₀, ?_⟩
  let W_one : Set M := O ∩ interior {y | χ y = 1}
  have hW_one : IsOpen W_one := hO.inter isOpen_interior
  have hx₀W : x₀ ∈ W_one := ⟨hx₀O, mem_interior_iff_mem_nhds.mpr χ.eventuallyEq_one⟩
  filter_upwards [hW_one.mem_nhds hx₀W] with y ⟨hyO, hyχ⟩
  have hσσ' : ∀ᶠ y' in 𝓝 y, σ y' = eV.symm y' (g y') := by
    filter_upwards [isOpen_interior.mem_nhds hyχ] with y' hy'
    have hχ1 : χ y' = 1 := interior_subset hy'
    simp [σ, hχ1]
  have hd_loc : MDiffAt (T% (fun y' ↦ eV.symm y' (g y'))) y :=
    (hsecO.contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp)
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hσsmooth.mdifferentiable (by simp) y) hd_loc univ_mem hσσ']
  have hyT : y ∈ eT.baseSet := by simpa [eT, φ, extChartAt_source] using hyO.1.1
  -- Test vanishing of `cov _ y` on `eT.symm y a` for arbitrary `a : E`.
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : E, eT.symm y a = v :=
    ⟨eT.continuousLinearMapAt ℝ y v, by
      rw [← eT.symmL_apply (R := ℝ) hyT, eT.symmL_continuousLinearMapAt hyT]⟩
  have hgdiff : MDifferentiableAt I 𝓘(ℝ, F) g y :=
    (hgO.contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp)
  rw [covariantDerivative_symm_comp_apply_symm_bundle cov bF hyO.1.2 hyT hgdiff a]
  have hsol_y : HasFDerivAt (fun z ↦ u (z, w₀)) (f (φ y, g y)) (φ y) :=
    husol (φ y, w₀) hyO.2
  have hφy : MDifferentiableAt I 𝓘(ℝ, E) φ y :=
    mdifferentiableAt_extChartAt (by simpa [φ, extChartAt_source] using hyO.1.1)
  have hgd : HasMFDerivAt I 𝓘(ℝ, F) g y ((f (φ y, g y)).comp (mfderiv I 𝓘(ℝ, E) φ y)) :=
    hsol_y.hasMFDerivAt.comp y hφy.hasMFDerivAt
  have hcomp_id : mfderiv I 𝓘(ℝ, E) φ y (eT.symm y a) = a := by
    rw [← eT.symmL_apply (R := ℝ) hyT,
      TangentBundle.symmL_trivializationAt (by simpa [φ, extChartAt_source] using hyO.1.1)]
    exact DFunLike.congr_fun (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hyO.1.1) a
  have hmv : mvfderiv I g y (eT.symm y a) = -(Γ y (g y) a) := by
    rw [mvfderiv, hgd.mfderiv]
    -- Unfold `ContinuousLinearMap.comp` before rewriting `mfderiv φ y (eT.symm y a)`.
    change f (φ y, g y) (mfderiv I 𝓘(ℝ, E) φ y (eT.symm y a)) = -(Γ y (g y) a)
    rw [hcomp_id]
    simp [f, φ.left_inv hyO.1.1]
  rw [hmv, neg_add_cancel, ← eV.symmL_apply (R := ℝ) hyO.1.2, map_zero, zero_apply]

/-- **Existence of a smooth local parallel frame extending a prescribed fibre basis.** If
`cov.curvatureTensor` vanishes near `x₀` on a boundaryless smooth manifold, then any basis `b` of
`V x₀` extends to globally smooth sections `{s i}` forming a smooth local parallel frame on an open
neighbourhood `W` of `x₀`. -/
theorem exists_isLocalFrameOn_parallel_of_basis {ι : Type*} {x₀ : M}
    (b : Basis ι ℝ (V x₀)) (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) :
    ∃ (W : Set M) (s : ι → Π x : M, V x),
      IsOpen W ∧ x₀ ∈ W ∧ (∀ i, CMDiff ∞ (T% (s i))) ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b i) ∧ ∀ y ∈ W, ∀ i, cov (s i) y = 0 := by
  classical
  let eV := trivializationAt F V x₀
  have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
  have : FiniteDimensional ℝ (V x₀) := Finite.equiv (eV.linearEquivAt ℝ x₀ hx₀V).symm
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  choose s hs_smooth hs_init hs_par using
    fun i : ι ↦ cov.exists_contMDiff_section_eventually_eq_zero hflat (b i)
  let bF : Basis ι ℝ F := b.map (eV.linearEquivAt ℝ x₀ hx₀V)
  -- Read the sections `s i` in `eV` as an operator `A y : F →L[ℝ] F` equal to `id` at `x₀`.
  let A : M → F →L[ℝ] F := fun y ↦
    ∑ i, (bF.coord i).toContinuousLinearMap.smulRight (eV ⟨y, s i y⟩).2
  have hA_smooth : CMDiff[eV.baseSet] ∞ A := by
    refine contMDiffOn_finsetSum fun i _ ↦ ?_
    refine (ContinuousLinearMap.smulRightL ℝ F F
      (bF.coord i).toContinuousLinearMap).contDiff.contMDiff.comp_contMDiffOn ?_
    exact ((eV.contMDiffOn_iff fun y (hy : y ∈ eV.baseSet) ↦ eV.mem_source.mpr hy).1
      (hs_smooth i).contMDiffOn).2
  have hA_cont : ContinuousAt A x₀ :=
    hA_smooth.continuousOn.continuousAt (eV.open_baseSet.mem_nhds hx₀V)
  have hA₀ : A x₀ = ContinuousLinearMap.id ℝ F := by
    refine ContinuousLinearMap.coe_injective (bF.ext fun j ↦ ?_)
    have heval : (eV ⟨x₀, s j x₀⟩).2 = bF j := by
      rw [hs_init j]
      simp [bF, Bundle.Trivialization.linearEquivAt_apply]
    simp [A, Basis.coord_apply, Finsupp.single_apply, heval]
  have hA_inv : ∀ᶠ y in 𝓝 x₀, (A y).IsInvertible := by
    have hid : (ContinuousLinearMap.id ℝ F).IsInvertible :=
      ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
    exact hA_cont.eventually (hA₀.symm ▸ hid.eventually_nhds)
  have hall_par : ∀ᶠ y in 𝓝 x₀, ∀ i, cov (s i) y = 0 :=
    eventually_all.mpr hs_par
  obtain ⟨W, hW_sub, hW_open, hx₀W⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (eV.open_baseSet.mem_nhds hx₀V) (hA_inv.and hall_par))
  refine ⟨W, s, hW_open, hx₀W, hs_smooth, ?_, hs_init, fun y hy i ↦ (hW_sub hy).2.2 i⟩
  -- Over `W`, `A y` is invertible, so `{s i y}` is the image of `bF` under a linear equivalence.
  have hbasis_y {y : M} (hy : y ∈ W) :
      ∃ B : Basis ι ℝ (V y), ∀ i, B i = s i y := by
    obtain ⟨hyV, ⟨φ, hφ⟩, -⟩ := hW_sub hy
    refine ⟨bF.map (φ.toLinearEquiv.trans (eV.linearEquivAt ℝ y hyV).symm), fun j ↦ ?_⟩
    have hAj : φ (bF j) = (eV ⟨y, s j y⟩).2 := by
      have h1 := DFunLike.congr_fun hφ (bF j)
      simp only [ContinuousLinearEquiv.coe_coe] at h1
      rw [h1]
      simp [A, Basis.coord_apply, Finsupp.single_apply]
    simp only [Basis.map_apply, LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      hAj, Bundle.Trivialization.linearEquivAt_symm_apply]
    exact eV.symm_apply_apply_mk hyV (s j y)
  refine ⟨fun {y} hy ↦ ?_, fun {y} hy ↦ ?_, fun i ↦ (hs_smooth i).contMDiffOn⟩
  · obtain ⟨B, hB⟩ := hbasis_y hy
    exact (funext hB) ▸ B.linearIndependent
  · obtain ⟨B, hB⟩ := hbasis_y hy
    exact (funext hB) ▸ B.span_eq.ge

/-- **Pointwise germ characterization of flat vector-bundle connections.** On a boundaryless smooth
manifold, `cov.curvatureTensor` vanishes near `x₀` if and only if `V` admits a smooth local
parallel frame on an open neighbourhood of `x₀`. -/
theorem eventually_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn {x₀ : M} :
    (∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) ↔
      ∃ (W : Set M) (s : Fin (finrank ℝ F) → Π x : M, V x),
        IsOpen W ∧ x₀ ∈ W ∧ IsLocalFrameOn I F ∞ s W ∧ ∀ y ∈ W, ∀ i, cov (s i) y = 0 := by
  constructor
  · intro hflat
    let eV := trivializationAt F V x₀
    have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
    let b : Basis (Fin (finrank ℝ F)) ℝ (V x₀) :=
      (finBasis ℝ F).map (eV.linearEquivAt ℝ x₀ hx₀V).symm
    obtain ⟨W, s, hW, hx₀W, -, hs, -, hpar⟩ := cov.exists_isLocalFrameOn_parallel_of_basis b hflat
    exact ⟨W, s, hW, hx₀W, hs, hpar⟩
  · rintro ⟨W, s, hW, hx₀W, hs, hpar⟩
    exact eventually_of_mem (hW.mem_nhds hx₀W) fun y hy ↦
      cov.curvatureTensor_eq_zero_of_isLocalFrameOn_parallel hs hW hpar hy

/-- **Open-set characterization of flat vector-bundle connections.** On an open subset `U` of a
boundaryless smooth manifold, `cov.curvatureTensor` vanishes everywhere on `U` if and only if every
point of `U` has an open neighbourhood `W ⊆ U` carrying a smooth local parallel frame of `V`. -/
theorem forall_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn {U : Set M} (hU : IsOpen U) :
    (∀ x ∈ U, cov.curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (W : Set M) (s : Fin (finrank ℝ F) → Π y : M, V y),
        IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsLocalFrameOn I F ∞ s W ∧ ∀ y ∈ W, ∀ i, cov (s i) y = 0 := by
  constructor
  · intro hflat x hxU
    obtain ⟨W, s, hW, hxW, hs, hpar⟩ :=
      (cov.eventually_curvatureTensor_eq_zero_iff_exists_isLocalFrameOn (x₀ := x)).1
        (eventually_of_mem (hU.mem_nhds hxU) hflat)
    exact ⟨W ∩ U, s, hW.inter hU, ⟨hxW, hxU⟩, inter_subset_right, hs.mono inter_subset_left,
      fun y hy i ↦ hpar y hy.1 i⟩
  · intro h x hxU
    obtain ⟨W, s, hW, hxW, -, hs, hpar⟩ := h x hxU
    exact cov.curvatureTensor_eq_zero_of_isLocalFrameOn_parallel hs hW hpar hxW

/-- **Uniqueness of parallel sections on preconnected flat open sets.** Let `U` be a preconnected
open set on which `cov.curvatureTensor = 0`. Two differentiable parallel sections on `U` that agree
at one point `x₀ ∈ U` agree everywhere on `U`. -/
theorem eqOn_of_parallel {U : Set M} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hflat : ∀ y ∈ U, cov.curvatureTensor y = 0) {σ τ : Π x : M, V x}
    (hσ : MDiff[U] (T% σ)) (hτ : MDiff[U] (T% τ))
    (hσ0 : ∀ y ∈ U, cov σ y = 0) (hτ0 : ∀ y ∈ U, cov τ y = 0)
    {x₀ : M} (hx₀ : x₀ ∈ U) (hinit : σ x₀ = τ x₀) :
    ∀ x ∈ U, σ x = τ x := by
  classical
  let δ : Π x : M, V x := σ - τ
  have hδ : MDiff[U] (T% δ) := mDifferentiableOn_sub_section hσ hτ
  have hδ0 (y : M) (hy : y ∈ U) : cov δ y = 0 := by
    rw [cov.isCovariantDerivativeOnUniv.sub
      ((hσ y hy).mdifferentiableAt (hU.mem_nhds hy))
      ((hτ y hy).mdifferentiableAt (hU.mem_nhds hy)), hσ0 y hy, hτ0 y hy, sub_self]
  -- Show `{y ∈ U | δ y = 0}` is both open and relatively closed in the preconnected set `U`.
  let S : Set M := {y ∈ U | δ y = 0}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyU, hyδ⟩
    -- Expand `δ` in a local trivialization `eV` and use a local parallel frame around `y`.
    let eV := trivializationAt F V y
    have hyV : y ∈ eV.baseSet := mem_baseSet_trivializationAt F V y
    let bF := Basis.ofVectorSpace ℝ F
    have := FiniteDimensional.fintypeBasisIndex bF
    obtain ⟨W, s, hW, hyW, hs_smooth, hs, -, hpar⟩ :=
      cov.exists_isLocalFrameOn_parallel_of_basis (eV.basisAt bF hyV)
        (eventually_of_mem (hU.mem_nhds hyU) hflat)
    -- Rather than differentiating `hs.coeff` directly, invert the smooth coordinate matrix of `s`
    -- in `eV` on `O := (U ∩ eV.baseSet) ∩ W` to obtain differentiable dual functionals.
    let A : M → F →L[ℝ] F := fun z ↦
      ∑ i, (bF.coord i).toContinuousLinearMap.smulRight (eV ⟨z, s i z⟩).2
    have hA_smooth : CMDiff[eV.baseSet] ∞ A := by
      refine contMDiffOn_finsetSum fun i _ ↦ ?_
      refine (ContinuousLinearMap.smulRightL ℝ F F
        (bF.coord i).toContinuousLinearMap).contDiff.contMDiff.comp_contMDiffOn ?_
      exact ((eV.contMDiffOn_iff fun z (hz : z ∈ eV.baseSet) ↦ eV.mem_source.mpr hz).1
        (hs_smooth i).contMDiffOn).2
    have hA_inv (z : M) (hz : z ∈ eV.baseSet ∩ W) : (A z).IsInvertible := by
      let eqv : F ≃L[ℝ] F :=
        (((hs.toBasisAt hz.2).equiv bF (Equiv.refl _)).symm.trans
          (eV.linearEquivAt ℝ z hz.1)).toContinuousLinearEquiv
      refine ⟨eqv, ContinuousLinearMap.coe_injective (bF.ext fun i ↦ ?_)⟩
      simp [A, eqv, Basis.coord_apply, Finsupp.single_apply,
        Bundle.Trivialization.linearEquivAt_apply]
    let O : Set M := (U ∩ eV.baseSet) ∩ W
    have hO : IsOpen O := (hU.inter eV.open_baseSet).inter hW
    have hyO : y ∈ O := ⟨⟨hyU, hyV⟩, hyW⟩
    let c : M → F := fun z ↦ (A z).inverse (eV ⟨z, δ z⟩).2
    have hc_diff : MDifferentiableOn I 𝓘(ℝ, F) c O := by
      intro z hz
      have hinv_diff : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A z) :=
        (hA_inv z ⟨hz.1.2, hz.2⟩).contDiffAt_map_inverse
      have hAz : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) A z :=
        ((hA_smooth.contMDiffAt (eV.open_baseSet.mem_nhds hz.1.2)).mdifferentiableAt (by simp))
      have hδz : MDifferentiableAt I 𝓘(ℝ, F) (fun z' ↦ (eV ⟨z', δ z'⟩).2) z :=
        ((eV.mdifferentiableAt_section_iff I _ hz.1.2).1
          ((hδ z hz.1.1).mdifferentiableAt (hU.mem_nhds hz.1.1)))
      exact ((hinv_diff.contMDiffAt.mdifferentiableAt (by simp)).comp z hAz |>.clm_apply
        hδz).mdifferentiableWithinAt
    have hδ_sum : ∀ z ∈ O, δ z = ∑ i, bF.coord i (c z) • s i z := by
      intro z hz
      have hAc : A z (c z) = (eV ⟨z, δ z⟩).2 :=
        (hA_inv z ⟨hz.1.2, hz.2⟩).self_apply_inverse _
      have heval : (eV ⟨z, ∑ i, bF.coord i (c z) • s i z⟩).2 = (eV ⟨z, δ z⟩).2 := by
        rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hz.1.2, map_sum, ← hAc]
        simp_rw [map_smul, Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hz.1.2]
        simp [A]
      apply (eV.linearEquivAt ℝ z hz.1.2).injective
      rw [Bundle.Trivialization.linearEquivAt_apply, Bundle.Trivialization.linearEquivAt_apply]
      exact heval.symm
    -- Differentiating `δ = ∑ cᵢ • sᵢ` with `cov δ = 0` and `cov sᵢ = 0` gives `dc = 0` on `O`.
    have hc_zero (z : M) (hz : z ∈ O) : mfderiv I 𝓘(ℝ, F) c z = 0 := by
      ext v
      have hcz : MDifferentiableAt I 𝓘(ℝ, F) c z :=
        (hc_diff z hz).mdifferentiableAt (hO.mem_nhds hz)
      have hterm (i : Basis.ofVectorSpaceIndex ℝ F) :
          MDiffAt (T% (fun z' ↦ bF.coord i (c z') • s i z')) z :=
        ((bF.coord i).toContinuousLinearMap.differentiableAt.mdifferentiableAt.comp z
          hcz).smul_section ((hs_smooth i).mdifferentiable (by simp) z)
      have hsum_diff : MDiffAt (T% (fun z' ↦ ∑ i, bF.coord i (c z') • s i z')) z := by
        simpa [Finset.sum_apply] using MDifferentiableAt.sum_section
          (t := fun i z' ↦ bF.coord i (c z') • s i z') (s := Finset.univ) fun i _ ↦ hterm i
      have hev : ∀ᶠ z' in 𝓝 z, δ z' = ∑ i, bF.coord i (c z') • s i z' :=
        eventually_of_mem (hO.mem_nhds hz) hδ_sum
      have h0 : cov (fun z' ↦ ∑ i, bF.coord i (c z') • s i z') z v = 0 := by
        rw [← cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
          ((hδ z hz.1.1).mdifferentiableAt (hU.mem_nhds hz.1.1)) hsum_diff univ_mem hev,
          hδ0 z hz.1.1, zero_apply]
      have hsum_cov : cov (fun z' ↦ ∑ i, bF.coord i (c z') • s i z') z v =
          ∑ i, mvfderiv I (fun z' ↦ bF.coord i (c z')) z v • s i z := by
        have hfn : (fun z' ↦ ∑ i, bF.coord i (c z') • s i z') =
            ∑ i, fun z' ↦ bF.coord i (c z') • s i z' := by ext z'; simp
        rw [hfn, covariantDerivative_sum cov.isCovariantDerivativeOnUniv trivial fun i _ ↦ hterm i,
          sum_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hci : MDiffAt (fun z' ↦ bF.coord i (c z')) z :=
          (bF.coord i).toContinuousLinearMap.differentiableAt.mdifferentiableAt.comp z hcz
        -- Fold pointwise scalar multiplication into section scalar multiplication for `leibniz`.
        change cov ((fun z' ↦ bF.coord i (c z')) • s i) z v =
          mvfderiv I (fun z' ↦ bF.coord i (c z')) z v • s i z
        rw [cov.isCovariantDerivativeOnUniv.leibniz
          ((hs_smooth i).mdifferentiable (by simp) z) hci trivial, hpar z hz.2 i]
        simp
      rw [hsum_cov] at h0
      have hli := linearIndependent_iff'.mp (hs.linearIndependent hz.2) Finset.univ
        (fun i ↦ mvfderiv I (fun z' ↦ bF.coord i (c z')) z v) h0
      rw [zero_apply]
      let w : F := mfderiv I 𝓘(ℝ, F) c z v
      -- Fold `mfderiv I 𝓘(ℝ, F) c z v` into `w` so `Basis.ext_elem` applies.
      change w = 0
      refine bF.ext_elem fun i ↦ ?_
      have hL : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun z' ↦ bF.coord i (c z')) z
          ((bF.coord i).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, F) c z)) :=
        (bF.coord i).toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.comp z hcz.hasMFDerivAt
      have hi := hli i (Finset.mem_univ i)
      rw [mvfderiv, hL.mfderiv] at hi
      have hi' : bF.coord i w = 0 := hi
      simpa [Basis.coord_apply] using hi'
    have hcy : c y = 0 := by
      simp [c, hyδ, ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hyV]
    filter_upwards [hc_diff.eventuallyEq_const_of_mfderiv_eq_zero hO hc_zero hyO,
      hO.mem_nhds hyO] with z hcz hzO
    refine ⟨hzO.1.1, ?_⟩
    rw [hδ_sum z hzO, hcz, hcy]
    simp
  -- `{y ∈ U | δ y ≠ 0}` is also open because `δ` is continuous on `U` and `V y` is Hausdorff.
  have hSc_open : IsOpen (U \ S) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyU, hyS⟩
    have hyne : δ y ≠ 0 := fun h ↦ hyS ⟨hyU, h⟩
    let eV := trivializationAt F V y
    have hyV : y ∈ eV.baseSet := mem_baseSet_trivializationAt F V y
    have hcoord_ne : (eV ⟨y, δ y⟩).2 ≠ 0 := fun h0 ↦ hyne <|
      (eV.linearEquivAt ℝ y hyV).map_eq_zero_iff.mp
        (by rw [Bundle.Trivialization.linearEquivAt_apply]; exact h0)
    have hcont : ContinuousAt (fun z ↦ (eV ⟨z, δ z⟩).2) y :=
      continuous_snd.continuousAt.comp ((eV.continuousAt (eV.mem_source.mpr hyV)).comp
        ((hδ.continuousOn.continuousAt (hU.mem_nhds hyU))))
    filter_upwards [hU.mem_nhds hyU, eV.open_baseSet.mem_nhds hyV,
      hcont.eventually_ne hcoord_ne] with z hzU hzV hzne
    exact ⟨hzU, fun ⟨_, hz0⟩ ↦ hzne (by
      simp [hz0, ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hzV])⟩
  intro y hyU
  by_contra hne
  have hx₀S : x₀ ∈ U ∩ S := ⟨hx₀, hx₀, sub_eq_zero.mpr hinit⟩
  have hySc : y ∈ U ∩ (U \ S) := ⟨hyU, hyU, fun h ↦ hne (sub_eq_zero.mp h.2)⟩
  obtain ⟨z, -, hzS, hzSc⟩ := hconn S (U \ S) hS_open hSc_open
    (fun z hz ↦ by by_cases h : z ∈ S <;> [exact Or.inl h; exact Or.inr ⟨hz, h⟩])
    ⟨x₀, hx₀S⟩ ⟨y, hySc⟩
  exact hzSc.2 hzS

end Boundaryless

end ChartFrobenius

/-! ### Metric-compatible flat connections and local orthonormal parallel frames -/

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

/-- For a metric-compatible connection, the inner product of two differentiable sections that are
parallel on an open set `U` has vanishing differential on `U`, hence agrees locally with a
constant near each point of `U`. -/
theorem IsMetricCompatible.eventuallyEq_inner_of_parallel
    [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    (hcov : cov.IsMetricCompatible) {U : Set M} (hU : IsOpen U)
    {σ τ : Π x : M, V x} (hσ : MDiff[U] (T% σ)) (hτ : MDiff[U] (T% τ))
    (hσ0 : ∀ y ∈ U, cov σ y = 0) (hτ0 : ∀ y ∈ U, cov τ y = 0) {x : M} (hx : x ∈ U) :
    (fun y ↦ inner ℝ (σ y) (τ y)) =ᶠ[𝓝 x] fun _ ↦ inner ℝ (σ x) (τ x) := by
  classical
  have hf : MDifferentiableOn I 𝓘(ℝ, ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) U := fun y hy ↦
    (((hσ y hy).mdifferentiableAt (hU.mem_nhds hy)).inner_bundle
      ((hτ y hy).mdifferentiableAt (hU.mem_nhds hy))).mdifferentiableWithinAt
  refine hf.eventuallyEq_const_of_mfderiv_eq_zero hU (fun y hy ↦ ?_) hx
  ext v
  let X : Π z : M, TangentSpace I z := fun z ↦ if h : z = y then h ▸ v else 0
  have hmv := hcov.mvfderiv_inner_eq X
    ((hσ y hy).mdifferentiableAt (hU.mem_nhds hy))
    ((hτ y hy).mdifferentiableAt (hU.mem_nhds hy))
  dsimp only [X] at hmv
  simp only [↓reduceDIte, hσ0 y hy, hτ0 y hy, zero_apply, inner_zero_left,
    inner_zero_right, add_zero] at hmv
  rw [zero_apply]
  exact hmv

/-- For a metric-compatible connection, the inner product of two differentiable parallel sections
is constant on any preconnected open set `U`. -/
theorem IsMetricCompatible.inner_eq_of_parallel
    [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    (hcov : cov.IsMetricCompatible) {U : Set M} (hU : IsOpen U) (hconn : IsPreconnected U)
    {σ τ : Π x : M, V x} (hσ : MDiff[U] (T% σ)) (hτ : MDiff[U] (T% τ))
    (hσ0 : ∀ y ∈ U, cov σ y = 0) (hτ0 : ∀ y ∈ U, cov τ y = 0)
    {x y : M} (hx : x ∈ U) (hy : y ∈ U) :
    inner ℝ (σ x) (τ x) = inner ℝ (σ y) (τ y) := by
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  have hloc : IsLocallyConstant (fun z : U ↦ inner ℝ (σ z.1) (τ z.1)) :=
    (IsLocallyConstant.iff_eventually_eq _).mpr fun z ↦
      continuous_subtype_val.continuousAt.eventually
        (hcov.eventuallyEq_inner_of_parallel hU hσ hτ hσ0 hτ0 z.2)
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- **Existence of a smooth local orthonormal parallel frame.** On a boundaryless Hausdorff smooth
manifold, if `cov` is smooth, metric-compatible, and has `cov.curvatureTensor = 0` near `x₀`, then
any orthonormal basis `b` of `V x₀` extends to globally smooth sections `{s i}` forming a smooth
local orthonormal parallel frame on an open neighbourhood `W` of `x₀`. -/
theorem IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]
    [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]
    (hcov : cov.IsMetricCompatible) {ι : Type*} [Fintype ι] {x₀ : M}
    (b : OrthonormalBasis ι ℝ (V x₀)) (hflat : ∀ᶠ y in 𝓝 x₀, cov.curvatureTensor y = 0) :
    ∃ (W : Set M) (s : ι → Π x : M, V x),
      IsOpen W ∧ x₀ ∈ W ∧ (∀ i, CMDiff ∞ (T% (s i))) ∧
      IsLocalFrameOn I F ∞ s W ∧ (∀ i, s i x₀ = b i) ∧
      (∀ y ∈ W, Orthonormal ℝ (s · y)) ∧ ∀ y ∈ W, ∀ i, cov (s i) y = 0 := by
  classical
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  obtain ⟨W₀, s, hW₀, hx₀W₀, hs_smooth, hs, hs_init, hpar⟩ :=
    cov.exists_isLocalFrameOn_parallel_of_basis b.toBasis hflat
  have hinner_ev : ∀ᶠ y in 𝓝 x₀, ∀ p : ι × ι,
      inner ℝ (s p.1 y) (s p.2 y) = inner ℝ (b p.1) (b p.2) := by
    refine eventually_all.mpr fun ⟨i, j⟩ ↦ ?_
    have hev := hcov.eventuallyEq_inner_of_parallel hW₀
      ((hs_smooth i).mdifferentiable (by simp)).mdifferentiableOn
      ((hs_smooth j).mdifferentiable (by simp)).mdifferentiableOn
      (fun y hy ↦ hpar y hy i) (fun y hy ↦ hpar y hy j) hx₀W₀
    exact hev.mono fun y hy ↦ by
      simpa only [hs_init i, hs_init j, OrthonormalBasis.coe_toBasis] using hy
  obtain ⟨W₁, hW₁_sub, hW₁_open, hx₀W₁⟩ := mem_nhds_iff.mp hinner_ev
  refine ⟨W₀ ∩ W₁, s, hW₀.inter hW₁_open, ⟨hx₀W₀, hx₀W₁⟩, hs_smooth,
    hs.mono inter_subset_left, hs_init, fun y hy ↦ ?_, fun y hy i ↦ hpar y hy.1 i⟩
  rw [orthonormal_iff_ite]
  intro i j
  have hij : inner ℝ (s i y) (s j y) = inner ℝ (b i) (b j) := hW₁_sub hy.2 (i, j)
  rw [hij]
  exact orthonormal_iff_ite.mp b.orthonormal i j

end MetricCompatible

end CovariantDerivative

end
