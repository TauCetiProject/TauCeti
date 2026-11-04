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
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

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

/-! ### Coordinate Christoffel map and Frobenius integrability on a general bundle -/

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

/-- The Christoffel form of `cov` in the preferred trivializations at `x₀`, transported to a
continuous bilinear map `F →L[ℝ] E →L[ℝ] F`. -/
private def bundleChristoffelMap (x₀ : M) (x : M) : F →L[ℝ] E →L[ℝ] F :=
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  let bF := Module.finBasis ℝ F
  let hcov := cov.isCovariantDerivativeOn (s := eV.baseSet)
  ((eV.continuousLinearMap (RingHom.id ℝ) (eT.continuousLinearMap (RingHom.id ℝ) eV))
    ⟨x, christoffelForm bF hcov x⟩).2

omit [FiniteDimensional ℝ E] [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
private theorem bundleChristoffelMap_apply (x₀ : M) {x : M}
    (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hxT : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (w : F) (u : E) :
    bundleChristoffelMap cov x₀ x w u =
      (trivializationAt F V x₀).continuousLinearMapAt ℝ x
        (christoffelForm (Module.finBasis ℝ F)
          (cov.isCovariantDerivativeOn (s := (trivializationAt F V x₀).baseSet)) x
          ((trivializationAt F V x₀).symmL ℝ x w)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x u)) := by
  have hxe : x ∈ ((trivializationAt E (TangentSpace I) x₀).continuousLinearMap
      (RingHom.id ℝ) (trivializationAt F V x₀)).baseSet := ⟨hxT, hxV⟩
  simp only [bundleChristoffelMap, Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMap
      (RingHom.id ℝ) (trivializationAt F V x₀)) hxe]
  simp only [Bundle.Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply]

omit [FiniteDimensional ℝ E] [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
private theorem covariantDerivative_symm_apply_symm_bundle (x₀ : M) {x : M}
    (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hxT : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (w : F) (u : E) :
    cov (fun y ↦ (trivializationAt F V x₀).symm y w) x
        ((trivializationAt E (TangentSpace I) x₀).symm x u) =
      (trivializationAt F V x₀).symm x (bundleChristoffelMap cov x₀ x w u) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  let bF := Module.finBasis ℝ F
  let hcov := cov.isCovariantDerivativeOn (s := eV.baseSet)
  rw [covariantDerivative_symm_eq_christoffelForm bF hcov hxV,
    bundleChristoffelMap_apply cov x₀ hxV hxT,
    eV.symmL_apply (R := ℝ) hxV, eT.symmL_apply (R := ℝ) hxT,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eV hxV]
  exact (eV.symm_apply_apply_mk hxV _).symm

omit [FiniteDimensional ℝ E] [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
private theorem covariantDerivative_symm_comp_apply_symm_bundle (x₀ : M) {x : M}
    (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hxT : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {g : M → F} (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) (u : E) :
    cov (fun y ↦ (trivializationAt F V x₀).symm y (g y)) x
        ((trivializationAt E (TangentSpace I) x₀).symm x u) =
      (trivializationAt F V x₀).symm x
        (mvfderiv I g x ((trivializationAt E (TangentSpace I) x₀).symm x u) +
          bundleChristoffelMap cov x₀ x (g x) u) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  let bF := Module.finBasis ℝ F
  let hcov := cov.isCovariantDerivativeOn (s := eV.baseSet)
  have hread : ∀ᶠ y in 𝓝 x, (eV ⟨y, eV.symm y (g y)⟩).2 = g y :=
    eventually_of_mem (eV.open_baseSet.mem_nhds hxV) fun y hy ↦ by rw [eV.apply_mk_symm hy]
  have hσ : MDiffAt (T% (fun y ↦ eV.symm y (g y))) x :=
    (eV.mdifferentiableAt_section_iff I _ hxV).2 (hg.congr_of_eventuallyEq hread)
  rw [covariantDerivative_eq_add_christoffelForm bF hcov hxV hσ, add_apply,
    ← eV.symmL_apply (R := ℝ) hxV (_ + _), map_add,
    bundleChristoffelMap_apply cov x₀ hxV hxT,
    eV.symmL_continuousLinearMapAt (R := ℝ) hxV,
    eV.symmL_apply (R := ℝ) hxV, eV.symmL_apply (R := ℝ) hxV, eT.symmL_apply (R := ℝ) hxT]
  congr 1
  rw [frameCovariantDerivative_apply]
  have hcoeff (i : Fin (Module.finrank ℝ F)) :
      mvfderiv I ((LinearMap.piApply (eV.localFrameCoeff I bF i))
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
    -- `NormedSpace.fromTangentSpace` is the identity on `ℝ` and `F`.
    rfl
  simp_rw [hcoeff, ← symmL_basis_eq_localFrame bF hxV, ← map_smul, ← map_sum]
  simp only [Basis.coord_apply, bF.sum_repr, eV.symmL_apply (R := ℝ) hxV]

private theorem contMDiffOn_bundleChristoffelMap (x₀ : M) :
    CMDiff[(trivializationAt F V x₀).baseSet ∩ (trivializationAt E (TangentSpace I) x₀).baseSet] ∞
      (bundleChristoffelMap cov x₀) := by
  let eV := trivializationAt F V x₀
  let eT := trivializationAt E (TangentSpace I) x₀
  let bF := Module.finBasis ℝ F
  let hcov := cov.isCovariantDerivativeOn (s := eV.baseSet)
  let O := eV.baseSet ∩ eT.baseSet
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun eV.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov eV.open_baseSet
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let eTV := eT.continuousLinearMap (RingHom.id ℝ) eV
  let eh := eV.continuousLinearMap (RingHom.id ℝ) eTV
  have hmaps : MapsTo (id : M → M) O (eV.baseSet ∩ eTV.baseSet) := fun y hy ↦
    ⟨hy.1, ⟨hy.2, hy.1⟩⟩
  have hframeEval (j : Fin (Module.finrank ℝ F)) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y
          (christoffelForm bF hcov y (eV.localFrame bF j y))) O := by
    have hj : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y
          (cov (eV.localFrame bF j) y)) eV.baseSet :=
      ContMDiffCovariantDerivativeOn.contMDiff (eV.contMDiffOn_localFrame_baseSet (∞ + 1) bF j)
    refine (hj.mono inter_subset_left).congr fun y hy ↦ ?_
    congr 1
    rw [christoffelForm_apply bF hcov hy.1]
    simp [localFrameCoeff_localFrame bF hy.1]
  have hsec : ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun z ↦ V z →L[ℝ] TangentSpace I z →L[ℝ] V z) y
        (christoffelForm bF hcov y)) O :=
    contMDiffOn_hom_of_localFrame (e' := eTV) bF contMDiffOn_id hmaps hframeEval
  exact ((eh.contMDiffOn_iff fun y hy ↦ eh.mem_source.mpr (hmaps hy)).1 hsec).2

/-- In the preferred trivializations at `x₀`, the curvature tensor of `cov` has the coordinate
formula `dΓ(a)(w, c) - dΓ(c)(w, a) + Γ(Γ(w, c), a) - Γ(Γ(w, a), c)`. -/
private theorem curvatureTensor_symm_trivializationAt_bundle (x₀ : M) {x : M}
    (hxV : x ∈ (trivializationAt F V x₀).baseSet)
    (hxchart : x ∈ (extChartAt I x₀).source) (a c : E) (w : F) :
    let Γ := bundleChristoffelMap cov x₀
    cov.curvatureTensor x
        ((trivializationAt E (TangentSpace I) x₀).symm x a)
        ((trivializationAt E (TangentSpace I) x₀).symm x c)
        ((trivializationAt F V x₀).symm x w) =
      (trivializationAt F V x₀).symm x
        (mvfderiv I Γ x ((trivializationAt E (TangentSpace I) x₀).symm x a) w c -
          mvfderiv I Γ x ((trivializationAt E (TangentSpace I) x₀).symm x c) w a +
          Γ x (Γ x w c) a - Γ x (Γ x w a) c) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  let O := eV.baseSet ∩ eT.baseSet
  have hxT : x ∈ eT.baseSet := by simpa [eT] using hxchart
  have hxO : x ∈ O := ⟨hxV, hxT⟩
  have hOopen : IsOpen O := eV.open_baseSet.inter eT.open_baseSet
  set Γ := bundleChristoffelMap cov x₀
  have hΓ : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ x :=
    ((contMDiffOn_bundleChristoffelMap cov x₀).contMDiffAt
      (hOopen.mem_nhds hxO)).mdifferentiableAt (by simp)
  have : ContMDiffCovariantDerivativeOn F ∞ cov.toFun eV.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov eV.open_baseSet
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hX (u : E) : CMDiff[O] ∞ (T% (fun y ↦ eT.symm y u)) :=
    (contMDiffOn_symm_baseSet u).mono inter_subset_right
  have hσw : CMDiff[O] ∞ (T% (fun y ↦ eV.symm y w)) :=
    (contMDiffOn_symm_baseSet w).mono inter_subset_left
  have h := cov.curvatureTensor_apply_of_contMDiffOn x hOopen hxO (hX a) (hX c) hσw
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  rw [h, curvatureOperator_apply, mlieBracket_symm_trivializationAt x₀ hxchart a c, map_zero,
    sub_zero]
  have hinner (v v' : E) :
      cov (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v')) x (eT.symm x v) =
        eV.symm x (mvfderiv I Γ x (eT.symm x v) w v' + Γ x (Γ x w v') v) := by
    have hL_diff : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ Γ y w v') x :=
      (hΓ.clm_apply mdifferentiableAt_const).clm_apply mdifferentiableAt_const
    have hL_mv : mvfderiv I (fun y ↦ Γ y w v') x (eT.symm x v) =
        mvfderiv I Γ x (eT.symm x v) w v' :=
      mvfderiv_clm_apply_const_apply₂ hΓ w v' (eT.symm x v)
    have hsmooth : CMDiff[O] ∞
        (T% (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v'))) :=
      ContMDiffOn.clm_bundle_apply
        ((ContMDiffCovariantDerivativeOn.contMDiff
          (contMDiffOn_symm_baseSet (e := eV) (n := ∞ + 1) w)).mono inter_subset_left)
        (hX v')
    have heq : ∀ᶠ y in 𝓝 x, cov (fun z ↦ eV.symm z w) y (eT.symm y v') = eV.symm y (Γ y w v') :=
      eventually_of_mem (hOopen.mem_nhds hxO) fun y hy ↦
        covariantDerivative_symm_apply_symm_bundle cov x₀ hy.1 hy.2 w v'
    have hd₁ : MDiffAt (T% (fun y ↦ cov (fun z ↦ eV.symm z w) y (eT.symm y v'))) x :=
      (hsmooth.contMDiffAt (hOopen.mem_nhds hxO)).mdifferentiableAt (by simp)
    have hd₂ : MDiffAt (T% (fun y ↦ eV.symm y (Γ y w v'))) x :=
      hd₁.congr_of_eventuallyEq (heq.mono fun y hy ↦ by simp only [hy])
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq hd₁ hd₂ univ_mem heq,
      covariantDerivative_symm_comp_apply_symm_bundle cov x₀ hxV hxT hL_diff v, hL_mv]
  have hsub (A B : F) : eV.symm x A - eV.symm x B = eV.symm x (A - B) := by
    simp only [← eV.symmL_apply (R := ℝ) hxV, map_sub]
  rw [hinner a c, hinner c a, hsub]
  congr 1
  abel

/-- Vanishing of `cov.curvatureTensor` at `(extChartAt I x₀).symm z` implies Frobenius
integrability of the total differential equation `D u z = -Γ((extChartAt I x₀).symm z)(u z)` at
every fibre point `(z, w)`. -/
private theorem isFrobeniusIntegrableAt_neg_bundleChristoffelMap (x₀ : M) {z : E}
    (hz : z ∈ interior (extChartAt I x₀).target)
    (hzV : (extChartAt I x₀).symm z ∈ (trivializationAt F V x₀).baseSet)
    (hflat : cov.curvatureTensor ((extChartAt I x₀).symm z) = 0) (w : F) :
    IsFrobeniusIntegrableAt
      (fun p : E × F ↦ -bundleChristoffelMap cov x₀ ((extChartAt I x₀).symm p.1) p.2) (z, w) := by
  set eV := trivializationAt F V x₀
  set eT := trivializationAt E (TangentSpace I) x₀
  set y := (extChartAt I x₀).symm z with hy_def
  have hzt : z ∈ (extChartAt I x₀).target := interior_subset hz
  have hysrc : y ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hzt
  have hyT : y ∈ eT.baseSet := by simpa [eT] using hysrc
  have hyz : extChartAt I x₀ y = z := (extChartAt I x₀).right_inv hzt
  set Γ := bundleChristoffelMap cov x₀
  set ΓE : E → F →L[ℝ] E →L[ℝ] F := fun ζ ↦ Γ ((extChartAt I x₀).symm ζ) with hΓE_def
  -- Smoothness of `ΓE` at `z` comes from `Γ` on `eV.baseSet ∩ eT.baseSet` and the inverse
  -- extended chart on `interior (extChartAt I x₀).target`.
  let OE : Set E := interior (extChartAt I x₀).target ∩
    (extChartAt I x₀).symm ⁻¹' eV.baseSet
  have hφsymm : CMDiff[interior (extChartAt I x₀).target] ∞ (extChartAt I x₀).symm :=
    (contMDiffOn_extChartAt_symm x₀).mono interior_subset
  have hOEopen : IsOpen OE :=
    hφsymm.continuousOn.isOpen_inter_preimage isOpen_interior eV.open_baseSet
  have hzOE : z ∈ OE := ⟨hz, hzV⟩
  have hΓE_mdiffOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) ∞ ΓE OE :=
    (contMDiffOn_bundleChristoffelMap cov x₀).comp (hφsymm.mono inter_subset_left) fun ζ hζ ↦
      ⟨hζ.2, by simpa [eT] using (extChartAt I x₀).map_target (interior_subset hζ.1)⟩
  have hΓE_diff : DifferentiableAt ℝ ΓE z :=
    (((contMDiffOn_iff_contDiffOn.1 hΓE_mdiffOn).contDiffAt
      (hOEopen.mem_nhds hzOE)).differentiableAt (by simp))
  -- Relate `fderiv ℝ ΓE z a` to `mvfderiv I Γ y (eT.symm y a)`.
  have hΓ_mdiff : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F) Γ y :=
    ((contMDiffOn_bundleChristoffelMap cov x₀).contMDiffAt
      ((eV.open_baseSet.inter eT.open_baseSet).mem_nhds ⟨hzV, hyT⟩)).mdifferentiableAt (by simp)
  have hsymm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm z :=
    (hφsymm.contMDiffAt (isOpen_interior.mem_nhds hz)).mdifferentiableAt (by simp)
  have hfderiv_ΓE (a : E) : fderiv ℝ ΓE z a = mvfderiv I Γ y (eT.symm y a) := by
    have hcomp := mvfderiv_comp_apply_of_eq z hΓ_mdiff hsymm_mdiff hy_def.symm
      ((NormedSpace.fromTangentSpace z).symm a)
    have hsymmL : eT.symm y a =
        mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z ((NormedSpace.fromTangentSpace z).symm a) := by
      have hchart : y ∈ (chartAt H x₀).source := by simpa using hysrc
      rw [← eT.symmL_apply (R := ℝ) hyT, TangentBundle.symmL_trivializationAt hchart, hyz,
        mfderivWithin_of_mem_nhds
          (mem_of_superset (isOpen_interior.mem_nhds hz)
            (interior_subset.trans (extChartAt_target_subset_range x₀)))]
      rfl
    rw [Function.comp_def, ← hΓE_def, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ← hsymmL] at hcomp
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hcomp
  -- Compute `fderiv ℝ f (z, w)` by the product rule for continuous linear map application.
  let f : E × F → E →L[ℝ] F := fun p ↦ -ΓE p.1 p.2
  have hf_deriv : HasFDerivAt f
      (-((ΓE z).comp (ContinuousLinearMap.snd ℝ E F) +
        ((fderiv ℝ ΓE z).comp (ContinuousLinearMap.fst ℝ E F)).flip w)) (z, w) := by
    have h1 : HasFDerivAt (ΓE ∘ Prod.fst)
        ((fderiv ℝ ΓE z).comp (ContinuousLinearMap.fst ℝ E F)) (z, w) :=
      hΓE_diff.hasFDerivAt.comp (z, w) hasFDerivAt_fst
    have h2 : HasFDerivAt (fun p : E × F ↦ p.2) (ContinuousLinearMap.snd ℝ E F) (z, w) :=
      hasFDerivAt_snd
    exact (h1.clm_apply h2).neg
  rw [isFrobeniusIntegrableAt_iff]
  intro a c
  have hcurv := curvatureTensor_symm_trivializationAt_bundle cov x₀ hzV hysrc a c w
  simp only [hflat, LinearMap.zero_apply] at hcurv
  have hinj : mvfderiv I Γ y (eT.symm y a) w c - mvfderiv I Γ y (eT.symm y c) w a +
      Γ y (Γ y w c) a - Γ y (Γ y w a) c = 0 := by
    have h0 := congrArg (eV.continuousLinearMapAt ℝ y) hcurv.symm
    rw [map_zero] at h0
    dsimp only [eV, eT, Γ] at h0 ⊢
    rwa [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt F V x₀) hzV, (trivializationAt F V x₀).apply_mk_symm hzV] at h0
  rw [hf_deriv.fderiv]
  have heval (ξ η : E) :
      ((-((ΓE z).comp (ContinuousLinearMap.snd ℝ E F) +
        ((fderiv ℝ ΓE z).comp (ContinuousLinearMap.fst ℝ E F)).flip w)) (ξ, f (z, w) ξ)) η =
        -mvfderiv I Γ y (eT.symm y ξ) w η + Γ y (Γ y w ξ) η := by
    simp only [f, neg_apply, add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      map_neg, hfderiv_ΓE]
    dsimp only [ΓE, y]
    abel
  rw [heval a c, heval c a, ← sub_eq_zero]
  convert neg_eq_zero.2 hinj using 1
  abel

/-! ### Local parallel sections and frames from vanishing curvature -/

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
  let φ := extChartPartialDiffeomorph I ∞ x₀
  let z₀ : E := extChartAt I x₀ x₀
  let y₀ : F := eV.continuousLinearMapAt ℝ x₀ w₀
  have hx₀V : x₀ ∈ eV.baseSet := mem_baseSet_trivializationAt F V x₀
  have hz₀ : z₀ ∈ interior (extChartAt I x₀).target := I.isInteriorPoint_iff.1 hx₀
  have hx₀φ : x₀ ∈ φ.source := (mem_extChartPartialDiffeomorph_source I ∞ x₀).2 hx₀
  let OE : Set E := interior (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' eV.baseSet
  have hφsymm : CMDiff[interior (extChartAt I x₀).target] ∞ (extChartAt I x₀).symm :=
    (contMDiffOn_extChartAt_symm x₀).mono interior_subset
  have hOE : IsOpen OE :=
    hφsymm.continuousOn.isOpen_inter_preimage isOpen_interior eV.open_baseSet
  have hz₀OE : z₀ ∈ OE := ⟨hz₀, by simpa [z₀] using hx₀V⟩
  set Γ := bundleChristoffelMap cov x₀
  let ΓE : E → F →L[ℝ] E →L[ℝ] F := fun ζ ↦ Γ ((extChartAt I x₀).symm ζ)
  have hΓE : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) ΓE OE :=
    contMDiffOn_iff_contDiffOn.1 <|
      (contMDiffOn_bundleChristoffelMap cov x₀).comp (hφsymm.mono inter_subset_left) fun ζ hζ ↦
        ⟨hζ.2, by simpa [eT] using (extChartAt I x₀).map_target (interior_subset hζ.1)⟩
  let f : E × F → E →L[ℝ] F := fun p ↦ -ΓE p.1 p.2
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) + 1) f (OE ×ˢ univ) :=
    ((hΓE.comp (contDiffOn_fst (s := OE ×ˢ univ)) fun _ hp ↦ hp.1).clm_apply contDiffOn_snd).neg
  have hint : ∀ᶠ p in 𝓝 (z₀, y₀), IsFrobeniusIntegrableAt f p := by
    have hcont : ContinuousAt ((extChartAt I x₀).symm ∘ Prod.fst) (z₀, y₀) :=
      ContinuousAt.comp (g := (extChartAt I x₀).symm) (f := Prod.fst)
        (hφsymm.continuousOn.continuousAt (isOpen_interior.mem_nhds hz₀)) continuousAt_fst
    have hflat' : ∀ᶠ p in 𝓝 (z₀, y₀), cov.curvatureTensor ((extChartAt I x₀).symm p.1) = 0 :=
      hcont.eventually (by simpa [z₀] using hflat)
    filter_upwards [(hOE.prod isOpen_univ).mem_nhds ⟨hz₀OE, mem_univ _⟩, hflat']
      with ⟨z, w⟩ ⟨hzE, _⟩ hzf
    exact isFrobeniusIntegrableAt_neg_bundleChristoffelMap cov x₀ hzE.1 hzE.2 hzf w
  -- Solve the total differential equation `D u = f` smoothly near `(z₀, y₀)`.
  obtain ⟨u, U, hU, hp₀U, husmooth, hu₀, -, husol⟩ :=
    exists_contDiffOn_solution_family_of_isFrobeniusIntegrableAt hf
      ((hOE.prod isOpen_univ).mem_nhds ⟨hz₀OE, mem_univ _⟩) hint
  let WE : Set E := (fun z ↦ (z, y₀)) ⁻¹' U ∩ OE
  have hWE : IsOpen WE := (hU.preimage (continuous_id.prodMk continuous_const)).inter hOE
  have hz₀WE : z₀ ∈ WE := ⟨hp₀U, hz₀OE⟩
  let u₀ : E → F := fun z ↦ u (z, y₀)
  have hu₀_smooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u₀ WE :=
    contMDiffOn_iff_contDiffOn.2 <|
      husmooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hz ↦ hz.1
  -- Pull the local coordinate solution back to an open neighbourhood `WM` of `x₀` in `M`.
  let WM : Set M := eV.baseSet ∩ (φ.source ∩ extChartAt I x₀ ⁻¹' WE)
  have hφto : CMDiff[φ.source] ∞ (extChartAt I x₀) := by
    simpa only [φ, coe_extChartPartialDiffeomorph] using φ.contMDiffOn_toFun
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
  have hσloc_par (y : M) (hy : y ∈ WM) : cov σloc y = 0 := by
    have hysrc : y ∈ (extChartAt I x₀).source :=
      ((extChartPartialDiffeomorph_source I ∞ x₀) ▸ hy.2.1).1
    have hyT : y ∈ eT.baseSet := by simpa [eT] using hysrc
    have hychart : y ∈ (chartAt H x₀).source := by simpa using hysrc
    have hg_diff : MDifferentiableAt I 𝓘(ℝ, F) g y :=
      (hg_smooth.contMDiffAt (hWM.mem_nhds hy)).mdifferentiableAt (by simp)
    ext w
    rw [← eT.symmL_continuousLinearMapAt (R := ℝ) hyT w, eT.symmL_apply (R := ℝ) hyT]
    set a := eT.continuousLinearMapAt ℝ y w
    rw [covariantDerivative_symm_comp_apply_symm_bundle cov x₀ hy.1 hyT hg_diff a]
    -- By the chain rule and `TangentBundle.continuousLinearMapAt_trivializationAt`, the
    -- coordinate directional derivative along `eT.symm y a` evaluates `D u₀` on `a`.
    have hsol_y : HasFDerivAt u₀ (f (extChartAt I x₀ y, u₀ (extChartAt I x₀ y)))
        (extChartAt I x₀ y) := husol _ hy.2.2.1
    have hchart_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) y :=
      mdifferentiableAt_extChartAt hychart
    have hclm : mvfderiv I (extChartAt I x₀) y (eT.symm y a) = a := by
      calc mvfderiv I (extChartAt I x₀) y (eT.symm y a)
        _ = eT.continuousLinearMapAt ℝ y (eT.symmL ℝ y a) := by
            rw [eT.symmL_apply (R := ℝ) hyT,
              TangentBundle.continuousLinearMapAt_trivializationAt hychart]
            rfl
        _ = a := eT.continuousLinearMapAt_symmL (R := ℝ) hyT a
    have hmv : mvfderiv I g y (eT.symm y a) = -Γ y (g y) a := by
      have hchain := mvfderiv_comp_apply_of_differentiableAt hsol_y.differentiableAt
        hchart_diff (eT.symm y a)
      rw [Function.comp_def, ← hg_def, hclm, hsol_y.fderiv] at hchain
      dsimp only [f, ΓE, g] at hchain ⊢
      rwa [(extChartAt I x₀).left_inv hysrc, neg_apply] at hchain
    rw [hmv, neg_add_cancel, ← eV.symmL_apply (R := ℝ) hy.1, map_zero, zero_apply]
  -- Cut `σloc` off by a smooth bump function supported in `WM`.
  obtain ⟨χ, -, hχsub⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp (hWM.mem_nhds hx₀WM)
  let σ : Π y : M, V y := fun y ↦ χ y • σloc y
  have hσ_smooth : CMDiff ∞ (T% σ) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hWM hχsub hσloc_smooth
  have hσ_x₀ : σ x₀ = w₀ := by
    simp only [σ, χ.eq_one, one_smul, σloc, g, u₀, hu₀, y₀]
    rw [← eV.symmL_apply (R := ℝ) hx₀V, eV.symmL_continuousLinearMapAt hx₀V]
  refine ⟨σ, hσ_smooth, hσ_x₀, ?_⟩
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
