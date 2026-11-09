/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.LinearAlgebra.TotallyReal.CompatibleForm
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.LinearAlgebra.TotallyReal.Frame

/-!
# Hermitian metrics compatible with a totally real subbundle

Let `V` be a smooth complex vector bundle over a real manifold and `L` a smooth real subbundle
of `V` whose fibres are maximal totally real, so that `V x = L x ⊕ i L x`. Write `P x` for the
projection of `V x` onto `L x` along `i L x`. For any smooth real bundle metric `g`, the metric

`g'(v, w) = g(P v, P w) + g(P (i v), P (i w))`

is again a smooth bundle metric. It is invariant under multiplication by `i`, so it is the real
part of a Hermitian metric, it agrees with `g` on `L`, and `i L x` is the `g'`-orthogonal
complement of `L x` at every point. Such metrics therefore exist whenever bundle metrics do,
for instance over a σ-compact Hausdorff base.

Smoothness of `P` is checked in a local frame `X` of `L`: read in a trivialization, the real
frame `X` becomes a smooth family of complex-linear isomorphisms `ℂᵏ → F`, and `P` is the
conjugate by this family of the coordinatewise real part. The same computation is local: near a
point where a `C^n` frame of `L` is a complex basis it stays one, so maximal total reality is an
open condition along `L`, and the projection is `C^n` wherever it is defined on a neighbourhood.

This gives the relative form needed for boundary value problems. When `L` is only given near a
closed set `S`, such as the boundary of a manifold with boundary, and is maximal totally real
over `S`, there is a smooth Hermitian metric with `i L x = (L x)^⊥` at the points of `S`: near `S`
use the compatible form of a fixed metric, away from `S` its Hermitian average, and glue with a
smooth partition of unity. This works because, at each point, the conditions on the metric are
convex.

## Main declarations

* `TauCeti.totallyRealProjection`: the fibrewise projection `P x`.
* `TauCeti.eventually_isMaximalTotallyReal`: along a `C^n` frame, maximal total reality is an
  open condition.
* `TauCeti.contMDiffAt_totallyRealProjection`, `TauCeti.contMDiff_totallyRealProjection`: `P` is
  a smooth bundle endomorphism.
* `Bundle.ContMDiffRiemannianMetric.totallyRealCompatible`: the metric `g'`.
* `TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal`: a smooth Hermitian metric
  with `i L x = (L x)^⊥` at every point exists over a σ-compact Hausdorff base.
* `TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal_on`: the same along a closed
  set `S`, for `L` given only near `S` and maximal totally real over `S`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS (2012), Section C.1.
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace TauCeti

section Projection

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {ι : Type*} [Finite ι] {L : ∀ x, Submodule ℝ (V x)}

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

variable (F) in
/-- The projection of a fibre onto a maximal totally real subspace along its `i`-image, as a
continuous real-linear map. It is continuous because the fibre is finite-dimensional. -/
def totallyRealProjection {x : B} {L : Submodule ℝ (V x)}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) L) :
    V x →L[ℝ] V x where
  toLinearMap := L.projection _ hL.isCompl
  cont := by
    let e := VectorBundle.continuousLinearEquivAt ℝ F V x
    let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
    let f : F →ₗ[ℝ] F := e.toLinearEquiv.toLinearMap ∘ₗ L.projection _ hL.isCompl ∘ₗ
      e.symm.toLinearEquiv.toLinearMap
    have hf : ⇑(L.projection _ hL.isCompl) = e.symm ∘ f ∘ e := by
      funext v
      simp [f]
    -- The `cont` field is stated for the bare `toFun` of the linear map; restate it for the
    -- function coercion so that `hf` can rewrite it.
    change Continuous ⇑(L.projection _ hL.isCompl)
    rw [hf]
    exact e.symm.continuous.comp (f.continuous_of_finiteDimensional.comp e.continuous)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- Evaluation of the fibrewise projection. -/
@[simp]
theorem totallyRealProjection_apply {x : B} {L : Submodule ℝ (V x)}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) L)
    (v : V x) : totallyRealProjection F hL v = L.projection _ hL.isCompl v :=
  (rfl)

section Frame

variable {U : Set B} {X : ι → Π x, V x}

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)] [Finite ι] in
/-- Read in the trivialization at `x₀`, a real frame `X` of `L` on `U` is the complex-linear
operator `c ↦ ∑ i, c i • X i y`. At a point of `U` where `L` is maximal totally real, this
operator is bijective: the real frame of `L y` is a complex basis of `V y`. -/
private theorem bijective_trivOperator [Fintype ι] (hX : IsSubbundleFrameOn F L X U)
    {x₀ y : B} (hyU : y ∈ U) (hy : y ∈ (trivializationAt F V x₀).baseSet)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y)) :
    Function.Bijective (IsSubbundleFrameOn.trivOperator ℂ F X x₀ y) := by
  set e := trivializationAt F V x₀
  have hAapply (c : ι → ℂ) : IsSubbundleFrameOn.trivOperator ℂ F X x₀ y c =
      (e ⟨y, ∑ i, c i • X i y⟩).2 :=
    IsSubbundleFrameOn.trivOperator_apply hy c
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_, fun w ↦ ?_⟩
  · have h := hAapply c
    rw [hc] at h
    have hc' : ∑ i, c i • X i y = 0 := (e.continuousLinearEquivAt ℂ y hy).injective (by
      rw [map_zero, Trivialization.continuousLinearEquivAt_apply]
      exact h.symm)
    have hli := hL.isTotallyReal.linearIndependent_complex (hX.linearIndependent hyU)
      (fun i ↦ hX.apply_mem i hyU)
    funext i
    exact Fintype.linearIndependent_iff.1 hli c hc' i
  · have hspan := hL.span_complex_eq_top (hX.span_eq hyU)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (hspan ▸ Submodule.mem_top : e.symm y w ∈ Submodule.span ℂ (range (X · y)))
    exact ⟨c, by rw [hAapply, hc, e.apply_mk_symm hy]⟩

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)] [Finite ι] in
/-- Conversely, where the frame operator is bijective, `L` is maximal totally real. -/
private theorem isMaximalTotallyReal_of_bijective_trivOperator [Fintype ι]
    (hX : IsSubbundleFrameOn F L X U)
    {x₀ y : B} (hyU : y ∈ U) (hy : y ∈ (trivializationAt F V x₀).baseSet)
    (hA : Function.Bijective (IsSubbundleFrameOn.trivOperator ℂ F X x₀ y)) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) := by
  set e := trivializationAt F V x₀
  let T : (ι → ℝ) →ₗ[ℝ] V y := Fintype.linearCombination ℝ (X · y)
  have hT : LinearMap.range T = L y := by
    rw [Fintype.range_linearCombination, hX.span_eq hyU]
  -- The doubled frame `(a, b) ↦ ∑ a i • X i y + i ∑ b i • X i y` is the frame operator applied
  -- to `a + i b`.
  let φ : (ι → ℝ) × (ι → ℝ) → ι → ℂ := fun p i ↦ p.1 i + p.2 i * Complex.I
  have hφ : Function.Bijective φ := by
    refine ⟨fun p q h ↦ ?_, fun c ↦ ⟨(fun i ↦ (c i).re, fun i ↦ (c i).im), ?_⟩⟩
    · have hre i := congrArg Complex.re (congrFun h i)
      have him i := congrArg Complex.im (congrFun h i)
      simp only [φ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
        Complex.mul_im, zero_add] at hre him
      exact Prod.ext (funext hre) (funext him)
    · funext i
      simp [φ, Complex.re_add_im]
  have hcoprod : ⇑(T.coprod (((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ).comp T)) =
      (e.continuousLinearEquivAt ℂ y hy).symm ∘ IsSubbundleFrameOn.trivOperator ℂ F X x₀ y ∘ φ := by
    funext p
    have hsmul (a : ℝ) (v : V y) : (a : ℂ) • v = a • v := algebraMap_smul ℂ a v
    rw [Function.comp_apply, Function.comp_apply, IsSubbundleFrameOn.trivOperator_apply hy,
      Trivialization.continuousLinearEquivAt_symm_apply, e.symm_apply_apply_mk hy]
    simp only [LinearMap.coprod_apply, LinearMap.comp_apply, T, Fintype.linearCombination_apply,
      LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, φ, Finset.smul_sum, add_smul,
      Finset.sum_add_distrib, hsmul, mul_comm _ Complex.I, mul_smul]
  rw [← hT]
  refine isMaximalTotallyReal_range_of_bijective_coprod ?_
  rw [hcoprod]
  exact (ContinuousLinearEquiv.bijective _).comp (hA.comp hφ)

omit [FiniteDimensional ℂ F] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- **Maximal total reality is an open condition along a frame.** If `L` has a `C^n` local frame
on an open set `U` and its fibre at `x₀ ∈ U` is maximal totally real, then so are its fibres at
all points near `x₀`. -/
theorem eventually_isMaximalTotallyReal [ContMDiffVectorBundle n F V IB] (hU : IsOpen U)
    (hX : IsSubbundleFrameOn F L X U) (hXs : ∀ i, CMDiff[U] n (T% (X i))) {x₀ : B}
    (hx₀ : x₀ ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x₀) Complex.I).restrictScalars ℝ) (L x₀)) :
    ∀ᶠ y in 𝓝 x₀,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) := by
  let := Fintype.ofFinite ι
  set e := trivializationAt F V x₀
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x₀
  let A : B → (ι → ℂ) →L[ℂ] F := IsSubbundleFrameOn.trivOperator ℂ F X x₀
  have hA : ContinuousAt A x₀ := (IsSubbundleFrameOn.contMDiffAt_trivOperator
      (fun i ↦ (hXs i).contMDiffAt (hU.mem_nhds hx₀)) he₀).continuousAt
  have hinv : (A x₀).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (A x₀ : (ι → ℂ) →ₗ[ℂ] F)
      (bijective_trivOperator hX hx₀ he₀ hL)).toContinuousLinearEquiv, rfl⟩
  filter_upwards [hA.eventually_mem
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds (x := A x₀) hinv),
    hU.mem_nhds hx₀, e.open_baseSet.mem_nhds he₀] with y ⟨f, hf⟩ hyU hye
  exact isMaximalTotallyReal_of_bijective_trivOperator hX hyU hye
    (show Function.Bijective (A y) from hf ▸ f.bijective)

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- **The projection onto a totally real subbundle is smooth, locally.** Let `L` have a `C^n`
frame on an open set `U` whose points all have maximal totally real fibres. A field of
endomorphisms equal on `U` to the projection onto `L` along `i L` is `C^n` at each point of `U`. -/
theorem contMDiffAt_totallyRealProjection [ContMDiffVectorBundle n F V IB] (hU : IsOpen U)
    (hX : IsSubbundleFrameOn F L X U) (hXs : ∀ i, CMDiff[U] n (T% (X i)))
    (hL : ∀ y ∈ U,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y))
    {P : ∀ y, V y →L[ℝ] V y} (hP : ∀ y (hy : y ∈ U), P y = totallyRealProjection F (hL y hy))
    {x₀ : B} (hx₀ : x₀ ∈ U) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun y ↦ V y →L[ℝ] V y) x (P x)) x₀ := by
  let := Fintype.ofFinite ι
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set e := trivializationAt F V x₀
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x₀
  let A : B → (ι → ℂ) →L[ℂ] F := IsSubbundleFrameOn.trivOperator ℂ F X x₀
  have hA : ContMDiffAt IB 𝓘(ℝ, (ι → ℂ) →L[ℂ] F) n A x₀ :=
    IsSubbundleFrameOn.contMDiffAt_trivOperator
      (fun i ↦ (hXs i).contMDiffAt (hU.mem_nhds hx₀)) he₀
  have hAapply {y : B} (hy : y ∈ e.baseSet) (c : ι → ℂ) :
      A y c = (e ⟨y, ∑ i, c i • X i y⟩).2 :=
    IsSubbundleFrameOn.trivOperator_apply hy c
  have hA₀ := bijective_trivOperator hX hx₀ he₀ (hL x₀ hx₀)
  have hleft : (A x₀).HasLeftInverse := by
    let a := LinearEquiv.ofBijective (A x₀ : (ι → ℂ) →ₗ[ℂ] F) hA₀
    refine ⟨(a.toContinuousLinearEquiv.symm : F →L[ℂ] (ι → ℂ)), fun c ↦ ?_⟩
    have : a.toContinuousLinearEquiv c = A x₀ c := rfl
    rw [ContinuousLinearEquiv.coe_coe, ← this, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨Linv, hLinv, hLA⟩ := hA.exists_contMDiffAt_leftInverse hleft
  let R : (ι → ℂ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.pi fun i ↦
    Complex.ofRealCLM ∘L Complex.reCLM ∘L ContinuousLinearMap.proj i
  have hAr : ContMDiffAt IB 𝓘(ℝ, (ι → ℂ) →L[ℝ] F) n (fun y ↦ (A y).restrictScalars ℝ) x₀ :=
    (ContinuousLinearMap.restrictScalarsL ℂ (ι → ℂ) F ℝ ℝ).contDiff.comp_contMDiffAt hA
  have hLr : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] (ι → ℂ)) n (fun y ↦ (Linv y).restrictScalars ℝ) x₀ :=
    (ContinuousLinearMap.restrictScalarsL ℂ F (ι → ℂ) ℝ ℝ).contDiff.comp_contMDiffAt hLinv
  refine (hAr.clm_comp ((contMDiffAt_const (c := R)).clm_comp hLr)).congr_of_eventuallyEq ?_
  filter_upwards [hLA, hU.mem_nhds hx₀, e.open_baseSet.mem_nhds he₀] with y hyL hyU hye
  ext w
  obtain ⟨c, rfl⟩ : ∃ c, A y c = w := (bijective_trivOperator hX hyU hye (hL y hyU)).2 w
  have hc : Linv y (A y c) = c := hyL c
  have hsymm : e.symm y (A y c) = ∑ i, c i • X i y := by
    rw [hAapply hye, e.symm_apply_apply_mk hye]
  rw [ContinuousLinearMap.inCoordinates_eq hye hye]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hc,
    ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_symm_apply]
  rw [hsymm, Trivialization.continuousLinearEquivAt_apply, hP y hyU, totallyRealProjection_apply,
    (hL y hyU).projection_sum_smul (fun i ↦ hX.apply_mem i hyU), hAapply hye]
  have hR : ∑ i, R c i • X i y = ∑ i, (c i).re • X i y :=
    Finset.sum_congr rfl fun i _ ↦ by
      simp only [R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply]
      rw [← smul_one_smul ℂ (c i).re (X i y), Complex.real_smul, mul_one]
  rw [hR]

end Frame

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- **The projection onto a smooth totally real subbundle is smooth.** If the fibres of a
real subbundle `L` with `C^n` local frames are maximal totally real, the projection onto `L`
along `i L` is a `C^n` section of the endomorphism bundle. -/
theorem contMDiff_totallyRealProjection [ContMDiffVectorBundle n F V IB]
    (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun y ↦ V y →L[ℝ] V y) x (totallyRealProjection F (hL x))) := by
  intro x₀
  let := Fintype.ofFinite ι
  obtain ⟨U, hU, hx₀, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs x₀
  exact contMDiffAt_totallyRealProjection hU hX hXs (fun y _ ↦ hL y) (fun _ _ ↦ rfl) hx₀

end Projection

end TauCeti

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {ι : Type*} [Finite ι] {L : ∀ x, Submodule ℝ (V x)}

local instance instVectorBundleRealTotallyReal : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle n F V IB]

/-- **A metric compatible with a totally real subbundle.** For a `C^n` real subbundle `L` of a
complex bundle whose fibres are maximal totally real, and `P` the projection onto `L` along
`i L`, the metric `g'(v, w) = g(P v, P w) + g(P (i v), P (i w))`. -/
def totallyRealCompatible (g : ContMDiffRiemannianMetric IB n F V)
    (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ContMDiffRiemannianMetric IB n F V :=
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : ∀ x, IsNormableSpace ℝ (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  let P x := totallyRealProjection F (hL x)
  have hP := contMDiff_totallyRealProjection hLs hL
  have hPJ := hP.clm_bundle_comp (contMDiff_smulIEquiv_bundle (IB := IB) (n := n) (G := F) (W := V))
  let b₁ : TauCeti.Manifold.BilinearSection IB F V ℝ n :=
    ⟨fun x ↦ (g.inner x).bilinearComp (P x) (P x), g.contMDiff.bilinearComp_bundle hP⟩
  let b₂ : TauCeti.Manifold.BilinearSection IB F V ℝ n :=
    ⟨fun x ↦ (g.inner x).bilinearComp (P x ∘L (Complex.smulIEquiv (V x) : V x →L[ℝ] V x))
      (P x ∘L (Complex.smulIEquiv (V x) : V x →L[ℝ] V x)),
      g.contMDiff.bilinearComp_bundle hPJ⟩
  have hJ := lsmul_I_comp_lsmul_I
  ofPositiveDefiniteSection (b₁ + b₂) <| by
    refine (TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ ?_, fun x v hv ↦ ?_⟩
    · simp [b₁, b₂, g.symm x (P x v), g.symm x (P x (Complex.I • v))]
    · have h := (hL x).compatibleForm_pos (hJ (V x)) (g := (g.inner x).toLinearMap₁₂)
        (fun a _ ha ↦ g.pos x a ha) hv
      simpa [b₁, b₂, P, Complex.smulIEquiv_apply] using h

variable (g : ContMDiffRiemannianMetric IB n F V)
  (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
  (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))

/-- Evaluation of the compatible metric. -/
@[simp]
theorem totallyRealCompatible_inner (x : B) (v w : V x) :
    (g.totallyRealCompatible hLs hL).inner x v w =
      g.inner x ((L x).projection _ (hL x).isCompl v) ((L x).projection _ (hL x).isCompl w) +
        g.inner x ((L x).projection _ (hL x).isCompl (Complex.I • v))
          ((L x).projection _ (hL x).isCompl (Complex.I • w)) := by
  simp [totallyRealCompatible]

/-- The compatible metric is the pointwise compatible form of `g`. -/
theorem toLinearMap₁₂_totallyRealCompatible_inner (x : B) :
    ((g.totallyRealCompatible hLs hL).inner x).toLinearMap₁₂ =
      (hL x).compatibleForm (g.inner x).toLinearMap₁₂ := by
  ext v w
  simp

/-- The compatible metric is invariant under multiplication by `i`, so it is the real part of a
Hermitian metric (`Bundle.ContMDiffRiemannianMetric.complexInnerProductSpace`). -/
theorem totallyRealCompatible_inner_smul_I (x : B) (v w : V x) :
    (g.totallyRealCompatible hLs hL).inner x (Complex.I • v) (Complex.I • w) =
      (g.totallyRealCompatible hLs hL).inner x v w := by
  have h := (hL x).compatibleForm_map_map (lsmul_I_comp_lsmul_I (V x))
    (g.inner x).toLinearMap₁₂ v w
  simpa using h

/-- The compatible metric agrees with `g` on `L`. -/
theorem totallyRealCompatible_inner_of_mem {x : B} {a b : V x} (ha : a ∈ L x) (hb : b ∈ L x) :
    (g.totallyRealCompatible hLs hL).inner x a b = g.inner x a b := by
  have h := (hL x).compatibleForm_apply_of_mem_of_mem (g.inner x).toLinearMap₁₂ ha hb
  simpa using h

/-- **`i L = L^⊥`.** For the compatible metric, the `i`-image of each fibre of `L` is the
orthogonal complement of that fibre. -/
theorem orthogonal_totallyRealCompatible (x : B) :
    LinearMap.BilinForm.orthogonal ((g.totallyRealCompatible hLs hL).inner x).toLinearMap₁₂ (L x) =
      (L x).map ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) := by
  rw [toLinearMap₁₂_totallyRealCompatible_inner]
  exact (hL x).orthogonal_compatibleForm fun a _ ha ↦ g.pos x a ha

/-- **Uniqueness of the compatible metric.** A metric invariant under multiplication by `i`,
agreeing with `g` on `L`, and making `L` orthogonal to `i L` is the compatible metric of `g`. -/
theorem eq_totallyRealCompatible {g' : ContMDiffRiemannianMetric IB n F V}
    (hI : ∀ x (v w : V x), g'.inner x (Complex.I • v) (Complex.I • w) = g'.inner x v w)
    (hLg : ∀ x, ∀ a ∈ L x, ∀ b ∈ L x, g'.inner x a b = g.inner x a b)
    (hLI : ∀ x, ∀ a ∈ L x, ∀ b ∈ L x, g'.inner x a (Complex.I • b) = 0) :
    g' = g.totallyRealCompatible hLs hL := by
  ext x v w
  have h := (hL x).eq_compatibleForm (lsmul_I_comp_lsmul_I (V x))
    (g := (g.inner x).toLinearMap₁₂) (h := (g'.inner x).toLinearMap₁₂)
    (fun v w ↦ by simpa using hI x v w) (fun a ha b hb ↦ by simpa using hLg x a ha b hb)
    (fun a ha b hb ↦ by simpa using hLI x a ha b hb)
  rw [← toLinearMap₁₂_totallyRealCompatible_inner g hLs hL] at h
  exact LinearMap.congr_fun₂ h v w

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B] [T2Space B] [SigmaCompactSpace B]
  [IsManifold IB ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {ι : Type*} [Finite ι] {L : ∀ x, Submodule ℝ (V x)}

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

/-- **Existence of metrics compatible with a totally real subbundle.** Let `L` be a `C^n` real
subbundle of a finite-rank `C^n` complex bundle over a σ-compact Hausdorff manifold, whose fibres
are maximal totally real. There is a `C^n` metric invariant under multiplication by `i`, hence
the real part of a Hermitian metric, for which `i (L x)` is the orthogonal complement of `L x`
at every point. -/
theorem exists_contMDiffRiemannianMetric_compatible_totallyReal {n : ℕ∞}
    [ContMDiffVectorBundle n F V IB] (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ∃ g : ContMDiffRiemannianMetric IB n F V,
      (∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) ∧
      ∀ x, LinearMap.BilinForm.orthogonal (g.inner x).toLinearMap₁₂ (L x) =
        (L x).map ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) := by
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : ∀ x, ContinuousConstSMul ℝ (V x) := fun x ↦ inferInstance
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := V)
  exact ⟨g.totallyRealCompatible hLs hL, g.totallyRealCompatible_inner_smul_I hLs hL,
    g.orthogonal_totallyRealCompatible hLs hL⟩

/-- **Metrics compatible with a totally real subbundle along a closed set.** Let `S` be a closed
subset of a σ-compact Hausdorff manifold, possibly with boundary or corners, for instance its
boundary, and let `L` be a family of real subspaces of the fibres of a finite-rank `C^n` complex
bundle which near every point of `S` has a `C^n` local frame and whose fibres over `S` are maximal
totally real. There is a `C^n` metric invariant under multiplication by `i`, hence the real part
of a Hermitian metric, for which `i (L x)` is the orthogonal complement of `L x` at every point of
`S`.

Near a point of `S` the fibres of `L` stay maximal totally real
(`TauCeti.eventually_isMaximalTotallyReal`) and the compatible form of a fixed metric is a local
solution; away from `S` the Hermitian average of that metric is one. The conditions on the metric
at a point are convex, so the local solutions glue along a smooth partition of unity. -/
theorem exists_contMDiffRiemannianMetric_compatible_totallyReal_on {n : ℕ∞}
    [ContMDiffVectorBundle n F V IB] {S : Set B} (hS : IsClosed S)
    (hLs : ∀ x ∈ S, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
      ∃ X : ι → Π x, V x, IsSubbundleFrameOn F L X U ∧ ∀ i, CMDiff[U] n (T% (X i)))
    (hL : ∀ x ∈ S,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ∃ g : ContMDiffRiemannianMetric IB n F V,
      (∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) ∧
      ∀ x ∈ S, LinearMap.BilinForm.orthogonal (g.inner x).toLinearMap₁₂ (L x) =
        (L x).map ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) := by
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : ∀ x, ContinuousConstSMul ℝ (V x) := fun x ↦ inferInstance
  let : ∀ x, IsNormableSpace ℝ (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  have : ∀ b, ContinuousAdd (V b →L[ℝ] ℝ) := fun b ↦ inferInstance
  let : ∀ b, AddCommGroup (V b →L[ℝ] V b →L[ℝ] ℝ) := fun b ↦ inferInstance
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := V)
  -- The fibrewise conditions: a positive definite symmetric form, invariant under `i`, and over
  -- `S` making `L` orthogonal to `i L`. Each is convex.
  let t (b : B) : Set (V b →L[ℝ] V b →L[ℝ] ℝ) := {s | (∀ v w, s v w = s w v) ∧
    (∀ v, v ≠ 0 → 0 < s v v) ∧ (∀ v w, s (Complex.I • v) (Complex.I • w) = s v w) ∧
    (b ∈ S → ∀ a ∈ L b, ∀ c ∈ L b, s a (Complex.I • c) = 0)}
  have ht (b : B) : Convex ℝ (t b) := by
    rintro s ⟨hs₁, hs₂, hs₃, hs₄⟩ s' ⟨hs₁', hs₂', hs₃', hs₄'⟩ a d ha hd had
    refine ⟨fun v w ↦ by simp [hs₁ v w, hs₁' v w], fun v hv ↦ ?_,
      fun v w ↦ by simp [hs₃ v w, hs₃' v w],
      fun hb x hx y hy ↦ by simp [hs₄ hb x hx y hy, hs₄' hb x hx y hy]⟩
    have heval : (a • s + d • s') v v = a * s v v + d * s' v v := by simp
    rw [heval]
    rcases ha.eq_or_lt with rfl | ha
    · have hd1 : d = 1 := by simpa using had
      simpa [hd1] using hs₂' v hv
    · exact add_pos_of_pos_of_nonneg (mul_pos ha (hs₂ v hv)) (mul_nonneg hd (hs₂' v hv).le)
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local (n := n) IB
    (fun b ↦ V b →L[ℝ] V b →L[ℝ] ℝ) t ht fun x₀ ↦ by
      by_cases hx₀ : x₀ ∈ S
      · -- Near a point of `S`: the compatible form of `g`.
        obtain ⟨U, hU, hx₀U, X, hX, hXs⟩ := hLs x₀ hx₀
        let W := U ∩ interior {y | IsMaximalTotallyReal
          ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y)}
        have hW : IsOpen W := hU.inter isOpen_interior
        have hx₀W : x₀ ∈ W := ⟨hx₀U, mem_interior_iff_mem_nhds.2
          (eventually_isMaximalTotallyReal hU hX hXs hx₀U (hL x₀ hx₀))⟩
        have hLW (y : B) (hy : y ∈ W) :
            IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) :=
          interior_subset hy.2
        classical
        let P (y : B) : V y →L[ℝ] V y := if h : IsMaximalTotallyReal
          ((LinearMap.lsmul ℂ (V y) Complex.I).restrictScalars ℝ) (L y) then
            totallyRealProjection F h else 0
        have hP (y : B) (hy : y ∈ W) : P y = totallyRealProjection F (hLW y hy) := by
          dsimp only [P]
          split_ifs with h
          · rfl
          · exact absurd (hLW y hy) h
        let J (y : B) : V y →L[ℝ] V y := (Complex.smulIEquiv (V y) : V y →L[ℝ] V y)
        let s (y : B) : V y →L[ℝ] V y →L[ℝ] ℝ :=
          (g.inner y).bilinearComp (P y) (P y) +
            (g.inner y).bilinearComp (P y ∘L J y) (P y ∘L J y)
        have hs (y : B) (hy : y ∈ W) (v w : V y) :
            s y v w = (hLW y hy).compatibleForm (g.inner y).toLinearMap₁₂ v w := by
          simp [s, hP y hy, J, Complex.smulIEquiv_apply]
        refine ⟨W, hW.mem_nhds hx₀W, s, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
        · have hPy := contMDiffAt_totallyRealProjection hW (hX.mono inter_subset_left)
            (fun i ↦ (hXs i).mono inter_subset_left) hLW hP hy
          have hPJy := hPy.clm_bundle_comp
            (contMDiff_smulIEquiv_bundle (IB := IB) (n := n) (G := F) (W := V) y)
          exact (((g.contMDiff y).bilinearComp_bundle hPy).add_section
            ((g.contMDiff y).bilinearComp_bundle hPJy)).contMDiffWithinAt
        · have hJ := lsmul_I_comp_lsmul_I (E := V y)
          refine ⟨fun v w ↦ ?_, fun v hv ↦ ?_, fun v w ↦ ?_, fun _ a ha c hc ↦ ?_⟩
          · rw [hs y hy, hs y hy]
            exact ((hLW y hy).isSymm_compatibleForm
              (LinearMap.BilinForm.isSymm_def.2 fun v w ↦ by simpa using g.symm y v w)).eq v w
          · rw [hs y hy]
            exact (hLW y hy).compatibleForm_pos hJ (fun a _ ha ↦ by simpa using g.pos y a ha) hv
          · rw [hs y hy, hs y hy]
            simpa using (hLW y hy).compatibleForm_map_map hJ (g.inner y).toLinearMap₁₂ v w
          · rw [hs y hy]
            simpa using (hLW y hy).compatibleForm_apply_map (g.inner y).toLinearMap₁₂ ha hc
      · -- Away from `S`: the Hermitian average of `g`.
        refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx₀, g.hermitianAverage.inner,
          g.hermitianAverage.contMDiff.contMDiffOn, fun y hy ↦ ⟨g.hermitianAverage.symm y,
            g.hermitianAverage.pos y, g.hermitianAverage_inner_smul_I y,
            fun hyS ↦ absurd hyS hy⟩⟩
  let G : ContMDiffRiemannianMetric IB n F V :=
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection ⟨σ, σ.contMDiff⟩
      ((TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
        ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ (hσ x).1 v w,
          fun x v hv ↦ (hσ x).2.1 v hv⟩)
  have hGσ (x : B) (v w : V x) : G.inner x v w = σ x v w :=
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ x v w
  refine ⟨G, fun x v w ↦ by rw [hGσ, hGσ]; exact (hσ x).2.2.1 v w, fun x hx ↦ ?_⟩
  -- At a point of `S` the metric is its own compatible form, so `i L` is `L^⊥`.
  have hJ := lsmul_I_comp_lsmul_I (E := V x)
  have hG : (G.inner x).toLinearMap₁₂ = (hL x hx).compatibleForm (G.inner x).toLinearMap₁₂ :=
    (hL x hx).eq_compatibleForm hJ (fun v w ↦ by simpa [hGσ] using (hσ x).2.2.1 v w)
      (fun _ _ _ _ ↦ rfl) fun a ha c hc ↦ by simpa [hGσ] using (hσ x).2.2.2 hx a ha c hc
  rw [hG]
  exact (hL x hx).orthogonal_compatibleForm fun a _ ha ↦ by simpa using G.pos x a ha

end TauCeti
