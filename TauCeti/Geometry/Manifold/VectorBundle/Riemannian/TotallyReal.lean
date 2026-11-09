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
conjugate by this family of the coordinatewise real part.

## Main declarations

* `TauCeti.totallyRealProjection`: the fibrewise projection `P x`.
* `TauCeti.contMDiff_totallyRealProjection`: `P` is a smooth bundle endomorphism.
* `Bundle.ContMDiffRiemannianMetric.totallyRealCompatible`: the metric `g'`.
* `TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal`: a smooth Hermitian metric
  with `i L x = (L x)^⊥` at every point exists over a σ-compact Hausdorff base.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS (2012), Section C.1.
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

section BilinearComp

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω}

/-- Precomposing both arguments of a `C^n` field of bilinear forms with a `C^n` field of
endomorphisms gives a `C^n` field of bilinear forms. -/
theorem contMDiff_bilinearComp_bundle [∀ x, IsNormableSpace ℝ (V x)]
    {β : ∀ x, V x →L[ℝ] V x →L[ℝ] ℝ}
    (hβ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n (fun x ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun y ↦ V y →L[ℝ] V y →L[ℝ] ℝ) x (β x)))
    {A : ∀ x, V x →L[ℝ] V x}
    (hA : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun x ↦
      TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (A x))) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n (fun x ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun y ↦ V y →L[ℝ] V y →L[ℝ] ℝ) x
        ((β x).bilinearComp (A x) (A x))) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let a (y : B) := ContinuousLinearMap.inCoordinates F V F V x y x y (A y)
  let q (y : B) := ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ)
    (fun z ↦ V z →L[ℝ] ℝ) x y x y (β y)
  have ha : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] F) n a x :=
    ((contMDiffAt_hom_bundle _).mp (hA x)).2
  have hq : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n q x :=
    ((contMDiffAt_hom_bundle _).mp (hβ x)).2
  have hc := (ha.clm_precomp (F₃ := ℝ)).clm_comp (hq.clm_comp ha)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F V x)] with y hy
  dsimp only [a, q]
  ext v w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  rw [inCoordinates_apply_eq₂ hy hy (by simp), inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [ContinuousLinearMap.inCoordinates, hy]

end BilinearComp

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
def totallyRealProjection
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    (x : B) : V x →L[ℝ] V x where
  toLinearMap := (hL x).projection
  cont := by
    let e := VectorBundle.continuousLinearEquivAt ℝ F V x
    let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
    let f : F →ₗ[ℝ] F := e.toLinearEquiv.toLinearMap ∘ₗ (hL x).projection ∘ₗ
      e.symm.toLinearEquiv.toLinearMap
    have hf : ⇑(hL x).projection = e.symm ∘ f ∘ e := by
      funext v
      simp [f]
    change Continuous ⇑(hL x).projection
    rw [hf]
    exact e.symm.continuous.comp (f.continuous_of_finiteDimensional.comp e.continuous)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- Evaluation of the fibrewise projection. -/
@[simp]
theorem totallyRealProjection_apply
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    (x : B) (v : V x) : totallyRealProjection F hL x v = (hL x).projection v :=
  (rfl)

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- **The projection onto a smooth totally real subbundle is smooth.** If the fibres of a
real subbundle `L` with `C^n` local frames are maximal totally real, the projection onto `L`
along `i L` is a `C^n` section of the endomorphism bundle. -/
theorem contMDiff_totallyRealProjection [ContMDiffVectorBundle n F V IB]
    (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    (hL : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun y ↦ V y →L[ℝ] V y) x (totallyRealProjection F hL x)) := by
  intro x₀
  let := Fintype.ofFinite ι
  obtain ⟨U, hU, hx₀, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs x₀
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
  -- The real frame of `L y` is a complex basis of `V y`.
  have hAsurj {y : B} (hyU : y ∈ U) (hy : y ∈ e.baseSet) : Function.Surjective (A y) := by
    intro w
    have hspan := (hL y).span_complex_eq_top (hX.span_eq hyU)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (hspan ▸ Submodule.mem_top : e.symm y w ∈ Submodule.span ℂ (range (X · y)))
    exact ⟨c, by rw [hAapply hy, hc, e.apply_mk_symm hy]⟩
  have hAinj {y : B} (hyU : y ∈ U) (hy : y ∈ e.baseSet) : Function.Injective (A y) := by
    refine (injective_iff_map_eq_zero (A y)).2 fun c hc ↦ ?_
    have h := hAapply hy c
    rw [hc] at h
    have hc' : ∑ i, c i • X i y = 0 := (e.continuousLinearEquivAt ℂ y hy).injective (by
      rw [map_zero, Trivialization.continuousLinearEquivAt_apply]
      exact h.symm)
    have hli := (hL y).isTotallyReal.linearIndependent_complex (hX.linearIndependent hyU)
      (fun i ↦ hX.apply_mem i hyU)
    funext i
    exact Fintype.linearIndependent_iff.1 hli c hc' i
  have hleft : (A x₀).HasLeftInverse := by
    let a := LinearEquiv.ofBijective (A x₀ : (ι → ℂ) →ₗ[ℂ] F)
      ⟨hAinj hx₀ he₀, hAsurj hx₀ he₀⟩
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
  obtain ⟨c, rfl⟩ := hAsurj hyU hye w
  have hc : Linv y (A y c) = c := hyL c
  have hsymm : e.symm y (A y c) = ∑ i, c i • X i y := by
    rw [hAapply hye, e.symm_apply_apply_mk hye]
  rw [ContinuousLinearMap.inCoordinates_eq hye hye]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hc,
    ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_symm_apply]
  rw [hsymm, Trivialization.continuousLinearEquivAt_apply, totallyRealProjection_apply,
    (hL y).projection_sum_smul (fun i ↦ hX.apply_mem i hyU), hAapply hye]
  have hR : ∑ i, R c i • X i y = ∑ i, (c i).re • X i y :=
    Finset.sum_congr rfl fun i _ ↦ by
      simp only [R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply]
      rw [← smul_one_smul ℂ (c i).re (X i y), Complex.real_smul, mul_one]
  rw [hR]

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

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

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
  let P := totallyRealProjection F hL
  have hP := contMDiff_totallyRealProjection hLs hL
  have hPJ := hP.clm_bundle_comp (contMDiff_smulIEquiv_bundle (IB := IB) (n := n) (G := F) (W := V))
  let b₁ : TauCeti.Manifold.BilinearSection IB F V ℝ n :=
    ⟨fun x ↦ (g.inner x).bilinearComp (P x) (P x), contMDiff_bilinearComp_bundle g.contMDiff hP⟩
  let b₂ : TauCeti.Manifold.BilinearSection IB F V ℝ n :=
    ⟨fun x ↦ (g.inner x).bilinearComp (P x ∘L (Complex.smulIEquiv (V x) : V x →L[ℝ] V x))
      (P x ∘L (Complex.smulIEquiv (V x) : V x →L[ℝ] V x)),
      contMDiff_bilinearComp_bundle g.contMDiff hPJ⟩
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
      g.inner x ((hL x).projection v) ((hL x).projection w) +
        g.inner x ((hL x).projection (Complex.I • v)) ((hL x).projection (Complex.I • w)) := by
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
  exact (hL x).orthogonal_compatibleForm (lsmul_I_comp_lsmul_I (V x))
    fun a _ ha ↦ g.pos x a ha

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

end TauCeti
