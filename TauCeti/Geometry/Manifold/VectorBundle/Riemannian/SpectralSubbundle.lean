/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Spectral.Inertia
import TauCeti.Analysis.InnerProductSpace.Spectral.Projection
import TauCeti.Analysis.Normed.Operator.IdempotentRange
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Spectral subbundles of a field of nondegenerate symmetric forms

Let `V` be a finite-rank `C^n` vector bundle with a `C^n` Riemannian metric, and let `Q` be a
`C^n` field of symmetric bilinear forms on `V` which is nondegenerate at every point. At each
point `x` the metric turns `Q x` into a self-adjoint invertible operator, its Riesz operator
`continuousLinearMapOfBilin (Q x)`, and the fibre `V x` splits orthogonally into the sum of the
eigenspaces with negative eigenvalues and the sum of those with positive eigenvalues. This file
shows that these two families of subspaces are `C^n` subbundles of `V`: near every point they are
spanned by `C^n` local frames (`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Iio` and
`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi`). Where their ranks are constant
this is the local frame criterion `TauCeti.HasLocalContMDiffSubbundleFrames` for a `C^n`
subbundle (`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Iio` and
`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Ioi`).

The rank of the negative part at `x` is the negative index of inertia of `Q x`
(`InnerProductSpace.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`), so it does not
depend on the metric, and it is locally constant
(`TauCeti.eventually_finrank_pointSpectralSubspace_Iio_eq`). The subspaces themselves do depend on
the metric.

No smooth choice of eigenvectors is made. Over the base set of a trivialization, normalized
Gram–Schmidt gives a smooth orthonormal frame
(`Bundle.Trivialization.exists_contMDiffOn_orthonormal`). Read in this frame, `Q` becomes a
smooth family of self-adjoint invertible operators on a fixed Euclidean space, whose negative
spectral projections are smooth
(`ContinuousLinearMap.starProjection_pointSpectralSubspace_Iio_zero_eq`, which writes them as
`(1 - A (A²)^(-1/2)) / 2`). Projecting a basis of the negative space at the base point and reading
the result back through the frame gives the local frame of the negative subbundle.

The motivating example is the normal Hessian of a Morse–Bott critical submanifold, whose negative
and positive parts are the negative and positive normal bundles.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. Hurtubise, *Lectures on Morse Homology*, Kluwer Texts in the Mathematical
  Sciences 29, Springer, 2004, Section 3.5.
-/

public section

open Bundle InnerProductSpace Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section Fibre

variable {M : Type*} {V : M → Type*} [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] {d : ℕ}

/-- The linear map sending coordinates `u` to the combination `∑ i, u i • ε i y` of the values of
a family of sections at `y`. -/
private def frameMap (ε : Fin d → Π x, V x) (y : M) : EuclideanSpace ℝ (Fin d) →L[ℝ] V y :=
  ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).smulRight (ε i y)

private theorem frameMap_apply (ε : Fin d → Π x, V x) (y : M) (u : EuclideanSpace ℝ (Fin d)) :
    frameMap ε y u = ∑ i, u i • ε i y := by
  simp [frameMap]

/-- For an orthonormal basis, `frameMap` is the inverse of the coordinate isometry. -/
private theorem frameMap_eq_repr_symm (ε : Fin d → Π x, V x) {y : M}
    (hon : Orthonormal ℝ (ε · y)) (hsp : ⊤ ≤ Submodule.span ℝ (range (ε · y))) :
    frameMap ε y =
      ((OrthonormalBasis.mk hon hsp).repr.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] V y) := by
  ext u
  simp [frameMap_apply, ← OrthonormalBasis.sum_repr_symm]

/-- A bilinear form read in coordinates is the sum of its values on pairs of frame vectors times
the elementary bilinear forms. -/
private theorem bilinearComp_frameMap_eq_sum (Q : Π x, V x →L[ℝ] V x →L[ℝ] ℝ)
    (ε : Fin d → Π x, V x) (y : M) :
    (Q y).bilinearComp (frameMap ε y) (frameMap ε y) =
      ∑ i, ∑ j, Q y (ε i y) (ε j y) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).smulRight
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := by
  ext u w
  simp only [frameMap_apply, ContinuousLinearMap.bilinearComp_apply, map_sum, map_smul,
    sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

variable [∀ x, CompleteSpace (V x)]

/-- Read in an orthonormal basis, the Riesz operator of a form is the Riesz operator of the form in
coordinates, so the point-spectral subspaces correspond. -/
private theorem pointSpectralSubspace_eq_map_frameMap (Q : Π x, V x →L[ℝ] V x →L[ℝ] ℝ)
    (ε : Fin d → Π x, V x) {y : M} (hon : Orthonormal ℝ (ε · y))
    (hsp : ⊤ ≤ Submodule.span ℝ (range (ε · y))) (Ω : Set ℝ) :
    Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (Q y)).toLinearMap Ω =
      (Module.End.pointSpectralSubspace (continuousLinearMapOfBilin
        ((Q y).bilinearComp (frameMap ε y) (frameMap ε y))).toLinearMap Ω).map
        (frameMap ε y).toLinearMap := by
  set b := OrthonormalBasis.mk hon hsp
  have hK : (continuousLinearMapOfBilin ((Q y).bilinearComp (frameMap ε y) (frameMap ε y))
      ).toLinearMap = b.repr.toLinearEquiv.conj (continuousLinearMapOfBilin (Q y)).toLinearMap := by
    rw [frameMap_eq_repr_symm ε hon hsp,
      ContinuousLinearMap.continuousLinearMapOfBilin_bilinearComp]
    ext u
    simp [b, LinearEquiv.conj_apply]
  rw [hK, Module.End.pointSpectralSubspace_conj, ← Submodule.map_comp]
  convert (Submodule.map_id _).symm
  ext v
  simp [frameMap_eq_repr_symm ε hon hsp, b]

end Fibre

section Bundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [∀ x, CompleteSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB] [IsContMDiffRiemannianBundle IB n F V]
  {Q : Π x, V x →L[ℝ] V x →L[ℝ] ℝ}

omit [FiniteDimensional ℝ F] [∀ x, CompleteSpace (V x)] [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- Read in a `C^n` family of frames, a `C^n` field of bilinear forms has a `C^n` Riesz operator in
coordinates. -/
private theorem contMDiffOn_continuousLinearMapOfBilin_frameMap {d : ℕ}
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    {ε : Fin d → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ continuousLinearMapOfBilin ((Q y).bilinearComp (frameMap ε y) (frameMap ε y)))
      U := by
  have hc (i j : Fin d) : ContMDiffOn IB 𝓘(ℝ) n (fun y ↦ Q y (ε i y) (ε j y)) U := fun y hy ↦ by
    have h := ContMDiffWithinAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial B ℝ)
      (b := id) (hQ y).contMDiffWithinAt (hε i y hy) (hε j y hy)
    exact (contMDiffWithinAt_totalSpace.mp h).2
  have hsum : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      n (fun y ↦ (Q y).bilinearComp (frameMap ε y) (frameMap ε y)) U := by
    simp_rw [bilinearComp_frameMap_eq_sum]
    exact contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
      (hc i j).smul contMDiffOn_const
  exact contDiff_continuousLinearMapOfBilin.contMDiff.comp_contMDiffOn hsum

omit [FiniteDimensional ℝ F] [∀ x, CompleteSpace (V x)] [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- Combining a `C^n` family of coordinates with a `C^n` family of frames gives a `C^n` section. -/
private theorem contMDiffOn_frameMap_apply {d : ℕ} {ε : Fin d → Π x, V x} {U : Set B}
    (hU : IsOpen U) (hε : ∀ i, CMDiff[U] n (T% (ε i))) {c : B → EuclideanSpace ℝ (Fin d)}
    (hc : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) n c U) :
    CMDiff[U] n (T% (fun y ↦ frameMap ε y (c y))) := by
  intro y hy
  have hy' := hU.mem_nhds hy
  have hci (i : Fin d) : ContMDiffAt IB 𝓘(ℝ) n (fun y ↦ EuclideanSpace.proj i (c y)) y :=
    ((EuclideanSpace.proj i).contMDiff.comp_contMDiffOn hc).contMDiffAt hy'
  have hsec := ContMDiffAt.sum_section (s := Finset.univ) fun i _ ↦
    (hci i).smul_section ((hε i).contMDiffAt hy')
  refine (hsec.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)).contMDiffWithinAt
  simp [frameMap]

omit [FiniteDimensional ℝ F] [∀ x, CompleteSpace (V x)] [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- Let `W y` be subspaces of a Euclidean space whose orthogonal projections are `C^n` on an open
set `U₀`, and read them in a `C^n` family of injective frames. Projecting a basis of `W x₀` onto
the nearby `W y` and reading the result in the frames gives a `C^n` local frame of the images of
the `W y`, on a neighbourhood of `x₀` in `U₀` where the dimension of `W y` stays `r`. -/
private theorem exists_isSubbundleFrameOn_map_frameMap {d r : ℕ} {ε : Fin d → Π x, V x}
    {U₀ : Set B} (hU₀ : IsOpen U₀) (hε : ∀ i, CMDiff[U₀] n (T% (ε i)))
    (hker : ∀ y ∈ U₀, LinearMap.ker (frameMap ε y).toLinearMap = ⊥)
    {W : B → Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (hP : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ (W y).starProjection) U₀) {x₀ : B} (hx₀ : x₀ ∈ U₀)
    (hr : Module.finrank ℝ (W x₀) = r) :
    ∃ U ⊆ U₀, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin r → Π x, V x,
      IsSubbundleFrameOn F (fun y ↦ (W y).map (frameMap ε y).toLinearMap) X U ∧
      ∀ i, CMDiff[U] n (T% (X i)) := by
  let β := Module.finBasisOfFinrankEq ℝ (W x₀) hr
  set Y : B → Fin r → EuclideanSpace ℝ (Fin d) := fun y k ↦ (W y).starProjection (β k)
  have hYc : ContinuousOn Y U₀ :=
    continuousOn_pi.mpr fun k ↦ hP.continuousOn.clm_apply continuousOn_const
  have hY₀ : LinearIndependent ℝ (Y x₀) := by
    have hY : Y x₀ = fun k ↦ ((β k : W x₀) : EuclideanSpace ℝ (Fin d)) :=
      funext fun k ↦ Submodule.starProjection_eq_self_iff.mpr (β k).2
    rw [hY]
    exact β.linearIndependent.map' (W x₀).subtype (Submodule.ker_subtype _)
  -- The rank of a continuous family of projections is locally constant.
  set S := Subtype.val '' {y : U₀ | Module.finrank ℝ (W y).starProjection.range = r}
  have hS : IsOpen S :=
    hU₀.isOpenMap_subtype_val _ ((isLocallyConstant_finrank_range
      (p := fun y : U₀ ↦ (W y).starProjection) hP.continuousOn.domRestrict
      fun y ↦ (W y).isIdempotentElem_starProjection).isOpen_fiber _)
  have hX (k : Fin r) := contMDiffOn_frameMap_apply hU₀ hε (hP.clm_apply contMDiffOn_const)
    (c := fun y ↦ (W y).starProjection (β k))
  refine ⟨S ∩ (U₀ ∩ Y ⁻¹' {f | LinearIndependent ℝ f}), fun y hy ↦ hy.2.1,
    hS.inter (hYc.isOpen_inter_preimage hU₀
    isOpen_setOfPred_linearIndependent), ⟨⟨⟨x₀, hx₀⟩, ?_, rfl⟩, hx₀, hY₀⟩,
    fun k y ↦ frameMap ε y (Y y k),
    ⟨fun k ↦ (hX k).continuousOn.mono fun y hy ↦ hy.2.1, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩,
    fun k ↦ (hX k).mono fun y hy ↦ hy.2.1⟩
  · rw [Set.mem_ofPred_eq, Submodule.range_starProjection]
    exact hr
  · exact hy.2.2.map' (frameMap ε y).toLinearMap (hker y hy.2.1)
  · obtain ⟨⟨⟨z, hzU⟩, hz, rfl⟩, -, hli⟩ := hy
    -- `r` independent vectors of the `r`-dimensional space `W z` span it.
    have hspan : Submodule.span ℝ (range (Y z)) = W z := by
      refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr
        (range_subset_iff.mpr fun k ↦ (W z).starProjection_apply_mem _)) ?_
      rw [Set.mem_ofPred_eq, Submodule.range_starProjection] at hz
      rw [finrank_span_eq_card hli, Fintype.card_fin, hz]
    rw [← hspan, Submodule.map_span, ← range_comp]
    rfl

omit [FiniteDimensional ℝ F] [∀ x, CompleteSpace (V x)] [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- Read in a `C^n` family of orthonormal bases, the negative spectral projections of a `C^n`
field of nondegenerate symmetric forms are `C^n`. -/
private theorem contMDiffOn_starProjection_frameMap {d : ℕ}
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x))
    {ε : Fin d → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i)))
    (hon : ∀ y ∈ U, Orthonormal ℝ (ε · y))
    (hsp : ∀ y ∈ U, ⊤ ≤ Submodule.span ℝ (range (ε · y))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ (Module.End.pointSpectralSubspace (continuousLinearMapOfBilin
        ((Q y).bilinearComp (frameMap ε y) (frameMap ε y))).toLinearMap (Iio 0)).starProjection)
      U := by
  refine ((contDiffOn_id (s := {A | IsSelfAdjoint A ∧ IsUnit A})
    ).starProjection_pointSpectralSubspace_Iio_zero (fun A hA ↦ hA.1)
    (fun A hA ↦ hA.2)).contMDiffOn.comp
    (contMDiffOn_continuousLinearMapOfBilin_frameMap hQ hε) fun y hy ↦
      ⟨isSelfAdjoint_continuousLinearMapOfBilin fun v w ↦ hsymm y _ _,
        isUnit_continuousLinearMapOfBilin fun u u' huu' ↦ ?_⟩
  -- The frame is the inverse of an orthonormal-basis isometry, hence bijective.
  have hb := frameMap_eq_repr_symm ε (hon y hy) (hsp y hy)
  have hinj : Function.Injective (frameMap ε y) := by
    rw [hb]
    exact (OrthonormalBasis.mk (hon y hy) (hsp y hy)).repr.symm.injective
  have hsurj : Function.Surjective (frameMap ε y) := by
    rw [hb]
    exact (OrthonormalBasis.mk (hon y hy) (hsp y hy)).repr.symm.surjective
  refine hinj (hnd y ?_)
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  exact congrArg (fun φ ↦ φ w) huu'

/-- **The negative spectral subspaces of a smooth field of nondegenerate symmetric forms have smooth
local frames.** Let `Q` be a `C^n` field of symmetric bilinear forms on a finite-rank `C^n`
Riemannian bundle `V`, nondegenerate at every point. If at `x₀` the negative spectral subspace of
the Riesz operator of `Q x₀` has dimension `r`, then on an open neighbourhood of `x₀` the negative
spectral subspaces of the Riesz operators of `Q x` are spanned by `r` sections of class `C^n`
forming a basis at each point. -/
theorem exists_isSubbundleFrameOn_pointSpectralSubspace_Iio
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x)) (x₀ : B) {r : ℕ}
    (hr : Module.finrank ℝ (Module.End.pointSpectralSubspace
      (continuousLinearMapOfBilin (Q x₀)).toLinearMap (Iio 0)) = r) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin r → Π x, V x,
      IsSubbundleFrameOn F (fun x ↦ Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin (Q x)).toLinearMap (Iio 0)) X U ∧
      ∀ i, CMDiff[U] n (T% (X i)) := by
  set e := trivializationAt F V x₀
  obtain ⟨ε, hε, hon⟩ := e.exists_contMDiffOn_orthonormal (I := IB) (n := n)
  -- Over the base set `ε` is an orthonormal basis of the fibre.
  have hsp (y : B) (hy : y ∈ e.baseSet) : ⊤ ≤ Submodule.span ℝ (range (ε · y)) := by
    have := (e.linearEquivAt ℝ y hy).symm.finiteDimensional
    refine ((hon y hy).linearIndependent.span_eq_top_of_card_eq_finrank' ?_).ge
    simpa using (e.linearEquivAt ℝ y hy).finrank_eq.symm
  have hker (y : B) (hy : y ∈ e.baseSet) : LinearMap.ker (frameMap ε y).toLinearMap = ⊥ := by
    rw [frameMap_eq_repr_symm ε (hon y hy) (hsp y hy)]
    exact LinearMap.ker_eq_bot.mpr (OrthonormalBasis.mk (hon y hy) (hsp y hy)).repr.symm.injective
  -- In these frames the negative spectral subspaces are the images of those in coordinates.
  have hspec (y : B) (hy : y ∈ e.baseSet) := pointSpectralSubspace_eq_map_frameMap Q ε (hon y hy)
    (hsp y hy) (Iio 0)
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  obtain ⟨U, hUe, hU, hxU, X, hX, hXn⟩ := exists_isSubbundleFrameOn_map_frameMap (r := r)
    e.open_baseSet hε
    hker (contMDiffOn_starProjection_frameMap hQ hsymm hnd hε hon hsp) hx₀ (by
      rw [← hr, hspec x₀ hx₀]
      exact (Submodule.equivMapOfInjective _ (LinearMap.ker_eq_bot.mp (hker x₀ hx₀)) _).finrank_eq)
  exact ⟨U, hU, hxU, X, ⟨hX.continuousOn, hX.linearIndependent, fun hy ↦
    (hX.span_eq hy).trans (hspec _ (hUe hy)).symm⟩, hXn⟩

/-- Where the negative spectral subspaces of a `C^n` field `Q` of nondegenerate symmetric forms
all have dimension `r`, they satisfy the local frame criterion for a `C^n` subbundle of rank `r`,
the negative spectral subbundle of `Q`. -/
theorem hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Iio
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x)) {r : ℕ}
    (hr : ∀ x, Module.finrank ℝ (Module.End.pointSpectralSubspace
      (continuousLinearMapOfBilin (Q x)).toLinearMap (Iio 0)) = r) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin r) fun x ↦
      Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (Q x)).toLinearMap (Iio 0) :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦
    exists_isSubbundleFrameOn_pointSpectralSubspace_Iio hQ hsymm hnd x₀ (hr x₀)

/-- The dimension of the negative spectral subspace of a `C^n` field of nondegenerate symmetric
forms, which is its negative index of inertia, is locally constant; `n = 0` is allowed. -/
theorem eventually_finrank_pointSpectralSubspace_Iio_eq
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x)) (x₀ : B) :
    ∀ᶠ x in 𝓝 x₀, Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin (Q x)).toLinearMap (Iio 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin (Q x₀)).toLinearMap (Iio 0)) := by
  obtain ⟨U, hU, hx₀, X, hX, -⟩ :=
    exists_isSubbundleFrameOn_pointSpectralSubspace_Iio hQ hsymm hnd x₀ rfl
  filter_upwards [hU.mem_nhds hx₀] with x hx
  rw [← hX.span_eq hx, finrank_span_eq_card (hX.linearIndependent hx), Fintype.card_fin]

omit [TopologicalSpace B] [ChartedSpace HB B] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle n F V IB] [IsContMDiffRiemannianBundle IB n F V] in
/-- Negating a form exchanges the negative and positive spectral subspaces of its Riesz
operator. -/
private theorem pointSpectralSubspace_Iio_neg (x : B) :
    Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (-Q x)).toLinearMap (Iio 0) =
      Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (Q x)).toLinearMap (Ioi 0) := by
  have h : continuousLinearMapOfBilin (-Q x) = -continuousLinearMapOfBilin (Q x) := by
    ext v
    refine ext_inner_right ℝ fun w ↦ ?_
    simp [continuousLinearMapOfBilin_apply, inner_neg_left]
  rw [h, ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Iio,
    neg_zero]

/-- **The positive spectral subspaces of a smooth field of nondegenerate symmetric forms have smooth
local frames.** This is `TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Iio` for `-Q`. -/
theorem exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x)) (x₀ : B) {r : ℕ}
    (hr : Module.finrank ℝ (Module.End.pointSpectralSubspace
      (continuousLinearMapOfBilin (Q x₀)).toLinearMap (Ioi 0)) = r) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin r → Π x, V x,
      IsSubbundleFrameOn F (fun x ↦ Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin (Q x)).toLinearMap (Ioi 0)) X U ∧
      ∀ i, CMDiff[U] n (T% (X i)) := by
  rw [← pointSpectralSubspace_Iio_neg] at hr
  simp_rw [← pointSpectralSubspace_Iio_neg]
  exact exists_isSubbundleFrameOn_pointSpectralSubspace_Iio (Q := fun x ↦ -Q x)
    (fun x ↦ (hQ x).neg_section)
    (fun x v w ↦ by simp [hsymm x v w]) (fun x ↦ neg_injective.comp (hnd x)) x₀ hr

/-- Where the positive spectral subspaces of a `C^n` field `Q` of nondegenerate symmetric forms
all have dimension `r`, they satisfy the local frame criterion for a `C^n` subbundle of rank `r`,
the positive spectral subbundle of `Q`. -/
theorem hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Ioi
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x)) {r : ℕ}
    (hr : ∀ x, Module.finrank ℝ (Module.End.pointSpectralSubspace
      (continuousLinearMapOfBilin (Q x)).toLinearMap (Ioi 0)) = r) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin r) fun x ↦
      Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (Q x)).toLinearMap (Ioi 0) :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦
    exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi hQ hsymm hnd x₀ (hr x₀)

end Bundle

end TauCeti
