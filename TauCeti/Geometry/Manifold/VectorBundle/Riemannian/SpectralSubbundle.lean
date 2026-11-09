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
import TauCeti.Analysis.Normed.Operator.Bilinear
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Spectral subbundles of a field of nondegenerate symmetric forms

Let `V` be a finite-rank `C^n` vector bundle with a `C^n` Riemannian metric, and let `Q` be a
`C^n` field of symmetric bilinear forms on `V` which is nondegenerate at every point. At each
point `x` the metric turns `Q x` into a self-adjoint invertible operator, its Riesz operator
`continuousLinearMapOfBilin (Q x)`, and the fibre `V x` splits orthogonally into the sum of the
eigenspaces with negative eigenvalues and the sum of those with positive eigenvalues. This file
shows that near every point these two families of subspaces are spanned by `C^n` local frames
(`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Iio` and
`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi`). If their ranks are the same at
every point of the base (for instance over a connected base), they therefore satisfy the local
frame criterion `TauCeti.HasLocalContMDiffSubbundleFrames` for a `C^n` subbundle
(`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Iio` and
`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Ioi`).

The ranks of the negative and positive parts at `x` are the negative and positive indices of
inertia of `Q x` (`InnerProductSpace.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`
and `InnerProductSpace.finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`), so they do
not depend on the metric, and they are locally constant
(`TauCeti.eventually_finrank_pointSpectralSubspace_Iio_eq` and
`TauCeti.eventually_finrank_pointSpectralSubspace_Ioi_eq`). The subspaces themselves do depend on
the metric. The positive case is the negative case for `-Q`
(`InnerProductSpace.pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg`).

No smooth choice of eigenvectors is made. Over the base set of a trivialization, the normalized
Gram–Schmidt orthonormal basis `Bundle.Trivialization.orthonormalBasis` is a smooth orthonormal
frame (`Bundle.Trivialization.contMDiffOn_orthonormalBasis`). Read in this frame, `Q` becomes a
smooth family of self-adjoint invertible operators on a fixed Euclidean space, whose spectral
subspaces are those of `Q` in coordinates
(`InnerProductSpace.pointSpectralSubspace_continuousLinearMapOfBilin_eq_map_synthesisMap`) and whose
negative spectral projections are smooth
(`ContinuousLinearMap.starProjection_pointSpectralSubspace_Iio_zero_eq`, which writes them as
`(1 - A (A²)^(-1/2)) / 2`). Projecting a basis of the negative space at the base point and
synthesizing the result against the frame gives the local frame of the negative subspaces
(`TauCeti.exists_isSubbundleFrameOn_map_synthesisMap`).

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
/-- Read through the synthesis maps of a `C^n` family of sections, a `C^n` field of bilinear forms
has a `C^n` Riesz operator in coordinates. -/
private theorem contMDiffOn_continuousLinearMapOfBilin_synthesisMap {d : ℕ}
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    {ε : Fin d → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ continuousLinearMapOfBilin ((Q y).bilinearComp
        (synthesisMap ℝ (ε · y)).toContinuousLinearMap
        (synthesisMap ℝ (ε · y)).toContinuousLinearMap)) U := by
  have hc (i j : Fin d) : ContMDiffOn IB 𝓘(ℝ) n (fun y ↦ Q y (ε i y) (ε j y)) U := fun y hy ↦ by
    have h := ContMDiffWithinAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial B ℝ)
      (b := id) (hQ y).contMDiffWithinAt (hε i y hy) (hε j y hy)
    exact (contMDiffWithinAt_totalSpace.mp h).2
  have hsum : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      n (fun y ↦ (Q y).bilinearComp (synthesisMap ℝ (ε · y)).toContinuousLinearMap
        (synthesisMap ℝ (ε · y)).toContinuousLinearMap) U := by
    simp_rw [bilinearComp_synthesisMap_eq_sum]
    exact contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
      (hc i j).smul contMDiffOn_const
  exact contDiff_continuousLinearMapOfBilin.contMDiff.comp_contMDiffOn hsum

omit [FiniteDimensional ℝ F] [∀ x, CompleteSpace (V x)] [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- Read through the synthesis maps of a `C^n` family of orthonormal bases, the negative spectral
projections of a `C^n` field of nondegenerate symmetric forms are `C^n`. -/
private theorem contMDiffOn_starProjection_synthesisMap {d : ℕ}
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x))
    {ε : Fin d → Π x, V x} {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i)))
    (hon : ∀ y ∈ U, Orthonormal ℝ (ε · y))
    (hsp : ∀ y ∈ U, ⊤ ≤ Submodule.span ℝ (range (ε · y))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ (Module.End.pointSpectralSubspace (continuousLinearMapOfBilin
        ((Q y).bilinearComp (synthesisMap ℝ (ε · y)).toContinuousLinearMap
          (synthesisMap ℝ (ε · y)).toContinuousLinearMap)).toLinearMap (Iio 0)).starProjection)
      U :=
  ((contDiffOn_id (s := {A | IsSelfAdjoint A ∧ IsUnit A})
    ).starProjection_pointSpectralSubspace_Iio_zero (fun A hA ↦ hA.1)
    (fun A hA ↦ hA.2)).contMDiffOn.comp
    (contMDiffOn_continuousLinearMapOfBilin_synthesisMap hQ hε) fun y hy ↦
      ⟨isSelfAdjoint_continuousLinearMapOfBilin fun v w ↦ hsymm y _ _,
        isUnit_continuousLinearMapOfBilin (ContinuousLinearMap.injective_bilinearComp (hnd y)
          (by simpa using bijective_synthesisMap (hon y hy).linearIndependent (hsp y hy)))⟩

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
  classical
  -- The Gram–Schmidt orthonormal basis of the fibres over the base set, extended by `0`.
  set ε : Fin (Module.finrank ℝ F) → Π x, V x := fun i y ↦
    if hy : y ∈ e.baseSet then e.orthonormalBasis (Module.finBasis ℝ F) ⟨y, hy⟩ i else 0
  have hε (i : Fin (Module.finrank ℝ F)) : CMDiff[e.baseSet] n (T% (ε i)) :=
    e.contMDiffOn_orthonormalBasis (I := IB) (n := n) (Module.finBasis ℝ F) i
  have hεb (y : B) (hy : y ∈ e.baseSet) :
      (ε · y) = e.orthonormalBasis (Module.finBasis ℝ F) ⟨y, hy⟩ := by
    funext i
    exact dite_eq_left_of_eq_true (eq_true hy)
  have hon (y : B) (hy : y ∈ e.baseSet) : Orthonormal ℝ (ε · y) := by
    rw [hεb y hy]
    exact OrthonormalBasis.orthonormal _
  have hsp (y : B) (hy : y ∈ e.baseSet) : ⊤ ≤ Submodule.span ℝ (range (ε · y)) := by
    rw [hεb y hy, ← OrthonormalBasis.coe_toBasis, Module.Basis.span_eq]
  -- In these frames the negative spectral subspaces are the images of those in coordinates.
  have hspec (y : B) (hy : y ∈ e.baseSet) :=
    pointSpectralSubspace_continuousLinearMapOfBilin_eq_map_synthesisMap (Q y) (hon y hy) (hsp y hy)
      (Iio 0)
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  obtain ⟨U, hUe, hU, hxU, X, hX, hXn⟩ := exists_isSubbundleFrameOn_map_synthesisMap (r := r)
    e.open_baseSet hε (fun y hy ↦ (hon y hy).linearIndependent)
    (contMDiffOn_starProjection_synthesisMap hQ hsymm hnd hε hon hsp) hx₀ (by
      rw [← hr, hspec x₀ hx₀]
      exact (Submodule.equivMapOfInjective _
        (bijective_synthesisMap (hon x₀ hx₀).linearIndependent (hsp x₀ hx₀)).1 _).finrank_eq)
  exact ⟨U, hU, hxU, X, ⟨hX.continuousOn, hX.linearIndependent, fun hy ↦
    (hX.span_eq hy).trans (hspec _ (hUe hy)).symm⟩, hXn⟩

/-- If the negative spectral subspaces of a `C^n` field `Q` of nondegenerate symmetric forms have
dimension `r` at every point of `B` (for instance when `B` is connected, by
`TauCeti.eventually_finrank_pointSpectralSubspace_Iio_eq`), they satisfy the local frame criterion
for a `C^n` subbundle of rank `r`, the negative spectral subbundle of `Q`. -/
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
  rw [← pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg] at hr
  simp_rw [← pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg]
  exact exists_isSubbundleFrameOn_pointSpectralSubspace_Iio (Q := fun x ↦ -Q x)
    (fun x ↦ (hQ x).neg_section)
    (fun x v w ↦ by simp [hsymm x v w]) (fun x ↦ neg_injective.comp (hnd x)) x₀ hr

/-- If the positive spectral subspaces of a `C^n` field `Q` of nondegenerate symmetric forms have
dimension `r` at every point of `B` (for instance when `B` is connected, by
`TauCeti.eventually_finrank_pointSpectralSubspace_Ioi_eq`), they satisfy the local frame criterion
for a `C^n` subbundle of rank `r`, the positive spectral subbundle of `Q`. -/
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

/-- The dimension of the positive spectral subspace of a `C^n` field of nondegenerate symmetric
forms, which is its positive index of inertia, is locally constant; `n = 0` is allowed. This is
`TauCeti.eventually_finrank_pointSpectralSubspace_Iio_eq` for `-Q`. -/
theorem eventually_finrank_pointSpectralSubspace_Ioi_eq
    (hQ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (Q x)))
    (hsymm : ∀ x v w, Q x v w = Q x w v) (hnd : ∀ x, Function.Injective (Q x)) (x₀ : B) :
    ∀ᶠ x in 𝓝 x₀, Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin (Q x)).toLinearMap (Ioi 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin (Q x₀)).toLinearMap (Ioi 0)) := by
  filter_upwards [eventually_finrank_pointSpectralSubspace_Iio_eq (Q := fun x ↦ -Q x)
    (fun x ↦ (hQ x).neg_section) (fun x v w ↦ by simp [hsymm x v w])
    (fun x ↦ neg_injective.comp (hnd x)) x₀] with x hx
  rwa [← pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg,
    ← pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg]

end Bundle

end TauCeti
