/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Inertia
import TauCeti.Analysis.InnerProductSpace.Spectral.Projection
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Synthesis
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

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
smooth family of self-adjoint invertible operators on a fixed Euclidean space
(`TauCeti.contMDiffOn_continuousLinearMapOfBilin_bilinearComp_synthesisMap`), whose spectral
subspaces are those of `Q` in coordinates
(`InnerProductSpace.pointSpectralSubspace_continuousLinearMapOfBilin_eq_map_synthesisMap`) and whose
negative spectral projections are smooth
(`ContinuousLinearMap.starProjection_pointSpectralSubspace_Iio_zero_eq`, which writes them as
`(1 - A (A²)^(-1/2)) / 2`). Projecting a basis of the negative space at the base point and
synthesizing the result against the frame gives the local frame of the negative subspaces
(`TauCeti.exists_isSubbundleFrameOn_map_synthesisMap`).

The motivating example is the normal Hessian of a Morse–Bott critical submanifold, whose negative
and positive parts are the negative and positive normal bundles.

The same holds for a `C^n` family `A x : V x →L[ℝ] V x` of fibrewise symmetric, injective
operators given as a section of the bundle of fibrewise continuous linear maps, on an open set `W`
where it has these properties: near every point of `W` their negative and positive spectral
subspaces have `C^n` local frames
(`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Iio_zero` and
`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi_zero`), their ranks are locally
constant (`TauCeti.eventually_finrank_pointSpectralSubspace_Iio_zero_eq`), and with constant rank
on all of `B` they are `C^n` subbundles
(`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Iio_zero`,
`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Ioi_zero`). Here a `C^n`
orthonormal frame `u` near `x₀` (`TauCeti.exists_isLocalFrameOn_orthonormal`) turns `A` into the
`C^n` family of matrices `⟪u i x, A x (u j x)⟫` on a fixed Euclidean space, whose spectral
projections are `C^n` (`ContMDiffOn.starProjection_pointSpectralSubspace_Iio_zero`); a projected
basis of the negative spectral subspace at `x₀` stays a basis nearby because the negative and
positive spectral subspaces have complementary dimensions
(`TauCeti.eventually_linearIndependent_and_span_starProjection`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. Hurtubise, *Lectures on Morse Homology*, Kluwer Texts in the Mathematical
  Sciences 29, Springer, 2004, Section 3.5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  (the local frame criterion for smooth subbundles).
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
    (contMDiffOn_continuousLinearMapOfBilin_bilinearComp_synthesisMap hQ hε) fun y hy ↦
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

section Endomorphism

open Module
open scoped InnerProductSpace

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}

section SmoothProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {S : B → E →L[ℝ] E} {W : Set B}

/-- The negative spectral projections of a `C^n` family of invertible self-adjoint operators on a
finite-dimensional space form a `C^n` family, also over a manifold. -/
theorem _root_.ContMDiffOn.starProjection_pointSpectralSubspace_Iio_zero (hS : CMDiff[W] n S)
    (hself : ∀ x ∈ W, IsSelfAdjoint (S x)) (hunit : ∀ x ∈ W, IsUnit (S x)) :
    CMDiff[W] n fun x ↦
      (Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0)).starProjection :=
  fun x hx ↦ (contDiffOn_id.starProjection_pointSpectralSubspace_Iio_zero
    (s := {T : E →L[ℝ] E | IsSelfAdjoint T ∧ IsUnit T}) (fun _ hT ↦ hT.1) (fun _ hT ↦ hT.2) (S x)
    ⟨hself x hx, hunit x hx⟩).comp_contMDiffWithinAt (hS x hx) fun y hy ↦ ⟨hself y hy, hunit y hy⟩

/-- The positive spectral projections of a `C^n` family of invertible self-adjoint operators on a
finite-dimensional space form a `C^n` family, also over a manifold. -/
theorem _root_.ContMDiffOn.starProjection_pointSpectralSubspace_Ioi_zero (hS : CMDiff[W] n S)
    (hself : ∀ x ∈ W, IsSelfAdjoint (S x)) (hunit : ∀ x ∈ W, IsUnit (S x)) :
    CMDiff[W] n fun x ↦
      (Module.End.pointSpectralSubspace (S x).toLinearMap (Ioi 0)).starProjection :=
  fun x hx ↦ (contDiffOn_id.starProjection_pointSpectralSubspace_Ioi_zero
    (s := {T : E →L[ℝ] E | IsSelfAdjoint T ∧ IsUnit T}) (fun _ hT ↦ hT.1) (fun _ hT ↦ hT.2) (S x)
    ⟨hself x hx, hunit x hx⟩).comp_contMDiffWithinAt (hS x hx) fun y hy ↦ ⟨hself y hy, hunit y hy⟩

end SmoothProjection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {A : Π x, V x →L[ℝ] V x}

section FrameMatrix

variable {d : ℕ}

/-- The matrix of the operators `A x` in a family of sections `u`, as a family of operators on
Euclidean space: its `(i, j)` entry is `⟪u i x, A x (u j x)⟫`. -/
private def frameMatrix (A : Π x, V x →L[ℝ] V x) (u : Fin d → Π x, V x) (x : B) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ∑ i, ∑ j, ⟪u i x, A x (u j x)⟫_ℝ •
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single i (1 : ℝ))

variable {u : Fin d → Π x, V x} {x : B} {b : OrthonormalBasis (Fin d) ℝ (V x)}

omit [TopologicalSpace B] in
/-- In an orthonormal basis given by the sections `u`, the frame matrix is the operator `A x`
read in coordinates. -/
private theorem repr_symm_frameMatrix_apply (hb : ⇑b = (u · x)) (c : EuclideanSpace ℝ (Fin d)) :
    b.repr.symm (frameMatrix A u x c) = A x (b.repr.symm c) := by
  apply b.repr.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  rw [b.repr_apply_apply, ← b.sum_repr_symm c, map_sum, inner_sum]
  simp only [frameMatrix, hb]
  simp [inner_smul_right, Pi.single_apply, mul_comm]

omit [TopologicalSpace B] in
/-- In an orthonormal basis given by the sections `u`, the coordinate map carries the
point-spectral subspaces of the frame matrix onto those of `A x`. -/
private theorem map_pointSpectralSubspace_frameMatrix (hb : ⇑b = (u · x)) (Ω : Set ℝ) :
    (Module.End.pointSpectralSubspace (frameMatrix A u x).toLinearMap Ω).map
        (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] V x) =
      Module.End.pointSpectralSubspace (A x).toLinearMap Ω :=
  Module.End.map_pointSpectralSubspace_of_comp_eq b.repr.symm.toLinearEquiv
    (LinearMap.ext fun c ↦ by simpa using (repr_symm_frameMatrix_apply hb c).symm) Ω

omit [TopologicalSpace B] in
/-- In an orthonormal basis, the frame matrix of a symmetric operator is self-adjoint. -/
private theorem isSelfAdjoint_frameMatrix (hb : ⇑b = (u · x))
    (hA : (A x).toLinearMap.IsSymmetric) : IsSelfAdjoint (frameMatrix A u x) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun c c' ↦ by
    simpa only [ContinuousLinearMap.coe_coe, ← repr_symm_frameMatrix_apply hb,
      LinearIsometryEquiv.inner_map_map] using hA (b.repr.symm c) (b.repr.symm c')

omit [TopologicalSpace B] in
/-- In an orthonormal basis, the frame matrix of an injective operator is invertible. -/
private theorem isUnit_frameMatrix (hb : ⇑b = (u · x)) (hA : Function.Injective (A x)) :
    IsUnit (frameMatrix A u x) := by
  have h : Function.Injective (frameMatrix A u x) := fun c c' h ↦
    b.repr.symm.injective (hA (by rw [← repr_symm_frameMatrix_apply hb,
      ← repr_symm_frameMatrix_apply hb, h]))
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨h, LinearMap.injective_iff_surjective.mp h⟩

omit [TopologicalSpace B] in
/-- In an orthonormal basis, the negative and positive spectral subspaces of the frame matrix of a
symmetric injective operator have complementary dimensions. -/
private theorem finrank_add_finrank_pointSpectralSubspace_frameMatrix (hb : ⇑b = (u · x))
    (hsymm : (A x).toLinearMap.IsSymmetric) (hinj : Function.Injective (A x)) :
    finrank ℝ (Module.End.pointSpectralSubspace (frameMatrix A u x).toLinearMap (Iio 0)) +
      finrank ℝ (Module.End.pointSpectralSubspace (frameMatrix A u x).toLinearMap (Ioi 0)) =
        finrank ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.finrank_add_eq_of_isCompl <|
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_frameMatrix hb hsymm))
      |>.isCompl_pointSpectralSubspace_Iio_zero_Ioi_zero <| LinearMap.ker_eq_bot.mpr
        (ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_frameMatrix hb hinj)).1

omit [TopologicalSpace B] in
/-- Coefficient vectors forming a basis of a point-spectral subspace of the frame matrix, read in
an orthonormal basis given by the sections `u`, form a basis of the same point-spectral subspace
of `A x`. -/
private theorem linearIndependent_and_span_sum_smul (hb : ⇑b = (u · x)) {Ω : Set ℝ} {k : ℕ}
    {c : Fin k → EuclideanSpace ℝ (Fin d)}
    (hc : LinearIndependent ℝ c ∧ Submodule.span ℝ (range c) =
      Module.End.pointSpectralSubspace (frameMatrix A u x).toLinearMap Ω) :
    LinearIndependent ℝ (fun i ↦ ∑ j, c i j • u j x) ∧
      Submodule.span ℝ (range fun i ↦ ∑ j, c i j • u j x) =
        Module.End.pointSpectralSubspace (A x).toLinearMap Ω := by
  have h : (fun i ↦ ∑ j, c i j • u j x) = b.repr.symm.toLinearEquiv.toLinearMap ∘ c := by
    funext i
    simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      ← b.sum_repr_symm, hb]
  rw [h, range_comp, Submodule.span_image, hc.2]
  exact ⟨hc.1.map' _ (LinearEquiv.ker _), map_pointSpectralSubspace_frameMatrix hb Ω⟩

variable [IsContMDiffRiemannianBundle IB n F V]

/-- The frame matrix of a `C^n` family of operators in `C^n` sections is `C^n`. -/
private theorem contMDiffAt_frameMatrix {x₀ : B}
    (hA : CMDiffAt n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)) x₀)
    (hu : ∀ i, CMDiffAt n (T% (u i)) x₀) :
    CMDiffAt n (frameMatrix A u) x₀ :=
  contMDiffAt_finsetSum fun i _ ↦ contMDiffAt_finsetSum fun j _ ↦
    ((hu i).inner_bundle (hA.clm_bundle_apply (hu j))).smul contMDiffAt_const

end FrameMatrix

/-- `C^n` coefficients read in `C^n` sections give a `C^n` section. -/
private theorem contMDiffAt_sum_smul {d : ℕ} {u : Fin d → Π x, V x}
    {c : B → EuclideanSpace ℝ (Fin d)} {x : B} (hc : CMDiffAt n c x)
    (hu : ∀ j, CMDiffAt n (T% (u j)) x) :
    CMDiffAt n (T% fun y ↦ ∑ j, c y j • u j y) x :=
  ContMDiffAt.sum_section fun j _ ↦ ((EuclideanSpace.proj j :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contMDiff.contMDiffAt.comp x hc).smul_section (hu j)

variable [ContMDiffVectorBundle n F V IB] [IsContMDiffRiemannianBundle IB n F V]
  [FiniteDimensional ℝ F] {W : Set B}

/-- **Smooth local frames of the negative spectral subspaces.** Let `A` be a `C^n` family of
symmetric injective operators on the fibres of a `C^n` Riemannian vector bundle over an open set
`W`. Near every point `x₀` of `W`, the negative spectral subspaces of the operators `A x` have a
`C^n` local frame with as many members as the dimension of the negative spectral subspace of
`A x₀`. -/
theorem exists_isSubbundleFrameOn_pointSpectralSubspace_Iio_zero (hW : IsOpen W)
    (hA : CMDiff[W] n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)))
    (hsymm : ∀ x ∈ W, (A x).toLinearMap.IsSymmetric)
    (hinj : ∀ x ∈ W, Function.Injective (A x)) {x₀ : B} (hx₀ : x₀ ∈ W) {k : ℕ}
    (hk : finrank ℝ (Module.End.pointSpectralSubspace (A x₀).toLinearMap (Iio 0)) = k) :
    ∃ U ⊆ W, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin k → Π x, V x,
      IsSubbundleFrameOn F (fun x ↦ Module.End.pointSpectralSubspace (A x).toLinearMap (Iio 0))
        X U ∧ ∀ i, CMDiff[U] n (T% (X i)) := by
  classical
  -- Read `A` in a smooth orthonormal frame `u` on `U₁`, as the frame matrix `S`.
  obtain ⟨U₁, hU₁, hx₀U₁, u, hu, hon⟩ :=
    exists_isLocalFrameOn_orthonormal (I := IB) (n := n) (F := F) (V := V) x₀
  have hob (x : B) (hx : x ∈ U₁) : ∃ b : OrthonormalBasis _ ℝ (V x), ⇑b = (u · x) :=
    ⟨OrthonormalBasis.mk (hon x hx) (hu.generating hx), OrthonormalBasis.coe_mk _ _⟩
  have hu' (x : B) (hx : x ∈ U₁) (j : Fin (finrank ℝ F)) : CMDiffAt n (T% (u j)) x :=
    (hu.contMDiffOn j x hx).contMDiffAt (hU₁.mem_nhds hx)
  have hW₁ := hW.inter hU₁
  set S := frameMatrix A u
  have hS : CMDiff[W ∩ U₁] n S := fun x hx ↦ (contMDiffAt_frameMatrix
    ((hA x hx.1).contMDiffAt (hW.mem_nhds hx.1)) (hu' x hx.2)).contMDiffWithinAt
  have hSsa (x : B) (hx : x ∈ W ∩ U₁) : IsSelfAdjoint (S x) :=
    (hob x hx.2).elim fun _ hb ↦ isSelfAdjoint_frameMatrix hb (hsymm x hx.1)
  have hSunit (x : B) (hx : x ∈ W ∩ U₁) : IsUnit (S x) :=
    (hob x hx.2).elim fun _ hb ↦ isUnit_frameMatrix hb (hinj x hx.1)
  have hPN := hS.starProjection_pointSpectralSubspace_Iio_zero hSsa hSunit
  have hPP := hS.starProjection_pointSpectralSubspace_Ioi_zero hSsa hSunit
  -- Project a basis of the negative spectral subspace of `S x₀`.
  obtain ⟨b₀, hb₀⟩ := hob x₀ hx₀U₁
  obtain ⟨bN⟩ : Nonempty (Basis (Fin k) ℝ
      (Module.End.pointSpectralSubspace (S x₀).toLinearMap (Iio 0))) :=
    ⟨Module.finBasisOfFinrankEq ℝ _ (by
      rw [← hk, ← map_pointSpectralSubspace_frameMatrix hb₀, LinearEquiv.finrank_map_eq])⟩
  have hW₁x₀ : W ∩ U₁ ∈ 𝓝 x₀ := hW₁.mem_nhds ⟨hx₀, hx₀U₁⟩
  obtain ⟨U, hUsub, hU, hx₀U⟩ := mem_nhds_iff.mp <|
    (eventually_linearIndependent_and_span_starProjection (hPN.continuousOn.continuousAt hW₁x₀)
      (hPP.continuousOn.continuousAt hW₁x₀) (eventually_of_mem hW₁x₀ fun x hx ↦
        (hob x hx.2).elim fun _ hb ↦
          finrank_add_finrank_pointSpectralSubspace_frameMatrix hb (hsymm x hx.1) (hinj x hx.1))
      bN).and hW₁x₀
  -- The frame is the projected basis read back in the orthonormal frame `u`.
  let PN (x : B) := (Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0)).starProjection
  have hXs (i : Fin k) : CMDiff[U] n (T% fun x ↦ ∑ j, PN x (bN i) j • u j x) := fun x hx ↦
    (contMDiffAt_sum_smul (((hPN x (hUsub hx).2).contMDiffAt (hW₁.mem_nhds (hUsub hx).2)).clm_apply
      contMDiffAt_const) (hu' x (hUsub hx).2.2)).contMDiffWithinAt
  have hX {x : B} (hx : x ∈ U) := (hob x (hUsub hx).2.2).elim fun _ hb ↦
    linearIndependent_and_span_sum_smul (Ω := Iio 0) hb (hUsub hx).1
  exact ⟨U, fun x hx ↦ (hUsub hx).2.1, hU, hx₀U, fun i x ↦ ∑ j, PN x (bN i) j • u j x,
    ⟨fun i ↦ (hXs i).continuousOn, fun hx ↦ (hX hx).1, fun hx ↦ (hX hx).2⟩, hXs⟩

/-- **Smooth local frames of the positive spectral subspaces.** Let `A` be a `C^n` family of
symmetric injective operators on the fibres of a `C^n` Riemannian vector bundle over an open set
`W`. Near every point `x₀` of `W`, the positive spectral subspaces of the operators `A x` have a
`C^n` local frame with as many members as the dimension of the positive spectral subspace of
`A x₀`. -/
theorem exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi_zero (hW : IsOpen W)
    (hA : CMDiff[W] n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)))
    (hsymm : ∀ x ∈ W, (A x).toLinearMap.IsSymmetric)
    (hinj : ∀ x ∈ W, Function.Injective (A x)) {x₀ : B} (hx₀ : x₀ ∈ W) {k : ℕ}
    (hk : finrank ℝ (Module.End.pointSpectralSubspace (A x₀).toLinearMap (Ioi 0)) = k) :
    ∃ U ⊆ W, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin k → Π x, V x,
      IsSubbundleFrameOn F (fun x ↦ Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0))
        X U ∧ ∀ i, CMDiff[U] n (T% (X i)) := by
  have h (x : B) : Module.End.pointSpectralSubspace (-A x).toLinearMap (Iio 0) =
      Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0) := by
    rw [ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, Set.neg_Iio,
      neg_zero]
  simpa only [Pi.neg_apply, h] using exists_isSubbundleFrameOn_pointSpectralSubspace_Iio_zero
    (A := -A) hW hA.neg_section (fun x hx ↦ by simpa using (hsymm x hx).neg)
    (fun x hx _ _ hab ↦ hinj x hx (neg_injective hab)) hx₀ (by rw [Pi.neg_apply, h x₀, hk])

/-- **The rank of the negative spectral subspaces is locally constant.** Let `A` be a `C^n` family
of symmetric injective operators on the fibres of a `C^n` Riemannian vector bundle over an open set
`W`. Near every point `x₀` of `W`, the negative spectral subspaces of the operators `A x` have the
same dimension as that of `A x₀`. -/
theorem eventually_finrank_pointSpectralSubspace_Iio_zero_eq (hW : IsOpen W)
    (hA : CMDiff[W] n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)))
    (hsymm : ∀ x ∈ W, (A x).toLinearMap.IsSymmetric)
    (hinj : ∀ x ∈ W, Function.Injective (A x)) {x₀ : B} (hx₀ : x₀ ∈ W) :
    ∀ᶠ x in 𝓝 x₀, finrank ℝ (Module.End.pointSpectralSubspace (A x).toLinearMap (Iio 0)) =
      finrank ℝ (Module.End.pointSpectralSubspace (A x₀).toLinearMap (Iio 0)) := by
  obtain ⟨U, -, hU, hx₀U, X, hX, -⟩ :=
    exists_isSubbundleFrameOn_pointSpectralSubspace_Iio_zero hW hA hsymm hinj hx₀ rfl
  filter_upwards [hU.mem_nhds hx₀U] with x hx
  rw [hX.finrank_eq hx, Fintype.card_fin]

/-- **The rank of the positive spectral subspaces is locally constant.** Let `A` be a `C^n` family
of symmetric injective operators on the fibres of a `C^n` Riemannian vector bundle over an open set
`W`. Near every point `x₀` of `W`, the positive spectral subspaces of the operators `A x` have the
same dimension as that of `A x₀`. -/
theorem eventually_finrank_pointSpectralSubspace_Ioi_zero_eq (hW : IsOpen W)
    (hA : CMDiff[W] n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)))
    (hsymm : ∀ x ∈ W, (A x).toLinearMap.IsSymmetric)
    (hinj : ∀ x ∈ W, Function.Injective (A x)) {x₀ : B} (hx₀ : x₀ ∈ W) :
    ∀ᶠ x in 𝓝 x₀, finrank ℝ (Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0)) =
      finrank ℝ (Module.End.pointSpectralSubspace (A x₀).toLinearMap (Ioi 0)) := by
  obtain ⟨U, -, hU, hx₀U, X, hX, -⟩ :=
    exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi_zero hW hA hsymm hinj hx₀ rfl
  filter_upwards [hU.mem_nhds hx₀U] with x hx
  rw [hX.finrank_eq hx, Fintype.card_fin]

/-- **The negative spectral subbundle.** For a `C^n` family of symmetric injective operators on
the fibres of a `C^n` Riemannian vector bundle whose negative spectral subspaces all have
dimension `k`, these subspaces have `C^n` local frames of size `k` near every point, so they form a
`C^n` subbundle (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Iio_zero
    (hA : CMDiff n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)))
    (hsymm : ∀ x, (A x).toLinearMap.IsSymmetric) (hinj : ∀ x, Function.Injective (A x)) {k : ℕ}
    (hk : ∀ x, finrank ℝ (Module.End.pointSpectralSubspace (A x).toLinearMap (Iio 0)) = k) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin k)
      fun x ↦ Module.End.pointSpectralSubspace (A x).toLinearMap (Iio 0) :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ by
    obtain ⟨U, -, hU, hx₀U, hX⟩ := exists_isSubbundleFrameOn_pointSpectralSubspace_Iio_zero
      isOpen_univ hA.contMDiffOn (fun x _ ↦ hsymm x) (fun x _ ↦ hinj x) (mem_univ x₀) (hk x₀)
    exact ⟨U, hU, hx₀U, hX⟩

/-- **The positive spectral subbundle.** For a `C^n` family of symmetric injective operators on
the fibres of a `C^n` Riemannian vector bundle whose positive spectral subspaces all have
dimension `k`, these subspaces have `C^n` local frames of size `k` near every point, so they form a
`C^n` subbundle (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Ioi_zero
    (hA : CMDiff n (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (A x)))
    (hsymm : ∀ x, (A x).toLinearMap.IsSymmetric) (hinj : ∀ x, Function.Injective (A x)) {k : ℕ}
    (hk : ∀ x, finrank ℝ (Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0)) = k) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin k)
      fun x ↦ Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0) :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ by
    obtain ⟨U, -, hU, hx₀U, hX⟩ := exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi_zero
      isOpen_univ hA.contMDiffOn (fun x _ ↦ hsymm x) (fun x _ ↦ hinj x) (mem_univ x₀) (hk x₀)
    exact ⟨U, hU, hx₀U, hX⟩

end Endomorphism

end TauCeti
