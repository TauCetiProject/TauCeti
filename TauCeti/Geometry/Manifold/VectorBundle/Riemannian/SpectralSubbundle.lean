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
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Projection
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic

/-!
# Spectral subbundles of a symmetric bundle endomorphism

Let `V` be a `C^n` Riemannian vector bundle with finite-dimensional model fibre `F` over a
manifold `B`, and let `A x : V x →L[ℝ] V x` be a `C^n` family of fibrewise symmetric, injective
operators, given as a `C^n` section of the bundle of fibrewise continuous linear maps. The
**negative spectral subspace** of `A x` is its point-spectral subspace selected by the negative
reals, the sum of its eigenspaces at negative eigenvalues; likewise for the positive one. This file
shows that, when `A` has these properties on an open set `W`, the subspaces have `C^n` local frames
near every point of `W` (`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Iio_zero` and
`TauCeti.exists_isSubbundleFrameOn_pointSpectralSubspace_Ioi_zero`). In particular their ranks are
locally constant on `W` (`TauCeti.eventually_finrank_pointSpectralSubspace_Iio_zero_eq`). When `A`
has these properties on all of `B` and the rank is a constant `k` on all of `B`, they are `C^n`
subbundles of `V` by the local frame criterion
(`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Iio_zero`,
`TauCeti.hasLocalContMDiffSubbundleFrames_pointSpectralSubspace_Ioi_zero`).

Applied to the Riesz representative of a nondegenerate symmetric form on a Riemannian vector
bundle, such as the normal Hessian along a Morse–Bott critical submanifold read through a normal
metric, these are the negative and positive subbundles of the form. The subspaces depend on the
metric; their ranks are the indices of inertia of the form.

No smoothly varying eigenbasis is chosen. Near a point `x₀`, a `C^n` orthonormal frame `u` of `V`
(`TauCeti.exists_isLocalFrameOn_orthonormal`) turns `A` into a `C^n` family `S` of symmetric
invertible operators on the fixed space `EuclideanSpace ℝ (Fin (finrank ℝ F))`, the matrices
`⟪u i x, A x (u j x)⟫`. Their spectral projections are `C^n`
(`ContMDiffOn.starProjection_pointSpectralSubspace_Iio_zero`), since they are given by the inverse
square root of `S x * S x`. Projecting a basis of the negative spectral subspace of `S x₀` therefore
gives `C^n` vectors which, for `x` near `x₀`, form a basis of the negative spectral subspace of
`S x`, because the negative and positive spectral subspaces have complementary dimensions
(`TauCeti.eventually_linearIndependent_and_span_starProjection`). Reading these vectors
in the frame `u` gives the local frame.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  (the local frame criterion for smooth subbundles).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti

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

end TauCeti
