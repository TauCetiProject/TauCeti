/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm.Norm
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import TauCeti.Analysis.InnerProductSpace.CourantFischer
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Principal curvatures and the mean curvature vector of an immersion

Let `f : M → N` be a map into a manifold with a Riemannian metric and a covariant derivative `∇`
on `TN`, and let `M` carry a Riemannian metric. The metric on `M` is an arbitrary instance,
unrelated to `f`: every inner product, trace and orthonormal basis on `T_xM` below is taken with
respect to it, and the objects defined here are the classical ones of an immersion exactly when it
is the pullback of the metric of `N` along `f`. At a point `x`, the pointwise second fundamental
form `B_x : T_xM × T_xM → T_{f x}N` (`TauCeti.immersionSecondFundamentalFormAt`) defines:

* for a vector `ν` at `f x`, the **shape operator** (Weingarten map) `S_ν : T_xM → T_xM`, the
  endomorphism with `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫` (`TauCeti.immersionShapeOperatorAt`). It is the
  pointwise counterpart, valued in `T_xM`, of the field-level shape operator
  `TauCeti.immersionShapeOperator`, whose values are kept in `range df_x ⊆ T_{f x}N`. It is linear
  in `ν`, and for a torsion-free `∇` it is self-adjoint; its eigenvalues, with multiplicity and in
  decreasing order, are the **principal curvatures** of `f` at `x` in the direction `ν`
  (`TauCeti.immersionPrincipalCurvatures`). Reversing `ν` negates `S_ν`, so it negates the
  principal curvatures and reverses their order.
* the **mean curvature vector** `H = (tr B_x) / m`, `m = dim M`, the metric trace of `B_x`
  divided by `m` (`TauCeti.immersionMeanCurvatureVector`). It is independent of frames:
  `H = (1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` for every orthonormal basis `(eᵢ)` of `T_xM`. It is normal, and
  `⟪H, ν⟫ = (tr S_ν) / m` is the average of the principal curvatures in the direction `ν`.
  `f` is minimal at `x` when `H = 0`; this holds where `B_x = 0`, at totally geodesic points.
  Near a point where `df_x` is injective, `H = (1 / m) ∑ᵢ B(Xᵢ, Xᵢ)` for a local orthonormal frame
  `(Xᵢ)` of `TM`, so `H` is `C^k` where `f` is `C^{k+2}`, the covariant derivative is `C^k`, and
  the metrics are `C^{k+1}` on `M` and `C^k` on `N`; this is the frame argument of
  `TauCeti.continuousAt_immersionSecondFundamentalFormNormSq`, through the shared
  `TauCeti.contMDiffAt_immersionSecondFundamentalForm`. In particular `H` is a smooth normal field
  along a smooth immersion.

## Main definitions

* `TauCeti.immersionShapeOperatorAt`: the pointwise shape operator `S_ν`.
* `TauCeti.immersionPrincipalCurvatures`: the principal curvatures in the direction `ν`.
* `TauCeti.immersionMeanCurvatureVector`: the mean curvature vector `H`.

## Main results

* `TauCeti.inner_immersionShapeOperatorAt`: `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫`.
* `TauCeti.immersionShapeOperatorAt_add`, `TauCeti.immersionShapeOperatorAt_smul`: `S_ν` is linear
  in `ν`.
* `TauCeti.isSymmetric_immersionShapeOperatorAt`: `S_ν` is self-adjoint for a torsion-free `∇`.
* `TauCeti.hasEigenvalue_immersionShapeOperatorAt_immersionPrincipalCurvatures`,
  `TauCeti.immersionPrincipalCurvatures_eq_of_eigenbasis`: the principal curvatures are the
  eigenvalues of `S_ν`, and a decreasing diagonalization of `S_ν` computes them.
* `TauCeti.immersionPrincipalCurvatures_neg`: reversing `ν` negates the principal curvatures and
  reverses their order.
* `TauCeti.immersionMeanCurvatureVector_eq_sum`: `H = (1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` in any orthonormal
  basis.
* `TauCeti.immersionMeanCurvatureVector_mem`: `H` is normal.
* `TauCeti.inner_immersionMeanCurvatureVector`,
  `TauCeti.inner_immersionMeanCurvatureVector_eq_sum_div`: `⟪H, ν⟫ = (tr S_ν) / m`, the average of
  the principal curvatures.
* `TauCeti.immersionMeanCurvatureVector_eq_zero_of_immersionSecondFundamentalFormAt_eq_zero`:
  totally geodesic points are minimal.
* `TauCeti.contMDiffAt_immersionMeanCurvatureVector`,
  `TauCeti.contMDiff_immersionMeanCurvatureVector`: `H` is `C^k` along a `C^{k+2}` immersion,
  including at boundary and corner points of the source.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the Weingarten equation, principal curvatures and the mean curvature vector, a smooth normal
  vector field along an immersion).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold Module
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

open TauCeti.Manifold

variable
  {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]

section Pointwise

variable [IsManifold J 2 N]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} {f : M → N} {x : M}

/-! ### The shape operator and the principal curvatures -/

variable (cov f x) in
/-- The **shape operator** (Weingarten map) `S_ν : T_xM → T_xM` of `f` at `x` in the direction of
a vector `ν` at `f x`: the endomorphism with `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫` for the pointwise second
fundamental form `B_x` (`TauCeti.inner_immersionShapeOperatorAt`). The inner product on `T_xM` is
that of the given metric on `M`; this is the classical shape operator when that metric is the
pullback one. -/
def immersionShapeOperatorAt (ν : TangentSpace J (f x)) : Module.End ℝ (TangentSpace I x) :=
  LinearMap.BilinForm.symmCompOfNondegenerate
    ((immersionSecondFundamentalFormAt (I := I) cov f x).toLinearMap₁₂.compr₂
      ((innerₗ (TangentSpace J (f x))).flip ν))
    (innerₗ (TangentSpace I x)) nondegenerate_inner

/-- **The defining property of the shape operator**: `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫`. -/
@[simp]
theorem inner_immersionShapeOperatorAt (ν : TangentSpace J (f x)) (v w : TangentSpace I x) :
    ⟪immersionShapeOperatorAt cov f x ν v, w⟫_ℝ =
      ⟪immersionSecondFundamentalFormAt cov f x v w, ν⟫_ℝ := by
  simpa only [immersionShapeOperatorAt, innerₗ_apply_apply, LinearMap.compr₂_apply,
    LinearMap.flip_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
      ((immersionSecondFundamentalFormAt (I := I) cov f x).toLinearMap₁₂.compr₂
        ((innerₗ (TangentSpace J (f x))).flip ν))
      (nondegenerate_inner (E := TangentSpace I x)) w v

/-- The shape operator is the unique endomorphism `S` with `⟪S v, w⟫ = ⟪B_x(v, w), ν⟫`. -/
theorem eq_immersionShapeOperatorAt_iff (ν : TangentSpace J (f x))
    (S : Module.End ℝ (TangentSpace I x)) :
    S = immersionShapeOperatorAt (I := I) cov f x ν ↔
      ∀ v w, ⟪S v, w⟫_ℝ = ⟪immersionSecondFundamentalFormAt cov f x v w, ν⟫_ℝ := by
  refine ⟨fun h ↦ h ▸ inner_immersionShapeOperatorAt ν, fun h ↦ ?_⟩
  ext v
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [h, inner_immersionShapeOperatorAt]

/-- The shape operator is additive in the normal direction: `S_{ν + ν'} = S_ν + S_{ν'}`. -/
@[simp]
theorem immersionShapeOperatorAt_add (ν ν' : TangentSpace J (f x)) :
    immersionShapeOperatorAt (I := I) cov f x (ν + ν') =
      immersionShapeOperatorAt cov f x ν + immersionShapeOperatorAt cov f x ν' := by
  refine ((eq_immersionShapeOperatorAt_iff _ _).mpr fun v w ↦ ?_).symm
  rw [LinearMap.add_apply, inner_add_left, inner_immersionShapeOperatorAt,
    inner_immersionShapeOperatorAt, inner_add_right]

/-- The shape operator is homogeneous in the normal direction: `S_{c ν} = c S_ν`. -/
@[simp]
theorem immersionShapeOperatorAt_smul (c : ℝ) (ν : TangentSpace J (f x)) :
    immersionShapeOperatorAt (I := I) cov f x (c • ν) = c • immersionShapeOperatorAt cov f x ν := by
  refine ((eq_immersionShapeOperatorAt_iff _ _).mpr fun v w ↦ ?_).symm
  rw [LinearMap.smul_apply, real_inner_smul_left, inner_immersionShapeOperatorAt,
    real_inner_smul_right]

/-- The shape operator in the zero direction vanishes: `S_0 = 0`. -/
@[simp]
theorem immersionShapeOperatorAt_zero :
    immersionShapeOperatorAt (I := I) cov f x 0 = 0 := by
  simpa using immersionShapeOperatorAt_smul (I := I) (cov := cov) (f := f) (x := x) 0 0

/-- Reversing the normal direction negates the shape operator: `S_{-ν} = -S_ν`. -/
@[simp]
theorem immersionShapeOperatorAt_neg (ν : TangentSpace J (f x)) :
    immersionShapeOperatorAt (I := I) cov f x (-ν) = -immersionShapeOperatorAt cov f x ν := by
  simpa using immersionShapeOperatorAt_smul (I := I) (cov := cov) (-1) ν

/-- **The shape operator is self-adjoint** for a torsion-free covariant derivative, since the
second fundamental form is then symmetric. -/
theorem isSymmetric_immersionShapeOperatorAt (ht : cov.IsTorsionFree) (ν : TangentSpace J (f x)) :
    (immersionShapeOperatorAt (I := I) cov f x ν).IsSymmetric := by
  intro v w
  rw [inner_immersionShapeOperatorAt, real_inner_comm (immersionShapeOperatorAt cov f x ν w) v,
    inner_immersionShapeOperatorAt, immersionSecondFundamentalFormAt_comm ht]

/-- Reversing the normal direction negates the eigenvalues of the shape operator: `μ` is an
eigenvalue of `S_{-ν}` exactly when `-μ` is an eigenvalue of `S_ν`. -/
theorem hasEigenvalue_immersionShapeOperatorAt_neg_iff (ν : TangentSpace J (f x)) (μ : ℝ) :
    Module.End.HasEigenvalue (immersionShapeOperatorAt (I := I) cov f x (-ν)) μ ↔
      Module.End.HasEigenvalue (immersionShapeOperatorAt (I := I) cov f x ν) (-μ) := by
  rw [immersionShapeOperatorAt_neg, Module.End.hasEigenvalue_neg_iff]

variable (I f x) in
/-- The **principal curvatures** `κ₁ ≥ ⋯ ≥ κₘ` of `f` at `x` in the direction `ν`, for a
torsion-free covariant derivative and `m = dim M`: the eigenvalues of the self-adjoint shape
operator `S_ν`, with multiplicity and in decreasing order. They are computed with the given metric
on `M`, and are the classical principal curvatures when that metric is the pullback one. -/
def immersionPrincipalCurvatures (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m)
    (ν : TangentSpace J (f x)) : Fin m → ℝ :=
  (isSymmetric_immersionShapeOperatorAt (I := I) (x := x) ht ν).eigenvalues
    (hm : finrank ℝ (TangentSpace I x) = m)

/-- The principal curvatures are listed in decreasing order. -/
theorem immersionPrincipalCurvatures_antitone (ht : cov.IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ E = m) (ν : TangentSpace J (f x)) :
    Antitone (immersionPrincipalCurvatures I f x ht hm ν) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

/-- Each principal curvature is an eigenvalue of the shape operator. -/
theorem hasEigenvalue_immersionShapeOperatorAt_immersionPrincipalCurvatures
    (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m) (ν : TangentSpace J (f x))
    (i : Fin m) :
    Module.End.HasEigenvalue (immersionShapeOperatorAt (I := I) cov f x ν)
      (immersionPrincipalCurvatures I f x ht hm ν i) :=
  LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ i

/-- **Computing the principal curvatures**: if a basis `b` of `T_xM` diagonalizes `S_ν` with a
decreasing list of eigenvalues `μ`, then `μ` is the list of principal curvatures. -/
theorem immersionPrincipalCurvatures_eq_of_eigenbasis (ht : cov.IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ E = m) (ν : TangentSpace J (f x))
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x))
    {μ : Fin m → ℝ} (hμ : Antitone μ)
    (hb : ∀ i, immersionShapeOperatorAt cov f x ν (b i) = μ i • b i) :
    immersionPrincipalCurvatures I f x ht hm ν = μ :=
  LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ _ b hμ hb

/-- If `S_ν = c • id`, every principal curvature in the direction `ν` equals `c`. -/
theorem immersionPrincipalCurvatures_eq_of_immersionShapeOperatorAt_eq_smul
    (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m) (ν : TangentSpace J (f x)) {c : ℝ}
    (hc : immersionShapeOperatorAt (I := I) cov f x ν = c • 1) (i : Fin m) :
    immersionPrincipalCurvatures I f x ht hm ν i = c :=
  congrFun (immersionPrincipalCurvatures_eq_of_eigenbasis ht hm ν
    (finBasisOfFinrankEq ℝ (TangentSpace I x) hm) antitone_const fun _ ↦ by simp [hc]) i

/-- **Reversing the normal direction negates the principal curvatures and reverses their
order**: `κᵢ(-ν) = -κ_{m-1-i}(ν)`. -/
theorem immersionPrincipalCurvatures_neg (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m)
    (ν : TangentSpace J (f x)) (i : Fin m) :
    immersionPrincipalCurvatures I f x ht hm (-ν) i =
      -immersionPrincipalCurvatures I f x ht hm ν i.rev := by
  -- `S_{-ν} = -S_ν`, and the sorted eigenvalues of `-S_ν` are known.
  exact (congrFun (LinearMap.IsSymmetric.eigenvalues_congr (immersionShapeOperatorAt_neg ν) _
    (isSymmetric_immersionShapeOperatorAt ht ν).neg _) i).trans
      (LinearMap.IsSymmetric.eigenvalues_neg _ _ i)

/-- The trace of the shape operator is the sum of the principal curvatures. -/
theorem trace_immersionShapeOperatorAt (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m)
    (ν : TangentSpace J (f x)) :
    LinearMap.trace ℝ _ (immersionShapeOperatorAt (I := I) cov f x ν) =
      ∑ i, immersionPrincipalCurvatures I f x ht hm ν i :=
  (isSymmetric_immersionShapeOperatorAt ht ν).trace_eq_sum_eigenvalues _

/-! ### The mean curvature vector -/

variable (cov f x) in
/-- The **mean curvature vector** `H = (tr B_x) / m` of `f` at `x`, `m = dim M`: the metric trace
of the pointwise second fundamental form divided by the dimension of `M`. In an orthonormal basis
it is `(1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` (`TauCeti.immersionMeanCurvatureVector_eq_sum`). For `m = 0` it is
`0`. The trace uses the given metric on `M`; this is the classical mean curvature vector when that
metric is the pullback one. -/
def immersionMeanCurvatureVector : TangentSpace J (f x) :=
  (finrank ℝ E : ℝ)⁻¹ • LinearMap.BilinMap.metricTrace (W := TangentSpace I x)
    (immersionSecondFundamentalFormAt (I := I) cov f x).toLinearMap₁₂

/-- **The mean curvature vector in an orthonormal basis**: `H = (1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` for every
orthonormal basis `(eᵢ)` of `T_xM`, so `H` does not depend on the choice of frame. -/
theorem immersionMeanCurvatureVector_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    immersionMeanCurvatureVector (I := I) cov f x =
      (finrank ℝ E : ℝ)⁻¹ • ∑ i, immersionSecondFundamentalFormAt cov f x (b i) (b i) := by
  rw [immersionMeanCurvatureVector, LinearMap.BilinMap.metricTrace_eq_sum _ b]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- The mean curvature vector is normal. -/
theorem immersionMeanCurvatureVector_mem :
    immersionMeanCurvatureVector (I := I) cov f x ∈ orthogonalNormalSpace I J f x := by
  rw [immersionMeanCurvatureVector_eq_sum (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun i _ ↦ immersionSecondFundamentalFormAt_mem _ _)

/-- **Totally geodesic points are minimal**: where the second fundamental form vanishes, so does
the mean curvature vector. -/
theorem immersionMeanCurvatureVector_eq_zero_of_immersionSecondFundamentalFormAt_eq_zero
    (hB : immersionSecondFundamentalFormAt (I := I) cov f x = 0) :
    immersionMeanCurvatureVector (I := I) cov f x = 0 := by
  simp [immersionMeanCurvatureVector, hB]

/-- The normal component of the mean curvature vector in the direction `ν` is the trace of the
shape operator divided by the dimension: `⟪H, ν⟫ = (tr S_ν) / m`. -/
theorem inner_immersionMeanCurvatureVector (ν : TangentSpace J (f x)) :
    ⟪immersionMeanCurvatureVector (I := I) cov f x, ν⟫_ℝ =
      LinearMap.trace ℝ _ (immersionShapeOperatorAt (I := I) cov f x ν) / finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [immersionMeanCurvatureVector_eq_sum b, LinearMap.trace_eq_sum_inner _ b, inner_smul_left,
    sum_inner, div_eq_inv_mul]
  simp only [RCLike.conj_to_real]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm (immersionShapeOperatorAt cov f x ν (b i)) (b i),
    inner_immersionShapeOperatorAt]

/-- For a torsion-free covariant derivative, `⟪H, ν⟫` is the average of the principal curvatures
in the direction `ν`: `⟪H, ν⟫ = (∑ᵢ κᵢ) / m`. For a hypersurface and a unit normal `ν` this is
the scalar mean curvature. -/
theorem inner_immersionMeanCurvatureVector_eq_sum_div (ht : cov.IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ E = m) (ν : TangentSpace J (f x)) :
    ⟪immersionMeanCurvatureVector (I := I) cov f x, ν⟫_ℝ =
      (∑ i, immersionPrincipalCurvatures I f x ht hm ν i) / m := by
  rw [inner_immersionMeanCurvatureVector, trace_immersionShapeOperatorAt ht hm, hm]

end Pointwise

/-! ### Regularity of the mean curvature vector -/

section Regularity

variable [IsManifold J ∞ N] [T2Space N] {k : ℕ∞ω} [ENat.LEInfty k] [IsManifold I (k + 1 + 1) M]
  [IsContMDiffRiemannianBundle I (k + 1) E (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle J k F (fun y : N ↦ TangentSpace J y)]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} [ContMDiffCovariantDerivative cov k]
  {f : M → N} {x : M}

/-- **The mean curvature vector is `C^k`** at a point where `f` is `C^{k+2}` with injective
differential, for a `C^k` covariant derivative, a `C^{k+1}` metric on `M` and a `C^k` metric on
`N`. This includes boundary and corner points of the source. -/
theorem contMDiffAt_immersionMeanCurvatureVector (hf : ContMDiffAt I J (k + 1 + 1) f x)
    (hinj : Function.Injective (mfderiv I J f x)) :
    ContMDiffAt I J.tangent k
      (fun y ↦ TotalSpace.mk' F (f y) (immersionMeanCurvatureVector (I := I) cov f y)) x := by
  have : ContMDiffVectorBundle (k + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  obtain ⟨s, hs, hx, X, hX, ho⟩ := exists_isLocalFrameOn_orthonormal
    (I := I) (n := k + 1) (F := E) (V := TangentSpace I) x
  set c : ℝ := (finrank ℝ E : ℝ)⁻¹
  have hval (i : Fin (finrank ℝ E)) :
      ContMDiffAt I J.tangent k
        (fun y ↦ TotalSpace.mk' F (f y) (immersionSecondFundamentalForm cov f (c • X i) (X i) y))
        x :=
    contMDiffAt_immersionSecondFundamentalForm hf hinj
      ((hX.contMDiffAt hs hx i).of_le le_self_add).const_smul_section (hX.contMDiffAt hs hx i)
  have hsum := ContMDiffAt.sum_sectionAlong Finset.univ _
    (hf.of_le (le_self_add.trans le_self_add)) fun i _ ↦ hval i
  apply hsum.congr_of_eventuallyEq
  have h2 : (2 : ℕ∞ω) ≤ k + 1 + 1 := by
    rw [← one_add_one_eq_two]; gcongr; exact le_add_self
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).1 (hf.of_le h2)
  filter_upwards [hs.mem_nhds hx, hfn] with y hy hyf2
  let b := OrthonormalBasis.mk (ho y hy) (hX.generating hy).ge
  refine congrArg (TotalSpace.mk' F (f y)) ?_
  rw [immersionMeanCurvatureVector_eq_sum b, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hXi := ((hX.contMDiffAt hs hy i).mdifferentiableAt (by simp))
  simp only [b, OrthonormalBasis.coe_mk]
  rw [immersionSecondFundamentalFormAt_apply (cov := cov) hyf2 hXi hXi,
    immersionSecondFundamentalForm_def, immersionSecondFundamentalForm_def, Pi.smul_apply,
    map_smul, map_smul]

/-- **The mean curvature vector of a `C^{k+2}` immersion is a `C^k` field along it**, for a `C^k`
covariant derivative, a `C^{k+1}` metric on `M` and a `C^k` metric on `N`. -/
theorem contMDiff_immersionMeanCurvatureVector (hf : ContMDiff I J (k + 1 + 1) f)
    (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    ContMDiff I J.tangent k
      (fun y ↦ TotalSpace.mk' F (f y) (immersionMeanCurvatureVector (I := I) cov f y)) :=
  fun y ↦ contMDiffAt_immersionMeanCurvatureVector (hf y) (hinj y)

end Regularity

end TauCeti
