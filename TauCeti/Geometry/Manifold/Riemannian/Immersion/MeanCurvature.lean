/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm.Norm
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Principal curvatures and the mean curvature vector of an immersion

Let `f : M → N` be a map into a manifold with a Riemannian metric and a covariant derivative `∇`
on `TN`, and let `M` carry a Riemannian metric (for an immersion, the pullback metric). At a point
`x`, the pointwise second fundamental form `B_x : T_xM × T_xM → T_{f x}N`
(`TauCeti.immersionSecondFundamentalFormAt`) defines:

* for a normal vector `ν` at `f x`, the **Weingarten map** `S_ν : T_xM → T_xM`, the endomorphism
  with `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫` (`TauCeti.immersionWeingartenAt`). For a torsion-free `∇` it
  is self-adjoint, and its eigenvalues, with multiplicity and in decreasing order, are the
  **principal curvatures** of `f` at `x` in the direction `ν`
  (`TauCeti.immersionPrincipalCurvatures`). Reversing `ν` negates `S_ν`, so it negates the
  principal values.
* the **mean curvature vector** `H = (tr B_x) / m`, `m = dim M`, the metric trace of `B_x`
  divided by `m` (`TauCeti.immersionMeanCurvatureVector`). It is independent of frames:
  `H = (1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` for every orthonormal basis `(eᵢ)` of `T_xM`. It is normal, and
  `⟪H, ν⟫ = (tr S_ν) / m` is the average of the principal curvatures in the direction `ν`.
  `f` is minimal at `x` when `H = 0`; this holds where `B_x = 0`, at totally geodesic points.

These are the definitions of RiemannianGeometry R5a.2.

## Main definitions

* `TauCeti.immersionWeingartenAt`: the pointwise Weingarten map `S_ν`.
* `TauCeti.immersionPrincipalCurvatures`: the principal curvatures in the direction `ν`.
* `TauCeti.immersionMeanCurvatureVector`: the mean curvature vector `H`.

## Main results

* `TauCeti.inner_immersionWeingartenAt`: `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫`.
* `TauCeti.isSymmetric_immersionWeingartenAt`: `S_ν` is self-adjoint for a torsion-free `∇`.
* `TauCeti.immersionWeingartenAt_neg`, `TauCeti.hasEigenvalue_immersionWeingartenAt_neg_iff`:
  reversing `ν` negates `S_ν` and its eigenvalues.
* `TauCeti.immersionMeanCurvatureVector_eq_sum`: `H = (1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` in any orthonormal
  basis.
* `TauCeti.immersionMeanCurvatureVector_mem`: `H` is normal.
* `TauCeti.inner_immersionMeanCurvatureVector`,
  `TauCeti.inner_immersionMeanCurvatureVector_eq_sum_div`: `⟪H, ν⟫ = (tr S_ν) / m`, the average of
  the principal curvatures.
* `TauCeti.immersionMeanCurvatureVector_eq_zero_of_eq_zero`: totally geodesic points are minimal.
-/

public section

noncomputable section

open Bundle Manifold Module
open scoped InnerProductSpace Manifold

namespace TauCeti

open TauCeti.Manifold

variable
  {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J 2 N]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} {f : M → N} {x : M}

/-! ### The Weingarten map and the principal curvatures -/

variable (cov f x) in
/-- The **Weingarten map** `S_ν : T_xM → T_xM` of `f` at `x` in the direction of a vector `ν` at
`f x`: the endomorphism with `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫` for the pointwise second fundamental
form `B_x` (`TauCeti.inner_immersionWeingartenAt`). -/
def immersionWeingartenAt (ν : TangentSpace J (f x)) : Module.End ℝ (TangentSpace I x) :=
  LinearMap.BilinForm.symmCompOfNondegenerate
    ((immersionSecondFundamentalFormAt (I := I) cov f x).toLinearMap₁₂.compr₂
      ((innerₗ (TangentSpace J (f x))).flip ν))
    (innerₗ (TangentSpace I x)) nondegenerate_inner

/-- **The defining property of the Weingarten map**: `⟪S_ν v, w⟫ = ⟪B_x(v, w), ν⟫`. -/
theorem inner_immersionWeingartenAt (ν : TangentSpace J (f x)) (v w : TangentSpace I x) :
    ⟪immersionWeingartenAt cov f x ν v, w⟫_ℝ =
      ⟪immersionSecondFundamentalFormAt cov f x v w, ν⟫_ℝ := by
  have := LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
    ((immersionSecondFundamentalFormAt (I := I) cov f x).toLinearMap₁₂.compr₂
      ((innerₗ (TangentSpace J (f x))).flip ν))
    (nondegenerate_inner (E := TangentSpace I x)) w v
  exact this

/-- The Weingarten map is the unique endomorphism `S` with `⟪S v, w⟫ = ⟪B_x(v, w), ν⟫`. -/
theorem eq_immersionWeingartenAt_iff (ν : TangentSpace J (f x))
    (S : Module.End ℝ (TangentSpace I x)) :
    S = immersionWeingartenAt (I := I) cov f x ν ↔
      ∀ v w, ⟪S v, w⟫_ℝ = ⟪immersionSecondFundamentalFormAt cov f x v w, ν⟫_ℝ := by
  refine ⟨fun h ↦ h ▸ inner_immersionWeingartenAt ν, fun h ↦ ?_⟩
  ext v
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [h, inner_immersionWeingartenAt]

/-- The Weingarten map is linear in the normal direction; in particular reversing `ν` negates
it: `S_{-ν} = -S_ν`. -/
theorem immersionWeingartenAt_neg (ν : TangentSpace J (f x)) :
    immersionWeingartenAt (I := I) cov f x (-ν) = -immersionWeingartenAt cov f x ν := by
  refine ((eq_immersionWeingartenAt_iff _ _).mpr fun v w ↦ ?_).symm
  rw [LinearMap.neg_apply, inner_neg_left, inner_immersionWeingartenAt, inner_neg_right]

/-- **The Weingarten map is self-adjoint** for a torsion-free covariant derivative, since the
second fundamental form is then symmetric. -/
theorem isSymmetric_immersionWeingartenAt (ht : cov.IsTorsionFree) (ν : TangentSpace J (f x)) :
    (immersionWeingartenAt (I := I) cov f x ν).IsSymmetric := by
  intro v w
  rw [inner_immersionWeingartenAt, real_inner_comm (immersionWeingartenAt cov f x ν w) v,
    inner_immersionWeingartenAt, immersionSecondFundamentalFormAt_comm ht]

/-- Reversing the normal direction negates the eigenvalues of the Weingarten map: `μ` is an
eigenvalue of `S_{-ν}` exactly when `-μ` is an eigenvalue of `S_ν`. -/
theorem hasEigenvalue_immersionWeingartenAt_neg_iff (ν : TangentSpace J (f x)) (μ : ℝ) :
    Module.End.HasEigenvalue (immersionWeingartenAt (I := I) cov f x (-ν)) μ ↔
      Module.End.HasEigenvalue (immersionWeingartenAt (I := I) cov f x ν) (-μ) := by
  have heig : (immersionWeingartenAt (I := I) cov f x (-ν)).eigenspace μ =
      (immersionWeingartenAt (I := I) cov f x ν).eigenspace (-μ) := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, immersionWeingartenAt_neg, LinearMap.neg_apply,
      neg_smul, neg_eq_iff_eq_neg]
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff, heig]

variable (I f x) in
/-- The **principal curvatures** `κ₁ ≥ ⋯ ≥ κₘ` of `f` at `x` in the direction `ν`, for a
torsion-free covariant derivative and `m = dim M`: the eigenvalues of the self-adjoint Weingarten
map `S_ν`, with multiplicity and in decreasing order. -/
def immersionPrincipalCurvatures (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m)
    (ν : TangentSpace J (f x)) : Fin m → ℝ :=
  (isSymmetric_immersionWeingartenAt (I := I) (x := x) ht ν).eigenvalues
    (hm : finrank ℝ (TangentSpace I x) = m)

/-- The principal curvatures are listed in decreasing order. -/
theorem immersionPrincipalCurvatures_antitone (ht : cov.IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ E = m) (ν : TangentSpace J (f x)) :
    Antitone (immersionPrincipalCurvatures I f x ht hm ν) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

/-- The trace of the Weingarten map is the sum of the principal curvatures. -/
theorem trace_immersionWeingartenAt (ht : cov.IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m)
    (ν : TangentSpace J (f x)) :
    LinearMap.trace ℝ _ (immersionWeingartenAt (I := I) cov f x ν) =
      ∑ i, immersionPrincipalCurvatures I f x ht hm ν i :=
  (isSymmetric_immersionWeingartenAt ht ν).trace_eq_sum_eigenvalues _

/-! ### The mean curvature vector -/

variable (cov f x) in
/-- The **mean curvature vector** `H = (tr B_x) / m` of `f` at `x`, `m = dim M`: the metric trace
of the pointwise second fundamental form divided by the dimension of `M`. In an orthonormal basis
it is `(1 / m) ∑ᵢ B_x(eᵢ, eᵢ)` (`TauCeti.immersionMeanCurvatureVector_eq_sum`). For `m = 0` it is
`0`. -/
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
  rfl

/-- The mean curvature vector is normal. -/
theorem immersionMeanCurvatureVector_mem :
    immersionMeanCurvatureVector (I := I) cov f x ∈ orthogonalNormalSpace I J f x := by
  rw [immersionMeanCurvatureVector_eq_sum (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun i _ ↦ immersionSecondFundamentalFormAt_mem _ _)

/-- **Totally geodesic points are minimal**: where the second fundamental form vanishes, so does
the mean curvature vector. -/
theorem immersionMeanCurvatureVector_eq_zero_of_eq_zero
    (hB : immersionSecondFundamentalFormAt (I := I) cov f x = 0) :
    immersionMeanCurvatureVector (I := I) cov f x = 0 := by
  simp [immersionMeanCurvatureVector, hB]

/-- The normal component of the mean curvature vector in the direction `ν` is the trace of the
Weingarten map divided by the dimension: `⟪H, ν⟫ = (tr S_ν) / m`. -/
theorem inner_immersionMeanCurvatureVector (ν : TangentSpace J (f x)) :
    ⟪immersionMeanCurvatureVector (I := I) cov f x, ν⟫_ℝ =
      LinearMap.trace ℝ _ (immersionWeingartenAt (I := I) cov f x ν) / finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [immersionMeanCurvatureVector_eq_sum b, LinearMap.trace_eq_sum_inner _ b, inner_smul_left,
    sum_inner, div_eq_inv_mul]
  simp only [RCLike.conj_to_real]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm (immersionWeingartenAt cov f x ν (b i)) (b i), inner_immersionWeingartenAt]

/-- For a torsion-free covariant derivative, `⟪H, ν⟫` is the average of the principal curvatures
in the direction `ν`: `⟪H, ν⟫ = (∑ᵢ κᵢ) / m`. For a hypersurface and a unit normal `ν` this is
the scalar mean curvature. -/
theorem inner_immersionMeanCurvatureVector_eq_sum_div (ht : cov.IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ E = m) (ν : TangentSpace J (f x)) :
    ⟪immersionMeanCurvatureVector (I := I) cov f x, ν⟫_ℝ =
      (∑ i, immersionPrincipalCurvatures I f x ht hm ν i) / m := by
  rw [inner_immersionMeanCurvatureVector, trace_immersionWeingartenAt ht hm, hm]

end TauCeti
