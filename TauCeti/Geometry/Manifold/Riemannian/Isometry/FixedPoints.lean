/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

/-!
# Fixed points of groups of Riemannian isometries

Let a group `K` act on a Riemannian manifold `M` by smooth maps preserving the metric. No
topology or Lie group structure on `K` is required. This file shows that the common fixed set
`M^K = MulAction.fixedPoints K M` is, near each of its points `p`, the exponential image of the
subspace

`V^K = {v ∈ T_p M | d(k •)_p v = v for every k ∈ K}`

of tangent vectors fixed by the derivatives at `p`. The argument uses only the naturality of the
exponential map under isometries, `k (exp_p v) = exp_p (d(k •)_p v)` at a fixed point `p`
(`TauCeti.RiemannianIsometry.riemannianExp_mfderiv`), and its injectivity on a normal ball. Each
`d(k •)_p` is a linear isometry of `T_p M`, so it maps every ball around the origin into itself,
and two vectors of a normal ball with the same exponential image are equal. No completeness of
the metric and no compactness of `M` or `K` is needed.

* The fixed set is closed, since each group element acts continuously
  (`TauCeti.isClosed_fixedPoints_of_continuousConstSMul`).
* At a point `x`, the tangent representation of the stabilizer of `x` acts on `T_x M` by linear
  isometries (`TauCeti.inner_tangentRepresentation_apply`); at a fixed point its invariant vectors
  are `V^K` (`TauCeti.mem_invariants_tangentRepresentation_iff`).
* A geodesic leaving a fixed point with fixed initial velocity stays in `M^K` for all times
  (`TauCeti.maximalGeodesic_mem_fixedPoints`): the fixed set is totally geodesic.
* On a normal domain at `p` stable under the derivatives, a vector `v` has `exp_p v ∈ M^K`
  exactly when it is fixed by every derivative
  (`TauCeti.Manifold.IsNormalDomain.riemannianExp_mem_fixedPoints_iff`). Every normal ball is such
  a domain, so `exp_p (B ∩ V^K) = M^K ∩ exp_p B` for each normal ball `B`
  (`TauCeti.Manifold.IsNormalDomain.image_riemannianExp_inter_eq`).
* Hence the Riemannian logarithm at `p`, a smooth chart of `M` around `p`, carries `M^K` onto the
  linear subspace `V^K` (`TauCeti.exists_isSliceChart_fixedPoints`). So `M^K` is an embedded
  submanifold near `p`, with tangent space `V^K` at `p`. Its dimension may vary from one fixed
  point to another.

For a group preserving a nondegenerate two-form as well, `V^K` is a symplectic subspace
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner`),
so the fixed set of a group of symplectic isometries is a symplectic submanifold.

The basic identities are stated for a single isometry fixing `p`, in the namespace
`TauCeti.RiemannianIsometry`. A compact group acting smoothly preserves the metric obtained by
averaging any smooth metric (`TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`), so the
results apply to smooth actions of compact Lie groups once that metric is chosen.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (the fixed set of a group of isometries via the
  exponential map).
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
-/

public section

open Bundle Manifold Set MulAction
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Maximal geodesics from equal base points with equal initial vectors agree. Both tangent spaces
are the model space, so the initial vectors are compared there. -/
private theorem maximalGeodesic_congr {q p : M} (h : q = p) {w : TangentSpace I q}
    {v : TangentSpace I p} (hw : (w : E) = v) (t : ℝ) :
    maximalGeodesic I M q w t = maximalGeodesic I M p v t := by
  subst h hw
  rfl

/-- The exponential maps at equal base points agree on equal vectors. -/
private theorem riemannianExp_congr {q p : M} (h : q = p) {w : TangentSpace I q}
    {v : TangentSpace I p} (hw : (w : E) = v) :
    riemannianExp I M q w = riemannianExp I M p v := by
  subst h hw
  rfl

variable [I.Boundaryless] [T2Space M]

namespace RiemannianIsometry

variable {Φ : Isom I M} {p : M} {v : TangentSpace I p}

/-- An isometry fixing a point `p` and a tangent vector `v` at `p` fixes the maximal geodesic
from `p` with initial velocity `v` at every time. -/
theorem apply_maximalGeodesic_of_mfderiv_eq (hp : Φ p = p) (hv : mfderiv I I Φ p v = v)
    (t : ℝ) : Φ (maximalGeodesic I M p v t) = maximalGeodesic I M p v t := by
  rw [← Φ.maximalGeodesic_mfderiv]
  exact maximalGeodesic_congr hp hv t

/-- An isometry fixing a point `p` and a tangent vector `v` at `p` fixes `exp_p v`. -/
theorem apply_riemannianExp_of_mfderiv_eq (hp : Φ p = p) (hv : mfderiv I I Φ p v = v) :
    Φ (riemannianExp I M p v) = riemannianExp I M p v := by
  rw [riemannianExp_def]
  exact Φ.apply_maximalGeodesic_of_mfderiv_eq hp hv 1

/-- **Fixed points in a normal neighbourhood.** Let an isometry fix `p`, and let `v` be a vector
of a normal domain at `p` whose image under the differential at `p` also lies in that domain.
Then the isometry fixes `exp_p v` exactly when its differential fixes `v`. -/
theorem apply_riemannianExp_eq_self_iff {U : Set (TangentSpace I p)}
    (hU : IsNormalDomain I M p U) (hp : Φ p = p) (hv : v ∈ U) (hΦv : mfderiv I I Φ p v ∈ U) :
    Φ (riemannianExp I M p v) = riemannianExp I M p v ↔ mfderiv I I Φ p v = v := by
  refine ⟨fun h ↦ hU.injOn hΦv hv ?_, Φ.apply_riemannianExp_of_mfderiv_eq hp⟩
  rw [← h, ← Φ.riemannianExp_mfderiv]
  exact (riemannianExp_congr hp rfl).symm

end RiemannianIsometry

/-! ### Groups acting by isometries -/

section Action

variable {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M] {p : M}
  {v : TangentSpace I p}
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless]
  [T2Space M] in
include hK in
/-- The differential at a fixed point `p` of a group element acting by an isometry maps every ball
around the origin of `T_p M` into itself. -/
private theorem mfderiv_smul_mem_ball (hp : p ∈ fixedPoints K M) (k : K) {r : ℝ}
    {w : TangentSpace I p} (hw : w ∈ Metric.ball (0 : TangentSpace I p) r) :
    mfderiv I I (k • ·) p w ∈ (Metric.ball 0 r : Set (TangentSpace I p)) := by
  have h := (RiemannianIsometry.constSMul hK k).mfderiv_mem_ball (by simpa using hp k) hw
  rwa [RiemannianIsometry.coe_constSMul] at h

include hK

/-- **The fixed set is totally geodesic.** For a group acting by isometries, the maximal
geodesic leaving a fixed point `p` with initial velocity fixed by the differential of every
group element stays in the fixed set at every time. -/
theorem maximalGeodesic_mem_fixedPoints (hp : p ∈ fixedPoints K M)
    (hv : ∀ k : K, mfderiv I I (k • ·) p v = v) (t : ℝ) :
    maximalGeodesic I M p v t ∈ fixedPoints K M := fun k ↦ by
  have h := (RiemannianIsometry.constSMul hK k).apply_maximalGeodesic_of_mfderiv_eq
    (by simpa using hp k) (by rw [RiemannianIsometry.coe_constSMul]; exact hv k) t
  rwa [RiemannianIsometry.coe_constSMul] at h

/-- For a group acting by isometries, the exponential map at a fixed point `p` sends tangent
vectors fixed by the differential of every group element into the fixed set. -/
theorem riemannianExp_mem_fixedPoints (hp : p ∈ fixedPoints K M)
    (hv : ∀ k : K, mfderiv I I (k • ·) p v = v) :
    riemannianExp I M p v ∈ fixedPoints K M := by
  rw [riemannianExp_def]
  exact maximalGeodesic_mem_fixedPoints hK hp hv 1

namespace Manifold.IsNormalDomain

variable {U : Set (TangentSpace I p)}

/-- **The fixed set in a normal neighbourhood.** Let a group act by isometries fixing `p`, and
let `U` be a normal domain at `p` mapped into itself by the differential at `p` of every group
element, for instance a normal ball. A vector `v ∈ U` has `exp_p v` in the fixed set exactly when
it is fixed by the differential of every group element. -/
theorem riemannianExp_mem_fixedPoints_iff (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hUK : ∀ k : K, ∀ w ∈ U, mfderiv I I (k • ·) p w ∈ U)
    (hv : v ∈ U) :
    riemannianExp I M p v ∈ fixedPoints K M ↔ ∀ k : K, mfderiv I I (k • ·) p v = v := by
  refine ⟨fun h k ↦ ?_, riemannianExp_mem_fixedPoints hK hp⟩
  have hk := (RiemannianIsometry.constSMul hK k).apply_riemannianExp_eq_self_iff hU
    (by simpa using hp k) hv (by rw [RiemannianIsometry.coe_constSMul]; exact hUK k v hv)
  rw [RiemannianIsometry.coe_constSMul] at hk
  exact hk.1 (h k)

/-- **The fixed set is the exponential image of the fixed tangent vectors.** For a group acting
by isometries fixing `p`, and a normal ball `B` at `p`, the fixed set meets the normal
neighbourhood `exp_p B` in the exponential image of the vectors of `B` fixed by the differential
of every group element. -/
theorem image_riemannianExp_inter_eq {r : ℝ} (hU : IsNormalDomain I M p (Metric.ball 0 r))
    (hp : p ∈ fixedPoints K M) :
    riemannianExp I M p '' (Metric.ball 0 r ∩ {v | ∀ k : K, mfderiv I I (k • ·) p v = v}) =
      fixedPoints K M ∩ riemannianExp I M p '' Metric.ball 0 r := by
  ext q
  constructor
  · rintro ⟨w, ⟨hw, hwK⟩, rfl⟩
    exact ⟨riemannianExp_mem_fixedPoints hK hp hwK, mem_image_of_mem _ hw⟩
  · rintro ⟨hq, w, hw, rfl⟩
    exact ⟨w, ⟨hw, (hU.riemannianExp_mem_fixedPoints_iff hK hp
      (fun k _ ↦ mfderiv_smul_mem_ball hK hp k) hw).1 hq⟩, rfl⟩

end Manifold.IsNormalDomain

/-- **The fixed set of a group of isometries is an embedded submanifold.** For a group acting
on `M` by isometries and a fixed point `p`, there is a smooth chart of `M` around `p` with values
in `T_p M`, centred at `p`, which carries the fixed set onto the linear subspace of tangent
vectors fixed by the differential at `p` of every group element. The chart is the Riemannian
logarithm on a normal ball. -/
theorem exists_isSliceChart_fixedPoints (hp : p ∈ fixedPoints K M) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, TangentSpace I p) M (TangentSpace I p) ∞,
      p ∈ φ.source ∧ φ p = 0 ∧
        IsSliceChart φ.toOpenPartialHomeomorph {v | ∀ k : K, mfderiv I I (k • ·) p v = v}
          (fixedPoints K M) := by
  obtain ⟨r, hr, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  refine ⟨hU.toPartialDiffeomorph.symm, ?_, ?_, isSliceChart_iff.2 fun q hq ↦ ?_⟩
  · simp [PartialDiffeomorph.symm_toPartialEquiv, hU.self_mem_image]
  · simpa [PartialDiffeomorph.symm_toPartialEquiv] using
      hU.riemannianLog_riemannianExp (Metric.mem_ball_self hr)
  · simp only [PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
      hU.toPartialDiffeomorph_target] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have hlog : hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph (riemannianExp I M p w) = w :=
      by simpa [PartialDiffeomorph.symm_toPartialEquiv] using hU.riemannianLog_riemannianExp hw
    rw [hlog, mem_ofPred_eq]
    exact hU.riemannianExp_mem_fixedPoints_iff hK hp
      (fun k _ ↦ mfderiv_smul_mem_ball hK hp k) hw

end Action

end TauCeti
