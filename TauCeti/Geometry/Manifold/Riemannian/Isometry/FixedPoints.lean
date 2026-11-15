/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Geometry.Manifold.LinearSlice

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
* At a fixed point the invariant vectors of the tangent representation are `V^K`
  (`TauCeti.mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints`), and each `d(k •)_p`
  preserves every ball around the origin of `T_p M`
  (`TauCeti.mfderiv_mem_ball_of_apply_eq_self`).
* A geodesic leaving a fixed point with fixed initial velocity stays in `M^K` for all times
  (`TauCeti.maximalGeodesic_mem_fixedPoints`): the fixed set is totally geodesic.
* On a normal domain `U` at `p` stable under the derivatives, a vector `v` has `exp_p v ∈ M^K`
  exactly when it is fixed by every derivative
  (`TauCeti.Manifold.IsNormalDomain.riemannianExp_mem_fixedPoints_iff`), so
  `exp_p (U ∩ V^K) = M^K ∩ exp_p U`
  (`TauCeti.Manifold.IsNormalDomain.image_riemannianExp_inter_eq_fixedPoints_inter`). Every normal
  ball is such a domain
  (`TauCeti.Manifold.IsNormalDomain.image_riemannianExp_ball_inter_eq_fixedPoints_inter`).
* Hence the Riemannian logarithm on such a domain, a smooth chart of `M` around `p`, carries `M^K`
  onto the linear subspace `V^K` (`TauCeti.Manifold.IsNormalDomain.isSliceChart_fixedPoints`).
  In particular `M^K` has a smooth slice chart around each of its points
  (`TauCeti.exists_isSliceChart_fixedPoints`), with model subspace `V^K` at `p`; its dimension may
  vary from one fixed point to another.

The subspace `V^K` is the fixed tangent subspace `TauCeti.fixedTangentSubspace I K p`. Its
dimension is the dimension of the fixed set at `p`, read in any two slice charts
(`TauCeti.IsSliceChart.finrank_eq`), so it is the same at every fixed point in the source of the
slice chart at `p` (`TauCeti.finrank_fixedTangentSubspace_eq_of_isSliceChart`). Hence:

* the dimension of `V^K` is locally constant on `M^K`
  (`TauCeti.eventually_finrank_fixedTangentSubspace_eq`), and constant on each connected
  component of `M^K` (`TauCeti.connectedComponentIn_fixedPoints_subset_fixedPointsFinrank`);
* for a subspace `L` of the model, the fixed points `TauCeti.fixedPointsFinrank I K M (dim L)` at
  which `V^K` has the dimension of `L` form a smooth manifold modelled on `L`, smoothly embedded
  in `M`, whose tangent space at each point `p` is `V^K`
  (`TauCeti.exists_isSmoothEmbedding_fixedPointsFinrank`). Its atlas consists of the Riemannian
  logarithms at its points followed by linear isomorphisms carrying `V^K` onto `L`.

So `M^K` is a disjoint union of embedded submanifolds, one for each dimension, and each of its
connected components lies in one of them. For a group preserving a nondegenerate two-form as
well, `V^K` is a symplectic subspace
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner`),
so these submanifolds are symplectic
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsFinrank`,
in `TauCeti.Geometry.Symplectic.Manifold.Invariants`).

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

open Bundle Manifold Set MulAction Topology
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

include hK

/-- **The fixed set is totally geodesic.** For a group acting by isometries, the maximal
geodesic leaving a fixed point `p` with initial velocity fixed by the differential of every
group element stays in the fixed set at every time. -/
theorem maximalGeodesic_mem_fixedPoints (hp : p ∈ fixedPoints K M)
    (hv : ∀ k : K, mfderiv I I (k • ·) p v = v) (t : ℝ) :
    maximalGeodesic I M p v t ∈ fixedPoints K M := fun k ↦ by
  have h := (RiemannianIsometry.constSMul k (hK k)).apply_maximalGeodesic_of_mfderiv_eq
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
  have hk := (RiemannianIsometry.constSMul k (hK k)).apply_riemannianExp_eq_self_iff hU
    (by simpa using hp k) hv (by rw [RiemannianIsometry.coe_constSMul]; exact hUK k v hv)
  rw [RiemannianIsometry.coe_constSMul] at hk
  exact hk.1 (h k)

/-- The case of a normal ball in `IsNormalDomain.riemannianExp_mem_fixedPoints_iff`: the
differential at `p` of each group element preserves the ball. -/
theorem riemannianExp_mem_fixedPoints_iff_of_mem_ball {r : ℝ}
    (hU : IsNormalDomain I M p (Metric.ball 0 r)) (hp : p ∈ fixedPoints K M)
    (hv : v ∈ Metric.ball 0 r) :
    riemannianExp I M p v ∈ fixedPoints K M ↔ ∀ k : K, mfderiv I I (k • ·) p v = v :=
  hU.riemannianExp_mem_fixedPoints_iff hK hp
    (fun k _ hw ↦ mfderiv_mem_ball_of_apply_eq_self (hp k) (hK k p) hw) hv

/-- **The fixed set is the exponential image of the fixed tangent vectors.** For a group acting
by isometries fixing `p`, and a normal domain `U` at `p` mapped into itself by the differential at
`p` of every group element, the fixed set meets the normal neighbourhood `exp_p U` in the
exponential image of the vectors of `U` fixed by the differential of every group element. -/
theorem image_riemannianExp_inter_eq_fixedPoints_inter (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hUK : ∀ k : K, ∀ w ∈ U, mfderiv I I (k • ·) p w ∈ U) :
    riemannianExp I M p '' (U ∩ {v | ∀ k : K, mfderiv I I (k • ·) p v = v}) =
      fixedPoints K M ∩ riemannianExp I M p '' U := by
  ext q
  constructor
  · rintro ⟨w, ⟨hw, hwK⟩, rfl⟩
    exact ⟨riemannianExp_mem_fixedPoints hK hp hwK, mem_image_of_mem _ hw⟩
  · rintro ⟨hq, w, hw, rfl⟩
    exact ⟨w, ⟨hw, (hU.riemannianExp_mem_fixedPoints_iff hK hp hUK hw).1 hq⟩, rfl⟩

/-- The case of a normal ball `B` in
`IsNormalDomain.image_riemannianExp_inter_eq_fixedPoints_inter`:
`exp_p (B ∩ V^K) = M^K ∩ exp_p B`. -/
theorem image_riemannianExp_ball_inter_eq_fixedPoints_inter {r : ℝ}
    (hU : IsNormalDomain I M p (Metric.ball 0 r)) (hp : p ∈ fixedPoints K M) :
    riemannianExp I M p '' (Metric.ball 0 r ∩ {v | ∀ k : K, mfderiv I I (k • ·) p v = v}) =
      fixedPoints K M ∩ riemannianExp I M p '' Metric.ball 0 r :=
  hU.image_riemannianExp_inter_eq_fixedPoints_inter hK hp
    fun k _ hw ↦ mfderiv_mem_ball_of_apply_eq_self (hp k) (hK k p) hw

/-- **The Riemannian logarithm is a slice chart for the fixed set.** For a group acting by
isometries fixing `p`, and a normal domain `U` at `p` mapped into itself by the differential at
`p` of every group element, the Riemannian logarithm on `exp_p U` carries the fixed set onto the
linear subspace of tangent vectors fixed by the differential at `p` of every group element. -/
theorem isSliceChart_fixedPoints (hU : IsNormalDomain I M p U) (hp : p ∈ fixedPoints K M)
    (hUK : ∀ k : K, ∀ w ∈ U, mfderiv I I (k • ·) p w ∈ U) :
    IsSliceChart hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph
      {v | ∀ k : K, mfderiv I I (k • ·) p v = v} (fixedPoints K M) := by
  refine isSliceChart_iff.2 fun q hq ↦ ?_
  simp only [PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
    PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
    hU.toPartialDiffeomorph_target] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have hlog : hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph (riemannianExp I M p w) = w :=
    by simpa [PartialDiffeomorph.symm_toPartialEquiv] using hU.riemannianLog_riemannianExp hw
  rw [hlog, mem_ofPred_eq]
  exact hU.riemannianExp_mem_fixedPoints_iff hK hp hUK hw

/-- The case of a normal ball in `IsNormalDomain.isSliceChart_fixedPoints`. -/
theorem isSliceChart_fixedPoints_of_ball {r : ℝ} (hU : IsNormalDomain I M p (Metric.ball 0 r))
    (hp : p ∈ fixedPoints K M) :
    IsSliceChart hU.toPartialDiffeomorph.symm.toOpenPartialHomeomorph
      {v | ∀ k : K, mfderiv I I (k • ·) p v = v} (fixedPoints K M) :=
  hU.isSliceChart_fixedPoints hK hp
    fun k _ hw ↦ mfderiv_mem_ball_of_apply_eq_self (hp k) (hK k p) hw

end Manifold.IsNormalDomain

/-- **A slice chart for the fixed set of a group of isometries.** For a group acting on `M` by
isometries and a fixed point `p`, there is a smooth chart of `M` around `p` with values in
`T_p M`, centred at `p` and with inverse the exponential map at `p`, which carries the fixed set
onto the linear subspace of tangent vectors fixed by the differential at `p` of every group
element. The chart is the Riemannian logarithm on a normal ball
(`TauCeti.Manifold.IsNormalDomain.isSliceChart_fixedPoints_of_ball`). -/
theorem exists_isSliceChart_fixedPoints (hp : p ∈ fixedPoints K M) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, TangentSpace I p) M (TangentSpace I p) ∞,
      p ∈ φ.source ∧ φ p = 0 ∧ ⇑φ.symm = riemannianExp I M p ∧
        IsSliceChart φ.toOpenPartialHomeomorph {v | ∀ k : K, mfderiv I I (k • ·) p v = v}
          (fixedPoints K M) := by
  obtain ⟨r, hr, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  refine ⟨hU.toPartialDiffeomorph.symm, ?_, ?_, ?_, hU.isSliceChart_fixedPoints_of_ball hK hp⟩
  · simp [PartialDiffeomorph.symm_toPartialEquiv, hU.self_mem_image]
  · simpa [PartialDiffeomorph.symm_toPartialEquiv] using
      hU.riemannianLog_riemannianExp (Metric.mem_ball_self hr)
  · simp

/-! ### The fixed set as a submanifold -/

/-- **The dimension of the fixed tangent subspace is constant along a slice chart.** If a smooth
chart around a fixed point `p` flattens the fixed set onto the fixed tangent subspace at `p`, then
every fixed point `z` in its source has a fixed tangent subspace of the same dimension: both are
the tangent space of the fixed set at `z`, read in this chart and in the slice chart at `z`. -/
theorem finrank_fixedTangentSubspace_eq_of_isSliceChart
    {φ : PartialDiffeomorph I 𝓘(ℝ, TangentSpace I p) M (TangentSpace I p) ∞}
    (hφ : IsSliceChart φ.toOpenPartialHomeomorph (fixedTangentSubspace I K p : Set _)
      (fixedPoints K M))
    {z : M} (hz : z ∈ φ.source) (hzK : z ∈ fixedPoints K M) :
    Module.finrank ℝ (fixedTangentSubspace I K z) =
      Module.finrank ℝ (fixedTangentSubspace I K p) := by
  obtain ⟨ψ, hzψ, -, -, hψ⟩ := exists_isSliceChart_fixedPoints hK hzK
  rw [← coe_fixedTangentSubspace hzK] at hψ
  have : FiniteDimensional ℝ (TangentSpace I z) := inferInstanceAs (FiniteDimensional ℝ E)
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  -- Both transition maps are smooth, being composites of smooth charts and inverse charts.
  have hφz : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ φ z :=
    φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hz)
  have hψz : ContMDiffAt I 𝓘(ℝ, TangentSpace I z) ∞ ψ z :=
    ψ.contMDiffOn.contMDiffAt (ψ.open_source.mem_nhds hzψ)
  have hφs : ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞ φ.symm (φ z) :=
    φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds (φ.map_source hz))
  have hψs : ContMDiffAt 𝓘(ℝ, TangentSpace I z) I ∞ ψ.symm (ψ z) :=
    ψ.symm.contMDiffOn.contMDiffAt (ψ.open_target.mem_nhds (ψ.map_source hzψ))
  refine hψ.finrank_eq hφ (Submodule.isClosed_of_finiteDimensional _)
    (Submodule.isClosed_of_finiteDimensional _) hzψ hz hzK ?_ ?_
  · exact (contMDiffAt_iff_contDiffAt.1 (hφz.comp_of_eq hψs (ψ.left_inv hzψ))).differentiableAt
      (by simp)
  · exact (contMDiffAt_iff_contDiffAt.1 (hψz.comp_of_eq hφs (φ.left_inv hz))).differentiableAt
      (by simp)

/-- **The dimension of the fixed tangent subspace is locally constant on the fixed set.** -/
theorem eventually_finrank_fixedTangentSubspace_eq (hp : p ∈ fixedPoints K M) :
    ∀ᶠ z in 𝓝 p, z ∈ fixedPoints K M →
      Module.finrank ℝ (fixedTangentSubspace I K z) =
        Module.finrank ℝ (fixedTangentSubspace I K p) := by
  obtain ⟨φ, hpφ, -, -, hφ⟩ := exists_isSliceChart_fixedPoints hK hp
  rw [← coe_fixedTangentSubspace hp] at hφ
  filter_upwards [φ.open_source.mem_nhds hpφ] with z hz hzK
  exact finrank_fixedTangentSubspace_eq_of_isSliceChart hK hφ hz hzK

/-- **Each connected component of the fixed set has a single dimension.** The connected component
of a fixed point `p` in the fixed set consists of fixed points whose fixed tangent subspaces have
the dimension of the one at `p`. -/
theorem connectedComponentIn_fixedPoints_subset_fixedPointsFinrank (hp : p ∈ fixedPoints K M) :
    connectedComponentIn (fixedPoints K M) p ⊆
      fixedPointsFinrank I K M (Module.finrank ℝ (fixedTangentSubspace I K p)) := by
  set C := connectedComponentIn (fixedPoints K M) p
  have hCK : C ⊆ fixedPoints K M := connectedComponentIn_subset _ _
  have : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hloc : IsLocallyConstant fun z : C ↦
      Module.finrank ℝ (fixedTangentSubspace I K (z : M)) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun z ↦ ?_
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (eventually_finrank_fixedTangentSubspace_eq hK (hCK z.2))] with w hw
    exact hw (hCK w.2)
  intro z hz
  exact mem_fixedPointsFinrank_iff.2 ⟨hCK hz, hloc.apply_eq_of_isPreconnected isPreconnected_univ
    (x := ⟨z, hz⟩) (y := ⟨p, mem_connectedComponentIn hp⟩) (mem_univ _) (mem_univ _)⟩

/-- A smooth chart around a point `y` of the piece of the fixed set where the fixed tangent
subspace has the dimension of a subspace `L` of the model, flattening that piece onto `L × {0}`
in `L × N` for a complement `N` of `L`. It is the Riemannian logarithm at `y` followed by a
linear isomorphism `T_y M ≃ L × N` carrying the fixed tangent subspace at `y` onto `L × {0}`. -/
private theorem exists_isSliceChart_fixedPointsFinrank {L N : Submodule ℝ E} (hLN : IsCompl L N)
    {y : M} (hy : y ∈ fixedPointsFinrank I K M (Module.finrank ℝ L)) :
    ∃ e : OpenPartialHomeomorph M (L × N), y ∈ e.source ∧
      IsSliceChart e ((univ : Set L) ×ˢ ({0} : Set N))
        (fixedPointsFinrank I K M (Module.finrank ℝ L)) ∧
      (∀ z ∈ e.source, ContMDiffAt I 𝓘(ℝ, L × N) ∞ e z) ∧
      (∀ z ∈ e.target, ContMDiffAt 𝓘(ℝ, L × N) I ∞ e.symm z) := by
  obtain ⟨hyK, hyd⟩ := mem_fixedPointsFinrank_iff.1 hy
  obtain ⟨φ, hyφ, -, -, hφ⟩ := exists_isSliceChart_fixedPoints hK hyK
  rw [← coe_fixedTangentSubspace hyK] at hφ
  set V := fixedTangentSubspace I K y
  have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  -- A linear isomorphism `T_y M ≃ L × N` carrying `V` onto `L × {0}`.
  obtain ⟨W, hVW⟩ := V.exists_isCompl
  have hWN : Module.finrank ℝ W = Module.finrank ℝ N := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hVW
    have h2 := Submodule.finrank_add_eq_of_isCompl hLN
    -- The tangent space `T_y M` is the model space `E`.
    have h3 : Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E := rfl
    omega
  let Φ : TangentSpace I y ≃L[ℝ] L × N :=
    (V.prodEquivOfIsTopCompl W (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hVW
      (Submodule.isClosed_of_finiteDimensional V))).symm.trans
      ((ContinuousLinearEquiv.ofFinrankEq hyd).prodCongr (ContinuousLinearEquiv.ofFinrankEq hWN))
  have hΦ (v : TangentSpace I y) : (Φ v).2 = 0 ↔ v ∈ V := by
    simp [Φ, Submodule.coe_symm_prodEquivOfIsTopCompl]
  refine ⟨φ.toOpenPartialHomeomorph.transHomeomorph Φ.toHomeomorph, hyφ,
    isSliceChart_iff.2 fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    simp only [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      Function.comp_apply, mem_prod, mem_univ, mem_singleton_iff, true_and, hΦ,
      ← SetLike.mem_coe, ← hφ.mem_iff hz, mem_fixedPointsFinrank_iff]
    exact ⟨fun h ↦ h.1, fun h ↦
      ⟨h, (finrank_fixedTangentSubspace_eq_of_isSliceChart hK hφ hz h).trans hyd⟩⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    have h : ContMDiffAt I 𝓘(ℝ, TangentSpace I y) ∞ φ.toOpenPartialHomeomorph z := by
      rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
      exact φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hz)
    exact Φ.contDiff.contMDiff.contMDiffAt.comp z h
  · have hzt : Φ.symm z ∈ φ.toOpenPartialHomeomorph.target := by
      simpa only [OpenPartialHomeomorph.transHomeomorph_target, mem_preimage,
        ContinuousLinearEquiv.coe_symm_toHomeomorph] using hz
    have h : ContMDiffAt 𝓘(ℝ, TangentSpace I y) I ∞ φ.toOpenPartialHomeomorph.symm (Φ.symm z) :=
      φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds hzt)
    exact h.comp z Φ.symm.contDiff.contMDiff.contMDiffAt

/-- **The fixed set of a group of isometries is a union of embedded submanifolds.** For a group
acting on a Riemannian manifold by isometries and a subspace `L` of the model, the fixed points
whose fixed tangent subspace has the dimension of `L` form a smooth manifold modelled on `L`,
smoothly embedded in `M`, whose tangent space at each point is the fixed tangent subspace there.
By `TauCeti.connectedComponentIn_fixedPoints_subset_fixedPointsFinrank`, each connected component
of the fixed set lies in one of these pieces, and different components may have different
dimensions. No completeness of the metric and no compactness of `M` or `K` is needed. -/
theorem exists_isSmoothEmbedding_fixedPointsFinrank (L : Submodule ℝ E) :
    ∃ C : ChartedSpace L (fixedPointsFinrank I K M (Module.finrank ℝ L)), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (fixedPointsFinrank I K M (Module.finrank ℝ L)) ∧
      IsSmoothEmbedding 𝓘(ℝ, L) I ∞
        (Subtype.val : fixedPointsFinrank I K M (Module.finrank ℝ L) → M) ∧
      ∀ y : fixedPointsFinrank I K M (Module.finrank ℝ L),
        LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap =
        fixedTangentSubspace I K (y : M) := by
  classical
  set s := fixedPointsFinrank I K M (Module.finrank ℝ L)
  obtain ⟨N, hLN⟩ := L.exists_isCompl
  choose e hcover he hs hi using fun y : s ↦ exists_isSliceChart_fixedPointsFinrank hK hLN y.2
  let := linearSliceChartedSpace e he hcover
  have hman := isManifold_linearSliceChartedSpace e he hs hi hcover
  have himm := isImmersion_subtypeVal_linearSliceChartedSpace e he hs hi hcover (by simp)
  have hval := contMDiff_subtypeVal_linearSliceChartedSpace e he hi hcover
  refine ⟨_, hman, ⟨himm, IsEmbedding.subtypeVal⟩, fun y ↦ ?_⟩
  have hyK : (y : M) ∈ fixedPoints K M := (mem_fixedPointsFinrank_iff.1 y.2).1
  -- The differential of the inclusion is fixed by the differential of every group element,
  -- since each group element fixes every point of `s`.
  have hle : LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap ≤
      fixedTangentSubspace I K (y : M) := by
    rintro _ ⟨u, rfl⟩
    refine (mem_fixedTangentSubspace_iff hyK).2 fun k ↦ ?_
    have hcomp : (fun z : M ↦ k • z) ∘ (Subtype.val : s → M) = Subtype.val :=
      funext fun z ↦ (mem_fixedPointsFinrank_iff.1 z.2).1 k
    have h := mfderiv_comp (I' := I) y
      ((contMDiff_const_smul (I := I) (n := ∞) k).mdifferentiableAt (by simp))
      ((hval y).mdifferentiableAt (by simp))
    rw [hcomp] at h
    exact (congrArg (fun A ↦ A u) h).symm
  have : FiniteDimensional ℝ (TangentSpace I (y : M)) := inferInstanceAs (FiniteDimensional ℝ E)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearMap.finrank_range_of_inj (himm.mfderiv_injective (by simp) y),
    (mem_fixedPointsFinrank_iff.1 y.2).2]
  -- The tangent space of the manifold `s`, modelled on `L`, is `L`.
  rfl

end Action

end TauCeti
