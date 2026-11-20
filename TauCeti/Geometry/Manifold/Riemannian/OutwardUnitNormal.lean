/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Unit
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.NormalBundle
import TauCeti.Geometry.Manifold.Boundary.Derivative
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# The outward unit normal along the boundary

Let `M` be a manifold modelled on the half-space `𝓡∂ (n + 1)` whose tangent spaces carry a
Riemannian metric, and let `ι : ∂M → M` be the inclusion of its boundary manifold. At a boundary
point `q` the differential `dι_q` maps the `n`-dimensional tangent space of `∂M` injectively into
the `(n + 1)`-dimensional `T_q M`, so its orthogonal complement is a line, the normal space
`TauCeti.orthogonalNormalSpace` of `ι` at `q`. That line contains exactly two unit vectors, and
exactly one of them points outward. This is the **outward unit normal**
`TauCeti.outwardUnitNormal q`: the unique vector of `T_q M` that has norm one, points outward
(`TauCeti.IsOutwardPointing`) and is orthogonal to the range of `dι_q`
(`TauCeti.eq_outwardUnitNormal_iff`).

It is the unit gradient of `-x⁰`, for the normal coordinate `x⁰` of the preferred half-space chart
at `q`. The same formula holds with the normal coordinate of every preferred chart whose source
contains `q` (`TauCeti.outwardUnitNormal_eq_normalize_mgradient`): the gradient of such an `x⁰` is
orthogonal to the boundary, since `x⁰` vanishes along it, and has positive normal coordinate.
Because the unit gradient of a function with nonvanishing differential is as regular as the metric
(`TauCeti.Manifold.contMDiffAt_normalize_mgradient`), this local formula makes `q ↦ (q, ν(q))` a
`C^k` map `∂M → TM` for a `C^k` metric on a `C^(k + 1)` manifold
(`TauCeti.contMDiff_outwardUnitNormal`). The pointwise uniqueness glues the chart formulas, so no
partition of unity, Hausdorff or countability hypothesis is needed.

The outward unit normal is the normal field of the divergence theorem on a Riemannian manifold
with boundary, and the reference vector of the hypersurface geometry of `∂M`: inward and outward
directions, boundary defining functions and the second fundamental form are read against it.

## Main declarations

* `TauCeti.outwardUnitNormal`: the outward unit normal at a boundary point.
* `TauCeti.norm_outwardUnitNormal`, `TauCeti.isOutwardPointing_outwardUnitNormal` and
  `TauCeti.inner_outwardUnitNormal_mfderiv_subtypeVal`: its three defining laws.
* `TauCeti.eq_outwardUnitNormal_iff`: the three laws characterize it.
* `TauCeti.outwardUnitNormal_eq_normalize_mgradient`: its formula in any preferred chart.
* `TauCeti.contMDiff_outwardUnitNormal`: it is a `C^k` map `∂M → TM` for a `C^k` metric.
* `TauCeti.exists_halfSpaceOutwardUnitNormal`: a smooth field along the boundary satisfying the
  three laws exists.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 15
  (the outward unit normal along the boundary of a Riemannian manifold with boundary) and
  Theorem 16.32 (the divergence theorem, which uses it).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

/-! ### The normal coordinate of a preferred chart -/

/-- Minus the normal coordinate of a preferred chart, read as a differential of a function on
`M`, is minus the normal component of the tangent coordinate change into that chart. -/
private theorem mvfderiv_neg_chartAt_normal_apply {α q : M}
    (hq : q ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q v =
      -tangentCoordChange (𝓡∂ (n + 1)) q α q v 0 := by
  have hfun : (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) =
      (-EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) ∘
        extChartAt (𝓡∂ (n + 1)) α := by
    ext y
    simp
  have hext := hasMFDerivAt_extChartAt (I := 𝓡∂ (n + 1)) hq
  rw [hfun, ContinuousLinearMap.mvfderiv_comp_apply _ hext.mdifferentiableAt,
    mvfderiv_apply_eq_mfderiv_apply, hext.mfderiv, mfderiv_chartAt_eq_tangentCoordChange hq]
  rfl

/-- At a boundary point, a vector points outward exactly when minus the normal coordinate of a
preferred chart increases along it. -/
private theorem isOutwardPointing_iff_mvfderiv_neg_chartAt_normal_pos {α q : M}
    (hqb : q ∈ (𝓡∂ (n + 1)).boundary M)
    (hq : q ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔
      0 < mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q v := by
  rw [isOutwardPointing_iff_tangentCoordChange hqb (by rwa [extChartAt_source]),
    mvfderiv_neg_chartAt_normal_apply hq, neg_pos]

/-- The normal coordinate of a preferred chart is constant along the boundary, so its differential
kills the tangent vectors of the boundary. -/
private theorem mvfderiv_neg_chartAt_normal_mfderiv_subtypeVal {α : M}
    {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) = 0 := by
  obtain ⟨a, -, h⟩ := tangentCoordChange_normal_pos q.2 (mem_extChartAt_source (q : M))
    (by rwa [extChartAt_source])
  rw [mvfderiv_neg_chartAt_normal_apply hq, mfderiv_subtypeVal_boundary, neg_eq_zero]
  exact (h _).trans (mul_eq_zero_of_right a (euclideanHalfSpaceBoundaryParam_apply_zero w))

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- At a boundary point, minus the normal coordinate of a preferred chart has nonzero gradient. -/
private theorem mgradient_neg_chartAt_normal_ne_zero {α q : M}
    (hqb : q ∈ (𝓡∂ (n + 1)).boundary M)
    (hq : q ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q ≠ 0 := by
  obtain ⟨a, ha, h⟩ := tangentCoordChange_normal_pos hqb (mem_extChartAt_source q)
    (by rwa [extChartAt_source])
  rw [Ne, Manifold.mgradient_eq_zero_iff]
  intro h0
  have h1 : mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q
      (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = 0 :=
    (DFunLike.congr_fun h0 _).trans (zero_apply _)
  have h2 : -(a * (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0) = 0 :=
    (congrArg Neg.neg (h _)).symm.trans ((mvfderiv_neg_chartAt_normal_apply hq _).symm.trans h1)
  exact ha.ne' (by simpa using h2)

/-- The unit gradient of minus the normal coordinate of a preferred chart is a unit vector,
outward pointing and orthogonal to the boundary, at every boundary point of the chart source. -/
private theorem normalize_mgradient_neg_chartAt_normal_spec {α : M}
    {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    let ν := NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q)
    ‖ν‖ = 1 ∧ IsOutwardPointing (q : M) ν ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
        ⟪ν, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0 := by
  have hne := mgradient_neg_chartAt_normal_ne_zero q.2 hq
  refine ⟨NormedSpace.norm_normalize_eq_one_iff.mpr hne, ?_, fun w ↦ ?_⟩
  · rw [isOutwardPointing_iff_mvfderiv_neg_chartAt_normal_pos q.2 hq,
      Manifold.mvfderiv_normalize_mgradient]
    exact norm_pos_iff.mpr hne
  · rw [Manifold.inner_normalize_mgradient, mvfderiv_neg_chartAt_normal_mfderiv_subtypeVal hq,
      mul_zero]

/-! ### The outward unit normal -/

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- Two unit outward vectors orthogonal to the boundary at the same point are equal: the vectors
orthogonal to the boundary form a line, which has only two unit vectors, and they point to
opposite sides. -/
private theorem eq_of_unit_outward_orthogonal {q : (𝓡∂ (n + 1)).boundary M}
    {u v : TangentSpace (𝓡∂ (n + 1)) (q : M)}
    (hu : ‖u‖ = 1 ∧ IsOutwardPointing (q : M) u ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
        ⟪u, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0)
    (hv : ‖v‖ = 1 ∧ IsOutwardPointing (q : M) v ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
        ⟪v, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0) :
    u = v := by
  let K := orthogonalNormalSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q
  have hmem {x : TangentSpace (𝓡∂ (n + 1)) (q : M)}
      (hx : ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
        ⟪x, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0) : x ∈ K :=
    mem_orthogonalNormalSpace_iff.mpr fun w ↦ by rw [real_inner_comm, hx w]
  have hK : Module.finrank ℝ K = 1 := by
    have h := finrank_orthogonalNormalSpace_add_finrank (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (J := 𝓡∂ (n + 1)) (f := (Subtype.val : (𝓡∂ (n + 1)).boundary M → M)) (x := q) (by
        rw [mfderiv_subtypeVal_boundary]
        exact euclideanHalfSpaceBoundaryParam_injective n)
    simp only [finrank_euclideanSpace_fin] at h
    simp only [K]
    omega
  have hu0 : (⟨u, hmem hu.2.2⟩ : K) ≠ 0 := fun h ↦ hu.2.1.ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hu0).mp hK ⟨v, hmem hv.2.2⟩
  have hcv : c • u = v := congrArg Subtype.val hc
  have hc1 : |c| = 1 := by
    simpa [← hcv, norm_smul, hu.1] using hv.1
  rcases abs_eq (zero_le_one' ℝ) |>.mp hc1 with rfl | rfl
  · simpa using hcv
  · rw [neg_one_smul] at hcv
    subst hcv
    exact absurd hv.2.1 fun h ↦ (hu.2.1.add h).ne_zero (add_neg_cancel u)

/-- The **outward unit normal** at a boundary point `q` of a Riemannian manifold modelled on the
half-space: the unit vector of `T_q M` orthogonal to the tangent space of the boundary and pointing
outward. It is defined as the unit gradient of minus the normal coordinate of the preferred chart
at `q`; `TauCeti.eq_outwardUnitNormal_iff` characterizes it by its three laws. -/
def outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) : TangentSpace (𝓡∂ (n + 1)) (q : M) :=
  NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1))
    (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).1 0) q)

/-- The outward unit normal has norm one. -/
@[simp]
theorem norm_outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) : ‖outwardUnitNormal q‖ = 1 :=
  (normalize_mgradient_neg_chartAt_normal_spec (mem_chart_source _ (q : M))).1

/-- The outward unit normal points outward. -/
theorem isOutwardPointing_outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing (q : M) (outwardUnitNormal q) :=
  (normalize_mgradient_neg_chartAt_normal_spec (mem_chart_source _ (q : M))).2.1

/-- The outward unit normal is orthogonal to the tangent vectors of the boundary. -/
@[simp]
theorem inner_outwardUnitNormal_mfderiv_subtypeVal (q : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    ⟪outwardUnitNormal q, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0 :=
  (normalize_mgradient_neg_chartAt_normal_spec (mem_chart_source _ (q : M))).2.2 w

/-- The outward unit normal lies in the normal space of the boundary inclusion. -/
theorem outwardUnitNormal_mem_orthogonalNormalSpace (q : (𝓡∂ (n + 1)).boundary M) :
    outwardUnitNormal q ∈ orthogonalNormalSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q :=
  mem_orthogonalNormalSpace_iff.mpr fun w ↦ by
    rw [real_inner_comm, inner_outwardUnitNormal_mfderiv_subtypeVal]

/-- **The three laws determine the outward unit normal**: a tangent vector at a boundary point is
the outward unit normal exactly when it has norm one, points outward and is orthogonal to the
tangent vectors of the boundary. -/
theorem eq_outwardUnitNormal_iff {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v = outwardUnitNormal q ↔ ‖v‖ = 1 ∧ IsOutwardPointing (q : M) v ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
        ⟪v, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0 := by
  refine ⟨?_, fun hv ↦ eq_of_unit_outward_orthogonal hv
    ⟨norm_outwardUnitNormal q, isOutwardPointing_outwardUnitNormal q,
      inner_outwardUnitNormal_mfderiv_subtypeVal q⟩⟩
  rintro rfl
  exact ⟨norm_outwardUnitNormal q, isOutwardPointing_outwardUnitNormal q,
    inner_outwardUnitNormal_mfderiv_subtypeVal q⟩

/-- **The outward unit normal in a chart**: for every preferred chart whose source contains the
boundary point `q`, the outward unit normal at `q` is the unit gradient of minus the normal
coordinate `x⁰` of that chart. -/
theorem outwardUnitNormal_eq_normalize_mgradient {α : M} {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    outwardUnitNormal q = NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).1 0) q) :=
  (eq_outwardUnitNormal_iff.mpr (normalize_mgradient_neg_chartAt_normal_spec hq)).symm

/-! ### Regularity -/

/-- **The outward unit normal is as regular as the metric**: for a `C^k` metric on a `C^(k + 1)`
manifold, `q ↦ (q, ν(q))` is a `C^k` map from the boundary manifold to the tangent bundle. -/
theorem contMDiff_outwardUnitNormal {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent k
      (fun q : (𝓡∂ (n + 1)).boundary M ↦
        (⟨q, outwardUnitNormal q⟩ : TangentBundle (𝓡∂ (n + 1)) M)) := by
  intro q₀
  -- Near `q₀`, the normal is the unit gradient of minus the normal coordinate of the chart at `q₀`.
  let ψ : M → ℝ := fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q₀ : M) y).1 0
  have hψ : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) (k + 1) ψ q₀ :=
    ((-EuclideanSpace.proj (0 : Fin (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contMDiff.contMDiffAt.comp _
        contMDiffAt_extChartAt).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
          simp [ψ])
  have hloc := (Manifold.contMDiffAt_normalize_mgradient hψ
    (mgradient_neg_chartAt_normal_ne_zero q₀.2 (mem_chart_source _ _))).comp q₀
      ((isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M).contMDiff.contMDiffAt.of_le
        le_self_add)
  refine hloc.congr_of_eventuallyEq ?_
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((chartAt (EuclideanHalfSpace (n + 1)) (q₀ : M)).open_source.mem_nhds
      (mem_chart_source _ _))] with q hq
  simp only [Function.comp_apply, outwardUnitNormal_eq_normalize_mgradient hq, ψ]

/-- **Existence of the outward unit normal**: along the boundary of a smooth Riemannian manifold
modelled on the half-space there is a smooth field of unit vectors that point outward and are
orthogonal to the tangent vectors of the boundary. By `TauCeti.eq_outwardUnitNormal_iff` it is
`TauCeti.outwardUnitNormal`. -/
theorem exists_halfSpaceOutwardUnitNormal [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ∃ N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent ∞
        (fun x : (𝓡∂ (n + 1)).boundary M ↦
          (⟨(x : M), N x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
        ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
          ⟪N x, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w⟫_ℝ = 0 := by
  have : IsManifold (𝓡∂ (n + 1)) (∞ + 1) M := by simpa using ‹IsManifold (𝓡∂ (n + 1)) ∞ M›
  exact ⟨outwardUnitNormal, contMDiff_outwardUnitNormal, fun x ↦
    eq_outwardUnitNormal_iff.mp rfl⟩

end TauCeti
