/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.TangentSpace
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Unit
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.NormalBundle
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic

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
(`TauCeti.IsOutwardUnitNormal`, `TauCeti.eq_outwardUnitNormal_iff`). It spans the normal space
(`TauCeti.orthogonalNormalSpace_subtypeVal_boundary_eq_span`).

It is the unit gradient of `-x⁰`, for the normal coordinate `x⁰` of the preferred half-space chart
at `q`: that gradient is orthogonal to the boundary, since `x⁰` vanishes along it, and has
positive normal coordinate. The same formula holds with the normal coordinate of every chart of the
`C¹` maximal atlas whose source contains `q` (`TauCeti.outwardUnitNormal_eq_normalize_mgradient`),
since at `q` the differentials of two such normal coordinates are positive multiples of each other.
Because the unit gradient of a function with nonvanishing differential is as regular as the metric
(`TauCeti.Manifold.contMDiffAt_normalize_mgradient`), this local formula makes `q ↦ (q, ν(q))` a
`C^k` map `∂M → TM` for a `C^k` metric on a `C^(k + 1)` manifold
(`TauCeti.contMDiff_outwardUnitNormal`). The pointwise uniqueness glues the chart formulas, so no
partition of unity, Hausdorff or countability hypothesis is needed. Since diffeomorphisms preserve
outward vectors and the tangent space of the boundary, the differential of an isometry of
Riemannian manifolds with boundary carries outward unit normals to outward unit normals
(`TauCeti.RiemannianIsometry.mfderiv_outwardUnitNormal`).

The outward unit normal is the normal field of the divergence theorem on a Riemannian manifold
with boundary, and the reference vector of the hypersurface geometry of `∂M`: inward and outward
directions, boundary defining functions and the second fundamental form are read against it.

## Main declarations

* `TauCeti.finrank_orthogonalNormalSpace_subtypeVal_boundary`: the normal space of the boundary
  is a line.
* `TauCeti.IsOutwardUnitNormal`: the three laws of an outward unit normal.
* `TauCeti.outwardUnitNormal`: the outward unit normal at a boundary point.
* `TauCeti.norm_outwardUnitNormal`, `TauCeti.isOutwardPointing_outwardUnitNormal` and
  `TauCeti.inner_outwardUnitNormal_mfderiv_subtypeVal`: its three defining laws.
* `TauCeti.eq_outwardUnitNormal_iff`: the three laws characterize it.
* `TauCeti.orthogonalNormalSpace_subtypeVal_boundary_eq_span`: it spans the normal space.
* `TauCeti.outwardUnitNormal_eq_normalize_mgradient`: its formula in any chart of the `C¹` maximal
  atlas.
* `TauCeti.contMDiff_outwardUnitNormal`: it is a `C^k` map `∂M → TM` for a `C^k` metric.
* `TauCeti.exists_halfSpaceOutwardUnitNormal`: a smooth field along the boundary satisfying the
  three laws exists.
* `TauCeti.inner_outwardUnitNormal_of_mem_boundaryTangentSpace`: it is orthogonal to `T_q∂M`.
* `TauCeti.RiemannianIsometry.mfderiv_outwardUnitNormal`: naturality under isometries.

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

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-! ### The normal space of the boundary -/

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- The normal space of the boundary inclusion at a boundary point is a line: `dι_q` embeds the
`n`-dimensional tangent space of the boundary into the `(n + 1)`-dimensional `T_q M`. -/
theorem finrank_orthogonalNormalSpace_subtypeVal_boundary (q : (𝓡∂ (n + 1)).boundary M) :
    Module.finrank ℝ (orthogonalNormalSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q) = 1 := by
  have h := finrank_orthogonalNormalSpace_add_finrank (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓡∂ (n + 1)) (f := (Subtype.val : (𝓡∂ (n + 1)).boundary M → M)) (x := q) (by
      rw [mfderiv_subtypeVal_boundary]
      exact euclideanHalfSpaceBoundaryParam_injective n)
  simp only [finrank_euclideanSpace_fin] at h
  omega

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- A tangent vector `v` at a boundary point `q` is an **outward unit normal** when it has norm
one, points outward and is orthogonal to the tangent vectors of the boundary. These three laws
determine `v`: it is `TauCeti.outwardUnitNormal q` (`TauCeti.eq_outwardUnitNormal_iff`). -/
structure IsOutwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) : Prop where
  /-- An outward unit normal has norm one. -/
  norm_eq_one : ‖v‖ = 1
  /-- An outward unit normal points outward. -/
  isOutwardPointing : IsOutwardPointing (q : M) v
  /-- An outward unit normal is orthogonal to the tangent vectors of the boundary. -/
  inner_mfderiv_subtypeVal_eq_zero : ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
    ⟪v, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- Two outward unit normals at the same boundary point are equal: the vectors orthogonal to the
boundary form a line, which has only two unit vectors, and they point to opposite sides. -/
private theorem eq_of_isOutwardUnitNormal {q : (𝓡∂ (n + 1)).boundary M}
    {u v : TangentSpace (𝓡∂ (n + 1)) (q : M)}
    (hu : IsOutwardUnitNormal q u) (hv : IsOutwardUnitNormal q v) : u = v := by
  let K := orthogonalNormalSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q
  have hmem {x : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hx : IsOutwardUnitNormal q x) : x ∈ K :=
    mem_orthogonalNormalSpace_iff.mpr fun w ↦ by
      rw [real_inner_comm, hx.inner_mfderiv_subtypeVal_eq_zero w]
  have hu0 : (⟨u, hmem hu⟩ : K) ≠ 0 := fun h ↦
    hu.isOutwardPointing.ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hu0).mp
    (finrank_orthogonalNormalSpace_subtypeVal_boundary q) ⟨v, hmem hv⟩
  have hcv : c • u = v := congrArg Subtype.val hc
  have hc1 : |c| = 1 := by
    simpa [← hcv, norm_smul, hu.norm_eq_one] using hv.norm_eq_one
  rcases abs_eq (zero_le_one' ℝ) |>.mp hc1 with rfl | rfl
  · simpa using hcv
  · rw [neg_one_smul] at hcv
    subst hcv
    exact absurd hv.isOutwardPointing fun h ↦
      (hu.isOutwardPointing.add h).ne_zero (add_neg_cancel u)

/-! ### The unit gradient of the normal coordinate of a preferred chart -/

/-- At a boundary point, minus the normal coordinate of a preferred chart has nonzero gradient. -/
private theorem mgradient_neg_chartAt_normal_ne_zero {α q : M}
    (hqb : q ∈ (𝓡∂ (n + 1)).boundary M)
    (hq : q ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q ≠ 0 := by
  obtain ⟨a, ha, h⟩ := tangentCoordChange_normal_pos hqb (mem_extChartAt_source q)
    (by rwa [extChartAt_source])
  rw [Ne, Manifold.mgradient_eq_zero_iff]
  intro h0
  have h1 : mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q
      (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = 0 :=
    (DFunLike.congr_fun h0 _).trans (zero_apply _)
  have h2 : -(a * (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0) = 0 :=
    (congrArg Neg.neg (h _)).symm.trans ((mvfderiv_neg_chartAt_normal_apply hq _).symm.trans h1)
  exact ha.ne' (by simpa using h2)

/-- The unit gradient of minus the normal coordinate of a preferred chart is an outward unit
normal at every boundary point of the chart source. -/
private theorem isOutwardUnitNormal_normalize_mgradient_neg_chartAt_normal {α : M}
    {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    IsOutwardUnitNormal q (NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q)) := by
  have hne := mgradient_neg_chartAt_normal_ne_zero q.property hq
  refine ⟨NormedSpace.norm_normalize_eq_one_iff.mpr hne, ?_, fun w ↦ ?_⟩
  · rw [isOutwardPointing_iff_mvfderiv_neg_chartAt_normal_pos q.property hq,
      Manifold.mvfderiv_normalize_mgradient]
    exact norm_pos_iff.mpr hne
  · rw [Manifold.inner_normalize_mgradient, mvfderiv_neg_chartAt_normal_apply hq,
      tangentCoordChange_mfderiv_subtypeVal_apply_zero (by rwa [extChartAt_source]), neg_zero,
      mul_zero]

/-! ### The outward unit normal -/

/-- The **outward unit normal** at a boundary point `q` of a Riemannian manifold modelled on the
half-space: the unit vector of `T_q M` orthogonal to the tangent space of the boundary and pointing
outward. It is defined as the unit gradient of minus the normal coordinate of the preferred chart
at `q`; `TauCeti.eq_outwardUnitNormal_iff` characterizes it by its three laws. -/
def outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) : TangentSpace (𝓡∂ (n + 1)) (q : M) :=
  NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1))
    (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).val 0) q)

/-- The outward unit normal satisfies the three laws of an outward unit normal. -/
theorem isOutwardUnitNormal_outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardUnitNormal q (outwardUnitNormal q) :=
  isOutwardUnitNormal_normalize_mgradient_neg_chartAt_normal (mem_chart_source _ (q : M))

/-- The outward unit normal has norm one. -/
@[simp]
theorem norm_outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) : ‖outwardUnitNormal q‖ = 1 :=
  (isOutwardUnitNormal_outwardUnitNormal q).norm_eq_one

/-- The outward unit normal points outward. -/
theorem isOutwardPointing_outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing (q : M) (outwardUnitNormal q) :=
  (isOutwardUnitNormal_outwardUnitNormal q).isOutwardPointing

/-- The outward unit normal is orthogonal to the tangent vectors of the boundary. -/
@[simp]
theorem inner_outwardUnitNormal_mfderiv_subtypeVal (q : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    ⟪outwardUnitNormal q, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ = 0 :=
  (isOutwardUnitNormal_outwardUnitNormal q).inner_mfderiv_subtypeVal_eq_zero w

/-- The tangent vectors of the boundary are orthogonal to the outward unit normal. -/
@[simp]
theorem inner_mfderiv_subtypeVal_outwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    ⟪mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w, outwardUnitNormal q⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_outwardUnitNormal_mfderiv_subtypeVal]

/-- The outward unit normal lies in the normal space of the boundary inclusion. -/
theorem outwardUnitNormal_mem_orthogonalNormalSpace (q : (𝓡∂ (n + 1)).boundary M) :
    outwardUnitNormal q ∈ orthogonalNormalSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q :=
  mem_orthogonalNormalSpace_iff.mpr (inner_mfderiv_subtypeVal_outwardUnitNormal q)

/-- The normal space of the boundary inclusion is the line spanned by the outward unit normal. -/
theorem orthogonalNormalSpace_subtypeVal_boundary_eq_span (q : (𝓡∂ (n + 1)).boundary M) :
    orthogonalNormalSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q = ℝ ∙ outwardUnitNormal q :=
  eq_span_singleton_of_mem_of_finrank_eq_one (finrank_orthogonalNormalSpace_subtypeVal_boundary q)
    (outwardUnitNormal_mem_orthogonalNormalSpace q) (isOutwardPointing_outwardUnitNormal q).ne_zero

/-- **The three laws determine the outward unit normal**: a tangent vector at a boundary point is
the outward unit normal exactly when it has norm one, points outward and is orthogonal to the
tangent vectors of the boundary. -/
theorem eq_outwardUnitNormal_iff {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v = outwardUnitNormal q ↔ IsOutwardUnitNormal q v :=
  ⟨fun hv ↦ hv ▸ isOutwardUnitNormal_outwardUnitNormal q,
    fun hv ↦ eq_of_isOutwardUnitNormal hv (isOutwardUnitNormal_outwardUnitNormal q)⟩

/-- **The outward unit normal in a chart**: for every chart of the `C¹` maximal atlas whose source
contains the boundary point `q`, the outward unit normal at `q` is the unit gradient of minus the
normal coordinate `x⁰` of that chart. -/
theorem outwardUnitNormal_eq_normalize_mgradient
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ e.source) :
    outwardUnitNormal q = NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(e y).val 0) q) := by
  -- The differential of the normal coordinate of `e` is a positive multiple of that of the
  -- preferred chart at `q`, and so are the gradients of minus these coordinates.
  obtain ⟨a, ha, h⟩ := exists_pos_mvfderiv_normal_eq_smul he
    (IsManifold.chart_mem_maximalAtlas (q : M)) q.property hq (mem_chart_source _ _)
  have hneg (g : M → ℝ) : Manifold.mgradient (𝓡∂ (n + 1)) (fun y ↦ -g y) q =
      -Manifold.mgradient (𝓡∂ (n + 1)) g q :=
    Manifold.mgradient_neg
  rw [hneg, Manifold.mgradient_def, h, map_smul, ← smul_neg, ← Manifold.mgradient_def, ← hneg,
    NormedSpace.normalize_smul_of_pos ha, outwardUnitNormal]

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
  let ψ : M → ℝ := fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q₀ : M) y).val 0
  have hψ : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) (k + 1) ψ q₀ :=
    contMDiffAt_neg_chartAt_normal (mem_chart_source _ _)
  have hloc := (Manifold.contMDiffAt_normalize_mgradient hψ
    (mgradient_neg_chartAt_normal_ne_zero q₀.property (mem_chart_source _ _))).comp q₀
      ((isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M).contMDiff.contMDiffAt.of_le
        le_self_add)
  refine hloc.congr_of_eventuallyEq ?_
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
    ((chartAt (EuclideanHalfSpace (n + 1)) (q₀ : M)).open_source.mem_nhds
      (mem_chart_source _ _))] with q hq
  simp only [Function.comp_apply,
    outwardUnitNormal_eq_normalize_mgradient (IsManifold.chart_mem_maximalAtlas _) hq, ψ]

/-- **Existence of the outward unit normal**: along the boundary of a smooth Riemannian manifold
modelled on the half-space there is a smooth field of unit vectors that point outward and are
orthogonal to the tangent vectors of the boundary. By `TauCeti.eq_outwardUnitNormal_iff` it is
`TauCeti.outwardUnitNormal`. The three laws are spelled out, rather than bundled as
`TauCeti.IsOutwardUnitNormal`, to keep the roadmap statement self-contained. -/
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
    ⟨norm_outwardUnitNormal x, isOutwardPointing_outwardUnitNormal x,
      inner_outwardUnitNormal_mfderiv_subtypeVal x⟩⟩

/-- The outward unit normal is orthogonal to the tangent space of the boundary. -/
theorem inner_outwardUnitNormal_of_mem_boundaryTangentSpace {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hv : v ∈ boundaryTangentSpace q) :
    ⟪outwardUnitNormal q, v⟫_ℝ = 0 := by
  rw [boundaryTangentSpace_def, LinearMap.mem_range] at hv
  obtain ⟨w, rfl⟩ := hv
  exact inner_outwardUnitNormal_mfderiv_subtypeVal q w

/-! ### Naturality -/

section Naturality

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 1 M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **Naturality of the outward unit normal.** The differential of an isometry of Riemannian
manifolds with boundary carries the outward unit normal at `q` to the outward unit normal at
`Φ q`. -/
theorem RiemannianIsometry.mfderiv_outwardUnitNormal
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M) :
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q (outwardUnitNormal q) =
      outwardUnitNormal (⟨Φ q, Φ.apply_mem_boundary q.property⟩ :
        (𝓡∂ (n + 1)).boundary M') := by
  refine eq_outwardUnitNormal_iff.mpr
    ⟨by rw [Φ.norm_mfderiv, norm_outwardUnitNormal], ?_, fun w ↦ ?_⟩
  · exact (isOutwardPointing_mfderiv_iff (by simp) Φ.toDiffeomorph _).mpr
      (isOutwardPointing_outwardUnitNormal q)
  · have hw := mfderiv_subtypeVal_mem_boundaryTangentSpace
      (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M') w
    obtain ⟨u, hu, hu'⟩ := (map_mfderiv_boundaryTangentSpace (by simp) Φ.toDiffeomorph q).ge hw
    rw [← hu']
    simp only [ContinuousLinearMap.coe_coe, RiemannianIsometry.coe_toDiffeomorph]
    rw [Φ.inner_mfderiv, inner_outwardUnitNormal_of_mem_boundaryTangentSpace hu]

end Naturality

end TauCeti
