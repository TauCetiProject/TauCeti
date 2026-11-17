/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Boundary.SmoothMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tangent, inward and outward directions at the boundary

Let `M` be a `C¹` manifold with boundary modelled on the Euclidean half-space `𝓡∂ (n + 1)`, and
let `q ∈ ∂M`. The tangent space of the boundary at `q`, `boundaryTangentSpace q`, is the subspace
`T_q∂M` of `T_qM` given by the range of the differential of the inclusion `ι : ∂M → M`, for Tau
Ceti's boundary manifold structure (`TauCeti.boundaryChartedSpace`).

Mathlib's half-space constrains the coordinate `x⁰`. In the preferred chart at `q`, `dι_q` is the
zero-insertion map, so `T_q∂M` is the coordinate hyperplane `{v⁰ = 0}`. More intrinsically,
`T_q∂M` is the kernel of the differential at `q` of the normal coordinate `x⁰` of every chart of the
maximal atlas around `q`. Each tangent vector at `q` is then exactly one of: outward
(`TauCeti.IsOutwardPointing`, `v⁰ < 0`), tangent (`v ∈ T_q∂M`), or inward (`-v` outward,
`v⁰ > 0`), and none of these classes depends on the chart. The inward and the outward vectors form
disjoint open half-spaces of `T_qM` with common frontier `T_q∂M`.

The velocity at `0` of a curve `c` on `[0, ∞)`, taken within `[0, ∞)`, is never outward, and the
velocity at `0` of a curve `c` on `ℝ` with `c 0 ∈ ∂M` is tangent to the boundary. A diffeomorphism
of class `C^k`, `k ≠ 0`, carries `T_q∂M` onto the tangent space of the boundary at the image
point.

## Main declarations

* `TauCeti.boundaryTangentSpace`: the tangent space `T_q∂M ⊆ T_qM` of the boundary.
* `TauCeti.boundaryTangentSpace_eq_euclideanHalfSpaceBoundary`: in the preferred chart it is the
  coordinate hyperplane; `TauCeti.finrank_boundaryTangentSpace`: it has dimension `n`.
* `TauCeti.boundaryTangentSpace_eq_ker_of_mem_maximalAtlas`: it is the kernel of the differential
  of the normal coordinate of any chart of the maximal atlas.
* `TauCeti.isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg`, with
  `TauCeti.IsOutwardPointing.notMem_boundaryTangentSpace` and
  `TauCeti.IsOutwardPointing.not_isOutwardPointing_neg`: the trichotomy.
* `TauCeti.frontier_setOf_isOutwardPointing`, `TauCeti.frontier_setOf_isOutwardPointing_neg`:
  the outward and inward half-spaces are open with frontier `T_q∂M`.
* `TauCeti.not_isOutwardPointing_mfderivWithin_Ici`,
  `TauCeti.mfderiv_apply_one_mem_boundaryTangentSpace`: velocities of curves.
* `TauCeti.map_mfderiv_boundaryTangentSpace`: naturality under diffeomorphisms.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Chapter 3 (inward, outward and tangent unit
  vectors at the boundary).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 5 (inward- and outward-pointing vectors).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-! ### Outward and inward vectors in the preferred chart -/

/-- At a boundary point, a vector is outward exactly when its normal coordinate in the preferred
chart is negative. -/
private theorem isOutwardPointing_iff_proj {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    {v : TangentSpace (𝓡∂ (n + 1)) x} :
    IsOutwardPointing x v ↔ EuclideanSpace.proj (0 : Fin (n + 1)) v < 0 := by
  rw [isOutwardPointing_iff, and_iff_right hx, (hasMFDerivAt_extChartAt_self x).mfderiv]
  rfl

/-- At a boundary point, a vector is inward exactly when its normal coordinate in the preferred
chart is positive. -/
private theorem isOutwardPointing_neg_iff_proj {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    {v : TangentSpace (𝓡∂ (n + 1)) x} :
    IsOutwardPointing x (-v) ↔ 0 < EuclideanSpace.proj (0 : Fin (n + 1)) v := by
  rw [isOutwardPointing_iff_proj hx,
    show EuclideanSpace.proj (0 : Fin (n + 1)) (-v) = -EuclideanSpace.proj (0 : Fin (n + 1)) v from
      map_neg _ _, neg_lt_zero]

/-- An outward vector is not inward: its negative is not outward. -/
theorem IsOutwardPointing.not_isOutwardPointing_neg {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) : ¬IsOutwardPointing x (-v) := by
  have hx := hv.mem_boundary
  rw [isOutwardPointing_iff_proj hx] at hv
  rw [isOutwardPointing_neg_iff_proj hx]
  exact hv.asymm

/-- The outward vectors at a point form an open set (empty away from the boundary). -/
theorem isOpen_setOf_isOutwardPointing (x : M) :
    IsOpen {v : TangentSpace (𝓡∂ (n + 1)) x | IsOutwardPointing x v} := by
  by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
  · simp_rw [isOutwardPointing_iff_proj hx]
    exact isOpen_lt (EuclideanSpace.proj (0 : Fin (n + 1))).continuous continuous_const
  · have h : {v : TangentSpace (𝓡∂ (n + 1)) x | IsOutwardPointing x v} = ∅ :=
      eq_empty_of_forall_notMem fun _ hv ↦ hx (IsOutwardPointing.mem_boundary hv)
    rw [h]
    exact isOpen_empty

/-- The inward vectors at a point form an open set (empty away from the boundary). -/
theorem isOpen_setOf_isOutwardPointing_neg (x : M) :
    IsOpen {v : TangentSpace (𝓡∂ (n + 1)) x | IsOutwardPointing x (-v)} :=
  (isOpen_setOf_isOutwardPointing x).preimage continuous_neg

/-- The preferred chart at a boundary point `x` reads every point with nonnegative normal
coordinate, and reads `x` itself with normal coordinate zero. -/
private theorem isMinOn_extChartAt_apply_zero {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (s : Set M) : IsMinOn (fun y ↦ extChartAt (𝓡∂ (n + 1)) x y 0) s x := by
  have h0 : 0 = extChartAt (𝓡∂ (n + 1)) x x 0 := by
    have h := (𝓡∂ (n + 1)).isBoundaryPoint_iff.mp hx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h
    exact h
  intro y _
  simp only [mem_ofPred_eq, ← h0]
  simp only [extChartAt_coe, Function.comp_apply, modelWithCornersEuclideanHalfSpace_toFun]
  exact (chartAt (EuclideanHalfSpace (n + 1)) x y).2

/-- The normal coordinate, in the preferred chart at `c 0`, of the velocity of a curve `c` within
`s` at `0` is the derivative of the normal coordinate of `c`. -/
private theorem hasFDerivWithinAt_extChartAt_comp_apply_zero {c : ℝ → M} {s : Set ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ (n + 1)) c s 0) :
    HasFDerivWithinAt (fun t ↦ extChartAt (𝓡∂ (n + 1)) (c 0) (c t) 0)
      ((EuclideanSpace.proj (0 : Fin (n + 1))).comp
        (mfderivWithin 𝓘(ℝ) (𝓡∂ (n + 1)) c s 0)) s 0 := by
  have hd := (hasMFDerivAt_extChartAt_self (I := 𝓡∂ (n + 1)) (c 0)).comp_hasMFDerivWithinAt
    (0 : ℝ) hc.hasMFDerivWithinAt
  rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hd
  exact (EuclideanSpace.proj (0 : Fin (n + 1))).hasFDerivAt.comp_hasFDerivWithinAt (0 : ℝ) hd

/-- The velocity at `0` of a curve `c` on `[0, ∞)`, taken within `[0, ∞)`, is not outward. When
`c 0 ∈ ∂M` it is therefore tangent to the boundary or inward. (Without differentiability the
velocity is `0` by convention, which is not outward either.) -/
theorem not_isOutwardPointing_mfderivWithin_Ici (c : ℝ → M) :
    ¬IsOutwardPointing (c 0) (mfderivWithin 𝓘(ℝ) (𝓡∂ (n + 1)) c (Ici 0) 0 (1 : ℝ)) := by
  intro hv
  by_cases hc : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ (n + 1)) c (Ici 0) 0
  swap
  · rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hc] at hv
    exact hv.ne_zero rfl
  have hmin : IsLocalMinOn (fun t ↦ extChartAt (𝓡∂ (n + 1)) (c 0) (c t) 0) (Ici 0) 0 :=
    ((isMinOn_extChartAt_apply_zero hv.mem_boundary univ).comp_of_mapsTo
      (mapsTo_univ c (Ici 0)) rfl).isLocalMinOn
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 :=
    mem_posTangentConeAt_of_segment_subset ((convex_Ici 0).segment_subset self_mem_Ici
      (by norm_num))
  have h := hmin.hasFDerivWithinAt_nonneg (hasFDerivWithinAt_extChartAt_comp_apply_zero hc) hcone
  rw [isOutwardPointing_iff_proj hv.mem_boundary] at hv
  exact (not_lt.mpr h) hv

/-! ### The tangent space of the boundary -/

variable [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- The tangent space `T_q∂M` of the boundary at `q ∈ ∂M`, as a subspace of `T_qM`: the range of
the differential of the inclusion `∂M → M`, for Tau Ceti's manifold structure on the boundary. It
is the hyperplane of vectors with vanishing normal coordinate
(`TauCeti.boundaryTangentSpace_eq_ker_of_mem_maximalAtlas`). -/
def boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M) :
    Submodule ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) :=
  LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap

/-- The defining formula of `boundaryTangentSpace`. -/
theorem boundaryTangentSpace_def (q : (𝓡∂ (n + 1)).boundary M) :
    boundaryTangentSpace q = LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap :=
  (rfl)

/-- In the preferred chart, the tangent space of the boundary is the coordinate hyperplane
`{v⁰ = 0}`: the differential of the inclusion is the zero-insertion map. -/
theorem boundaryTangentSpace_eq_euclideanHalfSpaceBoundary (q : (𝓡∂ (n + 1)).boundary M) :
    boundaryTangentSpace q = euclideanHalfSpaceBoundary n := by
  rw [boundaryTangentSpace_def, mfderiv_subtypeVal_boundary]
  ext v
  rw [LinearMap.mem_range]
  exact Set.ext_iff.mp (range_euclideanHalfSpaceBoundaryParam n) v

/-- The tangent space of the boundary has dimension `n`, one less than that of `M`. -/
theorem finrank_boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M) :
    Module.finrank ℝ (boundaryTangentSpace q) = n := by
  rw [boundaryTangentSpace_def,
    LinearMap.finrank_range_of_inj
      ((isImmersion_subtypeVal_boundary (n := n) M one_ne_zero).mfderiv_injective one_ne_zero q)]
  exact finrank_euclideanSpace_fin

/-- The tangent space of the boundary at `q` is the kernel of the differential at `q` of the normal
coordinate `x⁰` of any chart of the maximal atlas around `q`. In particular it is a hyperplane of
`T_qM`. -/
theorem boundaryTangentSpace_eq_ker_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ e.source) :
    boundaryTangentSpace q = LinearMap.ker
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0) (q : M)).toLinearMap := by
  let π : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hext := e.mdifferentiableAt_extend he hq
  have hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0) q :=
    π.mdifferentiableAt.comp (q : M) hext
  have hφ : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0) q =
      π.comp (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (e.extend (𝓡∂ (n + 1))) q) := by
    rw [← π.mfderiv_eq (x := e.extend (𝓡∂ (n + 1)) q)]
    exact mfderiv_comp (q : M) π.mdifferentiableAt hext
  -- The normal coordinate has nonzero differential, since the chart has invertible differential.
  have hne : (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0)
      (q : M)).toLinearMap ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := (isInvertible_mfderiv_extend he hq).surjective
      (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))
    have h1 := LinearMap.congr_fun h0 u
    rw [ContinuousLinearMap.coe_coe, hφ, LinearMap.zero_apply] at h1
    change π (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (e.extend (𝓡∂ (n + 1))) q u) = 0 at h1
    rw [hu] at h1
    simp [π] at h1
  -- The normal coordinate vanishes on the boundary near `q`, so its differential kills `T_q∂M`.
  have hle : boundaryTangentSpace q ≤ LinearMap.ker
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0) (q : M)).toLinearMap := by
    rintro _ ⟨w, rfl⟩
    have hι : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q :=
      ((isSmoothEmbedding_subtypeVal_boundary (n := n) M one_ne_zero).contMDiff.mdifferentiable
        one_ne_zero) q
    have hzero : (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0) ∘
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) =ᶠ[𝓝 q] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(e.open_source.preimage continuous_subtype_val).mem_nhds hq] with y hy
      exact (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_maximalAtlas
        one_ne_zero he hy).mp y.2
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      ← mfderiv_comp_apply _ hf hι, hzero.mfderiv_eq, mfderiv_const,
      ContinuousLinearMap.comp_zero]
    rfl
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have : FiniteDimensional ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (n + 1))))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) = n + 1 :=
    finrank_euclideanSpace_fin
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [finrank_boundaryTangentSpace]
  exact (Nat.add_right_cancel (hker.trans hdim)).symm

/-- A vector at a boundary point is tangent to the boundary exactly when its normal coordinate in
the preferred chart vanishes. -/
private theorem mem_boundaryTangentSpace_iff_proj {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v ∈ boundaryTangentSpace q ↔ EuclideanSpace.proj (0 : Fin (n + 1)) v = 0 := by
  rw [boundaryTangentSpace_eq_euclideanHalfSpaceBoundary]
  exact mem_euclideanHalfSpaceBoundary

/-- Whether a tangent vector at a boundary point is tangent to the boundary can be tested in any
preferred chart containing the point: its normal coordinate vanishes. -/
theorem mem_boundaryTangentSpace_iff_tangentCoordChange {q : (𝓡∂ (n + 1)).boundary M} {α : M}
    (hα : (q : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    v ∈ boundaryTangentSpace q ↔
      (tangentCoordChange (𝓡∂ (n + 1)) (q : M) α (q : M) v) 0 = 0 := by
  obtain ⟨a, ha, hnormal⟩ := tangentCoordChange_normal_pos q.2 (mem_extChartAt_source _) hα
  rw [mem_boundaryTangentSpace_iff_proj, hnormal v, mul_eq_zero, or_iff_right ha.ne']
  rfl

/-- Inwardness, that is outwardness of the negative, can be tested in any preferred chart
containing the boundary point: the normal coordinate is positive. -/
theorem isOutwardPointing_neg_iff_tangentCoordChange {x α : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x (-v) ↔ 0 < (tangentCoordChange (𝓡∂ (n + 1)) x α x v) 0 := by
  obtain ⟨a, ha, hnormal⟩ := tangentCoordChange_normal_pos hx (mem_extChartAt_source _) hα
  rw [isOutwardPointing_neg_iff_proj hx, hnormal v, mul_pos_iff_of_pos_left ha]
  rfl

/-- **Trichotomy.** A tangent vector at a boundary point is outward, tangent to the boundary, or
inward (its negative is outward). The three cases are mutually exclusive
(`TauCeti.IsOutwardPointing.notMem_boundaryTangentSpace`,
`TauCeti.IsOutwardPointing.not_isOutwardPointing_neg`). -/
theorem isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg
    (q : (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    IsOutwardPointing (q : M) v ∨ v ∈ boundaryTangentSpace q ∨ IsOutwardPointing (q : M) (-v) := by
  rw [isOutwardPointing_iff_proj q.2, isOutwardPointing_neg_iff_proj q.2,
    mem_boundaryTangentSpace_iff_proj]
  exact lt_trichotomy _ _

/-- An outward vector is not tangent to the boundary. -/
theorem IsOutwardPointing.notMem_boundaryTangentSpace {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hv : IsOutwardPointing (q : M) v) :
    v ∉ boundaryTangentSpace q := by
  rw [isOutwardPointing_iff_proj q.2] at hv
  rw [mem_boundaryTangentSpace_iff_proj]
  exact hv.ne

/-- The normal coordinate of the half-space model is surjective. -/
private theorem surjective_proj_zero :
    Surjective (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) :=
  fun r ↦ ⟨EuclideanSpace.single 0 r, by simp⟩

/-- The frontier of the open half-space of outward vectors at a boundary point is the tangent
space of the boundary. -/
theorem frontier_setOf_isOutwardPointing (q : (𝓡∂ (n + 1)).boundary M) :
    frontier {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) v} =
      boundaryTangentSpace q := by
  have h : {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) v} =
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) ⁻¹' Iio 0 := by
    ext v
    exact isOutwardPointing_iff_proj q.2
  rw [h]
  refine (ContinuousLinearMap.frontier_preimage _ surjective_proj_zero _).trans ?_
  rw [frontier_Iio]
  ext v
  exact mem_boundaryTangentSpace_iff_proj.symm

/-- The frontier of the open half-space of inward vectors at a boundary point is the tangent space
of the boundary. -/
theorem frontier_setOf_isOutwardPointing_neg (q : (𝓡∂ (n + 1)).boundary M) :
    frontier {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) (-v)} =
      boundaryTangentSpace q := by
  have h : {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) (-v)} =
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) ⁻¹' Ioi 0 := by
    ext v
    exact isOutwardPointing_neg_iff_proj q.2
  rw [h]
  refine (ContinuousLinearMap.frontier_preimage _ surjective_proj_zero _).trans ?_
  rw [frontier_Ioi]
  ext v
  exact mem_boundaryTangentSpace_iff_proj.symm

/-- The velocity at `0` of a curve `c` with `c 0 ∈ ∂M` is tangent to the boundary. (Without
differentiability the velocity is `0` by convention.) -/
theorem mfderiv_apply_one_mem_boundaryTangentSpace {c : ℝ → M}
    (hc0 : c 0 ∈ (𝓡∂ (n + 1)).boundary M) :
    mfderiv 𝓘(ℝ) (𝓡∂ (n + 1)) c 0 (1 : ℝ) ∈
      boundaryTangentSpace (⟨c 0, hc0⟩ : (𝓡∂ (n + 1)).boundary M) := by
  by_cases hc : MDifferentiableAt 𝓘(ℝ) (𝓡∂ (n + 1)) c 0
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hc]
    exact Submodule.zero_mem _
  have hmin : IsLocalMin (fun t ↦ extChartAt (𝓡∂ (n + 1)) (c 0) (c t) 0) 0 :=
    ((isMinOn_extChartAt_apply_zero hc0 univ).comp_of_mapsTo (mapsTo_univ c univ) rfl).isLocalMin
      univ_mem
  have hd := (hasFDerivWithinAt_extChartAt_comp_apply_zero (s := univ)
    hc.mdifferentiableWithinAt).hasFDerivAt univ_mem
  have h := congrArg (fun L ↦ L (1 : ℝ)) (hmin.hasFDerivAt_eq_zero hd)
  rw [mfderivWithin_univ] at h
  rw [mem_boundaryTangentSpace_iff_proj]
  exact h

section Naturality

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 1 M']

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M') := isManifold_boundary M' one_ne_zero

/-- **Naturality.** A diffeomorphism `Φ` of manifolds with boundary, of class `C^k` with `k ≠ 0`,
maps `∂M` onto `∂M'` (Mathlib's `Diffeomorph.image_boundary`), and its differential at `q ∈ ∂M`
carries `T_q∂M` onto `T_{Φ q}∂M'`. -/
theorem map_mfderiv_boundaryTangentSpace {k : WithTop ℕ∞} (hk : k ≠ 0)
    (Φ : M ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M') (q : (𝓡∂ (n + 1)).boundary M) :
    (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap =
      boundaryTangentSpace (⟨Φ q, Φ.image_boundary hk ▸ mem_image_of_mem Φ q.2⟩ :
        (𝓡∂ (n + 1)).boundary M') := by
  have h1 : 1 ≤ k := ENat.one_le_iff_ne_zero_withTop.2 hk
  let ψ : (𝓡∂ (n + 1)).boundary M → (𝓡∂ (n + 1)).boundary M' :=
    fun y ↦ ⟨Φ y, Φ.image_boundary hk ▸ mem_image_of_mem Φ y.2⟩
  have hΦ : MDifferentiableAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q :=
    (Φ.contMDiff.mdifferentiable hk) q
  have hι := (isSmoothEmbedding_subtypeVal_boundary (n := n) M one_ne_zero).contMDiff
  have hι' := (isSmoothEmbedding_subtypeVal_boundary (n := n) M' one_ne_zero).contMDiff
  have hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ψ :=
    (contMDiff_iff_comp_subtypeVal_boundary (M := M') one_ne_zero).2
      ((Φ.contMDiff.of_le h1).comp hι)
  have hle : (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap ≤
      boundaryTangentSpace (ψ q) := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ψ q w, ?_⟩
    simp only [ContinuousLinearMap.coe_coe]
    rw [← mfderiv_comp_apply _ (hι'.mdifferentiable one_ne_zero _)
      (hψ.mdifferentiable one_ne_zero q),
      ← mfderiv_comp_apply _ hΦ (hι.mdifferentiable one_ne_zero q)]
    rfl
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hinj : Injective (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q) :=
    (Φ.isInvertible_mfderiv hk).injective
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_boundaryTangentSpace]
  exact (finrank_boundaryTangentSpace _).symm

end Naturality

end TauCeti
