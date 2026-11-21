/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Boundary.SmoothMap
public import TauCeti.Analysis.InnerProductSpace.PiL2

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
`v⁰ > 0`), and none of these classes depends on the chart. The inward and the outward vectors
(open half-spaces by `Boundary/Orientation.lean`) have common frontier `T_q∂M`.

The velocity at `t` of a curve `c` on `ℝ` with `c t ∈ ∂M` is tangent to the boundary, and the
one-sided velocity of a curve starting at a boundary point is not outward
(`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici`, in `Boundary/Orientation.lean`). A
diffeomorphism of class `C^k`, `k ≠ 0`, carries `T_q∂M` onto the tangent space of the boundary at
the image point.

## Main declarations

* `TauCeti.boundaryTangentSpace`: the tangent space `T_q∂M ⊆ T_qM` of the boundary.
* `TauCeti.boundaryTangentSpace_eq_euclideanHalfSpaceBoundary`: in the preferred chart it is the
  coordinate hyperplane; `TauCeti.finrank_boundaryTangentSpace`: it has dimension `n`, the
  differential of the inclusion being injective (`TauCeti.injective_mfderiv_subtypeVal_boundary`).
* `TauCeti.boundaryTangentSpace_eq_ker_of_mem_maximalAtlas`: it is the kernel of the differential
  of the normal coordinate of any chart of the maximal atlas.
* `TauCeti.mem_boundaryTangentSpace_iff_proj`: `v ∈ T_q∂M` exactly when its normal coordinate in
  the preferred chart vanishes; `TauCeti.mem_boundaryTangentSpace_iff_tangentCoordChange`: the
  same in any preferred chart.
* `TauCeti.isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg`, with
  `TauCeti.IsOutwardPointing.notMem_boundaryTangentSpace` and
  `TauCeti.IsOutwardPointing.not_isOutwardPointing_neg` (in `Boundary/Orientation.lean`): the
  trichotomy, restated as
  `TauCeti.mem_boundaryTangentSpace_iff_not_isOutwardPointing_and_not_isOutwardPointing_neg`.
* `TauCeti.frontier_setOf_isOutwardPointing`, `TauCeti.frontier_setOf_isOutwardPointing_neg`:
  the outward and inward half-spaces have frontier `T_q∂M`.
* `TauCeti.curveVelocity_mem_boundaryTangentSpace`: velocities of curves through the boundary.
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

/-! ### The tangent space of the boundary -/

local instance instIsManifoldBoundaryTangentSpace [IsManifold (𝓡∂ (n + 1)) 1 M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

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

/-- The differential of the boundary inclusion takes values in the tangent space of the
boundary. -/
theorem mfderiv_subtypeVal_mem_boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u ∈ boundaryTangentSpace q :=
  LinearMap.mem_range_self _ u

/-- The differential of the boundary inclusion is injective: in the preferred chart it is the
zero-insertion map. -/
theorem injective_mfderiv_subtypeVal_boundary (q : (𝓡∂ (n + 1)).boundary M) :
    Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q) := by
  rw [mfderiv_subtypeVal_boundary]
  exact euclideanHalfSpaceBoundaryParam_injective n

/-- The tangent space of the boundary has dimension `n`, one less than that of `M`. -/
@[simp]
theorem finrank_boundaryTangentSpace (q : (𝓡∂ (n + 1)).boundary M) :
    Module.finrank ℝ (boundaryTangentSpace q) = n := by
  rw [boundaryTangentSpace_def,
    LinearMap.finrank_range_of_inj (injective_mfderiv_subtypeVal_boundary q)]
  exact finrank_euclideanSpace_fin

/-- The tangent space of the boundary at `q` is the kernel of the differential at `q` of the normal
coordinate `x⁰` of any chart of the maximal atlas around `q`. In particular it is a hyperplane of
`T_qM`. -/
theorem boundaryTangentSpace_eq_ker_of_mem_maximalAtlas [IsManifold (𝓡∂ (n + 1)) 1 M]
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
    -- The differential of `e.extend` lands in a `TangentSpace` of the model space, a type synonym
    -- of `EuclideanSpace`, so `π.comp _` is not type-correct at instance transparency and
    -- `rw [ContinuousLinearMap.comp_apply]` finds no match; `change` unfolds the composition.
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
      ((isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 1) M).contMDiff.mdifferentiable
        one_ne_zero) q
    have hzero : (fun y ↦ e.extend (𝓡∂ (n + 1)) y 0) ∘
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) =ᶠ[𝓝 q] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(e.open_source.preimage continuous_subtypeVal).mem_nhds hq] with y hy
      exact (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hy).mp y.property
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
@[simp]
theorem mem_boundaryTangentSpace_iff_proj {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v ∈ boundaryTangentSpace q ↔ EuclideanSpace.proj (0 : Fin (n + 1)) v = 0 := by
  rw [boundaryTangentSpace_eq_euclideanHalfSpaceBoundary]
  exact mem_euclideanHalfSpaceBoundary

/-- Whether a tangent vector at a boundary point is tangent to the boundary can be tested in any
preferred chart containing the point: its normal coordinate vanishes. -/
theorem mem_boundaryTangentSpace_iff_tangentCoordChange [IsManifold (𝓡∂ (n + 1)) 1 M]
    {q : (𝓡∂ (n + 1)).boundary M} {α : M}
    (hα : (q : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    v ∈ boundaryTangentSpace q ↔
      (tangentCoordChange (𝓡∂ (n + 1)) (q : M) α (q : M) v) 0 = 0 := by
  obtain ⟨a, ha, hnormal⟩ := tangentCoordChange_normal_pos q.property (mem_extChartAt_source _) hα
  rw [mem_boundaryTangentSpace_iff_proj, hnormal v, mul_eq_zero, or_iff_right ha.ne']
  rfl

/-- **Trichotomy.** A tangent vector at a boundary point is outward, tangent to the boundary, or
inward (its negative is outward). The three cases are mutually exclusive
(`TauCeti.IsOutwardPointing.notMem_boundaryTangentSpace`,
`TauCeti.IsOutwardPointing.not_isOutwardPointing_neg`). -/
theorem isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg
    (q : (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    IsOutwardPointing (q : M) v ∨ v ∈ boundaryTangentSpace q ∨ IsOutwardPointing (q : M) (-v) := by
  rw [isOutwardPointing_iff_proj q.property, isOutwardPointing_neg_iff_proj q.property,
    mem_boundaryTangentSpace_iff_proj]
  exact lt_trichotomy _ _

/-- An outward vector is not tangent to the boundary. -/
theorem IsOutwardPointing.notMem_boundaryTangentSpace {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hv : IsOutwardPointing (q : M) v) :
    v ∉ boundaryTangentSpace q := by
  rw [isOutwardPointing_iff_proj q.property] at hv
  rw [mem_boundaryTangentSpace_iff_proj]
  exact hv.ne

/-- A tangent vector at a boundary point is tangent to the boundary exactly when neither it nor
its negative is outward. -/
theorem mem_boundaryTangentSpace_iff_not_isOutwardPointing_and_not_isOutwardPointing_neg
    (q : (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    v ∈ boundaryTangentSpace q ↔
      ¬IsOutwardPointing (q : M) v ∧ ¬IsOutwardPointing (q : M) (-v) := by
  refine ⟨fun hv ↦ ⟨fun h ↦ h.notMem_boundaryTangentSpace hv,
    fun h ↦ h.notMem_boundaryTangentSpace ((boundaryTangentSpace q).neg_mem hv)⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  exact ((isOutwardPointing_or_mem_boundaryTangentSpace_or_isOutwardPointing_neg q v).resolve_left
    h₁).resolve_right h₂

/-- Adding a boundary tangent vector preserves `IsOutwardPointing`, since boundary tangent vectors
have zero constrained coordinate. -/
theorem isOutwardPointing_add_mfderiv_subtypeVal_boundary [IsManifold (𝓡∂ (n + 1)) 1 M]
    (x : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) (x : M)) (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    IsOutwardPointing (x : M) (v + mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) ↔ IsOutwardPointing (x : M) v := by
  rw [isOutwardPointing_iff, isOutwardPointing_iff, and_iff_right x.property,
    and_iff_right x.property, map_add, map_add, PiLp.add_apply]
  have hz : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) (x : M) (x : M))
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) (x : M)) (x : M)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w))) 0 = 0 := by
    rw [mfderiv_subtypeVal_boundary, mfderiv_extChartAt_self]
    exact euclideanHalfSpaceBoundaryParam_apply_zero w
  rw [hz, add_zero]

/-- The frontier of the open half-space of outward vectors at a boundary point is the tangent
space of the boundary. -/
theorem frontier_setOf_isOutwardPointing (q : (𝓡∂ (n + 1)).boundary M) :
    frontier {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) v} =
      boundaryTangentSpace q := by
  have h : {v : TangentSpace (𝓡∂ (n + 1)) (q : M) | IsOutwardPointing (q : M) v} =
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) ⁻¹' Iio 0 := by
    ext v
    exact isOutwardPointing_iff_proj q.property
  rw [h]
  refine (ContinuousLinearMap.frontier_preimage _
    (EuclideanSpace.surjective_proj (𝕜 := ℝ) (0 : Fin (n + 1))) _).trans ?_
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
    exact isOutwardPointing_neg_iff_proj q.property
  rw [h]
  refine (ContinuousLinearMap.frontier_preimage _
    (EuclideanSpace.surjective_proj (𝕜 := ℝ) (0 : Fin (n + 1))) _).trans ?_
  rw [frontier_Ioi]
  ext v
  exact mem_boundaryTangentSpace_iff_proj.symm

/-- The velocity at `t` of a curve `c` with `c t ∈ ∂M` is tangent to the boundary. (Without
differentiability the velocity is `0` by convention.) -/
theorem curveVelocity_mem_boundaryTangentSpace (c : ℝ → M) {t : ℝ}
    (hq : c t ∈ (𝓡∂ (n + 1)).boundary M) :
    Manifold.curveVelocity (𝓡∂ (n + 1)) c t ∈ boundaryTangentSpace ⟨c t, hq⟩ := by
  rw [Manifold.curveVelocity_apply]
  by_cases hc : MDifferentiableAt 𝓘(ℝ) (𝓡∂ (n + 1)) c t
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hc]
    exact Submodule.zero_mem _
  have hmin : IsLocalMin (fun u ↦ extChartAt (𝓡∂ (n + 1)) (c t) (c u) 0) t :=
    ((isMinOn_extChartAt_apply_zero hq univ).comp_of_mapsTo (mapsTo_univ c univ) rfl).isLocalMin
      univ_mem
  have hd := (hasFDerivWithinAt_extChartAt_comp_apply_zero (s := univ)
    hc.mdifferentiableWithinAt).hasFDerivAt univ_mem
  have h := congrArg (fun L ↦ L (1 : ℝ)) (hmin.hasFDerivAt_eq_zero hd)
  rw [mfderivWithin_univ] at h
  rw [mem_boundaryTangentSpace_iff_proj]
  exact h

section Naturality

variable [IsManifold (𝓡∂ (n + 1)) 1 M] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M'] [IsManifold (𝓡∂ (n + 1)) 1 M']

local instance instIsManifoldBoundaryTangentSpaceNaturality :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M') :=
  isManifold_boundary M'

/-- **Naturality.** A diffeomorphism `Φ` of manifolds with boundary, of class `C^k` with `k ≠ 0`,
maps `∂M` onto `∂M'` (Mathlib's `Diffeomorph.image_boundary`), and its differential at `q ∈ ∂M`
carries `T_q∂M` onto `T_{Φ q}∂M'`. -/
theorem map_mfderiv_boundaryTangentSpace {k : WithTop ℕ∞} (hk : k ≠ 0)
    (Φ : M ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M') (q : (𝓡∂ (n + 1)).boundary M) :
    (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap =
      boundaryTangentSpace (⟨Φ q, Φ.image_boundary hk ▸ mem_image_of_mem Φ q.property⟩ :
        (𝓡∂ (n + 1)).boundary M') := by
  have h1 : 1 ≤ k := ENat.one_le_iff_ne_zero_withTop.2 hk
  let ψ : (𝓡∂ (n + 1)).boundary M → (𝓡∂ (n + 1)).boundary M' :=
    fun y ↦ ⟨Φ y, Φ.image_boundary hk ▸ mem_image_of_mem Φ y.property⟩
  have hΦ : MDifferentiableAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q :=
    (Φ.contMDiff.mdifferentiable hk) q
  have hι := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 1) M).contMDiff
  have hι' := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 1) M').contMDiff
  have hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ψ :=
    (contMDiff_iff_comp_subtypeVal_boundary (M := M')).2
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
