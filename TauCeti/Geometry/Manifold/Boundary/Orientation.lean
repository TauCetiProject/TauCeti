/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.VectorField.Regularity
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.Boundary.TransitionNormal
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Outward-pointing vectors at the boundary

For a manifold modeled on Mathlib's Euclidean half-space, this file records the sign convention
for an outward tangent vector.  Mathlib puts the boundary coordinate in slot `0`; outward vectors
therefore have a negative slot-`0` derivative.  The definition uses the preferred chart through
`mfderiv`; the positive normal derivative of actual chart transitions proves coordinate
independence in `isOutwardPointing_iff_tangentCoordChange`; equivalently, minus the normal
coordinate of any preferred chart increases along outward vectors
(`isOutwardPointing_iff_mvfderiv_neg_chartAt_normal_pos`); this function is as smooth as the
manifold on the chart source (`contMDiffAt_neg_chartAt_normal`, a case of
`contMDiffAt_normal` for every chart of the maximal atlas). This is the interface used by
boundary orientation and Stokes constructions. When the inward coordinate of the preferred chart
is a nonzero multiple of `g - c` for a real function `g`, outwardness is the sign of the
derivative of `g` (`isOutwardPointing_iff_mul_mvfderiv_neg`); this is how a boundary defining
function, such as the function cutting out a sublevel, detects the outward direction.

The same sign can be read in any chart `e` of the maximal atlas: the differentials at a boundary
point of the normal coordinates `(e ·).1 0` of two such charts are positive multiples of each other
(`exists_pos_mvfderiv_normal_eq_smul`), so a vector is outward exactly when the differential of
the normal coordinate of `e` is negative on it (`isOutwardPointing_iff_mvfderiv_neg`).

A function `f` with a local minimum at a boundary point `q` has `df_q v ≥ 0` for every vector `v`
that is not outward (Fermat's theorem at a boundary point, `mvfderiv_nonneg_of_isLocalMin`). If
also `df_q ≠ 0`, then `df_q` is a positive multiple of the differential of the normal coordinate of
the preferred chart at `q` (`exists_pos_mvfderiv_eq_smul_chartAt_of_isLocalMin`), so `df_q v < 0`
exactly for the outward vectors `v` (`isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin`). Applied
to the normal coordinate of the preferred chart at the image point, this shows that local
diffeomorphisms of manifolds with boundary preserve outward vectors
(`IsLocalDiffeomorphAt.isOutwardPointing_mfderiv_iff`, `isOutwardPointing_mfderiv_iff`).

The sign convention follows J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition
15.33, adapted to Mathlib's convention that the constrained coordinate is in slot `0`.

In the preferred chart at a boundary point, a vector is outward exactly when its normal
coordinate is negative (`isOutwardPointing_iff_proj`) and inward, that is its negative is outward,
exactly when that coordinate is positive (`isOutwardPointing_neg_iff_proj`,
`isOutwardPointing_neg_iff_tangentCoordChange`). Hence no vector is both
(`IsOutwardPointing.not_isOutwardPointing_neg`), and the outward and the inward vectors form open
sets (`isOpen_setOf_isOutwardPointing`, `isOpen_setOf_isOutwardPointing_neg`). The one-sided
velocity at `t` of a curve on `[t, ∞)`, taken within `[t, ∞)`, is never outward
(`not_isOutwardPointing_curveVelocityWithin_Ici`).

The standard half-space supplies a concrete witness: the constant negative first-coordinate
vector is outward at every boundary point.
-/

public section

open Set
open Bundle
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- A tangent vector at a boundary point points outward when its preferred half-space coordinate
has negative derivative.  The zeroth coordinate is the constrained coordinate of
`EuclideanHalfSpace`; this sign convention agrees with the outward-first boundary orientation. -/
def IsOutwardPointing (x : M) (v : TangentSpace (𝓡∂ (n + 1)) x) : Prop :=
  x ∈ (𝓡∂ (n + 1)).boundary M ∧
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) x x)
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 < 0

/-- An outward-pointing vector is based at the boundary, with negative zeroth coordinate
derivative in the preferred half-space chart. -/
@[grind =]
theorem isOutwardPointing_iff {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x} :
    IsOutwardPointing x v ↔
      x ∈ (𝓡∂ (n + 1)).boundary M ∧
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) x x)
          (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
            (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 < 0 := Iff.rfl

/-- Outwardness can be tested in any preferred chart containing the boundary point. -/
theorem isOutwardPointing_iff_tangentCoordChange [IsManifold (𝓡∂ (n + 1)) 1 M]
    {x α : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x v ↔ (tangentCoordChange (𝓡∂ (n + 1)) x α x v) 0 < 0 := by
  obtain ⟨a, ha, hnormal⟩ := tangentCoordChange_normal_pos hx (mem_extChartAt_source x) hα
  rw [isOutwardPointing_iff, and_iff_right hx, mfderiv_extChartAt_self]
  -- The preferred tangent fibre is the model space and fromTangentSpace is its
  -- identity identification; expose the evaluation before applying the normal factor.
  change (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0) v < 0 ↔ _
  exact (smul_neg_iff_of_pos_left ha).symm.trans (iff_of_eq
    (congrArg (fun r : ℝ ↦ r < 0) (hnormal v).symm))

/-- In any tangent-bundle trivialization at `α` containing a boundary point `y`, the image of
`-e₀` under `symmL` points outward at `y`. -/
theorem isOutwardPointing_trivializationAt_symmL_neg_single_zero [IsManifold (𝓡∂ (n + 1)) 1 M]
    {α : M} {y : (𝓡∂ (n + 1)).boundary M}
    (hy : (y : M) ∈ (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).baseSet) :
    IsOutwardPointing (y : M) ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ (y : M) (-EuclideanSpace.single 0 1)) := by
  let v₀ : EuclideanSpace ℝ (Fin (n + 1)) := -EuclideanSpace.single 0 1
  have hyc : (y : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  have hy' : (y : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source := by rwa [extChartAt_source]
  rw [isOutwardPointing_iff_tangentCoordChange y.property hy']
  have hWs : ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ (y : M) v₀ : EuclideanSpace ℝ (Fin (n + 1))) =
      tangentCoordChange (𝓡∂ (n + 1)) α (y : M) (y : M) v₀ :=
    congrArg (· v₀) (TangentBundle.symmL_trivializationAt_eq_core (I := 𝓡∂ (n + 1)) hyc)
  have hcoord : tangentCoordChange (𝓡∂ (n + 1)) (y : M) α (y : M)
      ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ (y : M) v₀) = v₀ := by
    rw [hWs, tangentCoordChange_comp ⟨⟨hy', mem_extChartAt_source (y : M)⟩, hy'⟩,
      tangentCoordChange_self hy']
  rw [hcoord]; simp [v₀]

omit [ChartedSpace (EuclideanHalfSpace (n + 1)) M] in
/-- The normal coordinate of a chart is the zeroth coordinate of the extended chart. -/
private theorem normal_eq_proj_comp_extend
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    (fun y ↦ (e y).val 0) = EuclideanSpace.proj (0 : Fin (n + 1)) ∘ e.extend (𝓡∂ (n + 1)) := by
  ext y
  simp

/-- The normal coordinate of a chart of the maximal atlas is as smooth as the atlas on the chart
source. -/
theorem contMDiffAt_normal {k : ℕ∞ω} {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) k M) {q : M} (hqe : q ∈ e.source) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun y ↦ (e y).val 0) q := by
  rw [normal_eq_proj_comp_extend]
  exact (ContinuousLinearMap.contMDiff _).contMDiffAt.comp q (e.contMDiffAt_extend he hqe)

/-- The differential at `x` of the normal coordinate of the preferred chart at `x` is the zeroth
coordinate of the preferred-chart derivative, the quantity whose sign defines
`IsOutwardPointing`. -/
theorem mvfderiv_chartAt_normal_apply (x : M) (v : TangentSpace (𝓡∂ (n + 1)) x) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) x v =
      (NormedSpace.fromTangentSpace (extChartAt (𝓡∂ (n + 1)) x x)
        (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 := by
  have hext := (TauCeti.hasMFDerivAt_extChartAt_self (I := 𝓡∂ (n + 1)) x).mdifferentiableAt
  have hfun : (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) =
      EuclideanSpace.proj (0 : Fin (n + 1)) ∘ extChartAt (𝓡∂ (n + 1)) x :=
    normal_eq_proj_comp_extend _
  rw [hfun, (EuclideanSpace.proj (0 : Fin (n + 1))).mvfderiv_comp_apply (I := 𝓡∂ (n + 1)) hext]
  simp only [mvfderiv_apply_eq_mfderiv_apply, NormedSpace.fromTangentSpace_apply]
  -- The tangent fibre of the half-space model is the model space itself, on which `proj 0` is
  -- evaluation in slot `0`; the tangent-space wrapper blocks the rewriting lemmas for both.
  rfl

/-- The normal coordinate of the preferred chart at `x` is differentiable at `x`. -/
theorem mdifferentiableAt_chartAt_normal (x : M) :
    MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ)
      (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) x := by
  rw [normal_eq_proj_comp_extend]
  exact (EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).mdifferentiableAt.comp x
      (TauCeti.hasMFDerivAt_extChartAt_self (I := 𝓡∂ (n + 1)) x).mdifferentiableAt

/-- Minus the normal coordinate of a preferred chart is minus the zeroth coordinate of its extended
chart. -/
private theorem neg_normal_eq_neg_proj_comp_extChartAt (α : M) :
    (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) =
      (-EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) ∘
        extChartAt (𝓡∂ (n + 1)) α := by
  ext y
  simp

/-- Minus the normal coordinate of a preferred chart is as smooth as the manifold on the chart
source. -/
theorem contMDiffAt_neg_chartAt_normal {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) k M] {α x : M}
    (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) x :=
  (contMDiffAt_normal (IsManifold.chart_mem_maximalAtlas α) hx).neg

/-- Minus the normal coordinate of a preferred chart, read as a differential of a function on
`M`, is minus the normal component of the tangent coordinate change into that chart. -/
theorem mvfderiv_neg_chartAt_normal_apply [IsManifold (𝓡∂ (n + 1)) 1 M] {α q : M}
    (hq : q ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q v =
      -tangentCoordChange (𝓡∂ (n + 1)) q α q v 0 := by
  have hext := hasMFDerivAt_extChartAt (I := 𝓡∂ (n + 1)) hq
  rw [neg_normal_eq_neg_proj_comp_extChartAt,
    ContinuousLinearMap.mvfderiv_comp_apply _ hext.mdifferentiableAt,
    mvfderiv_apply_eq_mfderiv_apply, hext.mfderiv, mfderiv_chartAt_eq_tangentCoordChange hq]
  -- The tangent fibre of the half-space model is the model space itself, on which `-proj 0` is
  -- minus evaluation in slot `0`. The tangent-space wrapper makes `neg_apply` fail to typecheck
  -- and `simp` unfolds `tangentCoordChange` instead, so close the goal definitionally.
  rfl

/-- At a boundary point, a vector points outward exactly when minus the normal coordinate of a
preferred chart increases along it. -/
theorem isOutwardPointing_iff_mvfderiv_neg_chartAt_normal_pos [IsManifold (𝓡∂ (n + 1)) 1 M]
    {α q : M} (hqb : q ∈ (𝓡∂ (n + 1)).boundary M)
    (hq : q ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔
      0 < mvfderiv (𝓡∂ (n + 1))
        (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q v := by
  rw [isOutwardPointing_iff_tangentCoordChange hqb (by rwa [extChartAt_source]),
    mvfderiv_neg_chartAt_normal_apply hq, neg_pos]

/-- Suppose that, near a boundary point `x`, the inward coordinate (slot `0`) of the preferred
chart at `x` is `s * (g - c)` for a real function `g` and constants `c` and `s ≠ 0`. Then a
tangent vector `v` at `x` points outward exactly when `s` times the derivative of `g` is negative
on it. For `s = -1` this says that `g` increases along outward vectors. -/
theorem isOutwardPointing_iff_mul_mvfderiv_neg {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) {g : M → ℝ} {c s : ℝ} (hs : s ≠ 0)
    (hchart : ∀ᶠ w in 𝓝 x, (chartAt (EuclideanHalfSpace (n + 1)) x w).val 0 = s * (g w - c))
    (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x v ↔ s * mvfderiv (𝓡∂ (n + 1)) g x v < 0 := by
  -- The inward coordinate `t` of the preferred chart, and its derivative at `x`.
  set t : M → ℝ := fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0 with ht
  have hd : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) t x := mdifferentiableAt_chartAt_normal x
  -- Near `x`, `g` is the affine function `c + s⁻¹ * t`.
  have hg : g =ᶠ[𝓝 x] (fun r : ℝ ↦ c + s⁻¹ * r) ∘ t := by
    filter_upwards [hchart] with w hw
    simp only [ht, Function.comp_apply]
    rw [hw]
    field_simp
    ring
  have hφ : HasFDerivAt (fun r : ℝ ↦ c + s⁻¹ * r) (s⁻¹ • ContinuousLinearMap.id ℝ ℝ) (t x) :=
    ((hasFDerivAt_id _).const_mul s⁻¹).const_add c
  rw [isOutwardPointing_iff, and_iff_right hx, ← mvfderiv_chartAt_normal_apply, hg.mvfderiv_eq,
    mvfderiv_comp_apply_of_differentiableAt hφ.differentiableAt hd, hφ.fderiv, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_inv_cancel_left₀ hs]

namespace IsOutwardPointing

/-- An outward-pointing vector is based at a boundary point. -/
theorem mem_boundary {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) : x ∈ (𝓡∂ (n + 1)).boundary M :=
  isOutwardPointing_iff.mp hv |>.1

/-- The preferred-chart derivative of an outward-pointing vector is negative in slot `0`. -/
theorem coordinate_deriv_neg {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) x x)
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 < 0 :=
  isOutwardPointing_iff.mp hv |>.2

/-- Positive rescaling preserves the outward half-space of tangent vectors. -/
theorem smul_pos {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) {c : ℝ} (hc : 0 < c) :
    IsOutwardPointing x (c • v) := by
  rcases hv with ⟨hx, hv⟩
  refine ⟨hx, ?_⟩
  rw [ContinuousLinearMap.map_smul, map_smul]
  simpa [smul_eq_mul] using mul_neg_of_pos_of_neg hc hv

/-- The sum of two outward vectors is outward. -/
theorem add {x : M} {v w : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) (hw : IsOutwardPointing x w) :
    IsOutwardPointing x (v + w) := by
  rcases hv with ⟨hx, hv⟩
  rcases hw with ⟨-, hw⟩
  refine ⟨hx, ?_⟩
  rw [ContinuousLinearMap.map_add, map_add]
  simpa using add_neg hv hw

/-- The outward-pointing vectors at a fixed point form a convex set.  This is the pointwise
interface used when smooth local outward fields are glued by a partition of unity. -/
theorem convex (x : M) :
    Convex ℝ {v : TangentSpace (𝓡∂ (n + 1)) x | IsOutwardPointing x v} := by
  intro v hv w hw a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst a
    simpa [hb1] using hw
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    subst b
    simpa [ha1] using hv
  exact (hv.smul_pos (lt_of_le_of_ne ha (Ne.symm ha0))).add
    (hw.smul_pos (lt_of_le_of_ne hb (Ne.symm hb0)))

/-- An outward vector is nonzero. -/
theorem ne_zero {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) : v ≠ 0 := by
  intro hzero
  subst hzero
  rcases hv with ⟨-, hv⟩
  rw [ContinuousLinearMap.map_zero, map_zero] at hv
  exact (lt_irrefl 0) (by simp at hv)

end IsOutwardPointing

/-! ### Outward and inward vectors in the preferred chart -/

section PreferredChart

/-- At a boundary point, a vector is outward exactly when its normal coordinate in the preferred
chart is negative. -/
theorem isOutwardPointing_iff_proj {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    {v : TangentSpace (𝓡∂ (n + 1)) x} :
    IsOutwardPointing x v ↔ EuclideanSpace.proj (0 : Fin (n + 1)) v < 0 := by
  rw [isOutwardPointing_iff, and_iff_right hx, (hasMFDerivAt_extChartAt_self x).mfderiv]
  rfl

/-- At a boundary point, a vector is inward exactly when its normal coordinate in the preferred
chart is positive. -/
theorem isOutwardPointing_neg_iff_proj {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    {v : TangentSpace (𝓡∂ (n + 1)) x} :
    IsOutwardPointing x (-v) ↔ 0 < EuclideanSpace.proj (0 : Fin (n + 1)) v := by
  -- `TangentSpace` is a type synonym of the model space, so the target `proj 0 (-v)` is not
  -- type-correct at instance transparency and `rw [map_neg]` finds no match; the `show` states
  -- the instance of `map_neg` at the tangent space.
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
theorem isMinOn_extChartAt_apply_zero {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (s : Set M) : IsMinOn (fun y ↦ extChartAt (𝓡∂ (n + 1)) x y 0) s x := fun y _ ↦ by
  simpa only [mem_ofPred_eq, extChartAt_coe, Function.comp_apply,
    modelWithCornersEuclideanHalfSpace_toFun] using
    normal_le_of_mem_boundary hx (mem_chart_source _ x) y

/-- The normal coordinate, in the preferred chart at `c t`, of the velocity of a curve `c` within
`s` at `t` is the derivative of the normal coordinate of `c`. -/
theorem hasFDerivWithinAt_extChartAt_comp_apply_zero {c : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ (n + 1)) c s t) :
    HasFDerivWithinAt (fun u ↦ extChartAt (𝓡∂ (n + 1)) (c t) (c u) 0)
      ((EuclideanSpace.proj (0 : Fin (n + 1))).comp
        (mfderivWithin 𝓘(ℝ) (𝓡∂ (n + 1)) c s t)) s t := by
  have hd := (hasMFDerivAt_extChartAt_self (I := 𝓡∂ (n + 1)) (c t)).comp_hasMFDerivWithinAt
    t hc.hasMFDerivWithinAt
  rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hd
  exact (EuclideanSpace.proj (0 : Fin (n + 1))).hasFDerivAt.comp_hasFDerivWithinAt t hd

/-- A curve `c` running for parameters `≥ t` leaves `c t` in an inward or tangent direction: its
one-sided velocity at `t`, taken within `[t, ∞)`, is not outward. (Without differentiability the
velocity is `0` by convention, which is not outward either.) -/
theorem not_isOutwardPointing_curveVelocityWithin_Ici (c : ℝ → M) (t : ℝ) :
    ¬IsOutwardPointing (c t) (Manifold.curveVelocityWithin (𝓡∂ (n + 1)) c (Ici t) t) := by
  intro hv
  rw [Manifold.curveVelocityWithin_apply] at hv
  by_cases hc : MDifferentiableWithinAt 𝓘(ℝ) (𝓡∂ (n + 1)) c (Ici t) t
  swap
  · rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hc] at hv
    exact hv.ne_zero rfl
  have hmin : IsLocalMinOn (fun u ↦ extChartAt (𝓡∂ (n + 1)) (c t) (c u) 0) (Ici t) t :=
    ((isMinOn_extChartAt_apply_zero hv.mem_boundary univ).comp_of_mapsTo
      (mapsTo_univ c (Ici t)) rfl).isLocalMinOn
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici t) t :=
    mem_posTangentConeAt_of_segment_subset ((convex_Ici t).segment_subset self_mem_Ici
      (by simp))
  have h := hmin.hasFDerivWithinAt_nonneg (hasFDerivWithinAt_extChartAt_comp_apply_zero hc) hcone
  rw [isOutwardPointing_iff_proj hv.mem_boundary] at hv
  exact (not_lt.mpr h) hv

/-- Inwardness, that is outwardness of the negative, can be tested in any preferred chart
containing the boundary point: the normal coordinate is positive. -/
theorem isOutwardPointing_neg_iff_tangentCoordChange [IsManifold (𝓡∂ (n + 1)) 1 M] {x α : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x (-v) ↔ 0 < (tangentCoordChange (𝓡∂ (n + 1)) x α x v) 0 := by
  obtain ⟨a, ha, hnormal⟩ := tangentCoordChange_normal_pos hx (mem_extChartAt_source _) hα
  rw [isOutwardPointing_neg_iff_proj hx, hnormal v, mul_pos_iff_of_pos_left ha]
  rfl

end PreferredChart

/-! ### Functions with a local minimum at a boundary point -/

section LocalMin

/-- The differential at `x` of the normal coordinate of the preferred chart at `x` takes the value
`1` on the first standard basis vector. -/
private theorem mvfderiv_chartAt_normal_single (x : M) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) x
      (EuclideanSpace.single 0 1 : TangentSpace (𝓡∂ (n + 1)) x) = 1 := by
  refine (mvfderiv_chartAt_normal_apply x _).trans ?_
  rw [mfderiv_extChartAt_eq_id]
  -- The preferred tangent fibre is the model space, and both identifications with it are the
  -- identity.
  change (EuclideanSpace.single (𝕜 := ℝ) (0 : Fin (n + 1)) 1) 0 = 1
  simp

/-- At a boundary point `x`, a vector is outward exactly when the differential at `x` of the
normal coordinate of the preferred chart at `x` is negative on it. -/
theorem isOutwardPointing_iff_mvfderiv_chartAt_normal_neg {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x v ↔
      mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) x v < 0 := by
  rw [mvfderiv_chartAt_normal_apply, isOutwardPointing_iff, and_iff_right hx]

/-- At a boundary point, minus the first standard basis vector of the preferred chart is outward:
the first standard basis vector is inward. -/
theorem isOutwardPointing_neg_single_zero {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing x (-(EuclideanSpace.single 0 1 : TangentSpace (𝓡∂ (n + 1)) x)) :=
  (isOutwardPointing_neg_iff_proj hx).mpr (by simp)

/-- **Fermat's theorem at a boundary point.** A function with a local minimum at a boundary point
`q` has nonnegative differential on every tangent vector at `q` that is not outward. -/
theorem mvfderiv_nonneg_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q) {v : TangentSpace (𝓡∂ (n + 1)) q}
    (hv : ¬IsOutwardPointing q v) : 0 ≤ mvfderiv (𝓡∂ (n + 1)) f q v := by
  by_cases hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q
  swap
  · exact not_lt.mp fun h ↦ hf (mdifferentiableAt_of_mvfderiv_apply_ne_zero h.ne)
  -- Read `f` in the preferred chart at `q`, as a function on the model half-space.
  have hd := hf.hasMFDerivAt.2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp] at hd
  rw [isOutwardPointing_iff_proj hq, not_lt] at hv
  rw [mvfderiv_apply_eq_mfderiv_apply]
  -- The tangent space at `q` is the model space, in which `v` is a vector with `0 ≤ v 0`.
  exact hasFDerivWithinAt_nonneg_of_isLocalMin (v := (v : EuclideanSpace ℝ (Fin (n + 1)))) hq
    (mem_extChartAt_source q) hmin hd hv

/-- A function with a local minimum and nonzero differential at a boundary point `q` has
differential at `q` a positive multiple of the differential of the normal coordinate of the
preferred chart at `q`. -/
theorem exists_pos_mvfderiv_eq_smul_chartAt_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q)
    (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ mvfderiv (𝓡∂ (n + 1)) f q =
      a • mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).val 0) q := by
  let I := 𝓡∂ (n + 1)
  set ℓ := mvfderiv I (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).val 0) q
  set ℓf := mvfderiv I f q
  let w : TangentSpace I q := EuclideanSpace.single 0 1
  have hw : ℓ w = 1 := mvfderiv_chartAt_normal_single q
  -- A vector is not outward exactly when `ℓ` is nonnegative on it.
  have hnonneg (u : TangentSpace I q) (hu : 0 ≤ ℓ u) : 0 ≤ ℓf u :=
    mvfderiv_nonneg_of_isLocalMin hq hmin fun h ↦
      ((isOutwardPointing_iff_mvfderiv_chartAt_normal_neg hq u).mp h).not_ge hu
  have hfactor (u : TangentSpace I q) : ℓf u = ℓf w * ℓ u :=
    Module.Dual.apply_eq_mul_apply_of_nonneg (ℓ : TangentSpace I q →ₗ[ℝ] ℝ)
      (ℓf : TangentSpace I q →ₗ[ℝ] ℝ) hw hnonneg u
  refine ⟨ℓf w, (hnonneg w (hw ▸ zero_le_one)).lt_of_ne fun h0 ↦ hne ?_, ?_⟩
  · ext u
    rw [hfactor u, ← h0, zero_mul, zero_apply]
  · ext u
    rw [hfactor u, smul_apply, smul_eq_mul]

/-- **Sign test.** A function with a local minimum and nonzero differential `df_q` at a boundary
point `q` has `df_q v` strictly negative exactly for the outward vectors `v`. -/
theorem isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q)
    (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0) (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔ mvfderiv (𝓡∂ (n + 1)) f q v < 0 := by
  obtain ⟨a, ha, h⟩ := exists_pos_mvfderiv_eq_smul_chartAt_of_isLocalMin hq hmin hne
  rw [h, smul_apply, smul_neg_iff_of_pos_left ha,
    isOutwardPointing_iff_mvfderiv_chartAt_normal_neg hq]

/-- **Sign test.** A function with a local minimum and nonzero differential `df_q` at a boundary
point `q` has `df_q v` strictly positive exactly for the inward vectors `v`, those with `-v`
outward. -/
theorem isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q)
    (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0) (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q (-v) ↔ 0 < mvfderiv (𝓡∂ (n + 1)) f q v := by
  rw [isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq hmin hne, map_neg, neg_lt_zero]

end LocalMin

/-! ### Outward vectors in an arbitrary chart of the maximal atlas -/

section MaximalAtlas

/-- The normal coordinate of a chart of the maximal atlas is differentiable on its source. -/
theorem mdifferentiableAt_normal
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M} (hqe : q ∈ e.source) :
    MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) (fun y ↦ (e y).val 0) q :=
  (contMDiffAt_normal he hqe).mdifferentiableAt one_ne_zero

/-- The differential of the normal coordinate of a chart of the maximal atlas is nonzero on its
source, since the chart has invertible differential and the zeroth coordinate projection is
surjective. -/
theorem mvfderiv_normal_ne_zero
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M} (hqe : q ∈ e.source) :
    mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q ≠ 0 := by
  obtain ⟨u, hu⟩ := (isInvertible_mfderiv_extend he hqe).surjective
    (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))
  intro h0
  have h := (EuclideanSpace.proj (0 : Fin (n + 1))).mvfderiv_comp_apply (I := 𝓡∂ (n + 1))
    (e.mdifferentiableAt_extend he hqe) u
  rw [← normal_eq_proj_comp_extend, mvfderiv_apply_eq_mfderiv_apply (f := e.extend (𝓡∂ (n + 1))),
    hu, h0] at h
  simp at h

/-- The differential of the normal coordinate of a chart of the maximal atlas is a positive
multiple of that of the preferred chart. -/
private theorem exists_pos_mvfderiv_normal_eq_smul_chartAt
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source) :
    ∃ a : ℝ, 0 < a ∧ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q =
      a • mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) q y).val 0) q :=
  exists_pos_mvfderiv_eq_smul_chartAt_of_isLocalMin hq
    (Filter.Eventually.of_forall (normal_le_of_mem_boundary hq hqe))
    (mvfderiv_normal_ne_zero he hqe)

/-- At a boundary point, the differentials of the normal coordinates of two charts of the maximal
atlas are positive multiples of each other. -/
theorem exists_pos_mvfderiv_normal_eq_smul
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source) (hqe' : q ∈ e'.source) :
    ∃ a : ℝ, 0 < a ∧ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q =
      a • mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e' y).val 0) q := by
  obtain ⟨a, ha, h⟩ := exists_pos_mvfderiv_normal_eq_smul_chartAt he hq hqe
  obtain ⟨a', ha', h'⟩ := exists_pos_mvfderiv_normal_eq_smul_chartAt he' hq hqe'
  refine ⟨a / a', div_pos ha ha', ?_⟩
  rw [h, h', smul_smul, div_mul_cancel₀ a ha'.ne']

/-- A tangent vector at a boundary point is outward exactly when the differential of the normal
coordinate of any chart of the maximal atlas is negative on it. -/
theorem isOutwardPointing_iff_mvfderiv_neg
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hqe : q ∈ e.source)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔ mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q v < 0 :=
  isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq
    (Filter.Eventually.of_forall (normal_le_of_mem_boundary hq hqe))
    (mvfderiv_normal_ne_zero he hqe) v

end MaximalAtlas

/-! ### Local diffeomorphisms preserve outward vectors -/

section LocalDiffeomorph

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']

/-- **Local diffeomorphisms preserve outward vectors.** For a local diffeomorphism `f` at `q` of
manifolds with boundary, of class `C^k` with `k ≠ 0`, a tangent vector `v` at `q` is outward
exactly when its image `df_q v` is outward at `f q`. -/
theorem _root_.IsLocalDiffeomorphAt.isOutwardPointing_mfderiv_iff {k : WithTop ℕ∞} (hk : k ≠ 0)
    {f : M → M'} {q : M} (hf : IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k f q)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing (f q) (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) f q v) ↔
      IsOutwardPointing q v := by
  by_cases hq : q ∈ (𝓡∂ (n + 1)).boundary M
  swap
  · exact iff_of_false (fun h ↦ hq ((hf.isBoundaryPoint_iff hk).mpr h.mem_boundary))
      fun h ↦ hq h.mem_boundary
  have hfq : f q ∈ (𝓡∂ (n + 1)).boundary M' := (hf.isBoundaryPoint_iff hk).mp hq
  -- The normal coordinate of the preferred chart at `f q`, and its pullback along `f`.
  let x₀ : M' → ℝ := fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) (f q) y).val 0
  have hmin' : IsLocalMin x₀ (f q) := Filter.Eventually.of_forall fun y ↦
    normal_le_of_mem_boundary hfq (mem_chart_source _ _) y
  have hx₀ : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) x₀ (f q) := mdifferentiableAt_chartAt_normal (f q)
  have hne' : mvfderiv (𝓡∂ (n + 1)) x₀ (f q) ≠ 0 := DFunLike.ne_iff.mpr
    ⟨_, (mvfderiv_chartAt_normal_single (f q)).trans_ne one_ne_zero⟩
  rw [isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hfq hmin' hne',
    isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq
      (hmin'.comp_continuous (hf.mdifferentiableAt hk).continuousAt)
      (mt (mvfderiv_comp_eq_zero_iff_of_isInvertible hx₀ (hf.isInvertible_mfderiv hk)).mp hne'),
    mvfderiv_comp_apply q hx₀ (hf.mdifferentiableAt hk)]

/-- **Diffeomorphisms preserve outward vectors.** For a diffeomorphism `Φ` of manifolds with
boundary, of class `C^k` with `k ≠ 0`, a tangent vector `v` at `q` is outward exactly when its
image `dΦ_q v` is outward at `Φ q`. -/
theorem isOutwardPointing_mfderiv_iff {k : WithTop ℕ∞} (hk : k ≠ 0)
    (Φ : M ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M') {q : M} (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing (Φ q) (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q v) ↔
      IsOutwardPointing q v :=
  (Φ.isLocalDiffeomorph q).isOutwardPointing_mfderiv_iff hk v

end LocalDiffeomorph

/-- On the standard half-space, the constant vector `-e₀` is outward at every boundary point. -/
theorem isOutwardPointing_standard_halfSpace
    {x : EuclideanHalfSpace (n + 1)}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))) :
    IsOutwardPointing (n := n) x (-EuclideanSpace.single 0 1) := by
  refine ⟨hx, ?_⟩
  rw [mfderiv_extChartAt_self]
  -- The tangent space of the model space is definitionally the model space, and
  -- `NormedSpace.fromTangentSpace` is its canonical definitional identification.
  change (-EuclideanSpace.single (𝕜 := ℝ) 0 1) 0 < 0
  simp

/-- A smooth vector field is outward-pointing when each of its boundary values points out of the
half-space. Smoothness is recorded as regularity of the corresponding tangent-bundle section, so
the predicate does not depend on a choice of tangent-bundle trivialization. -/
def IsOutwardPointingField {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M]
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x) : Prop :=
  ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V) ∧
    ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (V x)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
  {V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}

/-- Characterization of a smooth outward-pointing field by its smoothness and boundary values. -/
@[grind =]
theorem isOutwardPointingField_iff :
    IsOutwardPointingField V ↔
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V) ∧
        ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (V x) :=
  Iff.rfl

namespace IsOutwardPointingField

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
  {V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}

/-- Construct a smooth outward-pointing field from its smoothness and boundary values. -/
theorem intro
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V))
    (hout : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (V x)) :
    IsOutwardPointingField V :=
  ⟨hV, hout⟩

/-- The field component of an outward-pointing field is smooth. -/
theorem contMDiff (hV : IsOutwardPointingField V) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V) :=
  hV.1

/-- Every boundary value of an outward-pointing field points out. -/
theorem isOutwardPointing (hV : IsOutwardPointingField V) {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing x (V x) :=
  hV.2 x hx

/-- The negative of an outward-pointing field is smooth. -/
theorem contMDiff_neg (hV : IsOutwardPointingField V) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% (-V)) :=
  fun x ↦ (hV.contMDiff x).neg_section

/-- The negative of an outward-pointing field points inward along the boundary: the negative of
its value at every boundary point is outward. This is the boundary hypothesis of the inward flow
lemmas, applied to the inward field `-V`. -/
theorem isOutwardPointing_neg_neg (hV : IsOutwardPointingField V) (x : M)
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) : IsOutwardPointing x (-(-V) x) := by
  simpa using hV.isOutwardPointing hx

/-- The sum of two smooth outward-pointing fields is outward-pointing. -/
theorem add {W : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}
    (hV : IsOutwardPointingField V) (hW : IsOutwardPointingField W) :
    IsOutwardPointingField (fun x ↦ V x + W x) := by
  refine ⟨hV.contMDiff.add_section hW.contMDiff, ?_⟩
  intro x hx
  exact (hV.isOutwardPointing hx).add (hW.isOutwardPointing hx)

/-- Multiplication by a smooth positive scalar preserves an outward-pointing field. -/
theorem smul {f : M → ℝ} (hV : IsOutwardPointingField V)
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, 0 < f x) :
    IsOutwardPointingField (fun x ↦ f x • V x) := by
  refine ⟨hf.smul_section hV.1, fun x hx ↦ (hV.2 x hx).smul_pos (hpos x hx)⟩

/-- Smooth convex combinations of outward-pointing fields remain outward-pointing.
The coefficients are smooth globally, nonnegative on the boundary, and sum to one there. -/
theorem smul_add_smul {W : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}
    (hV : IsOutwardPointingField V) (hW : IsOutwardPointingField W)
    {f g : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ g)
    (hf_nonneg : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, 0 ≤ f x)
    (hg_nonneg : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, 0 ≤ g x)
    (hfg : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, f x + g x = 1) :
    IsOutwardPointingField (fun x ↦ f x • V x + g x • W x) := by
  refine ⟨(hf.smul_section hV.contMDiff).add_section (hg.smul_section hW.contMDiff), ?_⟩
  intro x hx
  exact (IsOutwardPointing.convex x) (hV.isOutwardPointing hx) (hW.isOutwardPointing hx)
    (hf_nonneg x hx) (hg_nonneg x hx) (hfg x hx)

end IsOutwardPointingField

/-- The constant negative normal field on the standard Euclidean half-space. -/
noncomputable def standardOutwardVectorField (n : ℕ) :
    ∀ x : EuclideanHalfSpace (n + 1), TangentSpace (𝓡∂ (n + 1)) x :=
  fun _ ↦ -EuclideanSpace.single 0 1

/-- The standard field has constant negative zeroth coordinate. -/
@[simp]
theorem standardOutwardVectorField_apply (n : ℕ)
    (x : EuclideanHalfSpace (n + 1)) :
    standardOutwardVectorField n x = -EuclideanSpace.single 0 1 := by
  rfl

/-- The standard negative normal field is smooth as a tangent-bundle section. -/
theorem contMDiff_standardOutwardVectorField (n : ℕ) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (T% (standardOutwardVectorField n)) := by
  have h := contMDiff_tangentBundleModelSpaceHomeomorph_symm_prodMk_const
    (𝓡∂ (n + 1)) (-EuclideanSpace.single 0 1) ∞
  apply h.congr
  intro x
  simp only [tangentBundleModelSpaceHomeomorph_coe_symm, TotalSpace.toProd]
  rfl

/-- The standard Euclidean half-space has a smooth outward-pointing field. -/
theorem isOutwardPointingField_standard_halfSpace (n : ℕ) :
    IsOutwardPointingField (standardOutwardVectorField n) := by
  refine ⟨contMDiff_standardOutwardVectorField n, fun x hx ↦ ?_⟩
  exact isOutwardPointing_standard_halfSpace (n := n) (x := x) hx

end TauCeti
