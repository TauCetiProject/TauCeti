/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.MetricChange

/-!
# Checks: the Grassmann bundle of `ℝ²` for the metrics `diag(1, 4)` and `4 g`

On the plane `ℝ²`, recorded as the bundle over a point with fibre `EuclideanSpace ℝ (Fin 2)`,
consider the Euclidean metric `g`, the metric `h = diag(1, 4)`, that is
`h(u, v) = u₀ v₀ + 4 u₁ v₁ = ⟪u, v⟫ + 3 u₁ v₁`, and the metric `4 g`.

For `u = (1, 1)`, the `h`-orthogonal projection onto `span(u)` sends `e₀` to `u / 5`
(`P_h_apply_e₀`) and the Euclidean one sends `e₀` to `u / 2` (`P_g_apply_e₀`). The canonical
homeomorphism `G_1^g ≃ₜ G_1^h` sends the Euclidean projection onto `span(u)` to the `h`-orthogonal
one (`metricChangeHomeomorph_P`), so it is not the identity on projections (`P_h_apply_e₀_ne`).
For `4 g` it is (`coe_metricChangeHomeomorph_four`).
-/

public section

noncomputable section

open Bundle Module TauCeti TauCeti.WithFiberMetric
open scoped InnerProductSpace

namespace TauCeti.Examples.GrassmannBundleMetricChange

/-- The model plane `ℝ²`. -/
abbrev F := EuclideanSpace ℝ (Fin 2)

/-- `ℝ²` as a vector bundle over a point. -/
abbrev E := Bundle.Trivial Unit F

/-- A continuous Riemannian metric on `ℝ²`, seen as a bundle over a point, from a symmetric
bilinear form that dominates the Euclidean one. -/
def metricOfForm (A : F →L[ℝ] F →L[ℝ] ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hge : ∀ v, ‖v‖ ^ 2 ≤ A v v) : ContinuousRiemannianMetric F E where
  inner _ := A
  symm _ := hsymm
  pos _ v hv := (pow_pos (norm_pos_iff.2 hv) 2).trans_le (hge v)
  isVonNBounded _ := by
    rw [NormedSpace.isVonNBounded_iff]
    refine (Metric.isBounded_ball (x := (0 : F)) (r := 1)).subset fun v hv ↦ ?_
    rw [mem_ball_zero_iff]
    have h1 : ‖v‖ ^ 2 < 1 := (hge v).trans_lt hv
    nlinarith [norm_nonneg v]
  continuous := continuous_of_discreteTopology

theorem metricOfForm_inner (A : F →L[ℝ] F →L[ℝ] ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hge : ∀ v, ‖v‖ ^ 2 ≤ A v v) (b : Unit) : (metricOfForm A hsymm hge).inner b = A :=
  (rfl)

/-- The Euclidean inner product of `ℝ²`, as a bilinear form. -/
def euclidForm : F →L[ℝ] F →L[ℝ] ℝ :=
  innerSL ℝ

theorem euclidForm_apply (u v : F) : euclidForm u v = ⟪u, v⟫_ℝ :=
  (rfl)

/-- The Euclidean metric on `ℝ²`. -/
def g : ContinuousRiemannianMetric F E :=
  metricOfForm euclidForm (fun u v ↦ by rw [euclidForm_apply, euclidForm_apply, real_inner_comm])
    fun v ↦ by rw [euclidForm_apply, real_inner_self_eq_norm_sq]

/-- The form `u₁ v₁` on `ℝ²`. -/
def secondCoord : F →L[ℝ] F →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.proj (1 : Fin 2))

theorem secondCoord_apply (u v : F) : secondCoord u v = u 1 * v 1 :=
  (rfl)

/-- The metric `h = diag(1, 4)` on `ℝ²`: `h(u, v) = ⟪u, v⟫ + 3 u₁ v₁ = u₀ v₀ + 4 u₁ v₁`. -/
def h : ContinuousRiemannianMetric F E :=
  metricOfForm (euclidForm + (3 : ℝ) • secondCoord)
    (fun u v ↦ by simp [euclidForm_apply, secondCoord_apply, real_inner_comm v u, mul_comm (u 1)])
    fun v ↦ by
      change ‖v‖ ^ 2 ≤ euclidForm v v + 3 * secondCoord v v
      rw [euclidForm_apply, secondCoord_apply, real_inner_self_eq_norm_sq]
      nlinarith [mul_self_nonneg (v 1)]

/-- The metric `4 g` on `ℝ²`. -/
def h₄ : ContinuousRiemannianMetric F E :=
  metricOfForm ((4 : ℝ) • euclidForm)
    (fun u v ↦ by simp [euclidForm_apply, real_inner_comm v u])
    fun v ↦ by
      change ‖v‖ ^ 2 ≤ 4 * euclidForm v v
      rw [euclidForm_apply, real_inner_self_eq_norm_sq]
      nlinarith [sq_nonneg ‖v‖]

/-- A vector of `ℝ²`, in the copy carrying the metric `k`. -/
def vec (k : ContinuousRiemannianMetric F E) (w : F) : WithFiberMetric k () :=
  toWithFiberMetric k () w

/-- The first basis vector `e₀`. -/
def e₀ : F := EuclideanSpace.single 0 1

/-- The vector `u = (1, 1)`. -/
def u : F := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1

theorem vec_u_ne_zero (k : ContinuousRiemannianMetric F E) : vec k u ≠ 0 := by
  rw [vec, Ne, (toWithFiberMetric k ()).map_eq_zero_iff]
  intro hu
  have := congrArg (fun w : F ↦ w 0) hu
  simp [u] at this

/-- The line `span(u)` in the copy of `ℝ²` carrying the metric `k`, recorded by its
`k`-orthogonal projection. -/
def P (k : ContinuousRiemannianMetric F E) : Euclidean.grassmannian ℝ (WithFiberMetric k ()) 1 :=
  Euclidean.grassmannian.spanLine ℝ (vec k u) (vec_u_ne_zero k)

/-- The `k`-orthogonal projection onto `span(u)` at `e₀`, read in `ℝ²`. -/
theorem P_apply_e₀ (k : ContinuousRiemannianMetric F E) :
    (toWithFiberMetric k ()).symm ((P k : WithFiberMetric k () →L[ℝ] WithFiberMetric k ())
      (vec k e₀)) = (k.inner () u e₀ / k.inner () u u) • u := by
  rw [P, Euclidean.grassmannian.coe_spanLine, Submodule.starProjection_singleton,
    ← real_inner_self_eq_norm_sq, vec, vec, inner_toWithFiberMetric, inner_toWithFiberMetric,
    map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- **Check.** The Euclidean orthogonal projection onto `span(u)` sends `e₀` to `u / 2`. -/
theorem P_g_apply_e₀ :
    (toWithFiberMetric g ()).symm ((P g : WithFiberMetric g () →L[ℝ] WithFiberMetric g ())
      (vec g e₀)) = (2 : ℝ)⁻¹ • u := by
  rw [P_apply_e₀]
  simp [g, metricOfForm_inner, euclidForm_apply, u, e₀, EuclideanSpace.inner_single_left]
  norm_num

/-- **Check.** The `h`-orthogonal projection onto `span(u)`, for `h = diag(1, 4)`, sends `e₀` to
`u / 5`. -/
theorem P_h_apply_e₀ :
    (toWithFiberMetric h ()).symm ((P h : WithFiberMetric h () →L[ℝ] WithFiberMetric h ())
      (vec h e₀)) = (5 : ℝ)⁻¹ • u := by
  rw [P_apply_e₀]
  simp [h, metricOfForm_inner, euclidForm_apply, secondCoord_apply, u, e₀,
    EuclideanSpace.inner_single_left]
  norm_num

/-- **Check.** The canonical homeomorphism `G_1^g ≃ₜ G_1^h` sends the Euclidean projection onto
`span(u)` to the `h`-orthogonal projection onto `span(u)`. -/
theorem metricChangeHomeomorph_P :
    grassmannBundle.metricChangeHomeomorph g h 1 (grassmannBundle.fiberIncl F _ 1 () (P g)) =
      grassmannBundle.fiberIncl F _ 1 () (P h) := by
  rw [grassmannBundle.metricChangeHomeomorph_fiberIncl]
  congr 1
  refine Euclidean.grassmannian.ext_range ?_
  rw [range_coe_grassmannianMap_metricChange, P, P, Euclidean.grassmannian.coe_spanLine,
    Euclidean.grassmannian.coe_spanLine, Submodule.range_starProjection,
    Submodule.range_starProjection, Submodule.map_span, Set.image_singleton]
  change ℝ ∙ (metricChange g h () (vec g u)) = _
  rw [metricChange_apply, vec, vec, toWithFiberMetric_apply, toWithFiberMetric_apply]

/-- **Check.** The canonical homeomorphism is not the identity on projections: at `e₀`, the image
`P^h` of `P^g` takes the value `u / 5`, while `P^g` takes the value `u / 2`. -/
theorem P_h_apply_e₀_ne :
    (toWithFiberMetric h ()).symm ((P h : WithFiberMetric h () →L[ℝ] WithFiberMetric h ())
      (vec h e₀)) ≠
      (toWithFiberMetric g ()).symm ((P g : WithFiberMetric g () →L[ℝ] WithFiberMetric g ())
        (vec g e₀)) := by
  rw [P_h_apply_e₀, P_g_apply_e₀]
  intro hne
  have := congrArg (fun w : F ↦ w 0) hne
  simp [u] at this

/-- **Check.** For `4 g` the canonical homeomorphism `G_1^g ≃ₜ G_1^{4g}` is the identity on
projections, read through the change of metric. -/
theorem coe_metricChangeHomeomorph_four (p : grassmannBundle F (WithFiberMetric g) 1) :
    (grassmannBundle.metricChangeHomeomorph g h₄ 1 p).val =
      ⟨p.val.proj, (metricChange g h₄ p.val.proj : _ →L[ℝ] _) ∘L p.val.snd ∘L
        (metricChange h₄ g p.val.proj : _ →L[ℝ] _)⟩ :=
  grassmannBundle.coe_metricChangeHomeomorph_of_inner_eq (c := 2)
    (fun b u v ↦ by
      rw [h₄, g, metricOfForm_inner, metricOfForm_inner]
      change 4 * euclidForm u v = _
      norm_num) p

end TauCeti.Examples.GrassmannBundleMetricChange
