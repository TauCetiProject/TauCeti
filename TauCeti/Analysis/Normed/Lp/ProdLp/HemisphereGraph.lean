/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The hemispheres of the unit sphere of `WithLp 2 (E × ℝ)` as graphs

Let `E` be a real normed space, say `E = ℝᵏ⁺¹`. The closed upper and lower hemispheres of the
unit sphere `S^(k+1)` of the `L²` product `WithLp 2 (E × ℝ)` are the graphs of
`u ↦ ±√(1 - ‖u‖ ^ 2)` over the closed unit ball `D^(k+1)` of `E`. For a sign `c` (that is,
`c ^ 2 = 1`), `TauCeti.prodHemisphereGraph` sends a point `u` of the ball to
`(u, c √(1 - ‖u‖ ^ 2))`. Each hemisphere is a closed embedding of the ball, the two hemispheres
cover the sphere, agree on the equator `‖u‖ = 1`, and meet only there.

For `E = ℂ`, moved into `ℝ³` by the linear isometry `(u, t) ↦ (Re u, Im u, t)`, these are the
hemispheres `TauCeti.hemisphereGraph` of `S² ⊆ ℝ³` over the closed unit disc of `ℂ`.

## Main definitions

* `TauCeti.prodHemisphereGraphPoint c u`: the point `(u, c √(1 - ‖u‖ ^ 2))` of `WithLp 2 (E × ℝ)`.
* `TauCeti.prodHemisphereGraph hc`: the hemisphere of sign `c` of the unit sphere of
  `WithLp 2 (E × ℝ)`, as a map from the closed unit ball of `E`.

## Main results

* `TauCeti.isClosedEmbedding_prodHemisphereGraph`: each hemisphere is a closed embedding of the
  closed unit ball.
* `TauCeti.eq_of_prodHemisphereGraph_eq`: a point of a hemisphere determines the point of the
  ball.
* `TauCeti.prodHemisphereGraph_eq_of_norm_eq_one`: the hemispheres agree on the equator.
* `TauCeti.norm_eq_one_of_prodHemisphereGraph_eq`: hemispheres of opposite signs meet only over
  the boundary of the ball.
* `TauCeti.exists_prodHemisphereGraph_eq`: every point of the unit sphere lies on the hemisphere
  of the sign of its last coordinate.
-/

public section

noncomputable section

open Metric Topology

namespace TauCeti

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The point `(u, c √(1 - ‖u‖ ^ 2))` of `WithLp 2 (E × ℝ)`; for `c = 1` and `c = -1` and `u` in
the closed unit ball this is the upper and the lower hemisphere of the unit sphere. -/
def prodHemisphereGraphPoint (c : ℝ) (u : E) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (u, c * √(1 - ‖u‖ ^ 2))

/-- `TauCeti.prodHemisphereGraphPoint c u` is the point `(u, c √(1 - ‖u‖ ^ 2))`. -/
theorem prodHemisphereGraphPoint_def (c : ℝ) (u : E) :
    prodHemisphereGraphPoint c u = WithLp.toLp 2 (u, c * √(1 - ‖u‖ ^ 2)) :=
  (rfl)

/-- The first component of `TauCeti.prodHemisphereGraphPoint c u` is `u`. -/
@[simp]
theorem prodHemisphereGraphPoint_fst (c : ℝ) (u : E) : (prodHemisphereGraphPoint c u).fst = u :=
  (rfl)

/-- The last coordinate of `TauCeti.prodHemisphereGraphPoint c u` is `c √(1 - ‖u‖ ^ 2)`. -/
@[simp]
theorem prodHemisphereGraphPoint_snd (c : ℝ) (u : E) :
    (prodHemisphereGraphPoint c u).snd = c * √(1 - ‖u‖ ^ 2) :=
  (rfl)

/-- For a sign `c`, the points `TauCeti.prodHemisphereGraphPoint c u` over the closed unit ball lie
on the unit sphere. -/
theorem prodHemisphereGraphPoint_mem_sphere {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : E) 1) :
    prodHemisphereGraphPoint c (u : E) ∈ sphere (0 : WithLp 2 (E × ℝ)) 1 := by
  have hu : ‖(u : E)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp u.2)
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    WithLp.prod_norm_sq_eq_of_L2, prodHemisphereGraphPoint_fst, prodHemisphereGraphPoint_snd,
    Real.norm_eq_abs, sq_abs, mul_pow, hc, one_mul, Real.sq_sqrt (sub_nonneg.mpr hu)]
  ring

/-- The hemisphere of sign `c` of the unit sphere of `WithLp 2 (E × ℝ)`, the graph of
`u ↦ c √(1 - ‖u‖ ^ 2)` over the closed unit ball of `E`. -/
def prodHemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : E) 1) :
    sphere (0 : WithLp 2 (E × ℝ)) 1 :=
  ⟨prodHemisphereGraphPoint c u, prodHemisphereGraphPoint_mem_sphere hc u⟩

/-- `TauCeti.prodHemisphereGraph hc u` is the point `TauCeti.prodHemisphereGraphPoint c u`. -/
@[simp]
theorem coe_prodHemisphereGraph_apply {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : E) 1) :
    (prodHemisphereGraph hc u : WithLp 2 (E × ℝ)) = prodHemisphereGraphPoint c (u : E) :=
  (rfl)

/-- The hemisphere graphs are continuous. -/
@[fun_prop]
theorem continuous_prodHemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) :
    Continuous (prodHemisphereGraph (E := E) hc) := by
  refine Continuous.subtype_mk ((WithLp.prod_continuous_toLp 2 E ℝ).comp ?_) _
  fun_prop

/-- The first component of a point of a hemisphere recovers the point of the ball, whatever the
signs of the two hemispheres. -/
theorem eq_of_prodHemisphereGraph_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    {u v : closedBall (0 : E) 1} (h : prodHemisphereGraph hc u = prodHemisphereGraph hc' v) :
    u = v :=
  Subtype.ext (by
    simpa using congrArg (fun x : sphere (0 : WithLp 2 (E × ℝ)) 1 ↦
      (x : WithLp 2 (E × ℝ)).fst) h)

/-- Each hemisphere graph is injective. -/
theorem prodHemisphereGraph_injective {c : ℝ} (hc : c ^ 2 = 1) :
    Function.Injective (prodHemisphereGraph (E := E) hc) :=
  fun _ _ h ↦ eq_of_prodHemisphereGraph_eq h

/-- The hemispheres of any two signs agree on the equator. -/
theorem prodHemisphereGraph_eq_of_norm_eq_one {c c' : ℝ} (hc : c ^ 2 = 1) (hc' : c' ^ 2 = 1)
    {u : closedBall (0 : E) 1} (hu : ‖(u : E)‖ = 1) :
    prodHemisphereGraph hc u = prodHemisphereGraph hc' u := by
  simp [prodHemisphereGraph, prodHemisphereGraphPoint_def, hu]

/-- Hemispheres of opposite signs meet only over the boundary of the ball. -/
theorem norm_eq_one_of_prodHemisphereGraph_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    (hcc' : c ≠ c') {u v : closedBall (0 : E) 1}
    (h : prodHemisphereGraph hc u = prodHemisphereGraph hc' v) : ‖(v : E)‖ = 1 := by
  have huv := eq_of_prodHemisphereGraph_eq h
  subst huv
  have h2 := congrArg (fun x : sphere (0 : WithLp 2 (E × ℝ)) 1 ↦ (x : WithLp 2 (E × ℝ)).snd) h
  simp only [coe_prodHemisphereGraph_apply, prodHemisphereGraphPoint_snd] at h2
  have hs : √(1 - ‖(u : E)‖ ^ 2) = 0 :=
    (mul_eq_zero.mp (by linarith : (c - c') * √(1 - ‖(u : E)‖ ^ 2) = 0)).resolve_left
      (sub_ne_zero.mpr hcc')
  rw [Real.sqrt_eq_zero', sub_nonpos] at hs
  exact le_antisymm (mem_closedBall_zero_iff.mp u.2) ((one_le_sq_iff₀ (norm_nonneg _)).mp hs)

/-- Every point `x` of the unit sphere of `WithLp 2 (E × ℝ)` with `0 ≤ c x.snd` lies on the
hemisphere of sign `c`, over the point `x.fst` of the ball. -/
theorem exists_prodHemisphereGraph_eq {c : ℝ} (hc : c ^ 2 = 1)
    (x : sphere (0 : WithLp 2 (E × ℝ)) 1) (hx : 0 ≤ c * (x : WithLp 2 (E × ℝ)).snd) :
    ∃ u, prodHemisphereGraph hc u = x := by
  obtain ⟨w, hw⟩ := x
  have hsum : ‖w.fst‖ ^ 2 + w.snd ^ 2 = 1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 w
    rwa [mem_sphere_zero_iff_norm.1 hw, one_pow, Real.norm_eq_abs, sq_abs, eq_comm] at h
  have hu : w.fst ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg w.fst, sq_nonneg w.snd]
  have hroot : √(1 - ‖w.fst‖ ^ 2) = |w.snd| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    linarith
  refine ⟨⟨w.fst, hu⟩, Subtype.ext ?_⟩
  rw [coe_prodHemisphereGraph_apply, prodHemisphereGraphPoint_def, hroot]
  have hc' : c * |w.snd| = w.snd := by
    rcases mul_self_eq_one_iff.mp ((sq c).symm.trans hc) with rfl | rfl
    · rw [one_mul, abs_of_nonneg (by simpa using hx)]
    · rw [neg_one_mul, abs_of_nonpos (by linarith), neg_neg]
  rw [hc']
  simp only [← WithLp.ofLp_fst, ← WithLp.ofLp_snd, Prod.mk.eta, WithLp.toLp_ofLp]

end Seminormed

variable {E : Type*} [NormedAddCommGroup E]

/-- Each hemisphere graph is a closed embedding of the closed unit ball into the unit sphere of
`WithLp 2 (E × ℝ)`; its left inverse is the projection to the first component. -/
theorem isClosedEmbedding_prodHemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) :
    IsClosedEmbedding (prodHemisphereGraph (E := E) hc) := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun x : sphere (0 : WithLp 2 (E × ℝ)) 1 ↦ (⟨(x : WithLp 2 (E × ℝ)).fst,
      mem_closedBall_zero_iff.2
        ((WithLp.norm_fst_le (x := (x : WithLp 2 (E × ℝ)))).trans (norm_eq_of_mem_sphere x).le)⟩ :
        closedBall (0 : E) 1))
    (fun _ ↦ rfl) (.subtype_mk ?_ _) (continuous_prodHemisphereGraph hc)
  fun_prop

end TauCeti
