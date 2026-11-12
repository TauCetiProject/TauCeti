/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Lp.ProdLp.HemisphereGraph
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The hemispheres of `S²` as graphs over the unit disc

The closed upper and lower hemispheres of the unit sphere `S² ⊆ ℝ³` are the graphs of
`u ↦ ±√(1 - ‖u‖²)` over the closed unit disc of `ℂ`, identified with the plane `x₂ = 0` by
`u ↦ (Re u, Im u)`. For a sign `c` (that is, `c ^ 2 = 1`), `TauCeti.hemisphereGraph` sends a point
`u` of the disc to `(Re u, Im u, c √(1 - ‖u‖²))`. The two hemispheres cover the sphere, agree on
the equator `‖u‖ = 1`, and meet only there.

These are the hemispheres `TauCeti.prodHemisphereGraph` of the unit sphere of `WithLp 2 (ℂ × ℝ)`,
moved into `ℝ³` by the linear isometry `TauCeti.complexProdRealLinearIsometryEquiv`,
`(u, t) ↦ (Re u, Im u, t)`, and their properties are derived from the general ones there. They
are also the coordinate form, over the unit disc of `ℂ`, of the inverse of
`TauCeti.hemisphereHomeomorph`, which parametrizes the closed hemisphere around any unit vector
`p` of a real inner product space by the closed unit ball of `(ℝ ∙ p)ᗮ`. The disc of `ℂ` is the one
used by `D² × S¹` solid tori, so these graphs are the solid tori `S¹ × D²₊` and `S¹ × D²₋` of
`S¹ × S²`.

## Main definitions

* `TauCeti.complexProdRealLinearIsometryEquiv`: the linear isometry `WithLp 2 (ℂ × ℝ) ≃ ℝ³`,
  `(u, t) ↦ (Re u, Im u, t)`.
* `TauCeti.hemisphereGraphPoint c u`: the point `(Re u, Im u, c √(1 - ‖u‖²))` of `ℝ³`.
* `TauCeti.hemisphereGraph hc`: the hemisphere of sign `c` of `S²`, as a map from the closed unit
  disc of `ℂ`.

## Main results

* `TauCeti.eq_of_hemisphereGraph_eq`: a point of a hemisphere determines the point of the disc.
* `TauCeti.hemisphereGraph_eq_of_norm_eq_one`: the hemispheres agree on the equator.
* `TauCeti.norm_eq_one_of_hemisphereGraph_eq`: hemispheres of opposite signs meet only over the
  boundary of the disc.
* `TauCeti.exists_hemisphereGraph_eq`: every point of `S²` lies on the hemisphere of the sign of
  its last coordinate.
-/

public section

noncomputable section

open Metric

namespace TauCeti

/-- The linear isometry `WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] ℝ³` sending `(u, t)` to `(Re u, Im u, t)`. -/
def complexProdRealLinearIsometryEquiv : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := !₂[x.fst.re, x.fst.im, x.snd]
  invFun y := WithLp.toLp 2 (⟨y 0, y 1⟩, y 2)
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  left_inv x := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Complex.eta, ← WithLp.ofLp_fst, ← WithLp.ofLp_snd, Prod.mk.eta,
      WithLp.toLp_ofLp]
  right_inv y := by
    ext i
    fin_cases i <;> simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
    ring

/-- `TauCeti.complexProdRealLinearIsometryEquiv` sends `(u, t)` to `(Re u, Im u, t)`. -/
@[simp]
theorem complexProdRealLinearIsometryEquiv_apply (x : WithLp 2 (ℂ × ℝ)) :
    complexProdRealLinearIsometryEquiv x = !₂[x.fst.re, x.fst.im, x.snd] :=
  (rfl)

/-- The inverse of `TauCeti.complexProdRealLinearIsometryEquiv` sends `(x₀, x₁, x₂)` to
`(x₀ + i x₁, x₂)`. -/
@[simp]
theorem complexProdRealLinearIsometryEquiv_symm_apply (y : EuclideanSpace ℝ (Fin 3)) :
    complexProdRealLinearIsometryEquiv.symm y = WithLp.toLp 2 (⟨y 0, y 1⟩, y 2) :=
  (rfl)

/-- The point `(Re u, Im u, c √(1 - ‖u‖²))` of `ℝ³`, the image of
`TauCeti.prodHemisphereGraphPoint c u` under `TauCeti.complexProdRealLinearIsometryEquiv`; for
`c = 1` and `c = -1` and `u` in the closed unit disc this is the upper and the lower hemisphere of
`S²`. -/
def hemisphereGraphPoint (c : ℝ) (u : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  complexProdRealLinearIsometryEquiv (prodHemisphereGraphPoint c u)

/-- The first coordinate of `TauCeti.hemisphereGraphPoint c u` is the real part of `u`. -/
@[simp]
theorem hemisphereGraphPoint_apply_zero (c : ℝ) (u : ℂ) : hemisphereGraphPoint c u 0 = u.re := by
  simp [hemisphereGraphPoint]

/-- The second coordinate of `TauCeti.hemisphereGraphPoint c u` is the imaginary part of `u`. -/
@[simp]
theorem hemisphereGraphPoint_apply_one (c : ℝ) (u : ℂ) : hemisphereGraphPoint c u 1 = u.im := by
  simp [hemisphereGraphPoint]

/-- The last coordinate of `TauCeti.hemisphereGraphPoint c u` is `c √(1 - ‖u‖²)`. -/
@[simp]
theorem hemisphereGraphPoint_apply_two (c : ℝ) (u : ℂ) :
    hemisphereGraphPoint c u 2 = c * √(1 - ‖u‖ ^ 2) := by
  simp [hemisphereGraphPoint]

/-- For a sign `c`, the points `TauCeti.hemisphereGraphPoint c u` over the closed unit disc lie on
the unit sphere. -/
theorem hemisphereGraphPoint_mem_sphere {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    hemisphereGraphPoint c u ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (LinearIsometryEquiv.map_mem_unitSphere_iff _ _).2 (prodHemisphereGraphPoint_mem_sphere hc u)

/-- The hemisphere of `S²` of sign `c`, the graph of `u ↦ c √(1 - ‖u‖²)` over the closed unit
disc of `ℂ`: the hemisphere `TauCeti.prodHemisphereGraph hc` of the unit sphere of
`WithLp 2 (ℂ × ℝ)`, moved into `ℝ³` by `TauCeti.complexProdRealLinearIsometryEquiv`. -/
def hemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  complexProdRealLinearIsometryEquiv.unitSphereEquiv (prodHemisphereGraph hc u)

/-- `TauCeti.hemisphereGraph hc u` is the point `TauCeti.hemisphereGraphPoint c u`. -/
@[simp]
theorem coe_hemisphereGraph_apply {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    (hemisphereGraph hc u : EuclideanSpace ℝ (Fin 3)) = hemisphereGraphPoint c u := by
  simp [hemisphereGraph, hemisphereGraphPoint]

/-- The hemisphere graphs are continuous. -/
@[fun_prop]
theorem continuous_hemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) : Continuous (hemisphereGraph hc) :=
  (LinearIsometryEquiv.isometry_unitSphereEquiv _).continuous.comp
    (continuous_prodHemisphereGraph hc)

/-- The first two coordinates of a point of a hemisphere recover the point of the disc, whatever
the signs of the two hemispheres. -/
theorem eq_of_hemisphereGraph_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    {u v : closedBall (0 : ℂ) 1} (h : hemisphereGraph hc u = hemisphereGraph hc' v) : u = v :=
  eq_of_prodHemisphereGraph_eq (Equiv.injective _ h)

/-- The hemispheres of any two signs agree on the equator. -/
theorem hemisphereGraph_eq_of_norm_eq_one {c c' : ℝ} (hc : c ^ 2 = 1) (hc' : c' ^ 2 = 1)
    {u : closedBall (0 : ℂ) 1} (hu : ‖(u : ℂ)‖ = 1) :
    hemisphereGraph hc u = hemisphereGraph hc' u :=
  congrArg _ (prodHemisphereGraph_eq_of_norm_eq_one hc hc' hu)

/-- Hemispheres of opposite signs meet only over the boundary of the disc. -/
theorem norm_eq_one_of_hemisphereGraph_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    (hcc' : c ≠ c') {u v : closedBall (0 : ℂ) 1}
    (h : hemisphereGraph hc u = hemisphereGraph hc' v) : ‖(v : ℂ)‖ = 1 :=
  norm_eq_one_of_prodHemisphereGraph_eq hcc' (Equiv.injective _ h)

/-- Every point of `S²` whose last coordinate `x₂` has `0 ≤ c x₂` lies on the hemisphere of sign
`c`, over the point `x₀ + i x₁` of the disc. -/
theorem exists_hemisphereGraph_eq {c : ℝ} (hc : c ^ 2 = 1)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hx : 0 ≤ c * (x : EuclideanSpace ℝ (Fin 3)) 2) : ∃ u, hemisphereGraph hc u = x := by
  obtain ⟨u, hu⟩ := exists_prodHemisphereGraph_eq hc
    (complexProdRealLinearIsometryEquiv.unitSphereEquiv.symm x) (by simpa using hx)
  exact ⟨u, by rw [hemisphereGraph, hu, Equiv.apply_symm_apply]⟩

end TauCeti
