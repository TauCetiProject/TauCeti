/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Geometry.Manifold.Morse.Cell.Map
public import TauCeti.Geometry.Sphere.Circle
public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.Sphere.StandardCircle
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Circle
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Projectivization
import TauCeti.Geometry.Manifold.Projectivization.Map

/-!
# Morse cells of the real projective plane with attaching maps of degree `±2`

On the real projective plane `ℝP² = ℙ ℝ (Fin 3 → ℝ)` consider the height
`f [x : y : z] = (y² + 2z²) / (x² + y² + z²)` (`TauCeti.projectivePlaneHeight`), with minimum
`[1 : 0 : 0]`, saddle `[0 : 1 : 0]` and maximum `[0 : 0 : 1]` at the values `0`, `1`, `2`. This
file computes the cell attached when passing the maximum, as an example of how the attaching maps
of Morse cells (`OpenPartialHomeomorph.morseAttachingMap`) depend on the chosen normal-form chart.

In the affine coordinates `a = x / z`, `b = y / z` around the maximum, the chart
`(a, b) ↦ (√2 a, b) / √(1 + a² + b²)` (`TauCeti.projectivePlaneTopChart`) has target the ellipse
`u₀² / 2 + u₁² < 1` and puts `f` in the normal form `f = 2 - u₀² - u₁²` of index `2`. So does its
composite with the reflection `(u₀, u₁) ↦ (-u₀, u₁)` of the first negative coordinate
(`TauCeti.projectivePlaneTopChartReflect`). For `0 < ε < 1` both targets contain the closed disc
of radius `√ε`, and the two charts give attaching maps `α₊, α₋ : ∂D² → {f ≤ 2 - ε}` of the
`2`-cell (`TauCeti.projectivePlaneAttachingMap`, `TauCeti.projectivePlaneAttachingMapReflect`),
`w ↦ [√ε w₀ / √2 : √ε w₁ : √(1 - ε (w₀² / 2 + w₁²))]` and its reflection. They are related
strictly by the reflection `r` of the circle (`TauCeti.diskBoundaryTwoReflect`): `α₋ = α₊ ∘ r`
(`TauCeti.projectivePlaneAttachingMapReflect_eq_comp`).

The lower sublevel `{f ≤ c}`, `1 ≤ c < 2`, misses the maximum, and the flattening
`[x : y : z] ↦ [x : y : (1 - t) z]` lowers `f`. So the projection `[x : y : z] ↦ [x : y]` is a
homotopy equivalence onto the projective line `z = 0`
(`TauCeti.projectivePlaneSublevelHomotopyEquiv`), which is a circle by
`[x : y] ↦ (x + i y)² / (x² + y²)` (`TauCeti.projectivePlaneSublevelCircleEquiv`). The core circle
`t ↦ [cos πt : sin πt : 0]` (`TauCeti.projectivePlaneCoreLoop`) has degree `1` in this circle, and
so generates `π₁({f ≤ c})` (`TauCeti.zpowers_projectivePlaneCoreLoop_eq_top`). Read along the
counterclockwise loop of `∂D²` (`TauCeti.diskBoundaryTwoLoop`), the attaching map `α₊` has degree
`2` and `α₋` has degree `-2` (`TauCeti.degree_projectivePlaneAttachingMap`,
`TauCeti.degree_projectivePlaneAttachingMapReflect`): `α₊` is the core circle run twice and `α₋`
the reversed core circle run twice, up to homotopy and conjugation
(`TauCeti.homotopic_projectivePlaneAttachingMap`,
`TauCeti.homotopic_projectivePlaneAttachingMapReflect`). In particular `α₊` and `α₋` are not
homotopic with their labelled source fixed
(`TauCeti.not_homotopic_projectivePlaneAttachingMap_reflect`), although they differ only by the
reflection `r` of their source.

## Main results

* `TauCeti.projectivePlaneHeight_eq_of_mem_projectivePlaneTopChart_source`: the normal form at the
  maximum.
* `TauCeti.projectivePlaneAttachingMapReflect_eq_comp`: the strict relation `α₋ = α₊ ∘ r`.
* `TauCeti.projectivePlaneSublevelHomotopyEquiv`, `TauCeti.projectivePlaneSublevelCircleEquiv`:
  the sublevels below the maximum are homotopy equivalent to the projective line and the circle.
* `TauCeti.degree_projectivePlaneAttachingMap`, `TauCeti.degree_projectivePlaneAttachingMapReflect`:
  the attaching maps have degrees `2` and `-2`.
* `TauCeti.not_homotopic_projectivePlaneAttachingMap_reflect`: the two attaching maps are not
  homotopic.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (Theorem 3.2, Remark 3.3 and Lemma 3.6).
-/

public section

noncomputable section

open Set Metric Projectivization unitInterval
open scoped ContinuousMap Real
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-- The height `[x : y : z] ↦ (y² + 2z²) / (x² + y² + z²)` on the real projective plane. -/
def projectivePlaneHeight : ℙ ℝ (Fin 3 → ℝ) → ℝ :=
  Projectivization.lift
    (fun v ↦ (v.1 1 ^ 2 + 2 * v.1 2 ^ 2) / (v.1 0 ^ 2 + v.1 1 ^ 2 + v.1 2 ^ 2))
    fun a b t h ↦ by
      have ht : t ≠ 0 := by
        rintro rfl
        exact a.2 (by simpa using h)
      simp only [h, Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [show t ^ 2 * b.1 1 ^ 2 + 2 * (t ^ 2 * b.1 2 ^ 2) = t ^ 2 * (b.1 1 ^ 2 + 2 * b.1 2 ^ 2)
        by ring, show t ^ 2 * b.1 0 ^ 2 + t ^ 2 * b.1 1 ^ 2 + t ^ 2 * b.1 2 ^ 2 =
          t ^ 2 * (b.1 0 ^ 2 + b.1 1 ^ 2 + b.1 2 ^ 2) by ring]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

@[simp]
theorem projectivePlaneHeight_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectivePlaneHeight (mk ℝ v hv) = (v 1 ^ 2 + 2 * v 2 ^ 2) / (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) :=
  (rfl)

/-- The nonzero homogeneous coordinates `(u₀ / √2, u₁, √(1 - u₀² / 2 - u₁²))` of the inverse of
the top chart: they are nonzero everywhere, since the last one vanishes only when `(u₀, u₁) ≠ 0`. -/
private theorem topChartInvVec_ne_zero (u : EuclideanSpace ℝ (Fin 2)) :
    ![u 0 / √2, u 1, √(1 - (u 0 ^ 2 / 2 + u 1 ^ 2))] ≠ 0 := by
  intro h
  have h0 : u 0 / √2 = 0 := congrFun h 0
  have h1 : u 1 = 0 := congrFun h 1
  have h2 : √(1 - (u 0 ^ 2 / 2 + u 1 ^ 2)) = 0 := congrFun h 2
  have hu0 : u 0 = 0 := by simpa [Real.sqrt_ne_zero'] using h0
  simp [hu0, h1] at h2

/-- The top chart in the affine coordinates `a = (x / z, y / z)`. -/
private def topChartPlane (a : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (√(1 + a 0 ^ 2 + a 1 ^ 2))⁻¹ • !₂[√2 * a 0, a 1]

private theorem topChartPlane_apply_zero (a : Fin 2 → ℝ) :
    topChartPlane a 0 = √2 * a 0 / √(1 + a 0 ^ 2 + a 1 ^ 2) := by
  simp [topChartPlane, div_eq_inv_mul]

private theorem topChartPlane_apply_one (a : Fin 2 → ℝ) :
    topChartPlane a 1 = a 1 / √(1 + a 0 ^ 2 + a 1 ^ 2) := by
  simp [topChartPlane, div_eq_inv_mul]

private theorem continuous_topChartPlane : Continuous topChartPlane := by
  have hs : Continuous fun a : Fin 2 → ℝ ↦ √(1 + a 0 ^ 2 + a 1 ^ 2) := by fun_prop
  refine Continuous.smul (hs.inv₀ fun a ↦ ?_) ?_
  · exact Real.sqrt_ne_zero'.2 (by positivity)
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
    fin_cases i
    · exact continuous_const.mul (continuous_apply 0)
    · exact continuous_apply 1

private theorem topChartPlane_ellipse (a : Fin 2 → ℝ) :
    topChartPlane a 0 ^ 2 / 2 + topChartPlane a 1 ^ 2 =
      (a 0 ^ 2 + a 1 ^ 2) / (1 + a 0 ^ 2 + a 1 ^ 2) := by
  have hs : 0 < 1 + a 0 ^ 2 + a 1 ^ 2 := by positivity
  rw [topChartPlane_apply_zero, topChartPlane_apply_one, div_pow, div_pow, mul_pow,
    Real.sq_sqrt hs.le, Real.sq_sqrt zero_le_two]
  field_simp

private theorem topChartPlane_normSq (a : Fin 2 → ℝ) :
    topChartPlane a 0 ^ 2 + topChartPlane a 1 ^ 2 =
      (2 * a 0 ^ 2 + a 1 ^ 2) / (1 + a 0 ^ 2 + a 1 ^ 2) := by
  have hs : 0 < 1 + a 0 ^ 2 + a 1 ^ 2 := by positivity
  rw [topChartPlane_apply_zero, topChartPlane_apply_one, div_pow, div_pow, mul_pow,
    Real.sq_sqrt hs.le, Real.sq_sqrt zero_le_two]
  field_simp

private theorem affineChart_two_mk_zero (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    affineChart 2 (mk ℝ v hv) 0 = v 0 / v 2 := by
  rw [affineChart_mk]
  rfl

private theorem affineChart_two_mk_one (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    affineChart 2 (mk ℝ v hv) 1 = v 1 / v 2 := by
  rw [affineChart_mk]
  rfl

/-- The normalized Morse chart of `projectivePlaneHeight` at its maximum `[0 : 0 : 1]`: in the
affine coordinates `a = x / z`, `b = y / z` it is `(√2 a, b) / √(1 + a² + b²)`. Its target is the
open ellipse `u₀² / 2 + u₁² < 1`, and its inverse is
`u ↦ [u₀ / √2 : u₁ : √(1 - u₀² / 2 - u₁²)]`. -/
def projectivePlaneTopChart :
    OpenPartialHomeomorph (ℙ ℝ (Fin 3 → ℝ)) (EuclideanSpace ℝ (Fin 2)) where
  toFun y := topChartPlane (affineChart 2 y)
  invFun u := mk ℝ ![u 0 / √2, u 1, √(1 - (u 0 ^ 2 / 2 + u 1 ^ 2))] (topChartInvVec_ne_zero u)
  source := affineOpen 2
  target := {u | u 0 ^ 2 / 2 + u 1 ^ 2 < 1}
  map_source' y _ := by
    rw [mem_ofPred_eq, topChartPlane_ellipse, div_lt_one (by positivity)]
    linarith
  map_target' u hu := by
    rw [mk_mem_affineOpen_iff]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, ne_eq,
      Real.sqrt_eq_zero', not_le, sub_pos]
    exact hu
  left_inv' y hy := by
    induction y using ind with | h v hv =>
    rw [mk_mem_affineOpen_iff] at hy
    set a := affineChart 2 (mk ℝ v hv)
    have hs : 0 < 1 + a 0 ^ 2 + a 1 ^ 2 := by positivity
    have hr : √(1 - (topChartPlane a 0 ^ 2 / 2 + topChartPlane a 1 ^ 2)) =
        1 / √(1 + a 0 ^ 2 + a 1 ^ 2) := by
      rw [topChartPlane_ellipse, show 1 - (a 0 ^ 2 + a 1 ^ 2) / (1 + a 0 ^ 2 + a 1 ^ 2) =
        1 / (1 + a 0 ^ 2 + a 1 ^ 2) by field_simp; ring, Real.sqrt_div zero_le_one, Real.sqrt_one]
    rw [mk_eq_mk_iff']
    refine ⟨1 / (√(1 + a 0 ^ 2 + a 1 ^ 2) * v 2), ?_⟩
    have ha0 : a 0 = v 0 / v 2 := affineChart_two_mk_zero v hv
    have ha1 : a 1 = v 1 / v 2 := affineChart_two_mk_one v hv
    have hsq : √(1 + a 0 ^ 2 + a 1 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hs
    ext i
    fin_cases i
    · simp [topChartPlane_apply_zero, ha0]
      field_simp
    · simp [topChartPlane_apply_one, ha1]
      field_simp
    · simp [hr]
      field_simp
  right_inv' u hu := by
    have hρ : u 0 ^ 2 / 2 + u 1 ^ 2 < 1 := hu
    set r := √(1 - (u 0 ^ 2 / 2 + u 1 ^ 2))
    have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hr2 : r ^ 2 = 1 - (u 0 ^ 2 / 2 + u 1 ^ 2) := Real.sq_sqrt (by linarith)
    set a := affineChart 2 (mk ℝ ![u 0 / √2, u 1, r] (topChartInvVec_ne_zero u))
    have ha0 : a 0 = u 0 / √2 / r := affineChart_two_mk_zero _ _
    have ha1 : a 1 = u 1 / r := affineChart_two_mk_one _ _
    have hs : √(1 + a 0 ^ 2 + a 1 ^ 2) = 1 / r := by
      rw [ha0, ha1, div_pow, div_pow, div_pow, Real.sq_sqrt zero_le_two]
      rw [show 1 + u 0 ^ 2 / 2 / r ^ 2 + u 1 ^ 2 / r ^ 2 = (1 / r) ^ 2 by
        field_simp
        linarith]
      exact Real.sqrt_sq (by positivity)
    refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [topChartPlane_apply_zero, hs, ha0]
      field_simp
    · rw [topChartPlane_apply_one, hs, ha1]
      field_simp
  open_source := isOpen_affineOpen 2
  open_target := isOpen_lt (by fun_prop) continuous_const
  continuousOn_toFun := continuous_topChartPlane.comp_continuousOn (continuousOn_affineChart 2)
  continuousOn_invFun := (continuous_mk (by fun_prop) _).continuousOn

@[simp]
theorem projectivePlaneTopChart_source : projectivePlaneTopChart.source = affineOpen 2 :=
  (rfl)

@[simp]
theorem projectivePlaneTopChart_target :
    projectivePlaneTopChart.target = {u | u 0 ^ 2 / 2 + u 1 ^ 2 < 1} :=
  (rfl)

/-- The top chart in homogeneous coordinates: with `a = x / z` and `b = y / z`, it sends
`[x : y : z]` to `(√2 a, b) / √(1 + a² + b²)`. -/
theorem projectivePlaneTopChart_apply_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectivePlaneTopChart (mk ℝ v hv) = (√(1 + (v 0 / v 2) ^ 2 + (v 1 / v 2) ^ 2))⁻¹ •
      !₂[√2 * (v 0 / v 2), v 1 / v 2] := by
  rw [← affineChart_two_mk_zero v hv, ← affineChart_two_mk_one v hv]
  rfl

/-- The inverse of the top chart in homogeneous coordinates:
`u ↦ [u₀ / √2 : u₁ : √(1 - u₀² / 2 - u₁²)]`. -/
theorem projectivePlaneTopChart_symm_apply (u : EuclideanSpace ℝ (Fin 2))
    (hu : ![u 0 / √2, u 1, √(1 - (u 0 ^ 2 / 2 + u 1 ^ 2))] ≠ 0) :
    projectivePlaneTopChart.symm u = mk ℝ ![u 0 / √2, u 1, √(1 - (u 0 ^ 2 / 2 + u 1 ^ 2))] hu :=
  (rfl)

/-- The chart sends the maximum `[0 : 0 : 1]` to the origin. -/
theorem projectivePlaneTopChart_symm_zero :
    projectivePlaneTopChart.symm 0 = mk ℝ ![0, 0, 1] (by simp) := by
  rw [projectivePlaneTopChart_symm_apply _ (topChartInvVec_ne_zero 0)]
  simp

/-- **The normal form at the maximum.** In the top chart the height is
`2 - u₀² - u₁²`, the normal form `c - Σ_{j < 2} uⱼ²` of index `2` at the value `c = 2`. -/
theorem projectivePlaneHeight_eq_of_mem_projectivePlaneTopChart_source {y : ℙ ℝ (Fin 3 → ℝ)}
    (hy : y ∈ projectivePlaneTopChart.source) :
    projectivePlaneHeight y = 2 + ∑ j : Fin 2,
      (if j.val < 2 then -1 else 1) * projectivePlaneTopChart y j ^ 2 := by
  induction y using ind with | h v hv =>
  rw [projectivePlaneTopChart_source, mk_mem_affineOpen_iff] at hy
  have hcoe : ∀ y, projectivePlaneTopChart y = topChartPlane (affineChart 2 y) := fun _ ↦ rfl
  have key := topChartPlane_normSq (affineChart 2 (mk ℝ v hv))
  rw [affineChart_two_mk_zero, affineChart_two_mk_one] at key
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.ofNat_pos, ↓reduceIte,
    Nat.one_lt_ofNat, hcoe, neg_one_mul, projectivePlaneHeight_mk]
  rw [← neg_add, ← sub_eq_add_neg, key]
  have hs : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by positivity
  field_simp
  ring

/-- The target of the top chart contains the closed ball of radius `√ε` for `ε < 1`: the ellipse
`u₀² / 2 + u₁² < 1` contains the open unit disc. -/
theorem closedBall_subset_projectivePlaneTopChart_target {ε : ℝ} (hε : ε < 1) :
    closedBall 0 √ε ⊆ projectivePlaneTopChart.target := fun u hu ↦ by
  have h := EuclideanSpace.real_norm_sq_eq u
  rw [Fin.sum_univ_two] at h
  have hu' : ‖u‖ ^ 2 ≤ √ε ^ 2 := pow_le_pow_left₀ (norm_nonneg u) (mem_closedBall_zero_iff.1 hu) 2
  have hε' : √ε ^ 2 < 1 := by
    rcases le_or_gt ε 0 with h0 | h0
    · simp [Real.sqrt_eq_zero'.2 h0]
    · rwa [Real.sq_sqrt h0.le]
  rw [projectivePlaneTopChart_target, mem_ofPred_eq]
  nlinarith [sq_nonneg (u 0)]

/-- The reflection `(u₀, u₁) ↦ (-u₀, u₁)` of the plane. -/
private def reflectFirst : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i ↦
    if i = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

private theorem reflectFirst_apply_zero (u : EuclideanSpace ℝ (Fin 2)) :
    reflectFirst u 0 = -u 0 := by
  simp [reflectFirst, LinearIsometryEquiv.piLpCongrRight_apply]

private theorem reflectFirst_apply_one (u : EuclideanSpace ℝ (Fin 2)) :
    reflectFirst u 1 = u 1 := by
  simp [reflectFirst, LinearIsometryEquiv.piLpCongrRight_apply]

private theorem reflectFirst_symm_apply (u : EuclideanSpace ℝ (Fin 2)) :
    reflectFirst.symm u = reflectFirst u := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact PiLp.ext (Fin.forall_fin_two.2 ⟨by simp [reflectFirst_apply_zero],
    by simp [reflectFirst_apply_one]⟩)

/-- The top chart followed by the reflection `(u₀, u₁) ↦ (-u₀, u₁)` of its first negative
coordinate: a second normalized Morse chart at the maximum `[0 : 0 : 1]`. -/
def projectivePlaneTopChartReflect :
    OpenPartialHomeomorph (ℙ ℝ (Fin 3 → ℝ)) (EuclideanSpace ℝ (Fin 2)) :=
  projectivePlaneTopChart.trans reflectFirst.toHomeomorph.toOpenPartialHomeomorph

/-- The reflected chart has the same source as the top chart. -/
@[simp]
theorem projectivePlaneTopChartReflect_source :
    projectivePlaneTopChartReflect.source = affineOpen 2 := by
  simp [projectivePlaneTopChartReflect]

/-- The first coordinate of the reflected chart is the negative of that of the top chart. -/
@[simp]
theorem projectivePlaneTopChartReflect_apply_zero (y : ℙ ℝ (Fin 3 → ℝ)) :
    projectivePlaneTopChartReflect y 0 = -projectivePlaneTopChart y 0 := by
  simp [projectivePlaneTopChartReflect, reflectFirst_apply_zero]

/-- The second coordinate of the reflected chart is that of the top chart. -/
@[simp]
theorem projectivePlaneTopChartReflect_apply_one (y : ℙ ℝ (Fin 3 → ℝ)) :
    projectivePlaneTopChartReflect y 1 = projectivePlaneTopChart y 1 := by
  simp [projectivePlaneTopChartReflect, reflectFirst_apply_one]

/-- The inverse of the reflected chart is the inverse of the top chart after the reflection
`(u₀, u₁) ↦ (-u₀, u₁)`. -/
theorem projectivePlaneTopChartReflect_symm_apply (u : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneTopChartReflect.symm u = projectivePlaneTopChart.symm !₂[-u 0, u 1] := by
  simp only [projectivePlaneTopChartReflect, mfld_simps]
  rw [LinearIsometryEquiv.coe_symm_toHomeomorph, reflectFirst_symm_apply]
  congr 1
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simp [reflectFirst_apply_zero]
  · simp [reflectFirst_apply_one]

/-- The normal form at the maximum in the reflected chart. -/
theorem projectivePlaneHeight_eq_of_mem_projectivePlaneTopChartReflect_source {y : ℙ ℝ (Fin 3 → ℝ)}
    (hy : y ∈ projectivePlaneTopChartReflect.source) :
    projectivePlaneHeight y = 2 + ∑ j : Fin 2,
      (if j.val < 2 then -1 else 1) * projectivePlaneTopChartReflect y j ^ 2 := by
  rw [projectivePlaneHeight_eq_of_mem_projectivePlaneTopChart_source (by simpa using hy),
    Fin.sum_univ_two, Fin.sum_univ_two, projectivePlaneTopChartReflect_apply_zero,
    projectivePlaneTopChartReflect_apply_one, neg_sq]

/-- The target of the reflected chart contains the closed ball of radius `√ε` for `ε < 1`. -/
theorem closedBall_subset_projectivePlaneTopChartReflect_target {ε : ℝ} (hε : ε < 1) :
    closedBall 0 √ε ⊆ projectivePlaneTopChartReflect.target := fun u hu ↦ by
  refine ⟨mem_univ _, ?_⟩
  have : ‖reflectFirst.symm u‖ = ‖u‖ := reflectFirst.symm.norm_map u
  exact closedBall_subset_projectivePlaneTopChart_target hε
    (mem_closedBall_zero_iff.2 (this.trans_le (mem_closedBall_zero_iff.1 hu)))

/-! ### The attaching maps of the cell of the maximum -/

section Attaching

variable {ε : ℝ}

/-- Extending by zero along the identity `Fin 2 ↪ Fin 2` does nothing. -/
private theorem piLpExtendByZero_castLEEmb_refl (w : EuclideanSpace ℝ (Fin 2)) :
    LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb le_rfl) w = w :=
  PiLp.ext fun i ↦ EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE le_rfl w i

/-- The attaching map `α₊ : ∂D² → {f ≤ 2 - ε}` of the cell of the maximum in the top chart,
`OpenPartialHomeomorph.morseAttachingMap` for `projectivePlaneTopChart`, at level `2 - ε`. -/
abbrev projectivePlaneAttachingMap (hε : 0 ≤ ε) (hε1 : ε < 1) :
    TopCat.diskBoundary.{0} 2 ⟶ TopCat.of {y | projectivePlaneHeight y ≤ 2 - ε} :=
  projectivePlaneTopChart.morseAttachingMap le_rfl hε
    (closedBall_subset_projectivePlaneTopChart_target hε1)
    (fun _ ↦ projectivePlaneHeight_eq_of_mem_projectivePlaneTopChart_source)

/-- The attaching map `α₋ : ∂D² → {f ≤ 2 - ε}` of the cell of the maximum in the reflected chart,
`OpenPartialHomeomorph.morseAttachingMap` for `projectivePlaneTopChartReflect`. -/
abbrev projectivePlaneAttachingMapReflect (hε : 0 ≤ ε) (hε1 : ε < 1) :
    TopCat.diskBoundary.{0} 2 ⟶ TopCat.of {y | projectivePlaneHeight y ≤ 2 - ε} :=
  projectivePlaneTopChartReflect.morseAttachingMap le_rfl hε
    (closedBall_subset_projectivePlaneTopChartReflect_target hε1)
    (fun _ ↦ projectivePlaneHeight_eq_of_mem_projectivePlaneTopChartReflect_source)

/-- The attaching map `∂D² → {f ≤ 2 - ε}` of the top chart is `w ↦ ψ⁻¹(√ε • w)`. -/
theorem coe_projectivePlaneAttachingMap_apply (hε : 0 ≤ ε) (hε1 : ε < 1)
    (w : TopCat.diskBoundary.{0} 2) :
    (projectivePlaneAttachingMap hε hε1 w : ℙ ℝ (Fin 3 → ℝ)) =
      projectivePlaneTopChart.symm (√ε • (w.down : EuclideanSpace ℝ (Fin 2))) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, OpenPartialHomeomorph.morseCellMap_def,
    piLpExtendByZero_castLEEmb_refl]

/-- The attaching map `∂D² → {f ≤ 2 - ε}` of the reflected chart is `w ↦ ψ⁻¹(√ε • r w)`, where
`r (w₀, w₁) = (-w₀, w₁)`. -/
theorem coe_projectivePlaneAttachingMapReflect_apply (hε : 0 ≤ ε) (hε1 : ε < 1)
    (w : TopCat.diskBoundary.{0} 2) :
    (projectivePlaneAttachingMapReflect hε hε1 w : ℙ ℝ (Fin 3 → ℝ)) =
      projectivePlaneTopChart.symm
        (√ε • !₂[-(w.down : EuclideanSpace ℝ (Fin 2)) 0,
          (w.down : EuclideanSpace ℝ (Fin 2)) 1]) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, OpenPartialHomeomorph.morseCellMap_def,
    piLpExtendByZero_castLEEmb_refl, projectivePlaneTopChartReflect_symm_apply]
  congr 1
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> simp

/-- The attaching map of the reflected chart at `w` is the attaching map of the top chart at the
reflection `r w = (-w₀, w₁)` of `w` (`TauCeti.diskBoundaryTwoReflect`). -/
theorem projectivePlaneAttachingMapReflect_apply (hε : 0 ≤ ε) (hε1 : ε < 1)
    (w : TopCat.diskBoundary.{0} 2) :
    projectivePlaneAttachingMapReflect hε hε1 w =
      projectivePlaneAttachingMap hε hε1 (diskBoundaryTwoReflect.hom w) := by
  refine Subtype.ext ?_
  rw [coe_projectivePlaneAttachingMapReflect_apply hε hε1,
    coe_projectivePlaneAttachingMap_apply hε hε1]
  congr 2
  exact PiLp.ext (Fin.forall_fin_two.2 ⟨(diskBoundaryTwoReflect_hom_apply_zero w).symm,
    (diskBoundaryTwoReflect_hom_apply_one w).symm⟩)

open CategoryTheory in
/-- **The two attaching maps differ strictly by a reflection.** The attaching map of the reflected
chart is the attaching map of the top chart precomposed with the reflection
`r (w₀, w₁) = (-w₀, w₁)` of the boundary circle (`TauCeti.diskBoundaryTwoReflect`):
`α₋ = α₊ ∘ r`. -/
theorem projectivePlaneAttachingMapReflect_eq_comp (hε : 0 ≤ ε) (hε1 : ε < 1) :
    projectivePlaneAttachingMapReflect hε hε1 =
      diskBoundaryTwoReflect.hom ≫ projectivePlaneAttachingMap hε hε1 :=
  TopCat.ext (projectivePlaneAttachingMapReflect_apply hε hε1)

end Attaching

/-! ### The lower sublevels are homotopy equivalent to the projective line `z = 0` -/

section Sublevel

/-- Equal nonzero vectors span the same point of the projective space. -/
private theorem mk_eq_mk_of_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {v w : V} (h : v = w)
    {hv : v ≠ 0} {hw : w ≠ 0} : mk ℝ v hv = mk ℝ w hw := by
  subst h
  rfl

/-- The linear map `(x, y, z) ↦ (x, y)`. -/
private def dropLast : (Fin 3 → ℝ) →ₗ[ℝ] Fin 2 → ℝ :=
  LinearMap.funLeft ℝ ℝ Fin.castSucc

/-- The linear map `(x, y) ↦ (x, y, 0)`. -/
private def addLast : (Fin 2 → ℝ) →ₗ[ℝ] Fin 3 → ℝ :=
  Function.ExtendByZero.linearMap ℝ ℝ Fin.castSucc

private theorem dropLast_apply (v : Fin 3 → ℝ) : dropLast v = ![v 0, v 1] := by
  ext i
  fin_cases i <;> rfl

private theorem addLast_apply (w : Fin 2 → ℝ) : addLast w = ![w 0, w 1, 0] := by
  ext i
  fin_cases i
  · exact (Fin.castSucc_injective 2).extend_apply w 0 0
  · exact (Fin.castSucc_injective 2).extend_apply w 0 1
  · exact Function.extend_apply' _ _ _ fun ⟨a, ha⟩ ↦ (Fin.castSucc_lt_last a).ne ha

private theorem addLast_injective : Function.Injective addLast := fun w w' h ↦ by
  rw [addLast_apply, addLast_apply] at h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

private theorem dropLast_addLast (w : Fin 2 → ℝ) : dropLast (addLast w) = w := by
  rw [addLast_apply, dropLast_apply]
  ext i
  fin_cases i <;> rfl

private theorem sum_sq_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  by_contra h
  refine hv (funext fun i ↦ ?_)
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-- A point lies below the maximum value `2` exactly when it is off the maximum `[0 : 0 : 1]`,
that is, when its first two homogeneous coordinates do not both vanish. -/
private theorem projectivePlaneHeight_mk_lt_two_iff (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectivePlaneHeight (mk ℝ v hv) < 2 ↔ dropLast v ≠ 0 := by
  rw [projectivePlaneHeight_mk, div_lt_iff₀ (sum_sq_pos hv), dropLast_apply]
  simp only [ne_eq, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and_or]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at h
    nlinarith
  · rintro (h | h)
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 1), sq_nonneg (v 2)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0), sq_nonneg (v 2)]

/-- The linear maps `(x, y, z) ↦ (x, y, (1 - t) z)`, flattening the plane onto `z = 0` as `t`
goes from `0` to `1`. -/
private def flatten (t : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ where
  toFun v := ![v 0, v 1, (1 - t) * v 2]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_left_comm]

private theorem flatten_apply (t : ℝ) (v : Fin 3 → ℝ) :
    flatten t v = ![v 0, v 1, (1 - t) * v 2] :=
  (rfl)

private theorem dropLast_flatten (t : ℝ) (v : Fin 3 → ℝ) :
    dropLast (flatten t v) = dropLast v := by
  rw [dropLast_apply, dropLast_apply, flatten_apply]
  rfl

private theorem flatten_ne_zero {v : Fin 3 → ℝ} (hv : dropLast v ≠ 0) (t : ℝ) :
    flatten t v ≠ 0 := fun h ↦ hv (by rw [← dropLast_flatten t, h, map_zero])

private theorem flatten_zero (v : Fin 3 → ℝ) : flatten 0 v = v := by
  ext i
  fin_cases i <;> simp [flatten_apply]

private theorem flatten_one (v : Fin 3 → ℝ) : flatten 1 v = addLast (dropLast v) := by
  rw [flatten_apply, addLast_apply, dropLast_apply]
  ext i
  fin_cases i <;> simp

private theorem continuous_flatten :
    Continuous fun p : ℝ × (Fin 3 → ℝ) ↦ flatten p.1 p.2 := by
  simp only [flatten_apply]
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop

/-- Flattening towards the line `z = 0` lowers the height. -/
private theorem projectivePlaneHeight_flatten_le {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (hd : dropLast v ≠ 0) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    projectivePlaneHeight (mk ℝ (flatten t v) (flatten_ne_zero hd t)) ≤
      projectivePlaneHeight (mk ℝ v hv) := by
  have hd' : 0 < 2 * v 0 ^ 2 + v 1 ^ 2 := by
    have h := (projectivePlaneHeight_mk_lt_two_iff v hv).2 hd
    rw [projectivePlaneHeight_mk, div_lt_iff₀ (sum_sq_pos hv)] at h
    linarith
  have hs₀ : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  have hs₁ : (1 - t) ^ 2 ≤ 1 := by nlinarith
  simp only [projectivePlaneHeight_mk, flatten_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_pow]
  rw [div_le_div_iff₀ (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]) (sum_sq_pos hv)]
  have key : (v 1 ^ 2 + 2 * v 2 ^ 2) * (v 0 ^ 2 + v 1 ^ 2 + (1 - t) ^ 2 * v 2 ^ 2) -
      (v 1 ^ 2 + 2 * ((1 - t) ^ 2 * v 2 ^ 2)) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) =
      (1 - (1 - t) ^ 2) * v 2 ^ 2 * (2 * v 0 ^ 2 + v 1 ^ 2) := by ring
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hs₁) (sq_nonneg (v 2))) hd'.le]

/-- The family of projections `[v] ↦ [x : y : (1 - t) z]` is jointly continuous off the
maximum `[0 : 0 : 1]`. -/
private theorem continuousOn_linearProjection_flatten :
    ContinuousOn (fun p : I × ℙ ℝ (Fin 3 → ℝ) ↦ linearProjection (flatten p.1) p.2)
      (univ ×ˢ linearProjectionDomain dropLast) := by
  rintro ⟨t, y⟩ ⟨-, hy⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hq : IsOpenQuotientMap
      (Prod.map id (mk' ℝ) : I × {v : Fin 3 → ℝ // v ≠ 0} → I × ℙ ℝ (Fin 3 → ℝ)) :=
    IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk'
  obtain ⟨v, rfl⟩ := isOpenQuotientMap_mk'.surjective y
  -- The point `(t, [v])` is the image of `(t, v)` under the quotient map.
  rw [show (t, mk' ℝ v) = Prod.map id (mk' ℝ) (t, v) from rfl, ← hq.continuousAt_comp_iff]
  let U := {x : I × {v : Fin 3 → ℝ // v ≠ 0} | dropLast x.2.1 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun
    (dropLast.continuous_of_finiteDimensional.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  have hx : (t, v) ∈ U := by
    simpa [U, mk'_eq_mk, mk_mem_linearProjectionDomain_iff] using hy
  refine ContinuousOn.continuousAt ?_ (hU.mem_nhds hx)
  rw [continuousOn_iff_continuous_domRestrict]
  have hne (x : U) : flatten x.1.1 x.1.2.1 ≠ 0 := flatten_ne_zero x.2 _
  refine (continuous_mk (K := ℝ) (f := fun x : U ↦ flatten x.1.1 x.1.2.1) ?_ hne).congr
    fun x ↦ ?_
  · exact continuous_flatten.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd) |>.comp continuous_subtype_val)
  · simp [mk'_eq_mk, linearProjection_mk _ _ (hne x)]

variable {c : ℝ}

private theorem mem_linearProjectionDomain_of_le (hc : c < 2) {y : ℙ ℝ (Fin 3 → ℝ)}
    (hy : projectivePlaneHeight y ≤ c) : y ∈ linearProjectionDomain dropLast := by
  induction y using ind with | h v hv =>
  rw [mk_mem_linearProjectionDomain_iff, ← projectivePlaneHeight_mk_lt_two_iff v hv]
  exact hy.trans_lt hc

private theorem projectivePlaneHeight_linearProjection_flatten_le (hc : c < 2)
    {y : ℙ ℝ (Fin 3 → ℝ)} (hy : projectivePlaneHeight y ≤ c) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : projectivePlaneHeight (linearProjection (flatten t) y) ≤ c := by
  induction y using ind with | h v hv =>
  have hd : dropLast v ≠ 0 := (projectivePlaneHeight_mk_lt_two_iff v hv).1 (hy.trans_lt hc)
  rw [linearProjection_mk _ _ (flatten_ne_zero hd t)]
  exact (projectivePlaneHeight_flatten_le hv hd ht₀ ht₁).trans hy

private theorem projectivePlaneHeight_map_addLast_le_one (x : ℙ ℝ (Fin 2 → ℝ)) :
    projectivePlaneHeight (map addLast addLast_injective x) ≤ 1 := by
  induction x using ind with | h w hw =>
  have hs : 0 < w 0 ^ 2 + w 1 ^ 2 := by
    by_contra h
    exact hw (funext fun i ↦ by
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)])
  rw [map_mk, projectivePlaneHeight_mk]
  simp only [addLast_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [div_le_one (by simpa using hs)]
  nlinarith [sq_nonneg (w 0)]

/-- The projection `[x : y : z] ↦ [x : y]` of a sublevel below `2` onto the projective line. -/
private def sublevelToLine (hc : c < 2) :
    C({y | projectivePlaneHeight y ≤ c}, ℙ ℝ (Fin 2 → ℝ)) where
  toFun y := linearProjection dropLast y.1
  continuous_toFun := (contMDiffOn_linearProjection dropLast 0).continuousOn.comp_continuous
    continuous_subtype_val fun y ↦ mem_linearProjectionDomain_of_le hc y.2

/-- The inclusion `[x : y] ↦ [x : y : 0]` of the projective line into a sublevel above `1`. -/
private def lineToSublevel (hc : 1 ≤ c) :
    C(ℙ ℝ (Fin 2 → ℝ), {y | projectivePlaneHeight y ≤ c}) where
  toFun x := ⟨map addLast addLast_injective x,
    (projectivePlaneHeight_map_addLast_le_one x).trans hc⟩
  continuous_toFun := (continuous_map addLast_injective
    addLast.continuous_of_finiteDimensional).subtype_mk _

/-- The deformation `[x : y : z] ↦ [x : y : (1 - t) z]` of a sublevel onto the line `z = 0`. -/
private def flattenHomotopy (hc₁ : 1 ≤ c) (hc₂ : c < 2) :
    ContinuousMap.Homotopy (ContinuousMap.id _) ((lineToSublevel hc₁).comp (sublevelToLine hc₂))
    where
  toFun p := ⟨linearProjection (flatten p.1) p.2.1,
    projectivePlaneHeight_linearProjection_flatten_le hc₂ p.2.2 p.1.2.1 p.1.2.2⟩
  continuous_toFun := (continuousOn_linearProjection_flatten.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    fun p ↦ ⟨mem_univ _, mem_linearProjectionDomain_of_le hc₂ p.2.2⟩).subtype_mk _
  map_zero_left y := by
    obtain ⟨y, hy⟩ := y
    refine Subtype.ext ?_
    induction y using ind with | h v hv =>
    have hd : dropLast v ≠ 0 := (projectivePlaneHeight_mk_lt_two_iff v hv).1 (hy.trans_lt hc₂)
    simp only [Icc.coe_zero, ContinuousMap.id_apply]
    rw [linearProjection_mk _ _ (flatten_ne_zero hd 0)]
    exact mk_eq_mk_of_eq (flatten_zero v)
  map_one_left y := by
    obtain ⟨y, hy⟩ := y
    refine Subtype.ext ?_
    induction y using ind with | h v hv =>
    have hd : dropLast v ≠ 0 := (projectivePlaneHeight_mk_lt_two_iff v hv).1 (hy.trans_lt hc₂)
    simp only [Icc.coe_one, ContinuousMap.comp_apply, sublevelToLine, lineToSublevel,
      ContinuousMap.coe_mk]
    rw [linearProjection_mk _ _ (flatten_ne_zero hd 1), linearProjection_mk _ _ hd, map_mk]
    exact mk_eq_mk_of_eq (flatten_one v)

/-- **The lower sublevels deformation retract onto the projective line.** For `1 ≤ c < 2` the
projection `[x : y : z] ↦ [x : y]` is a homotopy equivalence from the sublevel `{f ≤ c}` onto
the projective line, with homotopy inverse the inclusion `[x : y] ↦ [x : y : 0]` of the line
`z = 0`; the homotopy is `[x : y : z] ↦ [x : y : (1 - t) z]`. -/
def projectivePlaneSublevelHomotopyEquiv (hc₁ : 1 ≤ c) (hc₂ : c < 2) :
    {y | projectivePlaneHeight y ≤ c} ≃ₕ ℙ ℝ (Fin 2 → ℝ) where
  toFun := sublevelToLine hc₂
  invFun := lineToSublevel hc₁
  left_inv := ⟨(flattenHomotopy hc₁ hc₂).symm⟩
  right_inv := by
    have h : (sublevelToLine hc₂).comp (lineToSublevel hc₁) = ContinuousMap.id _ := by
      ext x
      induction x using ind with | h w hw =>
      simp only [ContinuousMap.comp_apply, sublevelToLine, lineToSublevel, ContinuousMap.coe_mk,
        map_mk, ContinuousMap.id_apply]
      rw [linearProjection_mk _ _ (by rwa [dropLast_addLast])]
      exact mk_eq_mk_of_eq (dropLast_addLast w)
    rw [h]

private theorem projectivePlaneSublevelHomotopyEquiv_apply (hc₁ : 1 ≤ c) (hc₂ : c < 2)
    (y : {y | projectivePlaneHeight y ≤ c}) :
    projectivePlaneSublevelHomotopyEquiv hc₁ hc₂ y = linearProjection dropLast y.1 :=
  (rfl)

/-- The projection of the sublevel onto the line in homogeneous coordinates:
`[x : y : z] ↦ [x : y]`. -/
theorem projectivePlaneSublevelHomotopyEquiv_apply_of_eq (hc₁ : 1 ≤ c) (hc₂ : c < 2)
    {y : {y | projectivePlaneHeight y ≤ c}} {v : Fin 3 → ℝ} {hv : v ≠ 0}
    (hy : (y : ℙ ℝ (Fin 3 → ℝ)) = mk ℝ v hv) (hd : ![v 0, v 1] ≠ 0) :
    projectivePlaneSublevelHomotopyEquiv hc₁ hc₂ y = mk ℝ ![v 0, v 1] hd := by
  rw [projectivePlaneSublevelHomotopyEquiv_apply, hy,
    linearProjection_mk _ _ (by rwa [dropLast_apply])]
  exact mk_eq_mk_of_eq (dropLast_apply v)

/-- The homotopy inverse of the projection is the inclusion `[x : y] ↦ [x : y : 0]`. -/
theorem coe_projectivePlaneSublevelHomotopyEquiv_symm_apply_mk (hc₁ : 1 ≤ c) (hc₂ : c < 2)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) (hw' : ![w 0, w 1, 0] ≠ 0) :
    ((projectivePlaneSublevelHomotopyEquiv hc₁ hc₂).symm (mk ℝ w hw) : ℙ ℝ (Fin 3 → ℝ)) =
      mk ℝ ![w 0, w 1, 0] hw' :=
  (map_mk addLast addLast_injective w hw).trans
    (mk_eq_mk_of_eq (addLast_apply w))

end Sublevel

/-! ### The sublevels as circles -/

section Circle

variable {c : ℝ}

/-- **The lower sublevels are homotopy equivalent to the circle.** For `1 ≤ c < 2` the map
`[x : y : z] ↦ (x + i y)² / (x² + y²)` from the sublevel `{f ≤ c}` to the circle is a homotopy
equivalence: the composite of the deformation retraction onto the line `z = 0`
(`TauCeti.projectivePlaneSublevelHomotopyEquiv`) with the identification of the projective line
with the circle. -/
def projectivePlaneSublevelCircleEquiv (hc₁ : 1 ≤ c) (hc₂ : c < 2) :
    {y | projectivePlaneHeight y ≤ c} ≃ₕ Circle :=
  (projectivePlaneSublevelHomotopyEquiv hc₁ hc₂).trans lineHomeomorphCircle.toHomotopyEquiv

-- This holds by definition of `ContinuousMap.HomotopyEquiv.trans` and
-- `Homeomorph.toHomotopyEquiv`; Mathlib has no `HomotopyEquiv.trans_apply`.
private theorem projectivePlaneSublevelCircleEquiv_apply (hc₁ : 1 ≤ c) (hc₂ : c < 2)
    (y : {y | projectivePlaneHeight y ≤ c}) :
    projectivePlaneSublevelCircleEquiv hc₁ hc₂ y =
      lineHomeomorphCircle (projectivePlaneSublevelHomotopyEquiv hc₁ hc₂ y) :=
  (rfl)

/-- The circle map of the sublevel in homogeneous coordinates:
`[x : y : z] ↦ (x + i y)² / (x² + y²)`. -/
theorem coe_projectivePlaneSublevelCircleEquiv_apply_of_eq (hc₁ : 1 ≤ c) (hc₂ : c < 2)
    {y : {y | projectivePlaneHeight y ≤ c}} {v : Fin 3 → ℝ} {hv : v ≠ 0}
    (hy : (y : ℙ ℝ (Fin 3 → ℝ)) = mk ℝ v hv) :
    (projectivePlaneSublevelCircleEquiv hc₁ hc₂ y : ℂ) =
      (v 0 + v 1 * Complex.I) ^ 2 / (v 0 ^ 2 + v 1 ^ 2 : ℝ) := by
  have hd : ![v 0, v 1] ≠ 0 := by
    have h := y.2
    rw [mem_ofPred_eq, hy] at h
    simpa [dropLast_apply] using (projectivePlaneHeight_mk_lt_two_iff v hv).1 (h.trans_lt hc₂)
  have h := coe_lineHomeomorphCircle_mk ![v 0, v 1] hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, projectivePlaneSublevelCircleEquiv_apply,
    projectivePlaneSublevelHomotopyEquiv_apply_of_eq hc₁ hc₂ hy hd]

/-- The point `[1 : 0 : 0]`, the minimum of the height, as a point of a sublevel. -/
def projectivePlaneSublevelBase (hc : 0 ≤ c) : {y | projectivePlaneHeight y ≤ c} :=
  ⟨mk ℝ ![1, 0, 0] (by simp), by simpa using hc⟩

/-- The base point of the sublevel is `[1 : 0 : 0]`. -/
@[simp]
theorem coe_projectivePlaneSublevelBase (hc : 0 ≤ c) :
    (projectivePlaneSublevelBase hc : ℙ ℝ (Fin 3 → ℝ)) = mk ℝ ![1, 0, 0] (by simp) :=
  (rfl)

private theorem core_ne_zero (θ : ℝ) : ![Real.cos θ, Real.sin θ, 0] ≠ 0 := fun h ↦ by
  have h0 : Real.cos θ = 0 := congrFun h 0
  have h1 : Real.sin θ = 0 := congrFun h 1
  simpa [h0, h1] using Real.cos_sq_add_sin_sq θ

private theorem projectivePlaneHeight_core (θ : ℝ) :
    projectivePlaneHeight (mk ℝ ![Real.cos θ, Real.sin θ, 0] (core_ne_zero θ)) =
      Real.sin θ ^ 2 := by
  simp [Real.cos_sq_add_sin_sq]

private theorem projectivePlaneHeight_core_le (hc : 1 ≤ c) (θ : ℝ) :
    projectivePlaneHeight (mk ℝ ![Real.cos θ, Real.sin θ, 0] (core_ne_zero θ)) ≤ c := by
  rw [projectivePlaneHeight_core]
  exact (Real.sin_sq_le_one _).trans hc

private theorem mk_core_pi :
    mk ℝ ![Real.cos π, Real.sin π, 0] (core_ne_zero π) = mk ℝ ![1, 0, 0] (by simp) := by
  refine (mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨-1, ?_⟩
  ext i
  fin_cases i <;> simp

/-- The core circle `t ↦ [cos πt : sin πt : 0]` of a sublevel: the projective line `z = 0`, run
once from `[1 : 0 : 0]` back to `[-1 : 0 : 0] = [1 : 0 : 0]`. -/
def projectivePlaneCoreLoop (hc : 1 ≤ c) :
    Path (projectivePlaneSublevelBase (zero_le_one.trans hc))
      (projectivePlaneSublevelBase (zero_le_one.trans hc)) where
  toFun t := ⟨mk ℝ ![Real.cos (π * t), Real.sin (π * t), 0] (core_ne_zero _),
    projectivePlaneHeight_core_le hc _⟩
  continuous_toFun := (continuous_mk (by fun_prop) _).subtype_mk _
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simpa using mk_core_pi)

/-- The core circle at time `t` is `[cos πt : sin πt : 0]`. -/
@[simp]
theorem coe_projectivePlaneCoreLoop_apply (hc : 1 ≤ c) (t : I) :
    (projectivePlaneCoreLoop hc t : ℙ ℝ (Fin 3 → ℝ)) =
      mk ℝ ![Real.cos (π * t), Real.sin (π * t), 0] (by
        intro h
        have h₂ := congrArg (fun v : Fin 3 → ℝ ↦ v 0 ^ 2 + v 1 ^ 2) h
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
          Real.cos_sq_add_sin_sq] at h₂
        norm_num at h₂) :=
  (rfl)

/-- The core circle has degree `1` in the circle `TauCeti.projectivePlaneSublevelCircleEquiv`. -/
theorem degree_projectivePlaneCoreLoop_map (hc₁ : 1 ≤ c) (hc₂ : c < 2) :
    Circle.degree ((projectivePlaneCoreLoop hc₁).map
      (projectivePlaneSublevelCircleEquiv hc₁ hc₂).continuous) = 1 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * π * t) (by fun_prop) (fun t ↦ ?_)
    (by simp)
  refine Circle.coe_injective ?_
  rw [Path.map_coe, Function.comp_apply,
    coe_projectivePlaneSublevelCircleEquiv_apply_of_eq hc₁ hc₂ rfl, Circle.coe_exp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.cos_sq_add_sin_sq,
    Complex.ofReal_one, div_one]
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem sq_add_sq_pos {a : ℝ} (ha : a ≠ 0) (θ : ℝ) :
    0 < (a * Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
  have h1 := Real.cos_sq_add_sin_sq θ
  rcases eq_or_ne (Real.sin θ) 0 with hs | hs
  · rw [hs] at h1 ⊢
    rw [mul_pow, show Real.cos θ ^ 2 = 1 by linarith]
    positivity
  · positivity

/-- A loop in the circle with values `(a cos 2πt + i sin 2πt)² / (a² cos² 2πt + sin² 2πt)`,
`a > 0`, has degree `2`: deforming `a` to `1` gives the loop `t ↦ exp(4πit)`. -/
private theorem degree_eq_two_of_forall {x : Circle} (γ : Path x x) {a : ℝ} (ha : 0 < a)
    (hγ : ∀ t : I, (γ t : ℂ) =
      ((a * Real.cos (2 * π * t) : ℝ) + (Real.sin (2 * π * t) : ℝ) * Complex.I) ^ 2 /
        ((a * Real.cos (2 * π * t)) ^ 2 + Real.sin (2 * π * t) ^ 2 : ℝ)) :
    Circle.degree γ = 2 := by
  -- Deform `a` linearly to `1`, through the positive numbers `b s = (1 - s) a + s`.
  have hb (s : I) : 0 < (1 - (s : ℝ)) * a + s := by
    rcases s.2.1.eq_or_lt with h | h
    · simpa [← h] using ha
    · nlinarith [mul_nonneg (sub_nonneg.2 s.2.2) ha.le]
  let z : I × I → ℂ := fun p ↦ (((1 - (p.1 : ℝ)) * a + p.1) * Real.cos (2 * π * p.2) : ℝ) +
    (Real.sin (2 * π * p.2) : ℝ) * Complex.I
  let N : I × I → ℝ := fun p ↦ (((1 - (p.1 : ℝ)) * a + p.1) * Real.cos (2 * π * p.2)) ^ 2 +
    Real.sin (2 * π * p.2) ^ 2
  have hN (p : I × I) : 0 < N p := sq_add_sq_pos (hb p.1).ne' _
  have hzN (p : I × I) : ‖z p‖ ^ 2 = N p := by
    simp only [z, N, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hzc : Continuous z := by fun_prop
  have hNc : Continuous N := by fun_prop
  let F : C(I × I, Circle) :=
    { toFun p := ⟨z p ^ 2 / (N p : ℂ), mem_sphere_zero_iff_norm.2 (by
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hN p).le, hzN,
          div_self (hN p).ne'])⟩
      continuous_toFun := Continuous.subtype_mk ((hzc.pow 2).div
        (Complex.continuous_ofReal.comp hNc) fun p ↦ Complex.ofReal_ne_zero.2 (hN p).ne') _ }
  have hF (p : I × I) : (F p : ℂ) = z p ^ 2 / (N p : ℂ) := rfl
  let δ := Circle.expLoop.map (continuous_pow 2)
  have hδ : Circle.degree δ = 2 := by simp [δ, Circle.degree_map_pow]
  refine (Circle.degree_eq_of_homotopy γ δ F (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)).trans hδ
  · refine Circle.coe_injective ?_
    rw [hF, hγ t]
    simp [z, N]
  · refine Circle.coe_injective ?_
    rw [hF]
    simp only [z, N, δ, Path.map_coe, Function.comp_apply, Circle.expLoop_apply, Circle.coe_pow,
      Circle.coe_exp, Icc.coe_one, sub_self, zero_mul, zero_add, one_mul, Real.cos_sq_add_sin_sq,
      Complex.ofReal_one, div_one]
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
  · refine Circle.coe_injective ?_
    rw [hF, hF]
    simp [z, N]

end Circle

/-! ### The degrees of the attaching maps -/

section Degree

variable {ε : ℝ}

/-- Scaling `(x, y)` does not change `(x + i y)² / (x² + y²)`. -/
private theorem sq_div_sq_add_sq_mul (r x y : ℝ) (hr : r ≠ 0) :
    (((r * x : ℝ) : ℂ) + ((r * y : ℝ) : ℂ) * Complex.I) ^ 2 /
        (((r * x) ^ 2 + (r * y) ^ 2 : ℝ) : ℂ) =
      ((x : ℂ) + (y : ℂ) * Complex.I) ^ 2 / ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
  have h₁ : ((r * x : ℝ) : ℂ) + ((r * y : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  have h₂ : (((r * x) ^ 2 + (r * y) ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ 2 * ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h₁, h₂, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hr))]

/-- The value of the circle map on the attaching map of the top chart. -/
private theorem coe_projectivePlaneSublevelCircleEquiv_projectivePlaneAttachingMap (hε : 0 < ε)
    (hε1 : ε < 1) (w : TopCat.diskBoundary.{0} 2) :
    (projectivePlaneSublevelCircleEquiv (c := 2 - ε) (by linarith) (by linarith)
      (projectivePlaneAttachingMap hε.le hε1 w) : ℂ) =
      (((√2)⁻¹ * (w.down : EuclideanSpace ℝ (Fin 2)) 0 : ℝ) +
        ((w.down : EuclideanSpace ℝ (Fin 2)) 1 : ℝ) * Complex.I) ^ 2 /
      (((√2)⁻¹ * (w.down : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
        (w.down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 : ℝ) := by
  set u := √ε • (w.down : EuclideanSpace ℝ (Fin 2))
  rw [coe_projectivePlaneSublevelCircleEquiv_apply_of_eq _ _
    ((coe_projectivePlaneAttachingMap_apply hε.le hε1 w).trans
      (projectivePlaneTopChart_symm_apply u (topChartInvVec_ne_zero u)))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, u, PiLp.smul_apply, smul_eq_mul]
  rw [show √ε * (w.down : EuclideanSpace ℝ (Fin 2)) 0 / √2 =
    √ε * ((√2)⁻¹ * (w.down : EuclideanSpace ℝ (Fin 2)) 0) by ring,
    sq_div_sq_add_sq_mul √ε _ _ (Real.sqrt_pos.2 hε).ne']

/-- **The attaching map of the top chart has degree `2`.** Read in the circle
`TauCeti.projectivePlaneSublevelCircleEquiv`, in which the core circle has degree `1`, the
attaching map `α₊` along the counterclockwise loop of `∂D²` has degree `2`. -/
theorem degree_projectivePlaneAttachingMap (hε : 0 < ε) (hε1 : ε < 1) :
    Circle.degree ((diskBoundaryTwoLoop.map
      (projectivePlaneAttachingMap hε.le hε1).hom.continuous).map
      (projectivePlaneSublevelCircleEquiv (c := 2 - ε) (by linarith) (by linarith)).continuous) =
      2 := by
  refine degree_eq_two_of_forall _ (a := (√2)⁻¹) (by positivity) fun t ↦ ?_
  rw [Path.map_coe, Path.map_coe, Function.comp_apply, Function.comp_apply,
    coe_projectivePlaneSublevelCircleEquiv_projectivePlaneAttachingMap hε hε1,
    diskBoundaryTwoLoop_apply_zero, diskBoundaryTwoLoop_apply_one]

/-- The value of the circle map on the attaching map of the reflected chart, read off from the
strict relation `α₋ = α₊ ∘ r`. -/
private theorem coe_projectivePlaneSublevelCircleEquiv_projectivePlaneAttachingMapReflect
    (hε : 0 < ε) (hε1 : ε < 1) (w : TopCat.diskBoundary.{0} 2) :
    (projectivePlaneSublevelCircleEquiv (c := 2 - ε) (by linarith) (by linarith)
      (projectivePlaneAttachingMapReflect hε.le hε1 w) : ℂ) =
      ((-((√2)⁻¹ * (w.down : EuclideanSpace ℝ (Fin 2)) 0) : ℝ) +
        ((w.down : EuclideanSpace ℝ (Fin 2)) 1 : ℝ) * Complex.I) ^ 2 /
      ((-((√2)⁻¹ * (w.down : EuclideanSpace ℝ (Fin 2)) 0)) ^ 2 +
        (w.down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 : ℝ) := by
  rw [projectivePlaneAttachingMapReflect_apply hε.le hε1,
    coe_projectivePlaneSublevelCircleEquiv_projectivePlaneAttachingMap hε hε1,
    diskBoundaryTwoReflect_hom_apply_zero, diskBoundaryTwoReflect_hom_apply_one, mul_neg]

/-- **The attaching map of the reflected chart has degree `-2`.** Read in the circle
`TauCeti.projectivePlaneSublevelCircleEquiv`, the attaching map `α₋ = α₊ ∘ r` along the
counterclockwise loop of `∂D²` has degree `-2`: its values are the complex conjugates of those of
`α₊`. -/
theorem degree_projectivePlaneAttachingMapReflect (hε : 0 < ε) (hε1 : ε < 1) :
    Circle.degree ((diskBoundaryTwoLoop.map
      (projectivePlaneAttachingMapReflect hε.le hε1).hom.continuous).map
      (projectivePlaneSublevelCircleEquiv (c := 2 - ε) (by linarith) (by linarith)).continuous) =
      -2 := by
  rw [Circle.degree_congr _ ((diskBoundaryTwoLoop.map
      (projectivePlaneAttachingMap hε.le hε1).hom.continuous).map
      (projectivePlaneSublevelCircleEquiv (c := 2 - ε) (by linarith)
        (by linarith)).continuous).inv fun t ↦ ?_, Circle.degree_inv,
    degree_projectivePlaneAttachingMap hε hε1]
  refine Circle.coe_injective ?_
  rw [Path.inv_apply, Circle.coe_inv_eq_conj, Path.map_coe, Path.map_coe, Path.map_coe,
    Path.map_coe, Function.comp_apply, Function.comp_apply, Function.comp_apply,
    Function.comp_apply,
    coe_projectivePlaneSublevelCircleEquiv_projectivePlaneAttachingMapReflect hε hε1,
    coe_projectivePlaneSublevelCircleEquiv_projectivePlaneAttachingMap hε hε1]
  simp only [map_div₀, map_pow, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_sq]
  push_cast
  ring

end Degree

/-! ### The attaching maps in the fundamental group of the sublevel -/

section FundamentalGroup

variable {ε c : ℝ}

/-- **The core circle generates the fundamental group of the sublevel.** For `1 ≤ c < 2`,
`π₁({f ≤ c}, [1 : 0 : 0])` is generated by the class of the core circle
`t ↦ [cos πt : sin πt : 0]`: the sublevel retracts onto the line `z = 0`, a circle. -/
theorem zpowers_projectivePlaneCoreLoop_eq_top (hc₁ : 1 ≤ c) (hc₂ : c < 2) :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (projectivePlaneCoreLoop hc₁))) = ⊤ :=
  Circle.zpowers_fromPath_eq_top_of_degree_map_eq_one
    (d := (projectivePlaneSublevelCircleEquiv hc₁ hc₂).toFun)
    ((projectivePlaneSublevelCircleEquiv hc₁ hc₂).fundamentalGroup_map_bijective _).1
    (degree_projectivePlaneCoreLoop_map hc₁ hc₂)

/-- **The attaching map of the top chart is twice the core circle.** Along the counterclockwise
loop of `∂D²`, the attaching map `α₊` of the cell of the maximum is homotopic, through loops based
at its basepoint, to the core circle run twice, conjugated by any path from that basepoint to
`[1 : 0 : 0]`. -/
theorem homotopic_projectivePlaneAttachingMap (hε : 0 < ε) (hε1 : ε < 1)
    (p : Path (projectivePlaneAttachingMap hε.le hε1 diskBoundaryTwoBase)
      (projectivePlaneSublevelBase (c := 2 - ε) (by linarith))) :
    (diskBoundaryTwoLoop.map (projectivePlaneAttachingMap hε.le hε1).hom.continuous).Homotopic
      (p.trans (((projectivePlaneCoreLoop (c := 2 - ε) (by linarith)).trans
        (projectivePlaneCoreLoop (c := 2 - ε) (by linarith))).trans p.symm)) := by
  have hc₁ : 1 ≤ 2 - ε := by linarith
  have hc₂ : 2 - ε < 2 := by linarith
  refine Circle.homotopic_trans_of_degree_map_eq
    (d := (projectivePlaneSublevelCircleEquiv hc₁ hc₂).toFun)
    ((projectivePlaneSublevelCircleEquiv hc₁ hc₂).fundamentalGroup_map_bijective _).1 ?_ p
  rw [Path.map_trans, Circle.degree_trans]
  exact (degree_projectivePlaneAttachingMap hε hε1).trans
    (by rw [degree_projectivePlaneCoreLoop_map hc₁ hc₂]; norm_num)

/-- **The attaching map of the reflected chart is twice the reversed core circle.** Along the
counterclockwise loop of `∂D²`, the attaching map `α₋` of the cell of the maximum is homotopic,
through loops based at its basepoint, to the reversed core circle run twice, conjugated by any
path from that basepoint to `[1 : 0 : 0]`. -/
theorem homotopic_projectivePlaneAttachingMapReflect (hε : 0 < ε) (hε1 : ε < 1)
    (p : Path (projectivePlaneAttachingMapReflect hε.le hε1 diskBoundaryTwoBase)
      (projectivePlaneSublevelBase (c := 2 - ε) (by linarith))) :
    (diskBoundaryTwoLoop.map
        (projectivePlaneAttachingMapReflect hε.le hε1).hom.continuous).Homotopic
      (p.trans (((projectivePlaneCoreLoop (c := 2 - ε) (by linarith)).symm.trans
        (projectivePlaneCoreLoop (c := 2 - ε) (by linarith)).symm).trans p.symm)) := by
  have hc₁ : 1 ≤ 2 - ε := by linarith
  have hc₂ : 2 - ε < 2 := by linarith
  refine Circle.homotopic_trans_of_degree_map_eq
    (d := (projectivePlaneSublevelCircleEquiv hc₁ hc₂).toFun)
    ((projectivePlaneSublevelCircleEquiv hc₁ hc₂).fundamentalGroup_map_bijective _).1 ?_ p
  rw [Path.map_trans, Circle.degree_trans, ← Path.map_symm, Circle.degree_symm]
  exact (degree_projectivePlaneAttachingMapReflect hε hε1).trans
    (by rw [degree_projectivePlaneCoreLoop_map hc₁ hc₂]; norm_num)

/-- **The two attaching maps are not homotopic.** The attaching maps `α₊` and `α₋ = α₊ ∘ r` of the
cell of the maximum in the top chart and in its reflection are not homotopic as maps
`∂D² → {f ≤ 2 - ε}`, with their labelled source fixed: their degrees `2` and `-2` differ. -/
theorem not_homotopic_projectivePlaneAttachingMap_reflect (hε : 0 < ε) (hε1 : ε < 1) :
    ¬ (projectivePlaneAttachingMap hε.le hε1).hom.Homotopic
      (projectivePlaneAttachingMapReflect hε.le hε1).hom := by
  rintro ⟨H⟩
  set e := projectivePlaneSublevelCircleEquiv (c := 2 - ε) (by linarith) (by linarith)
  let F : C(I × I, Circle) := e.toFun.comp (H.toContinuousMap.comp
    (ContinuousMap.prodMap (ContinuousMap.id I) diskBoundaryTwoLoop.toContinuousMap))
  have h := Circle.degree_eq_of_homotopy ((diskBoundaryTwoLoop.map
      (projectivePlaneAttachingMap hε.le hε1).hom.continuous).map e.continuous)
    ((diskBoundaryTwoLoop.map
      (projectivePlaneAttachingMapReflect hε.le hε1).hom.continuous).map e.continuous)
    F (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)
  · rw [degree_projectivePlaneAttachingMap hε hε1,
      degree_projectivePlaneAttachingMapReflect hε hε1] at h
    norm_num at h
  · simp [F, e]
  · simp [F, e]
  · simp [F, e]

end FundamentalGroup

end TauCeti
