/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# Parabolic space-time

The heat operator `∂ₜ - Δ` scales one time derivative like two spatial derivatives, so the natural
distance on space-time `E × ℝ` is the *parabolic distance*
`d((x, t), (y, s)) = dist x y + √|t - s|`. Hölder spaces for parabolic equations are defined with
respect to this distance.

This file builds the parabolic distance from existing Mathlib constructions rather than putting a
second metric on `E × ℝ`. Time carries Mathlib's half-power snowflake metric
`Metric.Snowflaking ℝ (1 / 2)`, whose distance is `|t - s| ^ (1 / 2)`, and space-time is the
`WithLp 1` product of `E` with this snowflake, whose distance is the sum of the two factor
distances. The topology is the ordinary product topology on `E × ℝ`.

## Main declarations

* `TauCeti.ParabolicTime`: the real line with the distance `√|t - s|`.
* `TauCeti.ParabolicSpaceTime E`: space-time `E × ℝ` with the parabolic distance.
* `TauCeti.ParabolicSpaceTime.ofCoords`, `space`, `time`: the coordinates of a point.
* `TauCeti.ParabolicSpaceTime.dist_eq`: the parabolic distance formula.
* `TauCeti.ParabolicSpaceTime.ball_ofCoords_subset_preimage_ball_inter_preimage_Ioo` and
  `TauCeti.ParabolicSpaceTime.preimage_ball_inter_preimage_Ioo_subset_ball`: the parabolic ball of
  radius `r` about `(x, t)` lies in the cylinder `B(x, r) × (t - r², t + r²)` and contains the
  cylinder `B(x, r / 2) × (t - r² / 4, t + r² / 4)`.
* `TauCeti.ParabolicSpaceTime.coordsHomeomorph`: the homeomorphism with ordinary `E × ℝ`.
* `TauCeti.ParabolicSpaceTime.timeReverse`: the time reversal `(x, t) ↦ (x, T - t)`, an isometry.
* `TauCeti.ParabolicSpaceTime.slab`: the closed time slab `E × [a, b]`.
* `TauCeti.ParabolicSpaceTime.spatialSlice`, `TauCeti.ParabolicSpaceTime.timeSlice`: the
  continuous inclusions of a fixed-time spatial slice and of a fixed-position time slice.
* `TauCeti.ParabolicSpaceTime.iccTimeReverse` and `TauCeti.ParabolicSpaceTime.slabTimeReverse`:
  the time reversal `t ↦ T - t`, as an isometry from the interval `[T - b, T - a]` onto `[a, b]`
  and from the slab `E × [T - b, T - a]` onto `E × [a, b]`.
* `TauCeti.ParabolicSpaceTime.slabSpaceMap`: a spatial map `f` acting on a slab by
  `(x, t) ↦ (f x, t)`, Lipschitz for the parabolic distance when `f` is, and
  `TauCeti.ParabolicSpaceTime.slabSpaceIsometryEquiv`, the same action of an isometric equivalence
  of space, as an isometric equivalence of slabs.
* `TauCeti.ParabolicSpaceTime.lipschitzWith_slabSpace`: the spatial position of a point of a slab
  is `1`-Lipschitz for the parabolic distance.

## References

* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004.
-/

public section
noncomputable section

open Set Metric
open scoped NNReal

namespace TauCeti

/-- Real time with the parabolic half-power metric `dist t s = |t - s| ^ (1 / 2)`. -/
abbrev ParabolicTime : Type := Snowflaking ℝ (1 / 2 : ℝ) (by norm_num) (by norm_num)

/-- Space-time `E × ℝ` with the parabolic distance `dist x y + √|t - s|`: the `L¹` product of `E`
with the half-power snowflake of real time. -/
abbrev ParabolicSpaceTime (E : Type*) : Type _ := WithLp 1 (E × ParabolicTime)

namespace ParabolicSpaceTime

variable {E : Type*}

/-- The point of parabolic space-time with spatial position `x` and time `t`. -/
def ofCoords (x : E) (t : ℝ) : ParabolicSpaceTime E :=
  WithLp.toLp 1 (x, Snowflaking.toSnowflaking t)

/-- The spatial coordinate of a point of parabolic space-time. -/
def space (p : ParabolicSpaceTime E) : E := p.fst

/-- The real time coordinate of a point of parabolic space-time. -/
def time (p : ParabolicSpaceTime E) : ℝ := p.snd.ofSnowflaking

@[simp]
theorem space_ofCoords (x : E) (t : ℝ) : (ofCoords x t).space = x := (rfl)

@[simp]
theorem time_ofCoords (x : E) (t : ℝ) : (ofCoords x t).time = t := (rfl)

@[simp]
theorem ofCoords_space_time (p : ParabolicSpaceTime E) : ofCoords p.space p.time = p := (rfl)

/-- Points of parabolic space-time with the same coordinates are equal. -/
@[ext]
theorem ext {p q : ParabolicSpaceTime E} (hspace : p.space = q.space)
    (htime : p.time = q.time) : p = q := by
  rw [← ofCoords_space_time p, ← ofCoords_space_time q, hspace, htime]

/-! ### Closed time slabs -/

/-- The closed time slab `E × [a, b]` in parabolic space-time. -/
def slab (a b : ℝ) : Set (ParabolicSpaceTime E) := time ⁻¹' Icc a b

@[simp]
theorem mem_slab {a b : ℝ} {p : ParabolicSpaceTime E} : p ∈ slab a b ↔ p.time ∈ Icc a b :=
  Iff.rfl

/-- The point of the slab `E × [a, b]` with spatial position `x` and time `t ∈ [a, b]`. -/
def slabMk {a b : ℝ} (x : E) (t : Icc a b) : slab (E := E) a b :=
  ⟨ofCoords x t, t.property⟩

@[simp]
theorem space_slabMk {a b : ℝ} (x : E) (t : Icc a b) :
    (slabMk x t : ParabolicSpaceTime E).space = x :=
  (rfl)

@[simp]
theorem time_slabMk {a b : ℝ} (x : E) (t : Icc a b) :
    (slabMk x t : ParabolicSpaceTime E).time = t :=
  (rfl)

/-- The time coordinate of a point of the slab `E × [a, b]`, as an element of `[a, b]`. -/
def slabTime {a b : ℝ} (p : slab (E := E) a b) : Icc a b :=
  ⟨(p : ParabolicSpaceTime E).time, p.property⟩

@[simp]
theorem coe_slabTime {a b : ℝ} (p : slab (E := E) a b) :
    (slabTime p : ℝ) = (p : ParabolicSpaceTime E).time :=
  (rfl)

@[simp]
theorem slabTime_slabMk {a b : ℝ} (x : E) (t : Icc a b) : slabTime (slabMk x t) = t :=
  (rfl)

/-- Every point of a slab is given by its coordinates. -/
@[simp]
theorem slabMk_space_slabTime {a b : ℝ} (p : slab (E := E) a b) :
    slabMk (p : ParabolicSpaceTime E).space (slabTime p) = p :=
  (rfl)

/-- A slab over a smaller time interval is contained in the larger slab. -/
theorem slab_subset_slab {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    slab (E := E) a' b' ⊆ slab a b :=
  preimage_mono (Icc_subset_Icc ha hb)

/-- Including a smaller slab into a larger one keeps the coordinates of a point. -/
@[simp]
theorem inclusion_slabMk {a b a' b' : ℝ} (h : slab (E := E) a' b' ⊆ slab a b) (x : E)
    (t : Icc a' b') :
    inclusion h (slabMk x t) = slabMk x ⟨t, by simpa using h (slabMk x t).property⟩ :=
  (rfl)

/-- A spatial map `f` acting on the slab `E × [a, b]`, by `(x, t) ↦ (f x, t)`. -/
def slabSpaceMap {E' : Type*} {a b : ℝ} (f : E → E') (p : slab (E := E) a b) :
    slab (E := E') a b :=
  slabMk (f (p : ParabolicSpaceTime E).space) (slabTime p)

@[simp]
theorem slabSpaceMap_slabMk {E' : Type*} {a b : ℝ} (f : E → E') (x : E) (t : Icc a b) :
    slabSpaceMap f (slabMk x t) = slabMk (f x) t :=
  (rfl)

@[simp]
theorem slabTime_slabSpaceMap {E' : Type*} {a b : ℝ} (f : E → E') (p : slab (E := E) a b) :
    slabTime (slabSpaceMap f p) = slabTime p :=
  (rfl)

@[simp]
theorem space_slabSpaceMap {E' : Type*} {a b : ℝ} (f : E → E') (p : slab (E := E) a b) :
    (slabSpaceMap f p : ParabolicSpaceTime E').space = f (p : ParabolicSpaceTime E).space :=
  (rfl)

@[simp]
theorem time_slabSpaceMap {E' : Type*} {a b : ℝ} (f : E → E') (p : slab (E := E) a b) :
    (slabSpaceMap f p : ParabolicSpaceTime E').time = (p : ParabolicSpaceTime E).time :=
  (rfl)

@[simp]
theorem slabSpaceMap_id {a b : ℝ} : slabSpaceMap (a := a) (b := b) (id : E → E) = id :=
  (rfl)

@[simp]
theorem slabSpaceMap_slabSpaceMap {E' E'' : Type*} {a b : ℝ} (f : E' → E'') (g : E → E')
    (p : slab (E := E) a b) : slabSpaceMap f (slabSpaceMap g p) = slabSpaceMap (f ∘ g) p :=
  (rfl)

section PseudoEMetricSpace

variable [PseudoEMetricSpace E]

/-- The extended parabolic distance in coordinates: `edist x y + edist t s ^ (1 / 2)`. -/
theorem edist_ofCoords (x y : E) (t s : ℝ) :
    edist (ofCoords x t) (ofCoords y s) = edist x y + edist t s ^ (1 / 2 : ℝ) := by
  rw [WithLp.prod_edist_eq_add (by simp)]
  simp [ofCoords, Snowflaking.edist_def]

/-- The extended parabolic distance is the spatial distance plus the square root of the time
distance. -/
theorem edist_eq (p q : ParabolicSpaceTime E) :
    edist p q = edist p.space q.space + edist p.time q.time ^ (1 / 2 : ℝ) := by
  simpa using edist_ofCoords p.space q.space p.time q.time

/-- The extended parabolic distance between two points of a slab, in coordinates. -/
theorem edist_slabMk {a b : ℝ} (x y : E) (t s : Icc a b) :
    edist (slabMk x t) (slabMk y s) = edist x y + edist t s ^ (1 / 2 : ℝ) :=
  edist_ofCoords x y t s

/-- At a common position, the `α`-th power of the parabolic distance between two points of a slab
is the `α / 2`-th power of the time distance. -/
theorem edist_slabMk_same_space_rpow {a b : ℝ} (x : E) (t s : Icc a b) (α : ℝ≥0) :
    edist (slabMk x t) (slabMk x s) ^ (α : ℝ) = edist t s ^ ((α / 2 : ℝ≥0) : ℝ) := by
  rw [edist_slabMk, edist_self, zero_add, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

theorem edist_space_le (p q : ParabolicSpaceTime E) : edist p.space q.space ≤ edist p q :=
  WithLp.edist_fst_le p q

theorem edist_time_rpow_le (p q : ParabolicSpaceTime E) :
    edist p.time q.time ^ (1 / 2 : ℝ) ≤ edist p q := by
  rw [edist_eq]
  exact le_add_self

/-- The spatial position of a point of a slab is `1`-Lipschitz for the parabolic distance. -/
theorem lipschitzWith_slabSpace {a b : ℝ} :
    LipschitzWith 1 fun p : slab (E := E) a b ↦ (p : ParabolicSpaceTime E).space :=
  LipschitzWith.of_edist_le fun p q ↦ edist_space_le (p : ParabolicSpaceTime E) q

/-- A `K`-Lipschitz spatial map acts on a slab as a `max K 1`-Lipschitz map for the parabolic
distance. -/
theorem lipschitzWith_slabSpaceMap {E' : Type*} [PseudoEMetricSpace E'] {a b : ℝ} {K : ℝ≥0}
    {f : E → E'} (hf : LipschitzWith K f) :
    LipschitzWith (max K 1) (slabSpaceMap (a := a) (b := b) f) := by
  intro p q
  rw [← slabMk_space_slabTime p, ← slabMk_space_slabTime q, slabSpaceMap_slabMk,
    slabSpaceMap_slabMk, edist_slabMk, edist_slabMk, mul_add]
  gcongr
  · exact (hf _ _).trans (mul_le_mul_left (by exact_mod_cast le_max_left K 1) _)
  · exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast le_max_right K 1)

/-- An isometric equivalence `e` of space acts on the slab `E × [a, b]` by `(x, t) ↦ (e x, t)`, an
isometric equivalence for the parabolic distance. -/
def slabSpaceIsometryEquiv {E' : Type*} [PseudoEMetricSpace E'] {a b : ℝ} (e : E ≃ᵢ E') :
    slab (E := E) a b ≃ᵢ slab (E := E') a b where
  toFun := slabSpaceMap e
  invFun := slabSpaceMap e.symm
  left_inv p := by
    rw [← slabMk_space_slabTime p, slabSpaceMap_slabMk, slabSpaceMap_slabMk, e.symm_apply_apply]
  right_inv q := by
    rw [← slabMk_space_slabTime q, slabSpaceMap_slabMk, slabSpaceMap_slabMk, e.apply_symm_apply]
  isometry_toFun p q := by
    rw [← slabMk_space_slabTime p, ← slabMk_space_slabTime q, slabSpaceMap_slabMk,
      slabSpaceMap_slabMk, edist_slabMk, edist_slabMk, e.edist_eq]

@[simp]
theorem slabSpaceIsometryEquiv_apply {E' : Type*} [PseudoEMetricSpace E'] {a b : ℝ}
    (e : E ≃ᵢ E') (p : slab (E := E) a b) : slabSpaceIsometryEquiv e p = slabSpaceMap e p :=
  (rfl)

@[simp]
theorem slabSpaceIsometryEquiv_symm {E' : Type*} [PseudoEMetricSpace E'] {a b : ℝ}
    (e : E ≃ᵢ E') :
    (slabSpaceIsometryEquiv (a := a) (b := b) e).symm = slabSpaceIsometryEquiv e.symm :=
  (rfl)

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace E]

/-- The parabolic distance formula `d((x, t), (y, s)) = dist x y + √|t - s|`. -/
theorem dist_ofCoords (x y : E) (t s : ℝ) :
    dist (ofCoords x t) (ofCoords y s) = dist x y + √|t - s| := by
  rw [WithLp.prod_dist_eq_add (by simp)]
  simp [ofCoords, Real.sqrt_eq_rpow, Real.dist_eq]

/-- The parabolic distance is the spatial distance plus the square root of the time distance. -/
theorem dist_eq (p q : ParabolicSpaceTime E) :
    dist p q = dist p.space q.space + √|p.time - q.time| := by
  simpa using dist_ofCoords p.space q.space p.time q.time

theorem dist_space_le (p q : ParabolicSpaceTime E) : dist p.space q.space ≤ dist p q :=
  WithLp.dist_fst_le p q

theorem sqrt_abs_time_sub_le_dist (p q : ParabolicSpaceTime E) :
    √|p.time - q.time| ≤ dist p q := by
  rw [dist_eq]
  exact le_add_of_nonneg_left dist_nonneg

/-- At parabolic distance at most one, the time-coordinate difference is bounded by the
parabolic distance. -/
theorem abs_time_sub_le_dist_of_dist_le_one (p q : ParabolicSpaceTime E)
    (h : dist p q ≤ 1) : |p.time - q.time| ≤ dist p q := by
  have hs := sqrt_abs_time_sub_le_dist p q
  have hsq := Real.sq_sqrt (abs_nonneg (p.time - q.time))
  nlinarith [Real.sqrt_nonneg |p.time - q.time|]

/-- At a common time, the parabolic distance is the spatial distance. -/
@[simp]
theorem dist_ofCoords_ofCoords_same_time (x y : E) (t : ℝ) :
    dist (ofCoords x t) (ofCoords y t) = dist x y := by
  simp [dist_ofCoords]

/-- At a common spatial position, the parabolic distance is the square root of the time
distance. -/
@[simp]
theorem dist_ofCoords_ofCoords_same_space (x : E) (t s : ℝ) :
    dist (ofCoords x t) (ofCoords x s) = √|t - s| := by
  simp [dist_ofCoords]

/-- **A parabolic ball lies in a cylinder.** The parabolic ball of radius `r` about `(x, t)` lies
in the cylinder `B(x, r) × (t - r², t + r²)`. -/
theorem ball_ofCoords_subset_preimage_ball_inter_preimage_Ioo (x : E) (t r : ℝ) :
    ball (ofCoords x t) r ⊆ space ⁻¹' ball x r ∩ time ⁻¹' Ioo (t - r ^ 2) (t + r ^ 2) := by
  intro p hp
  rw [mem_ball] at hp
  have hsqrt : √|p.time - t| < r := by
    simpa only [time_ofCoords] using (sqrt_abs_time_sub_le_dist p _).trans_lt hp
  have habs := (Real.sqrt_lt' ((Real.sqrt_nonneg _).trans_lt hsqrt)).1 hsqrt
  refine ⟨mem_ball.2 (by simpa only [space_ofCoords] using (dist_space_le p _).trans_lt hp), ?_⟩
  rw [mem_preimage, mem_Ioo]
  constructor <;> linarith [abs_lt.1 habs]

/-- **A cylinder lies in a parabolic ball.** The parabolic ball of radius `r` about `(x, t)`
contains the cylinder `B(x, r / 2) × (t - r² / 4, t + r² / 4)`. With
`ball_ofCoords_subset_preimage_ball_inter_preimage_Ioo`, the
parabolic balls are comparable to, but not equal to, these cylinders. -/
theorem preimage_ball_inter_preimage_Ioo_subset_ball (x : E) (t r : ℝ) :
    space ⁻¹' ball x (r / 2) ∩ time ⁻¹' Ioo (t - r ^ 2 / 4) (t + r ^ 2 / 4) ⊆
      ball (ofCoords x t) r := by
  rintro p ⟨hx, ht⟩
  rw [mem_preimage, mem_ball] at hx
  rw [mem_preimage, mem_Ioo] at ht
  have hr : 0 < r / 2 := dist_nonneg.trans_lt hx
  have hsq : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
  have hsqrt : √|p.time - t| < r / 2 :=
    (Real.sqrt_lt' hr).2 (hsq ▸ abs_lt.2 ⟨by linarith, by linarith⟩)
  rw [mem_ball, dist_eq, space_ofCoords, time_ofCoords]
  linarith

end PseudoMetricSpace

section TopologicalSpace

variable [TopologicalSpace E]

/-- The homeomorphism between parabolic space-time and ordinary space-time `E × ℝ`. Functions on
parabolic space-time are differentiated by transporting them along this map. -/
def coordsHomeomorph : ParabolicSpaceTime E ≃ₜ E × ℝ :=
  (WithLp.homeomorphProd 1 E ParabolicTime).trans
    ((Homeomorph.refl E).prodCongr Snowflaking.homeomorph)

@[simp]
theorem coordsHomeomorph_apply (p : ParabolicSpaceTime E) :
    coordsHomeomorph p = (p.space, p.time) := (rfl)

@[simp]
theorem coordsHomeomorph_symm_apply (z : E × ℝ) :
    coordsHomeomorph.symm z = ofCoords z.1 z.2 := (rfl)

@[fun_prop]
theorem continuous_space : Continuous (space : ParabolicSpaceTime E → E) :=
  WithLp.continuous_fst 1 E ParabolicTime

@[fun_prop]
theorem continuous_time : Continuous (time : ParabolicSpaceTime E → ℝ) :=
  Snowflaking.continuous_ofSnowflaking.comp (WithLp.continuous_snd 1 E ParabolicTime)

/-- Building a point from its coordinates is jointly continuous in `(x, t)`. -/
@[fun_prop]
theorem continuous_ofCoords : Continuous fun z : E × ℝ => ofCoords z.1 z.2 :=
  coordsHomeomorph.symm.continuous

/-- Building a point of a slab from its coordinates is jointly continuous in `(x, t)`. -/
@[fun_prop]
theorem continuous_slabMk {a b : ℝ} :
    Continuous fun z : E × Icc a b => slabMk (a := a) (b := b) z.1 z.2 :=
  (continuous_ofCoords.comp (continuous_fst.prodMk
    (continuous_subtypeVal.comp continuous_snd))).subtype_mk _

@[fun_prop]
theorem continuous_slabTime {a b : ℝ} : Continuous (slabTime : slab (E := E) a b → Icc a b) :=
  (continuous_time.comp continuous_subtypeVal).subtype_mk _

/-- The spatial slice `x ↦ (x, t)` of a slab at the time `t`, as a continuous map. -/
def spatialSlice {a b : ℝ} (t : Icc a b) : C(E, slab (E := E) a b) :=
  ⟨fun x => slabMk x t, continuous_slabMk.comp (continuous_id.prodMk continuous_const)⟩

@[simp]
theorem spatialSlice_apply {a b : ℝ} (t : Icc a b) (x : E) : spatialSlice t x = slabMk x t :=
  (rfl)

/-- The time slice `t ↦ (x, t)` of a slab at the position `x`, as a continuous map. -/
def timeSlice {a b : ℝ} (x : E) : C(Icc a b, slab (E := E) a b) :=
  ⟨slabMk x, continuous_slabMk.comp (continuous_const.prodMk continuous_id)⟩

@[simp]
theorem timeSlice_apply {a b : ℝ} (x : E) (t : Icc a b) : timeSlice x t = slabMk x t :=
  (rfl)

theorem isClosed_slab (a b : ℝ) : IsClosed (slab (E := E) a b) :=
  isClosed_Icc.preimage continuous_time

end TopologicalSpace

/-! ### Time reversal -/

section TimeReversal

variable [PseudoEMetricSpace E]

/-- Time reversal `(x, t) ↦ (x, T - t)`, the reflection of time about `T / 2`, an isometry of
parabolic space-time. -/
def timeReverse (T : ℝ) : ParabolicSpaceTime E ≃ᵢ ParabolicSpaceTime E where
  toFun p := ofCoords p.space (T - p.time)
  invFun p := ofCoords p.space (T - p.time)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  isometry_toFun p q := by
    rw [edist_ofCoords, edist_eq, edist_dist, edist_dist p.time, Real.dist_eq, Real.dist_eq,
      sub_sub_sub_cancel_left, abs_sub_comm]

@[simp]
theorem space_timeReverse (T : ℝ) (p : ParabolicSpaceTime E) :
    (timeReverse T p).space = p.space := (rfl)

@[simp]
theorem time_timeReverse (T : ℝ) (p : ParabolicSpaceTime E) :
    (timeReverse T p).time = T - p.time := (rfl)

/-- Time reversal `t ↦ T - t` is an involution. -/
@[simp]
theorem timeReverse_timeReverse (T : ℝ) (p : ParabolicSpaceTime E) :
    timeReverse T (timeReverse T p) = p :=
  (timeReverse T).left_inv p

@[simp]
theorem timeReverse_symm (T : ℝ) :
    (timeReverse T).symm = (timeReverse T : ParabolicSpaceTime E ≃ᵢ _) := (rfl)

/-- Time reversal `t ↦ T - t` exchanges the slabs `E × [a, b]` and `E × [T - b, T - a]`. -/
theorem preimage_timeReverse_slab (T a b : ℝ) :
    timeReverse T ⁻¹' slab (E := E) a b = slab (T - b) (T - a) := by
  ext p
  simp only [mem_preimage, mem_slab, time_timeReverse,
    ← Set.mem_preimage (f := (T - ·)) (a := p.time), Set.preimage_const_sub_Icc]

/-- Time reversal `t ↦ T - t` maps the time interval `[a', b']` into `[a, b]`, where
`a' = T - b` and `b' = T - a`. -/
theorem sub_mem_Icc_of_eq_sub {a b a' b' : ℝ} (T : ℝ) (ha : a' = T - b) (hb : b' = T - a)
    {s : ℝ} (hs : s ∈ Icc a' b') : T - s ∈ Icc a b := by
  subst ha hb
  constructor <;> linarith [hs.1, hs.2]

/-- Time reversal `t ↦ T - t`, as an isometry from the time interval `[a', b']` onto `[a, b]`,
where `a' = T - b` and `b' = T - a`. It is the time component of `slabTimeReverse`. -/
def iccTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a) :
    Icc a' b' ≃ᵢ Icc a b where
  toFun t := ⟨T - t, sub_mem_Icc_of_eq_sub T ha hb t.property⟩
  invFun s := ⟨T - s,
    sub_mem_Icc_of_eq_sub T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel]) s.property⟩
  left_inv t := Subtype.ext (sub_sub_cancel T t)
  right_inv s := Subtype.ext (sub_sub_cancel T s)
  isometry_toFun := Isometry.of_dist_eq fun t s ↦ by
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_sub_left]

/-- Time reversal between intervals sends `t` to `T - t`. -/
theorem iccTimeReverse_apply (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (t : Icc a' b') :
    iccTimeReverse T ha hb t = ⟨T - t, sub_mem_Icc_of_eq_sub T ha hb t.property⟩ :=
  (rfl)

/-- The underlying real number of `iccTimeReverse T ha hb t` is `T - t`. -/
@[simp]
theorem coe_iccTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (t : Icc a' b') : (iccTimeReverse T ha hb t : ℝ) = T - t := (rfl)

/-- The inverse of time reversal between intervals is time reversal in the opposite direction. -/
@[simp]
theorem iccTimeReverse_symm (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a) :
    (iccTimeReverse T ha hb).symm =
      iccTimeReverse T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel]) := (rfl)

/-- Time reversal between intervals sends the left endpoint `a'` of `[a', b']` to the right
endpoint `b` of `[a, b]`. -/
theorem iccTimeReverse_left (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (h : a ≤ b) :
    iccTimeReverse T ha hb ⟨a', left_mem_Icc.2 (by rw [ha, hb]; exact sub_le_sub_left h T)⟩ =
      ⟨b, right_mem_Icc.2 h⟩ :=
  Subtype.ext (by simp [ha])

/-- Time reversal between intervals sends the right endpoint `b'` of `[a', b']` to the left
endpoint `a` of `[a, b]`. -/
theorem iccTimeReverse_right (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (h : a ≤ b) :
    iccTimeReverse T ha hb ⟨b', right_mem_Icc.2 (by rw [ha, hb]; exact sub_le_sub_left h T)⟩ =
      ⟨a, left_mem_Icc.2 h⟩ :=
  Subtype.ext (by simp [hb])

/-- Time reversal `t ↦ T - t`, as an isometry from the slab `E × [a', b']` onto the slab
`E × [a, b]`, where `a' = T - b` and `b' = T - a`. -/
def slabTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a) :
    slab (E := E) a' b' ≃ᵢ slab (E := E) a b where
  toFun p := ⟨timeReverse T p, by
    rw [← mem_preimage, preimage_timeReverse_slab, ← ha, ← hb]; exact p.property⟩
  invFun q := ⟨timeReverse T q, by
    rw [← mem_preimage, preimage_timeReverse_slab, ha, hb, sub_sub_cancel, sub_sub_cancel]
    exact q.property⟩
  left_inv p := Subtype.ext (timeReverse_timeReverse T (p : ParabolicSpaceTime E))
  right_inv q := Subtype.ext (timeReverse_timeReverse T (q : ParabolicSpaceTime E))
  isometry_toFun p q := (timeReverse T).edist_eq (p : ParabolicSpaceTime E) q

/-- Time reversal between slabs sends `(x, t)` to `(x, T - t)`. -/
@[simp]
theorem slabTimeReverse_slabMk (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (x : E) (t : Icc a' b') :
    slabTimeReverse T ha hb (slabMk x t) = slabMk x (iccTimeReverse T ha hb t) :=
  (rfl)

/-- The time component of time reversal between slabs is time reversal between intervals. -/
@[simp]
theorem slabTime_slabTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (p : slab (E := E) a' b') :
    slabTime (slabTimeReverse T ha hb p) = iccTimeReverse T ha hb (slabTime p) :=
  (rfl)

@[simp]
theorem coe_slabTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a)
    (p : slab (E := E) a' b') :
    (slabTimeReverse T ha hb p : ParabolicSpaceTime E) = timeReverse T p := (rfl)

/-- The time coordinate of the time reversal of `p` between slabs is `T` minus that of `p`. -/
theorem coe_slabTime_slabTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b)
    (hb : b' = T - a) (p : slab (E := E) a' b') :
    (slabTime (slabTimeReverse T ha hb p) : ℝ) = T - slabTime p := (rfl)

/-- Time reversal between slabs followed by time reversal in the opposite direction is the
identity. -/
@[simp]
theorem slabTimeReverse_slabTimeReverse (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b)
    (hb : b' = T - a) (ha' : a = T - b') (hb' : b = T - a') (p : slab (E := E) a' b') :
    slabTimeReverse T ha' hb' (slabTimeReverse T ha hb p) = p :=
  Subtype.ext (timeReverse_timeReverse T (p : ParabolicSpaceTime E))

/-- The inverse of time reversal between slabs is time reversal in the opposite direction. -/
@[simp]
theorem slabTimeReverse_symm (T : ℝ) {a b a' b' : ℝ} (ha : a' = T - b) (hb : b' = T - a) :
    (slabTimeReverse (E := E) T ha hb).symm =
      slabTimeReverse T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel]) := (rfl)

end TimeReversal

end ParabolicSpaceTime

end TauCeti
