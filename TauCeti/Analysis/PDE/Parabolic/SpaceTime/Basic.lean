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
* `TauCeti.ParabolicSpaceTime.coordsHomeomorph`: the homeomorphism with ordinary `E × ℝ`.
* `TauCeti.ParabolicSpaceTime.timeReverse`: reversal of time about `T`, an isometry.
* `TauCeti.ParabolicSpaceTime.slab`: the closed time slab `E × [a, b]`.

## References

* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004.
-/

public section
noncomputable section

open Set Metric
open scoped ENNReal NNReal

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
  ⟨ofCoords x t, t.2⟩

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
  ⟨(p : ParabolicSpaceTime E).time, p.2⟩

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

theorem edist_space_le (p q : ParabolicSpaceTime E) : edist p.space q.space ≤ edist p q :=
  WithLp.edist_fst_le p q

theorem edist_time_rpow_le (p q : ParabolicSpaceTime E) :
    edist p.time q.time ^ (1 / 2 : ℝ) ≤ edist p q := by
  rw [edist_eq]
  exact le_add_self

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
  (continuous_fst.comp coordsHomeomorph.continuous).congr fun _ => by simp

@[fun_prop]
theorem continuous_time : Continuous (time : ParabolicSpaceTime E → ℝ) :=
  (continuous_snd.comp coordsHomeomorph.continuous).congr fun _ => by simp

/-! ### Time reversal -/

/-- Reversal of time about `T`, `(x, t) ↦ (x, T - t)`, an isometry of parabolic space-time. -/
def timeReverse (T : ℝ) : ParabolicSpaceTime E ≃ᵢ ParabolicSpaceTime E where
  toFun p := ofCoords p.space (T - p.time)
  invFun p := ofCoords p.space (T - p.time)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  isometry_toFun := Isometry.of_dist_eq fun p q => by
    rw [dist_ofCoords, dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]

@[simp]
theorem space_timeReverse (T : ℝ) (p : ParabolicSpaceTime E) :
    (timeReverse T p).space = p.space := (rfl)

@[simp]
theorem time_timeReverse (T : ℝ) (p : ParabolicSpaceTime E) :
    (timeReverse T p).time = T - p.time := (rfl)

/-- Time reversal about `T` is an involution. -/
@[simp]
theorem timeReverse_timeReverse (T : ℝ) (p : ParabolicSpaceTime E) :
    timeReverse T (timeReverse T p) = p :=
  (timeReverse T).left_inv p

@[simp]
theorem timeReverse_symm (T : ℝ) :
    (timeReverse T).symm = (timeReverse T : ParabolicSpaceTime E ≃ᵢ _) := (rfl)

theorem isClosed_slab (a b : ℝ) : IsClosed (slab (E := E) a b) :=
  isClosed_Icc.preimage continuous_time

/-- Reversal of time about `T` exchanges the slabs `E × [a, b]` and `E × [T - b, T - a]`. -/
theorem preimage_timeReverse_slab (T a b : ℝ) :
    timeReverse T ⁻¹' slab (E := E) a b = slab (T - b) (T - a) := by
  ext p
  simp only [mem_preimage, mem_slab, time_timeReverse, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end PseudoMetricSpace

end ParabolicSpaceTime

end TauCeti
