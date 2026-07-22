/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.ReImTopology

/-!
# Reflection in a circle

This file defines reflection in the circle with centre `c : ℂ` and radius `r : ℝ` by

`z ↦ c + r² / conj (z - c)`.

For positive radius this map fixes the circle pointwise, is an involution away from its centre,
and exchanges the inside and outside of the circle.  It is the elementary Möbius-conjugation
input for the circle form of the Schwarz reflection principle in the conformal-mapping roadmap.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- Reflection in the circle with centre `c` and radius `r`.

At the centre the division-by-zero convention gives the value `c`; for nonzero radius the
involution law therefore holds on its natural domain, the complement of the centre. -/
noncomputable def circleReflection (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  c + (r : ℂ) ^ 2 / (starRingEnd ℂ) (z - c)

/-- Reflection in a circle is given by its standard conjugate-reciprocal formula. -/
theorem circleReflection_def (c : ℂ) (r : ℝ) (z : ℂ) :
    circleReflection c r z = c + (r : ℂ) ^ 2 / (starRingEnd ℂ) (z - c) := by
  rw [circleReflection]

/-- The centre is sent to itself by the totalized circle-reflection map. -/
@[simp]
theorem circleReflection_center (c : ℂ) (r : ℝ) : circleReflection c r c = c := by
  simp [circleReflection]

/-- Subtracting the centre exposes the conjugate-reciprocal part of circle reflection. -/
@[simp]
theorem circleReflection_sub_center (c : ℂ) (r : ℝ) (z : ℂ) :
    circleReflection c r z - c = (r : ℂ) ^ 2 / (starRingEnd ℂ) (z - c) := by
  simp [circleReflection]

/-- For nonzero radius, only the centre is sent to the centre. -/
@[simp]
theorem circleReflection_eq_center_iff {c : ℂ} {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    circleReflection c r z = c ↔ z = c := by
  constructor
  · intro h
    have hs : (r : ℂ) ^ 2 / (starRingEnd ℂ) (z - c) = 0 := by
      rw [← circleReflection_sub_center]
      exact sub_eq_zero.mpr h
    have : (starRingEnd ℂ) (z - c) = 0 :=
      (div_eq_zero_iff.mp hs).resolve_left (pow_ne_zero _ (ofReal_ne_zero.mpr hr))
    exact sub_eq_zero.mp ((map_eq_zero (starRingEnd ℂ)).mp this)
  · intro h
    subst z
    exact circleReflection_center c r

/-- The distance from the centre after reflection is `r² / dist z c`. -/
theorem dist_circleReflection_center (c : ℂ) (r : ℝ) (z : ℂ) :
    dist (circleReflection c r z) c = r ^ 2 / dist z c := by
  rw [dist_eq, circleReflection_sub_center, norm_div, RCLike.norm_conj, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, dist_eq]

/-- Equivalently, circle reflection sends the radial distance `ρ` to `r² / ρ`. -/
theorem norm_circleReflection_sub_center (c : ℂ) (r : ℝ) (z : ℂ) :
    ‖circleReflection c r z - c‖ = r ^ 2 / ‖z - c‖ := by
  simpa [dist_eq] using dist_circleReflection_center c r z

/-- Reflection in a nondegenerate circle is an involution away from its centre. -/
@[simp]
theorem circleReflection_circleReflection {c : ℂ} {r : ℝ} (hr : r ≠ 0)
    {z : ℂ} (hz : z ≠ c) :
    circleReflection c r (circleReflection c r z) = z := by
  rw [circleReflection, circleReflection_sub_center]
  have hz' : (starRingEnd ℂ) (z - c) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hz)
  rw [map_div₀, map_pow, starRingEnd_self_apply]
  have hrstar : (starRingEnd ℂ) (r : ℂ) = r := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hrstar]
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  field_simp
  ring

/-- Circle reflection is injective on the complement of the centre. -/
theorem injOn_circleReflection {c : ℂ} {r : ℝ} (hr : r ≠ 0) :
    Set.InjOn (circleReflection c r) ({c}ᶜ : Set ℂ) := by
  intro z hz w hw hzw
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz hw
  rw [← circleReflection_circleReflection hr hz,
    ← circleReflection_circleReflection hr hw, hzw]

/-- Circle reflection maps the complement of the centre to itself. -/
theorem mapsTo_circleReflection_compl_singleton {c : ℂ} {r : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (circleReflection c r) ({c}ᶜ : Set ℂ) ({c}ᶜ : Set ℂ) := by
  intro z hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
  exact (circleReflection_eq_center_iff hr z).not.mpr hz

/-- Circle reflection as a self-map of the punctured plane. -/
noncomputable def circleReflectionSubtype (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ({c}ᶜ : Set ℂ) → ({c}ᶜ : Set ℂ) :=
  fun z ↦ ⟨circleReflection c r z, mapsTo_circleReflection_compl_singleton hr z.2⟩

/-- Circle reflection on the punctured plane is involutive. -/
theorem circleReflectionSubtype_involutive (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    Function.Involutive (circleReflectionSubtype c r hr) :=
  fun z ↦ Subtype.ext (circleReflection_circleReflection hr z.2)

/-- Reflection in a nondegenerate circle is a self-equivalence of the punctured plane. -/
noncomputable def circleReflectionEquiv (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ({c}ᶜ : Set ℂ) ≃ ({c}ᶜ : Set ℂ) :=
  (circleReflectionSubtype_involutive c r hr).toPerm (circleReflectionSubtype c r hr)

/-- The punctured-plane equivalence acts by circle reflection. -/
@[simp]
theorem coe_circleReflectionEquiv_apply (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (z : ({c}ᶜ : Set ℂ)) :
    (circleReflectionEquiv c r hr z : ℂ) = circleReflection c r z := by
  rfl

/-- The punctured-plane circle-reflection equivalence is its own inverse. -/
@[simp]
theorem circleReflectionEquiv_symm (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    (circleReflectionEquiv c r hr).symm = circleReflectionEquiv c r hr := by
  exact (circleReflectionSubtype_involutive c r hr).toPerm_symm

/-- Every point on a circle is fixed by reflection in that circle. -/
@[simp]
theorem circleReflection_eq_self_of_mem_sphere {c z : ℂ} {r : ℝ}
    (hz : z ∈ sphere c r) : circleReflection c r z = z := by
  rw [mem_sphere, dist_eq] at hz
  have hr : 0 ≤ r := hz ▸ norm_nonneg (z - c)
  rcases hr.eq_or_lt with rfl | hr
  · have : z = c := sub_eq_zero.mp (norm_eq_zero.mp hz)
    subst z
    exact circleReflection_center c 0
  have hz0 : z - c ≠ 0 := by
    intro hzc
    have : z = c := sub_eq_zero.mp hzc
    subst z
    simp at hz
    linarith
  have hden : (starRingEnd ℂ) (z - c) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz0
  rw [circleReflection]
  apply add_eq_of_eq_sub'
  rw [div_eq_iff hden]
  rw [mul_conj, ← ofReal_pow, Complex.ofReal_inj, Complex.normSq_eq_norm_sq, hz]

/-- Reflection in a positive-radius circle sends its punctured open ball to the exterior of its
closed ball. -/
theorem circleReflection_mem_ball_iff {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ c) :
    circleReflection c r z ∈ ball c r ↔ r < dist z c := by
  rw [mem_ball, dist_circleReflection_center, div_lt_iff₀ (dist_pos.mpr hz)]
  constructor <;> intro h
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]

/-- Reflection in a positive-radius circle sends the punctured open ball to the exterior of the
closed ball. -/
theorem dist_lt_circleReflection_iff {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ c) :
    r < dist (circleReflection c r z) c ↔ dist z c < r := by
  rw [dist_circleReflection_center, lt_div_iff₀ (dist_pos.mpr hz)]
  constructor <;> intro h
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]

/-- Circle reflection is continuous away from the centre. -/
theorem continuousAt_circleReflection {c z : ℂ} {r : ℝ} (hz : z ≠ c) :
    ContinuousAt (circleReflection c r) z := by
  unfold circleReflection
  exact continuousAt_const.add (continuousAt_const.div₀
    (Complex.continuous_conj.continuousAt.comp (continuousAt_id.sub continuousAt_const))
    ((map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hz)))

/-- Circle reflection is continuous on the punctured plane. -/
theorem continuousOn_circleReflection (c : ℂ) (r : ℝ) :
    ContinuousOn (circleReflection c r) ({c}ᶜ : Set ℂ) := by
  intro z hz
  exact continuousAt_circleReflection (Set.mem_compl_singleton_iff.mp hz) |>.continuousWithinAt

/-- Reflection in a nondegenerate circle is a self-homeomorphism of the punctured plane. -/
noncomputable def circleReflectionHomeomorph (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ({c}ᶜ : Set ℂ) ≃ₜ ({c}ᶜ : Set ℂ) where
  toEquiv := circleReflectionEquiv c r hr
  continuous_toFun := (continuousOn_circleReflection c r).restrict.subtype_mk _
  continuous_invFun := by
    have h := (continuousOn_circleReflection c r).restrict.subtype_mk
      (fun z ↦ mapsTo_circleReflection_compl_singleton hr z.2)
    rw [show (circleReflectionEquiv c r hr).invFun = circleReflectionSubtype c r hr by
      funext z
      exact Equiv.congr_fun (circleReflectionEquiv_symm c r hr) z]
    exact h

/-- The punctured-plane homeomorphism acts by circle reflection. -/
@[simp]
theorem coe_circleReflectionHomeomorph_apply (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (z : ({c}ᶜ : Set ℂ)) :
    (circleReflectionHomeomorph c r hr z : ℂ) = circleReflection c r z := by
  simp [circleReflectionHomeomorph]

/-- The punctured-plane circle-reflection homeomorphism is its own inverse. -/
@[simp]
theorem circleReflectionHomeomorph_symm (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    (circleReflectionHomeomorph c r hr).symm = circleReflectionHomeomorph c r hr := by
  apply Homeomorph.toEquiv_injective
  exact circleReflectionEquiv_symm c r hr

end TauCeti
