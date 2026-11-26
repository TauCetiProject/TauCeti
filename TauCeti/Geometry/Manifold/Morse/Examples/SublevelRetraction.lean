/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Deformation
import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell

/-!
# Retracting the sublevels of the quadratic well

For `f(x) = x²` on `ℝ` and `0 ≤ a`, the sublevel `{x² ≤ a}` is the interval `[-√a, √a]`. Clamping
to this interval, `x ↦ max (-√a) (min √a x)`, maps every sublevel `{x² ≤ b}` into it
(`TauCeti.sqSublevelRetraction`), and for `a ≤ b` it is a retraction of `{x² ≤ b}` onto it
(`TauCeti.sqSublevelRetraction_sublevelInclusion`): it fixes `[-√a, √a]` and sends a point `x`
outside it to `sign(x) √a` (`TauCeti.coe_sqSublevelRetraction_apply_of_sqrt_le`,
`TauCeti.coe_sqSublevelRetraction_apply_of_le_neg_sqrt`). This is where the descent at unit speed
along the field `-1 / (2x)`, for which `f` decreases with derivative `-1`, takes a point `x` of the
band `f⁻¹[a, b]` at time `x² - a`.

The sublevels are taken with `≤`, not `<`: the point `x = 1` of the level `x² = 1` lies in
`{x² ≤ 1}` and stays in `{x² ≤ 4}` under the inclusion `TauCeti.sublevelInclusion`, while the strict
sublevel `{x² < 1}` excludes it.

This file tests two statements about the retractions across a band without critical points on this
example.

* **Uniqueness up to homotopy.** For `0 < a ≤ b` the band `f⁻¹[a, b]` is compact and contains no
  critical point, so every retraction of `{x² ≤ b}` onto `{x² ≤ a}` is homotopic to the clamp
  relative to `{x² ≤ a}` (`TauCeti.homotopicRel_sqSublevelRetraction`, an instance of
  `TauCeti.homotopicRel_sublevel_retraction`).
* **Restriction to smaller bands.** For `a ≤ a'` and `b' ≤ b`, restricting the clamp of `{x² ≤ b}`
  into `{x² ≤ a}` to `{x² ≤ b'}` is equal, not merely homotopic, to the composite of the clamp of
  `{x² ≤ b'}` into `{x² ≤ a'}` and the clamp of `{x² ≤ a'}` onto `{x² ≤ a}`
  (`TauCeti.sqSublevelRetraction_comp_sublevelInclusion`): a point of `[√a', √b']` goes to `√a'`
  and then to `√a`, which is where the clamp onto `[-√a, √a]` sends it. In general these two maps
  agree only up to homotopy relative to the lower sublevel
  (`TauCeti.homotopicRel_sublevel_retraction_comp_sublevelInclusion`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

/-- **Sublevels are taken with `≤`, not `<`.** The point `x = 1` on the level `x² = 1` lies in the
sublevel `{x² ≤ 1}`, and the inclusion of `{x² ≤ 1}` into `{x² ≤ 4}` keeps it. -/
example : (sublevelInclusion (fun x : ℝ ↦ x ^ 2) 1 4 (by norm_num) ⟨1, by norm_num⟩ : ℝ) = 1 :=
  coe_sublevelInclusion_apply _ _ _

/-- The strict sublevel `{x² < 1}` does not contain the point `x = 1` of the level `x² = 1`. -/
example : (1 : ℝ) ∉ {x : ℝ | x ^ 2 < 1} := by
  norm_num

/-- The clamp of the sublevel `{x² ≤ b}` of `x ↦ x²` on `ℝ` into the sublevel
`{x² ≤ a} = [-√a, √a]`, for `0 ≤ a`, sending `x` to the nearest point of that interval by
`Set.projIcc`. For `a ≤ b` it is a retraction of `{x² ≤ b}` onto `{x² ≤ a}`
(`TauCeti.sqSublevelRetraction_sublevelInclusion`). -/
noncomputable def sqSublevelRetraction {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    C({x : ℝ | x ^ 2 ≤ b}, {x : ℝ | x ^ 2 ≤ a}) where
  toFun x := ⟨projIcc (-√a) √a (neg_le_self (Real.sqrt_nonneg a)) x,
    (Real.sq_le ha).2 (projIcc (-√a) √a (neg_le_self (Real.sqrt_nonneg a)) x).property⟩
  continuous_toFun := (continuous_subtypeVal.comp
    (continuous_projIcc.comp continuous_subtypeVal)).subtype_mk _

@[simp]
theorem coe_sqSublevelRetraction_apply {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (x : {x : ℝ | x ^ 2 ≤ b}) :
    (sqSublevelRetraction ha b x : ℝ) = max (-√a) (min √a x) :=
  (rfl)

/-- `TauCeti.sqSublevelRetraction` is a retraction: it fixes the sublevel `{x² ≤ a}`. -/
@[simp]
theorem sqSublevelRetraction_sublevelInclusion {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (x : {x : ℝ | x ^ 2 ≤ a}) :
    sqSublevelRetraction ha b (sublevelInclusion (fun x : ℝ ↦ x ^ 2) a b hab x) = x := by
  ext
  rw [coe_sqSublevelRetraction_apply, coe_sublevelInclusion_apply,
    ← coe_projIcc _ _ (neg_le_self (Real.sqrt_nonneg a)),
    projIcc_of_mem _ ((Real.sq_le ha).1 x.property)]

/-- `TauCeti.sqSublevelRetraction` sends a point `x ≥ √a` to `√a`. -/
theorem coe_sqSublevelRetraction_apply_of_sqrt_le {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    {x : {x : ℝ | x ^ 2 ≤ b}} (hx : √a ≤ x) : (sqSublevelRetraction ha b x : ℝ) = √a := by
  rw [coe_sqSublevelRetraction_apply, ← coe_projIcc _ _ (neg_le_self (Real.sqrt_nonneg a)),
    projIcc_of_right_le _ hx]

/-- `TauCeti.sqSublevelRetraction` sends a point `x ≤ -√a` to `-√a`. -/
theorem coe_sqSublevelRetraction_apply_of_le_neg_sqrt {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    {x : {x : ℝ | x ^ 2 ≤ b}} (hx : (x : ℝ) ≤ -√a) :
    (sqSublevelRetraction ha b x : ℝ) = -√a := by
  rw [coe_sqSublevelRetraction_apply, ← coe_projIcc _ _ (neg_le_self (Real.sqrt_nonneg a)),
    projIcc_of_le_left _ hx]

/-- **Clamping across nested bands.** For `0 ≤ a ≤ a'` and `b' ≤ b`, the clamp of `{x² ≤ b}` into
`{x² ≤ a}`, restricted to `{x² ≤ b'}`, is the clamp of `{x² ≤ b'}` into `{x² ≤ a'}` followed by
the retraction of `{x² ≤ a'}` onto `{x² ≤ a}`. -/
theorem sqSublevelRetraction_comp_sublevelInclusion {a a' b' b : ℝ} (ha : 0 ≤ a)
    (haa' : a ≤ a') (hb'b : b' ≤ b) :
    (sqSublevelRetraction ha b).comp (sublevelInclusion (fun x : ℝ ↦ x ^ 2) b' b hb'b) =
      (sqSublevelRetraction ha a').comp (sqSublevelRetraction (ha.trans haa') b') := by
  ext x
  have h : √a ≤ √a' := Real.sqrt_le_sqrt haa'
  have h0 := Real.sqrt_nonneg a
  simp only [ContinuousMap.comp_apply, coe_sqSublevelRetraction_apply,
    coe_sublevelInclusion_apply, max_def, min_def]
  split_ifs <;> linarith

/-- **The clamp is the retraction across the band, up to homotopy.** For `0 < a ≤ b` the band
`{a ≤ x² ≤ b}` is compact and contains no critical point of `x ↦ x²`, so every retraction of
`{x² ≤ b}` onto `{x² ≤ a}` is homotopic to `TauCeti.sqSublevelRetraction` relative to
`{x² ≤ a}`. -/
theorem homotopicRel_sqSublevelRetraction {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {r : C({x : ℝ | x ^ 2 ≤ b}, {x : ℝ | x ^ 2 ≤ a})}
    (hr : ∀ x, r (sublevelInclusion (fun x : ℝ ↦ x ^ 2) a b hab x) = x) :
    (sqSublevelRetraction ha.le b).HomotopicRel r {x | (x : ℝ) ^ 2 ≤ a} := by
  refine homotopicRel_sublevel_retraction (I := 𝓘(ℝ, ℝ)) (f := fun x : ℝ ↦ x ^ 2)
    (contMDiff_iff_contDiff.2 (contDiff_id.pow 2)) hab ?_ ?_
    (sqSublevelRetraction_sublevelInclusion ha.le hab) hr
  · exact (isCompact_Icc (a := -√b) (b := √b)).of_isClosed_subset
      (isClosed_Icc.preimage (by fun_prop)) fun x hx ↦ (Real.sq_le (ha.le.trans hab)).1 hx.2
  · intro x hax _ h
    have hx : x ∉ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) := by
      rw [criticalPoints_sq_real, mem_singleton_iff]
      rintro rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hax
      linarith
    rw [mem_criticalPoints_iff_fderiv_eq_zero] at hx
    rw [mfderiv_eq_fderiv] at h
    exact hx h

end TauCeti
