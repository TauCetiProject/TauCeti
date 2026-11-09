/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Radial homeomorphisms from order isomorphisms of the real line

An order isomorphism `φ` of `ℝ` fixing `0` rescales the norm of every vector of a real normed space
`E` while keeping its direction: `x ↦ (φ ‖x‖ / ‖x‖) • x`. This is a homeomorphism of `E`
(`OrderIso.radialHomeomorph`) with inverse the rescaling by `φ.symm`, and it sends the norm `‖x‖`
to `φ ‖x‖`.

The main use is a homeomorphism of `E` which squeezes a closed ball `closedBall 0 r` into an
arbitrarily small closed ball `closedBall 0 δ` while fixing every point of norm at least `2 * r`
(`TauCeti.exists_homeomorph_mapsTo_closedBall`). Read through an open embedding of `E` and extended
by the identity, it shrinks a compact subset of a Euclidean open piece of a space by a homeomorphism
supported in that piece; this is the basic move in the theory of cellular sets. Dually, a
homeomorphism fixing a small closed ball `closedBall c (δ / 2)` squeezes any closed ball about `c`
into `ball c δ` (`TauCeti.exists_homeomorph_eqOn_closedBall_mapsTo_ball`); this pulls a compact set
towards a point while fixing a neighbourhood of it.

## Main definitions

* `OrderIso.radialHomeomorph`: the radial homeomorphism of `E` rescaling norms by `φ`.

## Main results

* `OrderIso.norm_radialHomeomorph`: it rescales norms by `φ`.
* `TauCeti.exists_homeomorph_mapsTo_closedBall`: a homeomorphism of `E` fixing the points of norm
  at least `2 * r` and mapping `closedBall 0 r` into `closedBall 0 δ`, for any `δ > 0`.
* `TauCeti.exists_homeomorph_eqOn_closedBall_mapsTo_ball`: a homeomorphism of `E` fixing
  `closedBall c (δ / 2)` and mapping `closedBall c r` into `ball c δ`, for any `δ > 0`.
-/

public section

open Set Metric Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace OrderIso

variable (φ : ℝ ≃o ℝ)

/-- The radial rescaling of `E` by `φ`, before it is bundled as a homeomorphism. -/
private noncomputable def radialFun (x : E) : E := (φ ‖x‖ / ‖x‖) • x

private theorem norm_radialFun (hφ : φ 0 = 0) (x : E) : ‖radialFun φ x‖ = φ ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialFun, hφ]
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hφx : 0 ≤ φ ‖x‖ := hφ ▸ φ.monotone hx'.le
  rw [radialFun, norm_smul, Real.norm_of_nonneg (div_nonneg hφx hx'.le), div_mul_cancel₀ _ hx'.ne']

private theorem radialFun_symm_radialFun (hφ : φ 0 = 0) (x : E) :
    radialFun φ.symm (radialFun φ x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialFun]
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hφx : 0 < φ ‖x‖ := hφ ▸ φ.strictMono hx'
  rw [radialFun, norm_radialFun φ hφ, symm_apply_apply, radialFun, smul_smul]
  convert one_smul ℝ x
  field_simp

private theorem continuous_radialFun (hφ : φ 0 = 0) : Continuous (radialFun φ : E → E) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · -- At the origin the rescaled vector has norm `φ ‖y‖`, which tends to `φ 0 = 0`.
    have h0 : radialFun φ (0 : E) = 0 := by simp [radialFun]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_radialFun φ hφ]
    simpa [hφ, Function.comp_def] using (φ.continuous.comp continuous_norm).tendsto (0 : E)
  · exact (((φ.continuous.comp continuous_norm).continuousAt.div continuous_norm.continuousAt
      (norm_ne_zero_iff.2 hx)).smul continuousAt_id)

/-- The **radial homeomorphism** of `E` defined by an order isomorphism `φ` of `ℝ` fixing `0`: it
sends `x` to `(φ ‖x‖ / ‖x‖) • x`, the vector in the direction of `x` with norm `φ ‖x‖`. -/
noncomputable def radialHomeomorph (hφ : φ 0 = 0) : E ≃ₜ E where
  toFun := radialFun φ
  invFun := radialFun φ.symm
  left_inv := radialFun_symm_radialFun φ hφ
  right_inv x := by
    simpa using radialFun_symm_radialFun φ.symm (by rw [symm_apply_eq, hφ]) x
  continuous_toFun := continuous_radialFun φ hφ
  continuous_invFun := continuous_radialFun φ.symm (by rw [symm_apply_eq, hφ])

theorem radialHomeomorph_apply (hφ : φ 0 = 0) (x : E) :
    radialHomeomorph (E := E) φ hφ x = (φ ‖x‖ / ‖x‖) • x :=
  (rfl)

@[simp]
theorem norm_radialHomeomorph (hφ : φ 0 = 0) (x : E) :
    ‖radialHomeomorph (E := E) φ hφ x‖ = φ ‖x‖ :=
  norm_radialFun φ hφ x

@[simp]
theorem radialHomeomorph_symm (hφ : φ 0 = 0) :
    (radialHomeomorph (E := E) φ hφ).symm =
      radialHomeomorph φ.symm (by rw [symm_apply_eq, hφ]) :=
  (rfl)

/-- The radial homeomorphism fixes every vector whose norm `φ` fixes. -/
theorem radialHomeomorph_eq_self (hφ : φ 0 = 0) {x : E} (hx : φ ‖x‖ = ‖x‖) :
    radialHomeomorph φ hφ x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [radialHomeomorph_apply]
  rw [radialHomeomorph_apply, hx, div_self (norm_ne_zero_iff.2 hx0), one_smul]

end OrderIso

namespace TauCeti

/-- **Squeezing a closed ball.** For every `δ > 0` there is a homeomorphism of `E` which fixes every
point of norm at least `2 * r` and maps the closed ball `closedBall 0 r` into `closedBall 0 δ`. -/
theorem exists_homeomorph_mapsTo_closedBall {r δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : E ≃ₜ E, (∀ x, 2 * r ≤ ‖x‖ → ρ x = x) ∧
      MapsTo ρ (closedBall 0 r) (closedBall 0 δ) := by
  rcases le_or_gt r δ with hrδ | hδr
  · exact ⟨Homeomorph.refl E, fun _ _ ↦ rfl, fun x hx ↦ closedBall_subset_closedBall hrδ hx⟩
  have hr : 0 < r := hδ.trans hδr
  -- A radial homeomorphism rescaling the norm by a piecewise linear map.
  set φ : ℝ → ℝ := fun t ↦ min t (max (δ / r * t) (2 * t - 2 * r)) with hφ_def
  have hk : 0 < δ / r := div_pos hδ hr
  have hk1 : δ / r ≤ 1 := (div_le_one hr).2 hδr.le
  have hmono : StrictMono φ := fun s t hst ↦
    min_lt_min hst (max_lt_max (mul_lt_mul_of_pos_left hst hk) (by linarith))
  have hcont : Continuous φ := by fun_prop
  -- `φ` is the identity outside `[0, 2 * r]`.
  have hφ_neg {t : ℝ} (ht : t ≤ 0) : φ t = t :=
    min_eq_left (le_max_of_le_left (by nlinarith))
  have hφ_big {t : ℝ} (ht : 2 * r ≤ t) : φ t = t :=
    min_eq_left (le_max_of_le_right (by linarith))
  have hsurj : Function.Surjective φ := by
    refine hcont.surjective ?_ ?_
    · exact tendsto_id.congr' (eventually_ge_atTop (2 * r) |>.mono fun t ht ↦ (hφ_big ht).symm)
    · exact tendsto_id.congr' (eventually_le_atBot 0 |>.mono fun t ht ↦ (hφ_neg ht).symm)
  set e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective φ hsurj
  have he (t : ℝ) : e t = φ t := rfl
  have he0 : e 0 = 0 := by rw [he, hφ_neg le_rfl]
  refine ⟨e.radialHomeomorph he0, fun x hx ↦ e.radialHomeomorph_eq_self he0 (hφ_big hx),
    fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff, e.norm_radialHomeomorph, he]
  calc φ ‖x‖ ≤ φ r := hmono.monotone (mem_closedBall_zero_iff.1 hx)
    _ ≤ max (δ / r * r) (2 * r - 2 * r) := min_le_right _ _
    _ = δ := by rw [div_mul_cancel₀ _ hr.ne', sub_self, max_eq_left hδ.le]

/-- **Squeezing towards a fixed core.** For every centre `c`, every `δ > 0` and every `r` there is
a homeomorphism of `E` which fixes every point of `closedBall c (δ / 2)` and maps the closed ball
`closedBall c r` into the open ball `ball c δ`. -/
theorem exists_homeomorph_eqOn_closedBall_mapsTo_ball (c : E) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : E ≃ₜ E, EqOn ρ id (closedBall c (δ / 2)) ∧ MapsTo ρ (closedBall c r) (ball c δ) := by
  set a := δ / 2
  have ha : 0 < a := half_pos hδ
  have hδa : a + a = δ := add_halves δ
  set R := max r 0
  -- A radial homeomorphism rescaling the norm by the identity up to `a`, and with slope `k` after.
  set k := a / (a + R)
  have hk : 0 < k := div_pos ha (by positivity)
  have hk1 : k ≤ 1 := (div_le_one (by positivity)).2 (le_add_of_nonneg_right (le_max_right r 0))
  set φ : ℝ → ℝ := fun t ↦ min t (a + k * (t - a)) with hφ_def
  have hmono : StrictMono φ := fun s t hst ↦
    min_lt_min hst (by have := mul_lt_mul_of_pos_left (sub_lt_sub_right hst a) hk; linarith)
  have hcont : Continuous φ := by fun_prop
  have hφ_small {t : ℝ} (ht : t ≤ a) : φ t = t :=
    min_eq_left (by nlinarith)
  have hφ_big {t : ℝ} (ht : a ≤ t) : φ t = a + k * (t - a) :=
    min_eq_right (by nlinarith)
  have hsurj : Function.Surjective φ := by
    refine hcont.surjective ?_ ?_
    · refine (tendsto_atTop_add_const_left _ a
        ((tendsto_atTop_add_const_right _ (-a) tendsto_id).const_mul_atTop hk)).congr' ?_
      filter_upwards [eventually_ge_atTop a] with t ht
      rw [hφ_big ht, sub_eq_add_neg, id]
    · exact tendsto_id.congr' (eventually_le_atBot a |>.mono fun t ht ↦ (hφ_small ht).symm)
  set e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective φ hsurj
  have he (t : ℝ) : e t = φ t := rfl
  have he0 : e 0 = 0 := by rw [he, hφ_small ha.le]
  -- The radial homeomorphism of `e`, centred at `c`.
  refine ⟨(Homeomorph.subRight c).trans ((e.radialHomeomorph he0).trans (Homeomorph.addRight c)),
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [mem_closedBall, dist_eq_norm] at hx
    simp [e.radialHomeomorph_eq_self he0 ((he _).trans (hφ_small hx))]
  rw [mem_closedBall, dist_eq_norm] at hx
  simp only [Homeomorph.trans_apply, Homeomorph.coe_subRight, Homeomorph.coe_addRight, mem_ball,
    dist_eq_norm, add_sub_cancel_right, e.norm_radialHomeomorph, he]
  have hxR : ‖x - c‖ ≤ R := hx.trans (le_max_left r 0)
  have hkR : k * R < a := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  calc φ ‖x - c‖ ≤ a + k * (‖x - c‖ - a) := min_le_right _ _
    _ ≤ a + k * R := by nlinarith [norm_nonneg (x - c)]
    _ < δ := by linarith

end TauCeti
