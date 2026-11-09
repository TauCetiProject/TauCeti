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
supported in that piece; this is the basic move in the theory of cellular sets. A variant fixes a
smaller closed ball `closedBall 0 t`, `t < δ`, pointwise
(`TauCeti.exists_homeomorph_eqOn_closedBall_mapsTo_closedBall`), so that the squeeze is the identity
near the centre.

## Main definitions

* `OrderIso.radialHomeomorph`: the radial homeomorphism of `E` rescaling norms by `φ`.

## Main results

* `OrderIso.norm_radialHomeomorph`: it rescales norms by `φ`.
* `TauCeti.exists_homeomorph_mapsTo_closedBall`: a homeomorphism of `E` fixing the points of norm
  at least `2 * r` and mapping `closedBall 0 r` into `closedBall 0 δ`, for any `δ > 0`.
* `TauCeti.exists_homeomorph_eqOn_closedBall_mapsTo_closedBall`: a homeomorphism of `E` fixing
  `closedBall 0 t` pointwise and mapping `closedBall 0 r` into `closedBall 0 δ`, for `0 ≤ t < δ`.
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

/-- **Squeezing a closed ball around a fixed core.** For `0 ≤ t < δ` there is a homeomorphism of
`E` which fixes every point of `closedBall 0 t` and maps `closedBall 0 r` into
`closedBall 0 δ`. -/
theorem exists_homeomorph_eqOn_closedBall_mapsTo_closedBall {t r δ : ℝ} (ht : 0 ≤ t)
    (htδ : t < δ) :
    ∃ ρ : E ≃ₜ E, EqOn ρ id (closedBall 0 t) ∧ MapsTo ρ (closedBall 0 r) (closedBall 0 δ) := by
  rcases le_or_gt r δ with hrδ | hδr
  · exact ⟨Homeomorph.refl E, fun _ _ ↦ rfl, fun x hx ↦ closedBall_subset_closedBall hrδ hx⟩
  have hr : 0 < r := by linarith
  -- A radial homeomorphism rescaling the norm by the identity up to `t`, and beyond `t` by the
  -- affine map of slope `k = (δ - t) / r ∈ (0, 1]` through `(t, t)`.
  set k := (δ - t) / r with hk_def
  have hk : 0 < k := div_pos (by linarith) hr
  have hk1 : k ≤ 1 := (div_le_one hr).2 (by linarith)
  have hkr : k * r = δ - t := div_mul_cancel₀ _ hr.ne'
  set φ : ℝ → ℝ := fun s ↦ min s (t + k * (s - t)) with hφ_def
  have hmono : StrictMono φ := fun s s' hss' ↦
    min_lt_min hss' (by nlinarith)
  have hcont : Continuous φ := by fun_prop
  have hφ_le {s : ℝ} (hs : s ≤ t) : φ s = s := min_eq_left (by nlinarith)
  have hsurj : Function.Surjective φ := by
    refine hcont.surjective ?_ ?_
    · have : Tendsto (fun s ↦ t + k * (s - t)) atTop atTop :=
        tendsto_atTop_add_const_left _ _
          ((tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop hk)
      exact this.congr' (eventually_ge_atTop t |>.mono fun s hs ↦
        (min_eq_right (by nlinarith)).symm)
    · exact tendsto_id.congr' (eventually_le_atBot t |>.mono fun s hs ↦ (hφ_le hs).symm)
  set e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective φ hsurj
  have he (s : ℝ) : e s = φ s := rfl
  have he0 : e 0 = 0 := by rw [he, hφ_le ht]
  refine ⟨e.radialHomeomorph he0, fun x hx ↦ e.radialHomeomorph_eq_self he0 ?_, fun x hx ↦ ?_⟩
  · rw [he, hφ_le (mem_closedBall_zero_iff.1 hx)]
  · rw [mem_closedBall_zero_iff, e.norm_radialHomeomorph, he]
    calc φ ‖x‖ ≤ φ r := hmono.monotone (mem_closedBall_zero_iff.1 hx)
      _ ≤ t + k * (r - t) := min_le_right _ _
      _ ≤ δ := by nlinarith

end TauCeti
