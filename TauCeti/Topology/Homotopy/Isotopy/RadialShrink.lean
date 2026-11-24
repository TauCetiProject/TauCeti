/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.UnitInterval
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Radial compressions of a normed space

For `0 < r` and `0 ≤ s`, the radial compression `v ↦ (1 + s ‖v‖ / r)⁻¹ • v` of a real normed
space `V` is a homeomorphism of `V` onto the open set `{u | s ‖u‖ < r}`, the ball of radius `r / s`
when `s > 0`, with inverse `u ↦ (1 - s ‖u‖ / r)⁻¹ • u`. At `s = 0` it is the identity, and it is
tangent to the identity at `0`. Running `s` over `[0, 1]` gives an isotopy of open embeddings of
`X × V` from the identity to the fibrewise compression onto `X × B(0, r)`; it shrinks a tube
`X × V → M` into a ball without changing it up to isotopy.

## Main definitions

* `TauCeti.radialShrink r s`: the radial compression `v ↦ (1 + s ‖v‖ / r)⁻¹ • v`.
* `TauCeti.radialExpand r s`: its inverse `u ↦ (1 - s ‖u‖ / r)⁻¹ • u` on `{u | s ‖u‖ < r}`.

## Main results

* `TauCeti.radialExpand_radialShrink`, `TauCeti.radialShrink_radialExpand`: the two maps are
  mutually inverse.
* `TauCeti.norm_radialShrink_sub_le`: the compression moves `v` by at most `s ‖v‖² / r`.
* `TauCeti.isOpenEmbedding_prodMap_radialShrink`: the fibrewise compression of `X × V` is an open
  embedding.
* `TauCeti.isOpenEmbedding_radialShrink_family`: the compressions for `s ∈ [0, 1]` form an
  isotopy of open embeddings of `X × V`.
-/

public section

open Function Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial compression `v ↦ (1 + s ‖v‖ / r)⁻¹ • v`. For `0 ≤ s` and `0 < r` it is a
homeomorphism of `V` onto the open set `{u | s ‖u‖ < r}`, the ball of radius `r / s` when `s > 0`,
with inverse `TauCeti.radialExpand r s`. -/
noncomputable def radialShrink (r s : ℝ) (v : V) : V :=
  (1 + s * ‖v‖ / r)⁻¹ • v

/-- The inverse `u ↦ (1 - s ‖u‖ / r)⁻¹ • u` of the radial compression on `{u | s ‖u‖ < r}`. -/
noncomputable def radialExpand (r s : ℝ) (u : V) : V :=
  (1 - s * ‖u‖ / r)⁻¹ • u

variable {r s : ℝ}

theorem radialShrink_def (r s : ℝ) (v : V) : radialShrink r s v = (1 + s * ‖v‖ / r)⁻¹ • v :=
  (rfl)

theorem radialExpand_def (r s : ℝ) (u : V) : radialExpand r s u = (1 - s * ‖u‖ / r)⁻¹ • u :=
  (rfl)

@[simp]
theorem radialShrink_zero (r s : ℝ) : radialShrink r s (0 : V) = 0 := by
  simp [radialShrink_def]

/-- At `s = 0` the compression is the identity. -/
@[simp]
theorem radialShrink_zero_left (r : ℝ) (v : V) : radialShrink r 0 v = v := by
  simp [radialShrink_def]

omit [NormedSpace ℝ V] in
private theorem radialShrink_factor_pos (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    0 < 1 + s * ‖v‖ / r := by
  positivity

theorem norm_radialShrink (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    ‖radialShrink r s v‖ = ‖v‖ / (1 + s * ‖v‖ / r) := by
  rw [radialShrink, norm_smul, norm_inv, Real.norm_of_nonneg (radialShrink_factor_pos hr hs v).le,
    inv_mul_eq_div]

/-- The compression maps `V` into `{u | s ‖u‖ < r}`. -/
theorem mul_norm_radialShrink_lt (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    s * ‖radialShrink r s v‖ < r := by
  have h := radialShrink_factor_pos hr hs v
  rw [norm_radialShrink hr hs, ← mul_div_assoc, div_lt_iff₀ h, mul_add, mul_one,
    mul_div_cancel₀ _ hr.ne']
  linarith

theorem norm_radialShrink_le (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    ‖radialShrink r s v‖ ≤ ‖v‖ := by
  rw [norm_radialShrink hr hs]
  exact div_le_self (norm_nonneg v) (le_add_of_nonneg_right (by positivity))

theorem radialExpand_radialShrink (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    radialExpand r s (radialShrink r s v) = v := by
  have h := radialShrink_factor_pos hr hs v
  have key : 1 - s * ‖radialShrink r s v‖ / r = (1 + s * ‖v‖ / r)⁻¹ := by
    rw [norm_radialShrink hr hs]
    field_simp
    ring
  rw [radialExpand, key, inv_inv, radialShrink, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

theorem radialShrink_radialExpand (hr : 0 < r) {u : V} (hu : s * ‖u‖ < r) :
    radialShrink r s (radialExpand r s u) = u := by
  have h : 0 < 1 - s * ‖u‖ / r := by
    rw [sub_pos, div_lt_one hr]
    exact hu
  have key : 1 + s * ‖radialExpand r s u‖ / r = (1 - s * ‖u‖ / r)⁻¹ := by
    rw [radialExpand, norm_smul, norm_inv, Real.norm_of_nonneg h.le]
    field_simp
    ring
  rw [radialShrink, key, inv_inv, radialExpand, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

/-- The compression moves `v` by at most `s ‖v‖² / r`; it is tangent to the identity at `0`. -/
theorem norm_radialShrink_sub_le (hr : 0 < r) (hs : 0 ≤ s) (v : V) :
    ‖radialShrink r s v - v‖ ≤ s * ‖v‖ ^ 2 / r := by
  set a := 1 + s * ‖v‖ / r with ha
  have ha1 : 1 ≤ a := le_add_of_nonneg_right (by positivity)
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have h1 : 1 - a⁻¹ = (a - 1) / a := by field_simp
  have hb : 1 - a⁻¹ ≤ s * ‖v‖ / r := by
    rw [h1]
    calc (a - 1) / a ≤ a - 1 := div_le_self (by linarith) ha1
      _ = s * ‖v‖ / r := by rw [ha]; ring
  have hv : radialShrink r s v - v = (a⁻¹ - 1) • v := by rw [radialShrink, ← ha, sub_smul, one_smul]
  rw [hv, norm_smul, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (by rw [h1]; exact div_nonneg (by linarith) ha0.le)]
  calc (1 - a⁻¹) * ‖v‖ ≤ s * ‖v‖ / r * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    _ = s * ‖v‖ ^ 2 / r := by ring

theorem continuous_radialShrink (hr : 0 < r) {X : Type*} [TopologicalSpace X]
    {s : X → ℝ} {v : X → V} (hs : Continuous s) (hs₀ : ∀ x, 0 ≤ s x) (hv : Continuous v) :
    Continuous fun x ↦ radialShrink r (s x) (v x) :=
  ((continuous_const.add ((hs.mul hv.norm).div_const r)).inv₀
    fun x ↦ (radialShrink_factor_pos hr (hs₀ x) (v x)).ne').smul hv

theorem continuousOn_radialExpand (hr : 0 < r) {X : Type*} [TopologicalSpace X]
    {s : X → ℝ} {u : X → V} (hs : Continuous s) (hu : Continuous u) :
    ContinuousOn (fun x ↦ radialExpand r (s x) (u x)) {x | s x * ‖u x‖ < r} := by
  refine (ContinuousOn.inv₀ (f := fun x ↦ 1 - s x * ‖u x‖ / r) (by fun_prop)
    fun x hx ↦ ?_).smul hu.continuousOn
  have : s x * ‖u x‖ / r < 1 := (div_lt_one hr).2 hx
  exact (sub_pos.2 this).ne'

variable {X : Type*} [TopologicalSpace X]

/-- For `0 ≤ s`, the fibrewise compression `(x, v) ↦ (x, (1 + s ‖v‖ / r)⁻¹ • v)` is an open
embedding of `X × V`. -/
theorem isOpenEmbedding_prodMap_radialShrink (hr : 0 < r) (hs : 0 ≤ s) :
    IsOpenEmbedding (Prod.map id (radialShrink r s) : X × V → X × V) :=
  IsOpenEmbedding.id.prodMap <| IsOpenEmbedding.of_continuousOn_inverse (W := {u | s * ‖u‖ < r})
    (continuous_radialShrink hr continuous_const (fun _ ↦ hs) continuous_id)
    (isOpen_lt (by fun_prop) continuous_const)
    (continuousOn_radialExpand hr continuous_const continuous_id)
    (mul_norm_radialShrink_lt hr hs) (radialExpand_radialShrink hr hs)
    fun _ hu ↦ radialShrink_radialExpand hr hu

/-- The compressions for `s ∈ [0, 1]` form an isotopy of open embeddings, from the identity to the
compression onto `X × B(0, r)`: the total map `(s, x, v) ↦ (s, x, (1 + s ‖v‖ / r)⁻¹ • v)` is an
open embedding of `[0, 1] × (X × V)`. -/
theorem isOpenEmbedding_radialShrink_family (hr : 0 < r) :
    IsOpenEmbedding fun q : unitInterval × (X × V) ↦ (q.1, (q.2.1, radialShrink r q.1 q.2.2)) := by
  refine IsOpenEmbedding.of_continuousOn_inverse (W := {q | (q.1 : ℝ) * ‖q.2.2‖ < r})
    (g := fun q ↦ (q.1, (q.2.1, radialExpand r q.1 q.2.2)))
    (continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_radialShrink hr
      (continuous_subtypeVal.comp continuous_fst) (fun q ↦ q.1.property.1) continuous_snd.snd)))
    (isOpen_lt (by fun_prop) continuous_const)
    (continuous_fst.continuousOn.prodMk (continuous_snd.fst.continuousOn.prodMk
      (continuousOn_radialExpand hr (continuous_subtypeVal.comp continuous_fst)
        continuous_snd.snd)))
    (fun q ↦ mul_norm_radialShrink_lt hr q.1.property.1 q.2.2) (fun q ↦ ?_) fun q hq ↦ ?_
  · rw [radialExpand_radialShrink hr q.1.property.1]
  · rw [radialShrink_radialExpand hr hq]

end TauCeti
