/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Sections of convex functions

A section of a real function `u` on `Ω`, centered at `x` with slope `ℓ` and height `h`, is
the set of `y ∈ Ω` with `u y < u x + ℓ (y - x) + h`. In an inner product space, taking
`ℓ y = ⟪p, y⟫` gives the usual section with subgradient `p`; at a differentiability point
one takes `ℓ = fderiv ℝ u x`. Keeping the slope as a linear functional allows changes of
coordinates without choosing an inner product.

These sets are the domains on which local Monge–Ampère estimates are normalized. We prove
convexity, openness, height nesting, contraction about the center, and invariance under adding
affine functions. A continuous potential takes the boundary value of the section on its
frontier, and a chord leaving a point of a section through a second point gives an inclusion
into a section at that second point, which is the step behind the engulfing property of
sections. Positive rescaling and linear coordinate changes give the exact unit-height
normalization identity. A supporting slope is required for the nonpositive-height emptiness
statement, but not for convexity or the normalization identities.

The function is real-valued on its specified domain; no extension outside the domain is used.
For an extended-real convex potential one can take its real representative on the interior of
its effective domain.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Birkhäuser, 2016, §1.8.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, EMS, 2017, Chapter 3.
-/

public section

open Set

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {Ω : Set E} {u : E → ℝ} {x y : E} {ℓ : E →ₗ[ℝ] ℝ} {h k : ℝ}

/-- The section of `u` on `Ω` at `x`, with slope `ℓ` and strict height `h`. -/
def convexSection (Ω : Set E) (u : E → ℝ) (x : E) (ℓ : E →ₗ[ℝ] ℝ) (h : ℝ) : Set E :=
  {y ∈ Ω | u y < u x + ℓ (y - x) + h}

/-- Membership in a section is membership in the domain and the strict supporting-plane bound. -/
@[simp]
theorem mem_convexSection_iff :
    y ∈ convexSection Ω u x ℓ h ↔ y ∈ Ω ∧ u y < u x + ℓ (y - x) + h := by
  rfl

/-- A section is contained in its domain. -/
theorem convexSection_subset : convexSection Ω u x ℓ h ⊆ Ω := fun _ hy ↦ hy.1

/-- A section is the strict sublevel set of the potential minus the slope on its domain. -/
theorem convexSection_eq_sep_sub :
    convexSection Ω u x ℓ h = {y ∈ Ω | (u - ℓ) y < u x - ℓ x + h} := by
  ext y
  simp only [mem_convexSection_iff, mem_ofPred_eq, Pi.sub_apply, map_sub]
  constructor <;> rintro ⟨hy, hb⟩ <;> exact ⟨hy, by linarith⟩

/-- Increasing the height enlarges a section. -/
@[gcongr]
theorem convexSection_mono_height (hhk : h ≤ k) :
    convexSection Ω u x ℓ h ⊆ convexSection Ω u x ℓ k := by
  intro y hy
  exact ⟨hy.1, hy.2.trans_le (add_le_add_right hhk _)⟩

/-- A section of a convex function is convex, even when the slope is not supporting. -/
theorem convex_convexSection (hu : ConvexOn ℝ Ω u) : Convex ℝ (convexSection Ω u x ℓ h) := by
  rw [convexSection_eq_sep_sub]
  exact (hu.sub (ℓ.concaveOn hu.1)).convex_lt _

/-- A supporting slope gives a nonempty section exactly at positive heights. -/
theorem convexSection_nonempty_iff (hx : x ∈ Ω)
    (hℓ : ∀ y ∈ Ω, u x + (ℓ y - ℓ x) ≤ u y) :
    (convexSection Ω u x ℓ h).Nonempty ↔ 0 < h := by
  constructor
  · rintro ⟨y, hy⟩
    have := hℓ y hy.1
    have hb := hy.2
    simp only [map_sub] at hb
    linarith
  · intro hh
    exact ⟨x, by simp [mem_convexSection_iff, hx, hh]⟩

/-- At a supporting slope, precisely the nonpositive heights give an empty section. -/
theorem convexSection_eq_empty_iff (hx : x ∈ Ω)
    (hℓ : ∀ y ∈ Ω, u x + (ℓ y - ℓ x) ≤ u y) :
    convexSection Ω u x ℓ h = ∅ ↔ h ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, convexSection_nonempty_iff hx hℓ, not_lt]

/-- Contracting a section by a positive factor at most one about its center contracts its
height by the same factor. This uses convexity and does not require a supporting slope. -/
theorem smul_sub_add_mem_convexSection (hu : ConvexOn ℝ Ω u) (hx : x ∈ Ω)
    (hy : y ∈ convexSection Ω u x ℓ h) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t • (y - x) + x ∈ convexSection Ω u x ℓ (t * h) := by
  have hid : t • (y - x) + x = (1 - t) • x + t • y := by
    module
  rw [hid]
  refine ⟨hu.1 hx hy.1 (by linarith) ht.le (by ring), ?_⟩
  have hconv := hu.2 hx hy.1 (show 0 ≤ 1 - t by linarith) ht.le (by ring : 1 - t + t = 1)
  have hstrict := mul_lt_mul_of_pos_left hy.2 ht
  simp only [map_sub] at hstrict
  simp only [smul_eq_mul] at hconv
  simp only [map_sub, map_add, map_smul, smul_eq_mul]
  nlinarith

/-- **Engulfing along a chord.** Let `m` be a supporting slope at `y`, and let `y` lie above the
plane through `x` with slope `ℓ`. If `z ∈ S(x, h)` and the chord from `z` through `y`, extended
beyond `y` by `t > 0` times its length, ends in `S(x, k)`, then `z` lies in the section at `y`
with slope `m` and height `h + k / t`. No convexity is needed: the supporting plane at `y` lies
below the potential at the end of the chord. -/
theorem mem_convexSection_of_add_smul_sub_mem {m : E →ₗ[ℝ] ℝ} {z : E} {t : ℝ}
    (hℓy : u x + (ℓ y - ℓ x) ≤ u y) (hm : ∀ p ∈ Ω, u y + (m p - m y) ≤ u p)
    (hz : z ∈ convexSection Ω u x ℓ h) (ht : 0 < t)
    (hw : y + t • (y - z) ∈ convexSection Ω u x ℓ k) :
    z ∈ convexSection Ω u y m (h + k / t) := by
  have hmw := hm _ hw.1
  have hwk := hw.2
  have hzh := hz.2
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hmw hwk hzh
  -- The plane at `y` lies below `u` at the end of the chord, which bounds `m (y - z)`.
  have key : (m y - m z) - (ℓ y - ℓ z) < k / t := by
    rw [lt_div_iff₀ ht]
    nlinarith
  refine ⟨hz.1, ?_⟩
  rw [map_sub]
  linarith

/-- Adding an affine function to the potential and its linear part to the slope preserves
every section. -/
@[simp]
theorem convexSection_add_affine (L : E →ₗ[ℝ] ℝ) (c : ℝ) :
    convexSection Ω (fun y ↦ u y + L y + c) x (ℓ + L) h =
      convexSection Ω u x ℓ h := by
  ext y
  simp only [mem_convexSection_iff, LinearMap.add_apply, map_sub]
  constructor <;> rintro ⟨hy, hb⟩ <;> exact ⟨hy, by linarith⟩

/-- Positive rescaling of the potential, slope and height preserves a section. -/
theorem convexSection_mul_pos {a : ℝ} (ha : 0 < a) :
    convexSection Ω (fun y ↦ a * u y) x (a • ℓ) (a * h) =
      convexSection Ω u x ℓ h := by
  ext y
  simp only [mem_convexSection_iff, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_add, ← mul_add, mul_lt_mul_iff_right₀ ha]

/-- Pulling back the domain, potential and slope by a linear map pulls back the section.
The map need not be injective or surjective. -/
theorem convexSection_comp_linearMap (A : F →ₗ[ℝ] E) (z : F) :
    convexSection (A ⁻¹' Ω) (u ∘ A) z (ℓ.comp A) h =
      A ⁻¹' convexSection Ω u (A z) ℓ h := by
  ext w
  simp [mem_convexSection_iff, map_sub]

/-- Translating coordinates translates the center and the domain of a section. -/
theorem convexSection_comp_add (a : E) :
    convexSection ((fun y ↦ y + a) ⁻¹' Ω) (fun y ↦ u (y + a)) x ℓ h =
      (fun y ↦ y + a) ⁻¹' convexSection Ω u (x + a) ℓ h := by
  ext y
  simp [mem_convexSection_iff]

/-- Subtracting the supporting plane, dividing by the positive height, and using coordinates
`y = x + A z` turns a section into a section centered at zero, with zero slope and height one.
For a linear equivalence this is the section normalization used in local estimates. -/
theorem convexSection_normalize (A : F →ₗ[ℝ] E) (hh : 0 < h) :
    convexSection ((fun z ↦ x + A z) ⁻¹' Ω)
        (fun z ↦ (u (x + A z) - u x - ℓ (A z)) / h) 0 0 1 =
      (fun z ↦ x + A z) ⁻¹' convexSection Ω u x ℓ h := by
  ext z
  simp only [mem_convexSection_iff, mem_preimage, map_zero, add_zero, sub_self,
    zero_div, LinearMap.zero_apply, zero_add, add_sub_cancel_left]
  rw [div_lt_iff₀ hh]
  constructor <;> rintro ⟨hz, hb⟩ <;> exact ⟨hz, by linarith⟩

section Topology

variable [TopologicalSpace E]

/-- Sections of a continuous potential on an open domain are open when the slope is
continuous. Convexity is not needed for this assertion. -/
theorem isOpen_convexSection (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) (hℓ : Continuous ℓ) :
    IsOpen (convexSection Ω u x ℓ h) := by
  rw [convexSection_eq_sep_sub]
  exact (hu.sub hℓ.continuousOn).isOpen_inter_preimage hΩ isOpen_Iio

/-- Within the domain, the closure of a section lies in every section of strictly larger
height. Continuity is needed only on the domain, which need not be closed. -/
theorem closure_convexSection_inter_subset (hu : ContinuousOn u Ω) (hℓ : Continuous ℓ)
    (hhk : h < k) :
    closure (convexSection Ω u x ℓ h) ∩ Ω ⊆ convexSection Ω u x ℓ k := by
  rintro y ⟨hy, hyΩ⟩
  have hsub : convexSection Ω u x ℓ h ⊆ Ω := convexSection_subset
  rw [convexSection_eq_sep_sub] at hy hsub ⊢
  have hbound : (u - ℓ) y ≤ u x - ℓ x + h :=
    ContinuousWithinAt.closure_le hy (((hu.sub hℓ.continuousOn) y hyΩ).mono hsub)
      continuousWithinAt_const (fun _ hz ↦ hz.2.le)
  exact ⟨hyΩ, hbound.trans_lt (add_lt_add_right hhk _)⟩

/-- If the closure of a section lies in the open domain of a continuous potential, then on the
frontier of the section the potential equals the supporting plane raised by the height. -/
theorem eq_of_mem_frontier_convexSection (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hℓ : Continuous ℓ) (hS : closure (convexSection Ω u x ℓ h) ⊆ Ω)
    (hy : y ∈ frontier (convexSection Ω u x ℓ h)) : u y = u x + ℓ (y - x) + h := by
  have hyΩ : y ∈ Ω := hS (frontier_subset_closure hy)
  rw [(isOpen_convexSection hΩ hu hℓ).frontier_eq] at hy
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_)
    (not_lt.1 fun hlt => hy.2 ⟨hyΩ, hlt⟩)
  simpa only [add_assoc] using (mem_convexSection_iff.1
    (closure_convexSection_inter_subset hu hℓ (lt_add_of_pos_right h hε) ⟨hy.1, hyΩ⟩)).2

end Topology

end TauCeti
