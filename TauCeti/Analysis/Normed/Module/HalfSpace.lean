/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-!
# Half-spaces of a real normed space

A strict half-space `{y | φ y < u}` cut out by a nonzero linear functional holds points of
arbitrarily large norm, and is therefore unbounded. Linearity alone suffices: `φ` need not be
continuous, so the results apply to a discontinuous functional on an infinite-dimensional space.
For such a `φ` the set need not be topologically open, which is why it is called strict rather
than open here.

For continuous functionals, the second part of the file describes the interior of an
intersection of closed half-spaces `{x | 0 ≤ φ i x}` over a compact family of indices `i ∈ S` on
which `φ` depends continuously: as soon as no `φ i` vanishes, the interior is the intersection
`{x | ∀ i ∈ S, 0 < φ i x}` of the open half-spaces. Compactness makes this intersection open; it
is what identifies a closed convex cone given by infinitely many linear inequalities, such as a
cone of curvature tensors, with its strict counterpart.

## Main results

* `TauCeti.exists_apply_lt_and_lt_norm` and `TauCeti.exists_lt_apply_and_lt_norm` — either side
  of a nonzero linear functional holds points of arbitrarily large norm.
* `TauCeti.not_isBounded_halfSpace_lt` and `TauCeti.not_isBounded_halfSpace_gt` — either strict
  half-space is unbounded.
* `TauCeti.isOpen_setOf_forall_mem_pos_apply` — over a compact continuous family of continuous
  functionals, the intersection of the open half-spaces is open.
* `TauCeti.interior_setOf_forall_mem_nonneg_apply` — the interior of the intersection of the
  closed half-spaces is the intersection of the open ones.
* `TauCeti.interior_setOf_forall_nonneg_apply` — the same for a continuous family indexed by a
  proper space that scales quadratically, `φ (c • v) = c ^ 2 • φ v`: the conditions on the unit
  sphere, which is compact, are those at every vector, respectively every nonzero vector.
-/

public section

namespace TauCeti

open Bornology Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A strict half-space contains points of arbitrarily large norm.** For a nonzero linear
functional `φ`, every bound `u` and every radius `R` admit a `y` with `φ y < u` and `R < ‖y‖`.
Linearity suffices; `φ` need not be continuous. -/
theorem exists_apply_lt_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, φ y < u ∧ R < ‖y‖ := by
  obtain ⟨v, hv⟩ := LinearMap.surjective_iff_ne_zero.mpr hφ (-1)
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr <| by rintro rfl; simp at hv
  -- Walk along the ray `t • v`, where `φ = -t`, past both the bound `u` and the radius `R`.
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, (R + 1) / ‖v‖ ≤ t ∧ |u| + 1 ≤ t :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  refine ⟨t • v, ?_, ?_⟩
  · simp only [map_smul, hv, smul_eq_mul, mul_neg_one]
    linarith [neg_abs_le u]
  · rw [norm_smul, Real.norm_of_nonneg (by linarith [abs_nonneg u])]
    linarith [(div_le_iff₀ hv0).mp ht1]

/-- **The other side of a nonzero linear functional also contains points of arbitrarily large
norm**: every bound `u` and radius `R` admit a `y` with `u < φ y` and `R < ‖y‖`. -/
theorem exists_lt_apply_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, u < φ y ∧ R < ‖y‖ := by
  simpa using exists_apply_lt_and_lt_norm (neg_ne_zero.mpr hφ) (-u) R

/-- **A strict half-space cut out by a nonzero linear functional is unbounded.** No radius bounds
`{y | φ y < u}`. Linearity suffices; `φ` need not be continuous. -/
theorem not_isBounded_halfSpace_lt {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | φ y < u} := by
  rw [isBounded_iff_forall_norm_le]
  push Not
  exact exists_apply_lt_and_lt_norm hφ u

/-- **The half-space on the other side of a nonzero linear functional is unbounded.** No radius
bounds `{y | u < φ y}` either. Linearity suffices; `φ` need not be continuous. -/
theorem not_isBounded_halfSpace_gt {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | u < φ y} := by
  simpa using not_isBounded_halfSpace_lt (neg_ne_zero.mpr hφ) (-u)

/-! ### Intersections of half-spaces over a compact family -/

section Compact

variable {ι : Type*} [TopologicalSpace ι] {S : Set ι} {φ : ι → StrongDual ℝ E}

/-- **Over a compact family, the intersection of open half-spaces is open.** If `φ` depends
continuously on `i` in the compact set `S`, then `{x | ∀ i ∈ S, 0 < φ i x}` is open. -/
theorem isOpen_setOf_forall_mem_pos_apply (hS : IsCompact S) (hφ : ContinuousOn φ S) :
    IsOpen {x | ∀ i ∈ S, 0 < φ i x} := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hcont : Continuous fun p : E × S ↦ φ p.2 p.1 :=
    (hφ.domRestrict.comp continuous_snd).clm_apply continuous_fst
  refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  -- The tube lemma over the compact space `S` turns pointwise neighbourhoods into a uniform one.
  filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually (x₀ := x)
    (P := fun y (i : S) ↦ 0 < φ i y)
    fun i _ ↦ hcont.continuousAt.eventually (lt_mem_nhds (hx i i.property))] with y hy i hi
  exact hy ⟨i, hi⟩ (mem_univ _)

/-- **The interior of an intersection of closed half-spaces over a compact family.** If `φ`
depends continuously on `i` in the compact set `S` and no `φ i` with `i ∈ S` vanishes, then the
interior of `{x | ∀ i ∈ S, 0 ≤ φ i x}` is `{x | ∀ i ∈ S, 0 < φ i x}`. -/
theorem interior_setOf_forall_mem_nonneg_apply (hS : IsCompact S) (hφ : ContinuousOn φ S)
    (hφ₀ : ∀ i ∈ S, φ i ≠ 0) :
    interior {x | ∀ i ∈ S, 0 ≤ φ i x} = {x | ∀ i ∈ S, 0 < φ i x} := by
  refine Subset.antisymm (fun x hx i hi ↦ ?_)
    ((isOpen_setOf_forall_mem_pos_apply hS hφ).subset_interior_iff.mpr fun x hx i hi ↦
      (hx i hi).le)
  -- Push `x` slightly against a direction `y` in which `φ i` increases; it stays in the set.
  obtain ⟨y, hy⟩ : ∃ y, 0 < φ i y := by
    obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (hφ₀ i hi)
    rw [zero_apply] at hy
    rcases hy.lt_or_gt with h | h
    · exact ⟨-y, by simpa using h⟩
    · exact ⟨y, h⟩
  have hlim : Tendsto (fun t : ℝ ↦ x - t • y) (𝓝[>] 0) (𝓝 x) := by
    have : Tendsto (fun t : ℝ ↦ x - t • y) (𝓝 0) (𝓝 (x - (0 : ℝ) • y)) :=
      tendsto_const_nhds.sub (tendsto_id.smul_const y)
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, ht₀⟩ :=
    ((hlim.eventually (mem_interior_iff_mem_nhds.mp hx)).and self_mem_nhdsWithin).exists
  have := ht i hi
  rw [map_sub, map_smul, smul_eq_mul] at this
  nlinarith [mem_Ioi.mp ht₀]

end Compact

/-! ### Quadratically homogeneous families -/

section Homogeneous

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : F → StrongDual ℝ E}

/-- For a family of functionals scaling as `φ (c • v) = c ^ 2 • φ v`, nonnegativity on the unit
sphere is nonnegativity everywhere. -/
theorem setOf_forall_mem_sphere_nonneg_apply (hφ : ∀ (c : ℝ) v, φ (c • v) = c ^ 2 • φ v) :
    {x | ∀ v ∈ Metric.sphere (0 : F) 1, 0 ≤ φ v x} = {x | ∀ v, 0 ≤ φ v x} := by
  refine Subset.antisymm (fun x hx v ↦ ?_) fun x hx v _ ↦ hx v
  rcases eq_or_ne v 0 with rfl | hv
  · simp [show φ 0 = 0 by simpa using hφ 0 0]
  have h := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)])
  rw [hφ, smul_apply, smul_eq_mul] at h
  exact nonneg_of_mul_nonneg_right h (pow_pos (inv_pos.mpr (norm_pos_iff.mpr hv)) 2)

/-- For a family of functionals scaling as `φ (c • v) = c ^ 2 • φ v`, positivity on the unit sphere
is positivity at every nonzero vector. -/
theorem setOf_forall_mem_sphere_pos_apply (hφ : ∀ (c : ℝ) v, φ (c • v) = c ^ 2 • φ v) :
    {x | ∀ v ∈ Metric.sphere (0 : F) 1, 0 < φ v x} = {x | ∀ v ≠ 0, 0 < φ v x} := by
  refine Subset.antisymm (fun x hx v hv ↦ ?_) fun x hx v hv ↦ hx v (by rintro rfl; simp at hv)
  have h := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)])
  rw [hφ, smul_apply, smul_eq_mul] at h
  exact pos_of_mul_pos_right h (by positivity)

/-- **The interior of the cone cut out by a quadratically homogeneous family.** If `φ` is
continuous on a proper space (for instance a finite-dimensional one), scales as
`φ (c • v) = c ^ 2 • φ v`, and `φ v ≠ 0` for `v ≠ 0`, then the interior of
`{x | ∀ v, 0 ≤ φ v x}` is `{x | ∀ v ≠ 0, 0 < φ v x}`. -/
theorem interior_setOf_forall_nonneg_apply [ProperSpace F] (hcont : Continuous φ)
    (hφ : ∀ (c : ℝ) v, φ (c • v) = c ^ 2 • φ v) (hφ₀ : ∀ v ≠ 0, φ v ≠ 0) :
    interior {x | ∀ v, 0 ≤ φ v x} = {x | ∀ v ≠ 0, 0 < φ v x} := by
  rw [← setOf_forall_mem_sphere_nonneg_apply hφ, ← setOf_forall_mem_sphere_pos_apply hφ]
  exact interior_setOf_forall_mem_nonneg_apply (isCompact_sphere 0 1) hcont.continuousOn
    fun v hv ↦ hφ₀ v (by rintro rfl; simp at hv)

end Homogeneous

end TauCeti
