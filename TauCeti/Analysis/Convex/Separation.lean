/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Proof-only: strict separation, Riesz representation, and affine-span interiority in finite
-- dimension.
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Separation of points from open convex sets and supporting hyperplanes

In a real Hilbert space, a point outside a nonempty open convex set `W` is strictly separated from
`W` by a continuous linear functional (`geometric_hahn_banach_open_point`). By the Riesz
representation, such a functional is a positive multiple of the height `x ↦ ⟪u, x⟫` along a unit
vector `u`. Hence a set whose heights along every unit vector are heights of points of `W` is
contained in `W`.

In finite dimension, every frontier point `x ∈ frontier C` of a convex set `C` admits a supporting
hyperplane (`Convex.exists_ne_zero_forall_closure_inner_sub_nonpos`, Rockafellar's Theorem 11.6):
when `interior C` is nonempty this comes from separating `x` from `interior C`, and when
`interior C` is empty `affineSpan ℝ C` is a proper closed affine subspace whose orthogonal
complement supplies a nonzero normal.

## Main results

* `Convex.subset_of_image_inner_subset`: a set whose heights along every unit vector are heights
  of points of a nonempty open convex set `W` is contained in `W`.
* `Convex.exists_norm_eq_one_closure_subset_setOf_inner_eq`: the closure of a nonempty convex
  set with empty interior in a finite-dimensional real inner product space lies in an affine
  hyperplane `{x | ⟪x, e⟫ = c}` with unit normal `e`.
* `Convex.exists_ne_zero_forall_closure_inner_sub_nonpos`: at every frontier point `x` of a convex
  set `C` in a finite-dimensional real inner product space, there is a nonzero vector `y` with
  `⟪z - x, y⟫ ≤ 0` for all `z ∈ closure C`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 11.6.
-/

public section

open Set
open scoped RealInnerProductSpace

/-- **Containment in an open convex set from directional images.** If the heights `⟪u, x⟫` of the
points of `U` along every unit vector `u` are heights of points of a nonempty open convex set `W`,
then `U ⊆ W`: a point outside `W` is strictly separated from it by a continuous linear functional,
which is a positive multiple of the height along a unit vector. -/
theorem Convex.subset_of_image_inner_subset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {U W : Set E} (hW : Convex ℝ W) (hWo : IsOpen W)
    (hWn : W.Nonempty)
    (hUW : ∀ u : E, ‖u‖ = 1 → (fun x ↦ ⟪u, x⟫) '' U ⊆ (fun x ↦ ⟪u, x⟫) '' W) : U ⊆ W := by
  intro x hx
  by_contra hxW
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hW hWo hxW
  set w := (InnerProductSpace.toDual ℝ E).symm f
  have hfw (y : E) : f y = ⟪w, y⟫ := InnerProductSpace.toDual_symm_apply.symm
  have hw : w ≠ 0 := by
    rintro hw
    obtain ⟨a, ha⟩ := hWn
    simpa [hfw, hw] using hf a ha
  obtain ⟨a, ha, hax⟩ : ⟪‖w‖⁻¹ • w, x⟫ ∈ (fun y ↦ ⟪‖w‖⁻¹ • w, y⟫) '' W :=
    hUW _ (norm_smul_inv_norm (𝕜 := ℝ) hw) (mem_image_of_mem _ hx)
  simp only [real_inner_smul_left] at hax
  have := hf a ha
  rw [hfw, hfw, ← mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.2 hw)) hax] at this
  exact lt_irrefl _ this

/-- **Affine-hyperplane containment for convex sets with empty interior.** In a finite-dimensional
real inner product space `E`, the closure of a nonempty convex set `C` with empty interior is
contained in a single affine hyperplane `{x | ⟪x, e⟫ = c}` for some unit normal `e` and scalar `c`.
-/
theorem Convex.exists_norm_eq_one_closure_subset_setOf_inner_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E} (hC : Convex ℝ C)
    (hCne : C.Nonempty) (hint : interior C = ∅) :
    ∃ (e : E) (c : ℝ), ‖e‖ = 1 ∧ closure C ⊆ {x | ⟪x, e⟫ = c} := by
  have haff_ne : affineSpan ℝ C ≠ ⊤ := fun htop =>
    (Set.not_nonempty_iff_eq_empty.mpr hint)
      (hC.interior_nonempty_iff_affineSpan_eq_top.mpr htop)
  have hdir_ne : vectorSpan ℝ C ≠ ⊤ := by
    rw [← direction_affineSpan]
    exact fun hdir => haff_ne
      ((AffineSubspace.direction_eq_top_iff_of_nonempty
        (hCne.mono (subset_affineSpan ℝ C))).mp hdir)
  obtain ⟨v, hv_mem, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.mp hdir_ne)
  obtain ⟨x₀, hx₀⟩ := hCne
  let e : E := ‖v‖⁻¹ • v
  refine ⟨e, ⟪x₀, e⟫, by simp [e, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)],
    closure_minimal (fun x hx => ?_) (isClosed_eq (by fun_prop) continuous_const)⟩
  have hsub_mem : x - x₀ ∈ vectorSpan ℝ C := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hx) (subset_affineSpan ℝ C hx₀)
  rw [mem_ofPred_eq, ← sub_eq_zero, ← inner_sub_left]
  exact Submodule.inner_right_of_mem_orthogonal hsub_mem (Submodule.smul_mem _ _ hv_mem)

/-- **Supporting hyperplane at a frontier point** (Rockafellar, *Convex Analysis*, Theorem 11.6).
At every point `x ∈ frontier C` of a convex set `C` in a finite-dimensional real inner product
space `E`, there is a nonzero vector `y` such that `⟪z - x, y⟫ ≤ 0` for all `z ∈ closure C`. No
nonemptiness of `interior C` is required. -/
theorem Convex.exists_ne_zero_forall_closure_inner_sub_nonpos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E} (hC : Convex ℝ C) {x : E}
    (hx : x ∈ frontier C) :
    ∃ y : E, y ≠ 0 ∧ ∀ z ∈ closure C, ⟪z - x, y⟫ ≤ 0 := by
  obtain ⟨hx_cl, hx_not_int⟩ := hx
  rcases (interior C).eq_empty_or_nonempty with hint_empty | hint
  · obtain ⟨e, c, he, hsub⟩ := hC.exists_norm_eq_one_closure_subset_setOf_inner_eq
      (closure_nonempty_iff.mp ⟨x, hx_cl⟩) hint_empty
    refine ⟨e, fun h0 => by simp [h0] at he, fun z hz => ?_⟩
    rw [inner_sub_left, (hsub hz : ⟪z, e⟫ = c), (hsub hx_cl : ⟪x, e⟫ = c), sub_self]
  · have hcl_int : interior (closure C) = interior C :=
      hC.interior_closure_eq_interior_of_nonempty_interior hint
    obtain ⟨L, hL0, hcl_le⟩ := geometric_hahn_banach_of_nonempty_interior_point hC.closure
      (hcl_int ▸ hx_not_int) (hcl_int.symm ▸ hint)
    refine ⟨(InnerProductSpace.toDual ℝ E).symm L, by simpa using hL0, fun z hz => ?_⟩
    rw [real_inner_comm, ← InnerProductSpace.toDual_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, map_sub, sub_nonpos]
    exact hcl_le z hz
