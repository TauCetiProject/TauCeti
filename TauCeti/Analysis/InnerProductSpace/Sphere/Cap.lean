/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Caps of a unit sphere

For a unit vector `a` of a real inner product space and a real number `r`, the closed cap of the
unit sphere around `a` at height `r` is the set of unit vectors `x` with `⟪x, a⟫ ≥ r`. For
`r > 0` it is the closed ball around `a` of angular radius `arccos r`. This file records two
criteria, stated through inner products only, for caps to be disjoint and for a cap to lie in an
open hemisphere. They are what keeps knotted arcs confined to small caps apart when the caps are
slid along a great circle. In finite dimension, finitely many caps at any height below one cover
the unit sphere.

## Main results

* `TauCeti.inner_lt_of_le_inner`: two caps at height `r` around `a` and `b` are disjoint when
  `⟪a, b⟫ < 2 r² - 1`.
* `TauCeti.inner_pos_of_le_inner`: a cap at height `r` around `a` lies in the open hemisphere
  around `u` when `⟪a, u⟫ ≥ 0` and `1 - ⟪a, u⟫² < r²`.
* `TauCeti.exists_finset_forall_exists_le_inner`: for `κ < 1`, finitely many caps at height `κ`
  cover the unit sphere of a finite-dimensional space.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {x a b u : F} {r : ℝ}

/-- **Disjoint caps.** For `r > 0`, the closed caps `⟪x, a⟫ ≥ r` and `⟪x, b⟫ ≥ r` of the unit
sphere around unit vectors `a` and `b` are disjoint when `⟪a, b⟫ < 2 r² - 1`: a unit vector `x`
in the first cap has `⟪x, b⟫ < r`. -/
theorem inner_lt_of_le_inner (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hr : 0 < r)
    (hab : ⟪a, b⟫ < 2 * r ^ 2 - 1) (hxa : r ≤ ⟪x, a⟫) : ⟪x, b⟫ < r := by
  by_contra! hxb
  have hab' : ⟪a + b, a + b⟫ = 2 + 2 * ⟪a, b⟫ := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, ha, hb, real_inner_comm a b]
    ring
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h := real_inner_mul_inner_self_le x (a + b)
  rw [hab', hxx, inner_add_right] at h
  nlinarith

/-- **A cap inside a hemisphere.** For `r > 0`, the closed cap `⟪x, a⟫ ≥ r` of the unit sphere
around a unit vector `a` lies in the open hemisphere `⟪x, u⟫ > 0` around a unit vector `u` when
`⟪a, u⟫ ≥ 0` and `1 - ⟪a, u⟫² < r²`, that is, when the component of `a` orthogonal to `u` is
shorter than `r`. -/
theorem inner_pos_of_le_inner (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (hr : 0 < r)
    (hau : 0 ≤ ⟪a, u⟫) (hau' : 1 - ⟪a, u⟫ ^ 2 < r ^ 2) (hxa : r ≤ ⟪x, a⟫) : 0 < ⟪x, u⟫ := by
  by_contra! hxu
  have hd : ⟪a - ⟪a, u⟫ • u, a - ⟪a, u⟫ • u⟫ = 1 - ⟪a, u⟫ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hu, real_inner_comm u a]
    ring
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h := real_inner_mul_inner_self_le x (a - ⟪a, u⟫ • u)
  rw [hd, hxx, inner_sub_right, real_inner_smul_right] at h
  have h₂ : r ≤ ⟪x, a⟫ - ⟪a, u⟫ * ⟪x, u⟫ := by nlinarith
  nlinarith

/-- **Finitely many caps cover the sphere.** In a finite-dimensional real inner product space, for
`κ < 1` there are finitely many unit vectors `θ` such that every unit vector `v` satisfies
`κ ≤ ⟪θ, v⟫` for one of them. -/
theorem exists_finset_forall_exists_le_inner [FiniteDimensional ℝ F] {κ : ℝ} (hκ : κ < 1) :
    ∃ S : Finset F, (∀ θ ∈ S, ‖θ‖ = 1) ∧ ∀ v : F, ‖v‖ = 1 → ∃ θ ∈ S, κ ≤ ⟪θ, v⟫ := by
  classical
  -- Take a `δ`-net of the unit sphere, since `⟪θ, v⟫ = 1 - ‖v - θ‖² / 2` for unit vectors.
  set δ := min 1 (1 - κ)
  have hδ : 0 < δ := lt_min one_pos (by linarith)
  obtain ⟨t, hts, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : F) 1).totallyBounded δ hδ
  refine ⟨htf.toFinset, fun θ hθ ↦ by simpa using hts (htf.mem_toFinset.1 hθ), fun v hv ↦ ?_⟩
  obtain ⟨θ, hθt, hvθ⟩ := Set.mem_iUnion₂.1 (hcov (by simpa using hv))
  refine ⟨θ, htf.mem_toFinset.2 hθt, ?_⟩
  have hθ : ‖θ‖ = 1 := by simpa using hts hθt
  have hd : ‖v - θ‖ < δ := by simpa [dist_eq_norm] using hvθ
  have h1 : ‖v - θ‖ ^ 2 ≤ δ := by
    have : ‖v - θ‖ ≤ 1 := hd.le.trans (min_le_left _ _)
    nlinarith [norm_nonneg (v - θ)]
  have h2 : δ ≤ 1 - κ := min_le_right _ _
  have hsq := norm_sub_sq_real v θ
  rw [hv, hθ, real_inner_comm] at hsq
  nlinarith

end TauCeti
