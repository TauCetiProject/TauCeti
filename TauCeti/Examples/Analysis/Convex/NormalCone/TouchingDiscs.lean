/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Convex.NormalCone

/-!
# Checks: the sum rule fails without a qualification condition

In `ℝ² = EuclideanSpace ℝ (Fin 2)` let `C₁` and `C₂` be the closed unit discs centred at `(-1, 0)`
and `(1, 0)` (`disc₁`, `disc₂`), which touch at `0`. Take the energy `E = ι_{C₁}` and the
constraint `C = C₂`. Both sets are convex, but the sum rule
`∂(E + ι_C)(0) = ∂E(0) + N_C(0)` fails:

* `C₁ ∩ C₂ = {0}` (`disc₁_inter_disc₂`), so `E + ι_C` is the indicator of `{0}`, whose
  subdifferential at `0` is the whole dual (`subdifferential_add_eq_univ`);
* `∂E(0) = N_{C₁}(0)` is the ray `{(t, 0) | t ≥ 0}`
  (`mem_subdifferential_constraintIndicator_disc₁_iff`) and `N_C(0)` is the ray `{(t, 0) | t ≤ 0}`
  (`mem_normalCone_disc₂_iff`), where a functional is written through its values on the standard
  basis;
* their sum is the line `ℝ × {0}`: the functionals vanishing on `(0, 1)`
  (`mem_subdifferential_add_normalCone_iff`), so the second coordinate functional is in
  `∂(E + ι_C)(0)` but not in `∂E(0) + N_C(0)` (`subdifferential_add_normalCone_ne`).

The qualification of `TauCeti.subdifferential_add_constraintIndicator_eq` asks for a real energy,
continuous at a point of `C`. Here `E` is finite on no neighbourhood of any point of `C`: the
interior of `C₁` misses `C₂` (`interior_disc₁_inter_disc₂`).
-/

public section

open Set Metric Pointwise

namespace TauCeti.Examples.NormalConeTouchingDiscs

/-- The closed unit disc centred at `(-1, 0)`. -/
noncomputable abbrev disc₁ : Set (EuclideanSpace ℝ (Fin 2)) :=
  closedBall (EuclideanSpace.single 0 (-1)) 1

/-- The closed unit disc centred at `(1, 0)`. -/
noncomputable abbrev disc₂ : Set (EuclideanSpace ℝ (Fin 2)) :=
  closedBall (EuclideanSpace.single 0 1) 1

private theorem dist_single_sq (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    dist v (EuclideanSpace.single 0 c) ^ 2 = (v 0 - c) ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

private theorem mem_closedBall_single_iff (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    v ∈ closedBall (EuclideanSpace.single 0 c) 1 ↔ (v 0 - c) ^ 2 + v 1 ^ 2 ≤ 1 := by
  rw [mem_closedBall, ← dist_single_sq, sq_le_one_iff₀ dist_nonneg]

private theorem mem_ball_single_iff (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    v ∈ ball (EuclideanSpace.single 0 c) 1 ↔ (v 0 - c) ^ 2 + v 1 ^ 2 < 1 := by
  rw [mem_ball, ← dist_single_sq, sq_lt_one_iff₀ dist_nonneg]

/-- A functional on `ℝ²` is determined by its values on the standard basis. -/
private theorem apply_eq (f : StrongDual ℝ (EuclideanSpace ℝ (Fin 2)))
    (v : EuclideanSpace ℝ (Fin 2)) :
    f v = v 0 * f (EuclideanSpace.single 0 1) + v 1 * f (EuclideanSpace.single 1 1) := by
  have hv : v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp [smul_eq_mul]

/-- If `k t² + b t ≤ 0` for every `t` with `t² ≤ 1`, then `b = 0`: test at `t = b / D` with
`D = |b| + |k| + 1`, where the left side is `b² (D + k) / D²` and `D + k > 0`. -/
private theorem eq_zero_of_forall_sq_le_one {k b : ℝ}
    (h : ∀ t : ℝ, t ^ 2 ≤ 1 → k * t ^ 2 + t * b ≤ 0) : b = 0 := by
  have hDpos : 0 < |b| + |k| + 1 := by positivity
  have ht : (b / (|b| + |k| + 1)) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity), ← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) (by linarith [abs_nonneg k]) 2
  have h₂ := h _ ht
  have hk : 0 < |b| + |k| + 1 + k := by linarith [abs_nonneg b, neg_le_abs k]
  have e : k * (b / (|b| + |k| + 1)) ^ 2 + b / (|b| + |k| + 1) * b =
      b ^ 2 * (|b| + |k| + 1 + k) / (|b| + |k| + 1) ^ 2 := by
    field_simp
    ring
  rw [e, div_nonpos_iff] at h₂
  have key : b ^ 2 * (|b| + |k| + 1 + k) ≤ 0 := by
    rcases h₂ with ⟨-, h₂⟩ | ⟨h₂, -⟩
    · nlinarith [sq_nonneg (|b| + |k| + 1)]
    · exact h₂
  have : b ^ 2 ≤ 0 := by
    by_contra hb'
    push Not at hb'
    nlinarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg b))

/-- The normal cone at `0` of the unit disc centred at `(c, 0)`, `c = ±1`: the functionals `f` with
`f (0, 1) = 0` and `c f (1, 0) ≤ 0`. -/
private theorem mem_normalCone_disc_iff {c : ℝ} (hc : c ^ 2 = 1)
    {f : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))} :
    f ∈ normalCone (closedBall (EuclideanSpace.single 0 c) 1) 0 ↔
      f (EuclideanSpace.single 1 1) = 0 ∧ c * f (EuclideanSpace.single 0 1) ≤ 0 := by
  simp only [mem_normalCone_iff, sub_zero, mem_closedBall_single_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ : ∃ a, f (EuclideanSpace.single 0 1) = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, f (EuclideanSpace.single 1 1) = b := ⟨_, rfl⟩
    have hf (v : EuclideanSpace ℝ (Fin 2)) : f v = v 0 * a + v 1 * b := by rw [apply_eq, ha, hb]
    rw [ha, hb]
    -- The point `(2c, 0)` gives `c a ≤ 0`.
    have h₁ := h (EuclideanSpace.single 0 (2 * c)) (by
      have : (2 * c - c) ^ 2 + 0 ^ 2 ≤ 1 := by nlinarith
      simpa using this)
    rw [hf] at h₁
    replace h₁ : 2 * c * a ≤ 0 := by simpa using h₁
    refine ⟨?_, by nlinarith⟩
    -- The points `(c t², t)`, `t² ≤ 1`, lie in the disc and force `b = 0`.
    refine eq_zero_of_forall_sq_le_one (k := c * a) fun t ht ↦ ?_
    have h₂ := h (EuclideanSpace.single 0 (c * t ^ 2) + EuclideanSpace.single 1 t) (by
      have e : (c * t ^ 2 - c) ^ 2 + t ^ 2 = 1 - t ^ 2 * (1 - t ^ 2) := by
        linear_combination (t ^ 2 - 1) ^ 2 * hc
      have : (c * t ^ 2 - c) ^ 2 + t ^ 2 ≤ 1 := by
        rw [e]
        nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.2 ht)]
      simpa using this)
    rw [hf] at h₂
    replace h₂ : c * t ^ 2 * a + t * b ≤ 0 := by simpa using h₂
    linarith
  · rintro ⟨hb, hca⟩ v hv
    rw [apply_eq, hb, mul_zero, add_zero]
    -- `c v₀ ≥ 0` on the disc, so `v₀ a = (c a) (c v₀) ≤ 0`.
    have hcv : 0 ≤ c * v 0 := by nlinarith [sq_nonneg (v 1)]
    have : v 0 * f (EuclideanSpace.single 0 1) =
        (c * f (EuclideanSpace.single 0 1)) * (c * v 0) := by
      linear_combination (-(v 0 * f (EuclideanSpace.single 0 1))) * hc
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg hca hcv

/-- `N_{C₁}(0)` is the ray `{(t, 0) | t ≥ 0}`. -/
theorem mem_normalCone_disc₁_iff {f : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))} :
    f ∈ normalCone disc₁ 0 ↔
      f (EuclideanSpace.single 1 1) = 0 ∧ 0 ≤ f (EuclideanSpace.single 0 1) := by
  rw [mem_normalCone_disc_iff (by norm_num)]
  simp

/-- `N_{C₂}(0)` is the ray `{(t, 0) | t ≤ 0}`. -/
theorem mem_normalCone_disc₂_iff {f : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))} :
    f ∈ normalCone disc₂ 0 ↔
      f (EuclideanSpace.single 1 1) = 0 ∧ f (EuclideanSpace.single 0 1) ≤ 0 := by
  rw [mem_normalCone_disc_iff (by norm_num)]
  simp

/-- `0 ∈ C₁`. -/
theorem zero_mem_disc₁ : (0 : EuclideanSpace ℝ (Fin 2)) ∈ disc₁ := by
  rw [mem_closedBall_single_iff]
  norm_num

/-- `0 ∈ C₂`. -/
theorem zero_mem_disc₂ : (0 : EuclideanSpace ℝ (Fin 2)) ∈ disc₂ := by
  rw [mem_closedBall_single_iff]
  norm_num

/-- `∂ι_{C₁}(0)` is the ray `{(t, 0) | t ≥ 0}`. -/
theorem mem_subdifferential_constraintIndicator_disc₁_iff
    {f : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))} :
    f ∈ subdifferential (topDualPairing ℝ _).flip (constraintIndicator disc₁) 0 ↔
      f (EuclideanSpace.single 1 1) = 0 ∧ 0 ≤ f (EuclideanSpace.single 0 1) := by
  rw [subdifferential_constraintIndicator zero_mem_disc₁, SetLike.mem_coe,
    mem_normalCone_disc₁_iff]

/-- The two discs touch at `0` only: `C₁ ∩ C₂ = {0}`. -/
theorem disc₁_inter_disc₂ : disc₁ ∩ disc₂ = {0} := by
  ext v
  simp only [mem_inter_iff, mem_closedBall_single_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
    ext i
    fin_cases i <;> simp [h0, h1]
  · rintro rfl
    norm_num

/-- `E + ι_C = ι_{C₁} + ι_{C₂}` is the indicator of `{0}`, so its subdifferential at `0` is the
whole dual. -/
theorem subdifferential_add_eq_univ :
    subdifferential (topDualPairing ℝ (EuclideanSpace ℝ (Fin 2))).flip
      (fun v ↦ constraintIndicator disc₁ v + constraintIndicator disc₂ v) 0 = univ := by
  simp_rw [constraintIndicator_add_constraintIndicator, disc₁_inter_disc₂]
  rw [subdifferential_constraintIndicator rfl]
  ext f
  simp

/-- `∂E(0) + N_C(0)` is the line `ℝ × {0}`: the functionals vanishing on `(0, 1)`. -/
theorem mem_subdifferential_add_normalCone_iff {f : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))} :
    f ∈ subdifferential (topDualPairing ℝ _).flip (constraintIndicator disc₁) 0 +
        normalCone disc₂ 0 ↔
      f (EuclideanSpace.single 1 1) = 0 := by
  constructor
  · rintro ⟨g, hg, n, hn, rfl⟩
    rw [mem_subdifferential_constraintIndicator_disc₁_iff] at hg
    rw [SetLike.mem_coe, mem_normalCone_disc₂_iff] at hn
    simp [hg.1, hn.1]
  · intro hf
    rcases le_total 0 (f (EuclideanSpace.single 0 1)) with ha | ha
    · exact ⟨f, mem_subdifferential_constraintIndicator_disc₁_iff.2 ⟨hf, ha⟩, 0, zero_mem _,
        add_zero f⟩
    · refine ⟨0, mem_subdifferential_constraintIndicator_disc₁_iff.2 (by simp), f, ?_, zero_add f⟩
      exact mem_normalCone_disc₂_iff.2 ⟨hf, ha⟩

/-- **The sum rule fails**: `∂E(0) + N_C(0) ≠ ∂(E + ι_C)(0)`, witnessed by the second coordinate
functional. -/
theorem subdifferential_add_normalCone_ne :
    subdifferential (topDualPairing ℝ _).flip (constraintIndicator disc₁) 0 +
        (normalCone disc₂ 0 : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin 2)))) ≠
      subdifferential (topDualPairing ℝ _).flip
        (fun v ↦ constraintIndicator disc₁ v + constraintIndicator disc₂ v) 0 := by
  rw [subdifferential_add_eq_univ, Ne, eq_univ_iff_forall, not_forall]
  refine ⟨EuclideanSpace.proj 1, fun h ↦ ?_⟩
  rw [mem_subdifferential_add_normalCone_iff] at h
  simp at h

/-- The qualification fails: the interior of `C₁`, where `E = ι_{C₁}` is finite near a point,
misses `C₂`. -/
theorem interior_disc₁_inter_disc₂ : interior disc₁ ∩ disc₂ = ∅ := by
  rw [interior_closedBall _ one_ne_zero, eq_empty_iff_forall_notMem]
  rintro v ⟨h₁, h₂⟩
  rw [mem_ball_single_iff] at h₁
  rw [mem_closedBall_single_iff] at h₂
  nlinarith

end TauCeti.Examples.NormalConeTouchingDiscs
