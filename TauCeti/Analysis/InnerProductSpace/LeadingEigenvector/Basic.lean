/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Leading unit eigenvectors

A *leading unit eigenvector* of a linear operator `M` on a real inner product space is a unit
vector `u` maximizing the quadratic form on the unit sphere: `⟪v, M v⟫ ≤ ⟪u, M u⟫ ‖v‖²` for
every `v`. For a symmetric `M` such a vector is an eigenvector for the largest eigenvalue
`⟪u, M u⟫`, and in finite dimension one exists as soon as the space is nonzero.

## Main declarations

* `LinearMap.IsLeadingUnitEigenvector`: `u` is a unit maximizer of the quadratic form of `M`,
  with `LinearMap.isLeadingUnitEigenvector_iff` and the constructor
  `LinearMap.IsLeadingUnitEigenvector.of_norm_eq_one_of_le`.
* `LinearMap.IsLeadingUnitEigenvector.inner_apply_add_inner_apply`: the first variation
  `⟪w, M u⟫ + ⟪u, M w⟫ = 2 ⟪u, M u⟫ ⟪w, u⟫`.
* `LinearMap.IsLeadingUnitEigenvector.apply_eq_smul`: for symmetric `M`,
  `M u = ⟪u, M u⟫ u`.
* `LinearMap.exists_isLeadingUnitEigenvector`: existence in a nonzero finite-dimensional space.
* `LinearMap.IsLeadingUnitEigenvector.le_of_apply_eq_smul`: if the quadratic form is at most
  `c ‖v‖²` on the orthogonal complement of some vector, every eigenvalue carried by an
  eigenvector orthogonal to a leading unit eigenvector is at most `c`.
* `LinearMap.IsLeadingUnitEigenvector.eq_or_eq_neg`: if no nonzero eigenvector for the largest
  eigenvalue is orthogonal to `u`, the leading unit eigenvector is unique up to sign.

## References

* Existence and uniqueness up to sign are adapted from lean-CKSD
  (<https://github.com/bjbraams/lean-CKSD>),
  `CKSD/Nonparametric/HighDimensional/EigenvectorPerturbation.lean`:
  `exists_unit_eigenvector_rayleigh_le` and
  `mem_span_singleton_of_eigenvector_of_forall_inner_eq_zero`.
-/

public section

open scoped RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : E →ₗ[ℝ] E} {u v : E}

/-- A leading unit eigenvector of `M`: a unit vector `u` maximizing the Rayleigh quotient,
`⟪v, M v⟫ ≤ ⟪u, M u⟫ ‖v‖²` for every `v`. -/
def IsLeadingUnitEigenvector (M : E →ₗ[ℝ] E) (u : E) : Prop :=
  ‖u‖ = 1 ∧ ∀ v, ⟪v, M v⟫ ≤ ⟪u, M u⟫ * ‖v‖ ^ 2

/-- `u` is a leading unit eigenvector of `M` if and only if `‖u‖ = 1` and
`⟪v, M v⟫ ≤ ⟪u, M u⟫ ‖v‖²` for every `v`. -/
theorem isLeadingUnitEigenvector_iff :
    M.IsLeadingUnitEigenvector u ↔ ‖u‖ = 1 ∧ ∀ v, ⟪v, M v⟫ ≤ ⟪u, M u⟫ * ‖v‖ ^ 2 :=
  Iff.rfl

namespace IsLeadingUnitEigenvector

/-- A unit vector `u` with `⟪v, M v⟫ ≤ ⟪u, M u⟫ ‖v‖²` for every `v` is a leading unit
eigenvector of `M`. -/
theorem of_norm_eq_one_of_le (h1 : ‖u‖ = 1) (h : ∀ v, ⟪v, M v⟫ ≤ ⟪u, M u⟫ * ‖v‖ ^ 2) :
    M.IsLeadingUnitEigenvector u :=
  isLeadingUnitEigenvector_iff.mpr ⟨h1, h⟩

/-- A leading unit eigenvector has norm one. -/
theorem norm_eq_one (hu : M.IsLeadingUnitEigenvector u) : ‖u‖ = 1 :=
  (isLeadingUnitEigenvector_iff.mp hu).1

/-- The quadratic form of `M` is bounded by `⟪u, M u⟫ ‖v‖²` at a leading unit eigenvector `u`. -/
theorem inner_self_apply_le (hu : M.IsLeadingUnitEigenvector u) (v : E) :
    ⟪v, M v⟫ ≤ ⟪u, M u⟫ * ‖v‖ ^ 2 :=
  (isLeadingUnitEigenvector_iff.mp hu).2 v

/-- The negative of a leading unit eigenvector is a leading unit eigenvector. -/
theorem neg (hu : M.IsLeadingUnitEigenvector u) : M.IsLeadingUnitEigenvector (-u) := by
  refine of_norm_eq_one_of_le (by rw [norm_neg, hu.norm_eq_one]) fun v ↦ ?_
  simpa only [map_neg, inner_neg_neg] using hu.inner_self_apply_le v

/-- Two leading unit eigenvectors of `M` have the same Rayleigh quotient. -/
theorem inner_self_apply_eq (hu : M.IsLeadingUnitEigenvector u)
    (hv : M.IsLeadingUnitEigenvector v) : ⟪v, M v⟫ = ⟪u, M u⟫ := by
  have h₁ := hu.inner_self_apply_le v
  have h₂ := hv.inner_self_apply_le u
  rw [hv.norm_eq_one, one_pow, mul_one] at h₁
  rw [hu.norm_eq_one, one_pow, mul_one] at h₂
  exact le_antisymm h₁ h₂

/-- **First variation at a leading unit eigenvector.** For every `w`,
`⟪w, M u⟫ + ⟪u, M w⟫ = 2 ⟪u, M u⟫ ⟪w, u⟫`: the quadratic form minus `⟪u, M u⟫ ‖·‖²` is
nonpositive and vanishes at `u`, so its derivative at `u` vanishes. No symmetry is needed. -/
theorem inner_apply_add_inner_apply (hu : M.IsLeadingUnitEigenvector u) (w : E) :
    ⟪w, M u⟫ + ⟪u, M w⟫ = 2 * ⟪u, M u⟫ * ⟪w, u⟫ := by
  set b := ⟪u, M u⟫
  set a := ⟪w, M u⟫ + ⟪u, M w⟫ - 2 * b * ⟪w, u⟫
  set K := b * ‖w‖ ^ 2 - ⟪w, M w⟫
  have hK : 0 ≤ K := by linarith [hu.inner_self_apply_le w]
  have hquad (t : ℝ) : t * a ≤ t ^ 2 * K := by
    have h := hu.inner_self_apply_le (u + t • w)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_trivial, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, hu.norm_eq_one, one_pow] at h
    rw [real_inner_comm w u] at h
    nlinarith
  -- `t * a ≤ t ^ 2 * K` for all `t` forces `a = 0`: at `t = a / (K + 1)`, so that
  -- `a = t (K + 1)`, it reads `t ^ 2 (K + 1) ≤ t ^ 2 K`, hence `t = 0`.
  set t := a / (K + 1)
  have hat : a = t * (K + 1) := by simp only [t]; rw [div_mul_cancel₀ _ (by positivity)]
  have h := hquad t
  rw [hat] at h
  have ht0 : t = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm (by nlinarith) (sq_nonneg t))
  have ha : a = 0 := by rw [hat, ht0, zero_mul]
  linarith

/-- A leading unit eigenvector `u` of a symmetric operator `M` is an eigenvector for the
eigenvalue `⟪u, M u⟫`. -/
theorem apply_eq_smul (hM : M.IsSymmetric) (hu : M.IsLeadingUnitEigenvector u) :
    M u = ⟪u, M u⟫ • u := by
  refine ext_inner_left ℝ fun w ↦ ?_
  have h := hu.inner_apply_add_inner_apply w
  rw [← hM u w, real_inner_comm w (M u)] at h
  rw [inner_smul_right]
  linarith

/-- If the quadratic form of `M` is at most `c ‖v‖²` on the orthogonal complement of `x`, then
every eigenvalue of `M` carried by a nonzero eigenvector orthogonal to a leading unit
eigenvector `u` is at most `c`. The combination `⟪y, x⟫ u - ⟪u, x⟫ y` is orthogonal to `x`,
and the quadratic form on it is at least `μ` times its squared norm. -/
theorem le_of_apply_eq_smul (hu : M.IsLeadingUnitEigenvector u) {x : E}
    {c : ℝ} (hc : ∀ v, ⟪v, x⟫ = 0 → ⟪v, M v⟫ ≤ c * ‖v‖ ^ 2) {y : E} (hy0 : y ≠ 0)
    (hyu : ⟪y, u⟫ = 0) {μ : ℝ} (hy : M y = μ • y) : μ ≤ c := by
  have hy2 : 0 < ‖y‖ ^ 2 := by positivity
  have hyM : ⟪y, M y⟫ = μ * ‖y‖ ^ 2 := by
    rw [hy, inner_smul_right, real_inner_self_eq_norm_sq]
  by_cases hyx : ⟪y, x⟫ = 0
  · have h := hc y hyx
    rw [hyM] at h
    exact le_of_mul_le_mul_right h hy2
  set b := ⟪u, M u⟫
  have hμb : μ ≤ b := by
    have h := hu.inner_self_apply_le y
    rw [hyM] at h
    exact le_of_mul_le_mul_right h hy2
  have huy : ⟪u, y⟫ = 0 := by rw [real_inner_comm]; exact hyu
  have hyMu : ⟪y, M u⟫ = 0 := by
    have h := hu.inner_apply_add_inner_apply y
    rw [hy, inner_smul_right, huy, hyu] at h
    linarith
  have hu1 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
  set z := ⟪y, x⟫ • u - ⟪u, x⟫ • y
  have hzx : ⟪z, x⟫ = 0 := by
    simp only [z, inner_sub_left, inner_smul_left, conj_trivial]
    ring
  have hzz : ‖z‖ ^ 2 = ⟪y, x⟫ ^ 2 + ⟪u, x⟫ ^ 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [z, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, hu1, huy, hyu]
    ring
  have hzM : ⟪z, M z⟫ = ⟪y, x⟫ ^ 2 * b + ⟪u, x⟫ ^ 2 * (μ * ‖y‖ ^ 2) := by
    rw [← hyM]
    simp only [z, map_sub, map_smul, hy, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, conj_trivial, huy, hyMu, real_inner_self_eq_norm_sq]
    ring
  have h := hc z hzx
  rw [hzM, hzz] at h
  have hyx2 : 0 < ⟪y, x⟫ ^ 2 := by positivity
  by_contra hlt
  have := mul_pos (sub_pos.2 (not_le.mp hlt))
    (add_pos_of_pos_of_nonneg hyx2 (mul_nonneg (sq_nonneg ⟪u, x⟫) hy2.le))
  nlinarith [mul_le_mul_of_nonneg_left hμb hyx2.le]

/-- If no nonzero vector orthogonal to the leading unit eigenvector `u` of a symmetric `M` is an
eigenvector for the largest eigenvalue `⟪u, M u⟫`, then every leading unit eigenvector of `M` is
`u` or `-u`. -/
theorem eq_or_eq_neg (hM : M.IsSymmetric) (hu : M.IsLeadingUnitEigenvector u)
    (h : ∀ y, ⟪y, u⟫ = 0 → M y = ⟪u, M u⟫ • y → y = 0) (hv : M.IsLeadingUnitEigenvector v) :
    v = u ∨ v = -u := by
  have hu1 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
  set b := ⟪u, M u⟫
  have hMu : M u = b • u := hu.apply_eq_smul hM
  have hMv : M v = b • v := by rw [hv.apply_eq_smul hM, hu.inner_self_apply_eq hv]
  have hy := h (v - ⟪u, v⟫ • u)
    (by rw [inner_sub_left, inner_smul_left, hu1, real_inner_comm]; simp)
    (by rw [map_sub, map_smul, hMv, hMu, smul_sub, smul_comm])
  rw [sub_eq_zero] at hy
  have hn : |⟪u, v⟫| = 1 := by
    simpa [norm_smul, hu.norm_eq_one, hv.norm_eq_one, eq_comm] using congrArg norm hy
  rcases abs_eq (zero_le_one' ℝ) |>.mp hn with h1 | h1
  · exact .inl (by rw [hy, h1, one_smul])
  · exact .inr (by rw [hy, h1, neg_one_smul])

end IsLeadingUnitEigenvector

/-- In a nonzero finite-dimensional real inner product space every linear operator has a leading
unit eigenvector: a maximizer of its quadratic form on the compact unit sphere. -/
theorem exists_isLeadingUnitEigenvector [FiniteDimensional ℝ E] [Nontrivial E] (M : E →ₗ[ℝ] E) :
    ∃ u, M.IsLeadingUnitEigenvector u := by
  have hcont : Continuous fun v ↦ ⟪v, M v⟫ :=
    continuous_id.inner M.continuous_of_finiteDimensional
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
    ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩ hcont.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨u, .of_norm_eq_one_of_le hu1 fun v ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := hmax (show ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 by simp [norm_smul, hv'.ne'])
  simp only [Set.mem_ofPred_eq, map_smul, inner_smul_left, inner_smul_right, conj_trivial] at h
  calc ⟪v, M v⟫ = ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * ⟪v, M v⟫)) := by field_simp
    _ ≤ ‖v‖ ^ 2 * ⟪u, M u⟫ := by gcongr
    _ = ⟪u, M u⟫ * ‖v‖ ^ 2 := mul_comm _ _

end LinearMap
