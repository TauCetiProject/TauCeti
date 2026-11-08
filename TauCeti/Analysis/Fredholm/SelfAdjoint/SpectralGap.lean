/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Normed.Operator.ClosedRange
public import TauCeti.Topology.Indicator

/-!
# The spectral gap of a self-adjoint Fredholm operator

A self-adjoint Fredholm operator `T` on a Hilbert space has a spectral gap at zero: there is
`c > 0` such that every nonzero point of the real spectrum of `T` has absolute value at least `c`.
Consequently, for `0 < c' < c` the spectral projection of `T` onto `(-c', c')`, computed by the
continuous functional calculus, maps into the kernel of `T` and so has finite rank. This is the
local input for the spectral flow of a path of self-adjoint Fredholm operators: near zero, the
spectrum of such an operator consists of finitely many eigenvalues of finite multiplicity.

The range of `T` is closed, and orthogonal to the kernel since `T` is self-adjoint, so `T` is
bounded below on its range: `‖x‖ ≤ C ‖T x‖` there. If `λ ≠ 0` were a spectral value with
`|λ| < C⁻¹`, take a continuous bump `k` at `λ` supported in a small interval around `λ`, and
`Q = (x ↦ x k(x))(T) = T k(T)`. Then `Q` maps into the range of `T`, and `T Q = h(T) Q` for a
function `h` with `|x h(x)| < C⁻¹`, so the lower bound forces `Q = 0`. But `‖Q‖ ≥ |λ k(λ)| = |λ|`
since the functional calculus is isometric.

The real functional calculus is used for operators on a Hilbert space over any `RCLike` field, as
long as it is isometric: this holds for complex Hilbert spaces (Mathlib) and for real ones
(`ContinuousLinearMap.instIsometricContinuousFunctionalCalculusRealIsSelfAdjoint`).

## Main results

* `IsSelfAdjoint.exists_pos_forall_mem_spectrum_of_isFredholm`: the spectral gap of a
  self-adjoint Fredholm operator.
* `IsSelfAdjoint.exists_pos_range_cfc_indicator_Ioo_le_ker_of_isFredholm`: for some `c > 0`, the
  spectral projection onto `(-c, c)` maps into the kernel, and `±c` lie outside the spectrum.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460–467.
-/

public section

open Set

namespace IsSelfAdjoint

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A continuous bump `k` at `l` with `k l = 1` and a continuous plateau `h` equal to one on the
support of `k`, such that `|x h(x)| ≤ |l| + 2δ` everywhere. -/
private theorem exists_bump_plateau (l : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k h : ℝ → ℝ, Continuous k ∧ Continuous h ∧ k l = 1 ∧ (∀ x, h x * k x = k x) ∧
      ∀ x, ‖x * h x‖ ≤ |l| + 2 * δ := by
  refine ⟨fun x ↦ max 0 (1 - |x - l| / δ), fun x ↦ max 0 (min 1 (2 - |x - l| / δ)),
    by fun_prop, by fun_prop, by simp, fun x ↦ ?_, fun x ↦ ?_⟩
  · rcases le_or_gt δ |x - l| with hx | hx
    · have : 1 - |x - l| / δ ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hδ]; linarith
      simp [max_eq_left this]
    · have : 1 ≤ 2 - |x - l| / δ := by rw [le_sub_comm, div_le_iff₀ hδ]; linarith
      simp [min_eq_left this]
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_or_gt (2 * δ) |x - l| with hx | hx
    · have : 2 - |x - l| / δ ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hδ]; linarith
      simp only [min_eq_right (this.trans zero_le_one), max_eq_left this, abs_zero, mul_zero]
      positivity
    · have h0 : 0 ≤ max 0 (min 1 (2 - |x - l| / δ)) := le_max_left _ _
      have h1 : max 0 (min 1 (2 - |x - l| / δ)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hx' : |x| ≤ |l| + 2 * δ := by have := abs_sub_abs_le_abs_sub x l; linarith
      rw [abs_of_nonneg h0]
      nlinarith [abs_nonneg x]

/-- If `‖Q y‖ ≤ C ‖T (Q y)‖` for all `y` and `T Q = R Q` with `C ‖R‖ < 1`, then `Q = 0`. -/
private theorem eq_zero_of_norm_le_mul_norm_apply {T Q R : E →L[𝕜] E} {C : ℝ}
    (hle : ∀ y, ‖Q y‖ ≤ C * ‖T (Q y)‖) (hTQ : T * Q = R * Q) (hC : 0 ≤ C) (hCR : C * ‖R‖ < 1) :
    Q = 0 := by
  ext y
  have hTQy : T (Q y) = R (Q y) := by simpa [mul_apply_eq_comp] using congr($hTQ y)
  have : ‖Q y‖ ≤ C * ‖R‖ * ‖Q y‖ :=
    calc ‖Q y‖ ≤ C * ‖R (Q y)‖ := hTQy ▸ hle y
      _ ≤ C * (‖R‖ * ‖Q y‖) := by gcongr; exact R.le_opNorm _
      _ = _ := by ring
  have : ‖Q y‖ = 0 := by nlinarith [norm_nonneg (Q y)]
  simpa using this

variable [CompleteSpace E] [NormedAlgebra ℝ (E →L[𝕜] E)]
  [IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- A **self-adjoint Fredholm operator has a spectral gap at zero**: every nonzero point of its
real spectrum has absolute value at least some `c > 0`. -/
theorem exists_pos_forall_mem_spectrum_of_isFredholm {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (hF : T.IsFredholm) : ∃ c > 0, ∀ x ∈ spectrum ℝ T, x = 0 ∨ c ≤ |x| := by
  have : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  -- `T` is bounded below on the orthogonal complement of its kernel, which contains its range.
  obtain ⟨C, hC, hle⟩ := T.exists_norm_le_mul_norm_of_mem hF.isClosed_range
    T.ker.isTopCompl_orthogonal
  have hrange : T.range ≤ T.kerᗮ := by
    rw [← hT.adjoint_eq, ← ContinuousLinearMap.orthogonal_range, hT.adjoint_eq]
    exact Submodule.le_orthogonal_orthogonal _
  refine ⟨C⁻¹, inv_pos.2 hC, fun l hl ↦ or_iff_not_imp_left.2 fun hl0 ↦ ?_⟩
  by_contra! hlt
  set δ := min (|l| / 3) ((C⁻¹ - |l|) / 3)
  have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
  have hsmall : C * (|l| + 2 * δ) < 1 := by
    have : δ ≤ (C⁻¹ - |l|) / 3 := min_le_right _ _
    calc C * (|l| + 2 * δ) < C * C⁻¹ := by gcongr; linarith
      _ = 1 := mul_inv_cancel₀ hC.ne'
  obtain ⟨k, h, hkc, hhc, hkl, hhk, hbound⟩ := exists_bump_plateau l hδ0
  -- `Q = T k(T)` maps into the range of `T`, and `T Q = R Q` for `R = (x ↦ x h(x))(T)`.
  have hidc : ContinuousOn (fun x : ℝ ↦ x) (spectrum ℝ T) := continuousOn_id
  have hxkc : ContinuousOn (fun x ↦ x * k x) (spectrum ℝ T) := (continuous_id.mul hkc).continuousOn
  have hxhc : ContinuousOn (fun x ↦ x * h x) (spectrum ℝ T) := (continuous_id.mul hhc).continuousOn
  set Q := cfc (fun x ↦ x * k x) T with hQ
  have hQT : Q = T * cfc k T := by
    rw [hQ, cfc_mul (fun x ↦ x) k T hidc hkc.continuousOn, cfc_id' ℝ T]
  have hTQ : T * Q = cfc (fun x ↦ x * h x) T * Q := by
    rw [hQ, ← cfc_mul _ _ T hxhc hxkc]
    nth_rw 1 [← cfc_id' ℝ T]
    rw [← cfc_mul _ _ T hidc hxkc]
    congr 1
    funext x
    rw [show x * h x * (x * k x) = x * (x * (h x * k x)) by ring, hhk]
  have hQ0 : Q = 0 := eq_zero_of_norm_le_mul_norm_apply
    (fun y ↦ hle _ (hrange ⟨cfc k T y, by simp [hQT, mul_apply_eq_comp]⟩)) hTQ hC.le
    (lt_of_le_of_lt (by gcongr; exact norm_cfc_le (by positivity) fun x _ ↦ hbound x) hsmall)
  -- But `‖Q‖ ≥ |l k(l)| = |l| > 0`, since the functional calculus is isometric.
  have := norm_apply_le_norm_cfc (fun x ↦ x * k x) T hl hxkc
  rw [← hQ, hQ0, norm_zero, norm_mul, hkl, norm_one, mul_one, norm_le_zero_iff] at this
  exact hl0 this

/-- For a self-adjoint Fredholm operator `T` there is `c > 0` such that `±c` lie outside the
spectrum of `T` and the spectral projection of `T` onto `(-c, c)` maps into the kernel of `T`; in
particular it has finite rank. -/
theorem exists_pos_range_cfc_indicator_Ioo_le_ker_of_isFredholm {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) (hF : T.IsFredholm) :
    ∃ c > 0, c ∉ spectrum ℝ T ∧ -c ∉ spectrum ℝ T ∧
      (cfc ((Ioo (-c) c).indicator 1) T).range ≤ T.ker := by
  obtain ⟨c, hc, hgap⟩ := hT.exists_pos_forall_mem_spectrum_of_isFredholm hF
  have hnot : ∀ x ∈ spectrum ℝ T, x ∈ Ioo (-(c / 2)) (c / 2) → x = 0 := fun x hx hx' ↦
    (hgap x hx).resolve_right fun h ↦ by
      have := abs_lt.2 hx'; linarith
  refine ⟨c / 2, by positivity, fun h ↦ ?_, fun h ↦ ?_, ?_⟩
  · rcases hgap _ h with h | h
    · linarith
    · rw [abs_of_pos (by positivity)] at h; linarith
  · rcases hgap _ h with h | h
    · linarith
    · rw [abs_neg, abs_of_pos (by positivity)] at h; linarith
  -- On the spectrum, `x 𝟙_(-c/2, c/2)(x) = 0`, so `T` kills the spectral projection.
  rintro _ ⟨y, rfl⟩
  have hfr : Disjoint (spectrum ℝ T) (frontier (Ioo (-(c / 2)) (c / 2))) := by
    rw [frontier_Ioo (by linarith), disjoint_iff_forall_ne]
    rintro x hx _ (rfl | rfl) <;> rintro rfl
    · rcases hgap _ hx with h | h
      · linarith
      · rw [abs_neg, abs_of_pos (by positivity)] at h; linarith
    · rcases hgap _ hx with h | h
      · linarith
      · rw [abs_of_pos (by positivity)] at h; linarith
  have hcont : ContinuousOn ((Ioo (-(c / 2)) (c / 2)).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) :=
    ContinuousOn.indicator_of_disjoint_frontier (by exact continuousOn_const) hfr
  have hTP : T * cfc ((Ioo (-(c / 2)) (c / 2)).indicator 1) T = 0 := by
    conv_lhs => enter [1]; rw [← cfc_id' ℝ T]
    rw [← cfc_mul (fun x ↦ x) _ T continuousOn_id hcont, ← cfc_zero ℝ T]
    refine cfc_congr fun x hx ↦ ?_
    by_cases hx' : x ∈ Ioo (-(c / 2)) (c / 2)
    · simp [hnot x hx hx']
    · simp [indicator_of_notMem hx']
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  simpa [ContinuousLinearMap.mul_def] using congr($hTP y)

end IsSelfAdjoint
