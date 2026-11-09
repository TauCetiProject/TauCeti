/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Normed.Operator.ClosedRange
public import TauCeti.Analysis.Real.BumpPlateau
public import TauCeti.Topology.Indicator

/-!
# The spectral gap of a self-adjoint operator with closed range

A self-adjoint operator `T` with closed range on a Hilbert space, for instance a self-adjoint
Fredholm operator, has a spectral gap at zero: there is `c > 0` such that every nonzero point of
the real spectrum of `T` has absolute value at least `c`. Consequently, for `0 < c' < c` the
spectral projection of `T` onto `(-c', c')`, computed by the continuous functional calculus, maps
into the kernel of `T`, so it has finite rank when `T` is Fredholm. This is the local input for the
spectral flow of a path of self-adjoint Fredholm operators: near zero, the spectrum of such an
operator consists of finitely many eigenvalues of finite multiplicity.

The range of `T` is closed, and orthogonal to the kernel since `T` is self-adjoint, so `T` is
bounded below on its range: `‖x‖ ≤ C ‖T x‖` there. If `λ ≠ 0` were a spectral value with
`|λ| < C⁻¹`, take a continuous bump `k` at `λ` supported in a small interval around `λ`, and
`Q = (x ↦ x k(x))(T) = T k(T)`. Then `Q` maps into the range of `T`, and `T Q = R Q` for
`R = (x ↦ x h(x))(T)`, where `h` is a plateau equal to one on the support of `k` with
`|x h(x)| < C⁻¹`. So `‖R‖ < C⁻¹`, and the lower bound forces `Q = 0`. But
`‖Q‖ ≥ |λ k(λ)| = |λ|` since the functional calculus is isometric.

The real functional calculus is used for operators on a Hilbert space over any `RCLike` field, as
long as it is isometric: this holds for complex Hilbert spaces (Mathlib) and for real ones
(`ContinuousLinearMap.instIsometricContinuousFunctionalCalculusRealIsSelfAdjoint`).

## Main results

* `IsSelfAdjoint.exists_pos_forall_mem_spectrum_of_isClosed_range`: the spectral gap of a
  self-adjoint operator with closed range.
* `IsSelfAdjoint.exists_pos_range_cfc_indicator_Ioo_le_ker_of_isClosed_range`: for some `c > 0`,
  the spectral projection onto `(-c, c)` maps into the kernel, and `±c` lie outside the spectrum.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460–467.
-/

public section

open Set

namespace IsSelfAdjoint

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAlgebra ℝ (E →L[𝕜] E)] [IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- A **self-adjoint operator with closed range has a spectral gap at zero**: every nonzero point
of its real spectrum has absolute value at least some `c > 0`. -/
theorem exists_pos_forall_mem_spectrum_of_isClosed_range {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (hR : IsClosed (T.range : Set E)) : ∃ c > 0, ∀ x ∈ spectrum ℝ T, x = 0 ∨ c ≤ |x| := by
  have : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  -- `T` is bounded below on the orthogonal complement of its kernel, which contains its range.
  obtain ⟨C, hC, hle⟩ := T.exists_norm_le_mul_norm_of_mem hR
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
  obtain ⟨k, h, hkc, hhc, hkl, hhk, hbound⟩ := Real.exists_bump_plateau l hδ0
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
  have hQ0 : Q = 0 := ContinuousLinearMap.eq_zero_of_norm_le_mul_norm_apply
    (fun y ↦ hle _ (hrange ⟨cfc k T y, by simp [hQT, mul_apply_eq_comp]⟩)) hTQ hC.le
    (lt_of_le_of_lt (by gcongr; exact norm_cfc_le (by positivity) fun x _ ↦ hbound x) hsmall)
  -- But `‖Q‖ ≥ |l k(l)| = |l| > 0`, since the functional calculus is isometric.
  have := norm_apply_le_norm_cfc (fun x ↦ x * k x) T hl hxkc
  rw [← hQ, hQ0, norm_zero, norm_mul, hkl, norm_one, mul_one, norm_le_zero_iff] at this
  exact hl0 this

/-- For a self-adjoint operator `T` with closed range there is `c > 0` such that `±c` lie outside
the spectrum of `T` and the spectral projection of `T` onto `(-c, c)` maps into the kernel of `T`;
in particular it has finite rank when `T` is Fredholm. -/
theorem exists_pos_range_cfc_indicator_Ioo_le_ker_of_isClosed_range {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) (hR : IsClosed (T.range : Set E)) :
    ∃ c > 0, c ∉ spectrum ℝ T ∧ -c ∉ spectrum ℝ T ∧
      (cfc ((Ioo (-c) c).indicator 1) T).range ≤ T.ker := by
  obtain ⟨c, hc, hgap⟩ := hT.exists_pos_forall_mem_spectrum_of_isClosed_range hR
  have hnot : ∀ x ∈ spectrum ℝ T, |x| < c → x = 0 := fun x hx hx' ↦
    (hgap x hx).resolve_right hx'.not_ge
  have hpos : c / 2 ∉ spectrum ℝ T := fun h ↦ by
    have := hnot _ h (by rw [abs_of_pos (by positivity)]; linarith); linarith
  have hneg : -(c / 2) ∉ spectrum ℝ T := fun h ↦ by
    have := hnot _ h (by rw [abs_neg, abs_of_pos (by positivity)]; linarith); linarith
  refine ⟨c / 2, by positivity, hpos, hneg, ?_⟩
  -- On the spectrum, `x 𝟙_(-c/2, c/2)(x) = 0`, so `T` kills the spectral projection.
  rintro _ ⟨y, rfl⟩
  have hfr : Disjoint (spectrum ℝ T) (frontier (Ioo (-(c / 2)) (c / 2))) :=
    TauCeti.disjoint_frontier_of_Ioo_subset_of_subset_Icc subset_rfl Ioo_subset_Icc_self hneg hpos
  have hcont : ContinuousOn ((Ioo (-(c / 2)) (c / 2)).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) :=
    ContinuousOn.indicator_of_disjoint_frontier (by exact continuousOn_const) hfr
  have hTP : T * cfc ((Ioo (-(c / 2)) (c / 2)).indicator 1) T = 0 := by
    conv_lhs => enter [1]; rw [← cfc_id' ℝ T]
    rw [← cfc_mul (fun x ↦ x) _ T continuousOn_id hcont, ← cfc_zero ℝ T]
    refine cfc_congr fun x hx ↦ ?_
    by_cases hx' : x ∈ Ioo (-(c / 2)) (c / 2)
    · simp [hnot x hx (abs_lt.2 ⟨by linarith [hx'.1], hx'.2.trans (by linarith)⟩)]
    · simp [indicator_of_notMem hx']
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  simpa [ContinuousLinearMap.mul_def] using congr($hTP y)

end IsSelfAdjoint
