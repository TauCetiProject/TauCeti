/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Comp
public import TauCeti.Analysis.SpecialFunctions.ConcaveTruncation
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Concave truncation of a harmonic function near infinity

Let `h` be harmonic outside a ball in a finite-dimensional real inner product space `E`, with
`h < 1` there and `h → 1` at infinity. This is the conformal factor of a negative-mass end
`h ^ (4 / (n - 2)) δ` of a harmonically flat metric, whose expansion is
`h = 1 + (m / 2) ‖x‖ ^ (2 - n) + O(‖x‖ ^ (1 - n))` with `m < 0`. Lohkamp replaces `h` by
`F ∘ h` for a smooth concave truncation `F = TauCeti.concaveTruncation a b` with levels
`a < b < 1`: the identity below `a` and constant above `b`. Then:

* `F ∘ h` is superharmonic wherever `h` is harmonic
  (`TauCeti.laplacian_concaveTruncation_comp_nonpos`), so by the conformal law
  `Scal = aₙ u ^ (-(n + 2) / (n - 2)) (-Δ u)` for the flat metric rescaled by
  `u ^ (4 / (n - 2))` (`TauCeti.Yamabe.scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian`
  with `TauCeti.Yamabe.conformalLaplacian_eq_conformalCoefficient_mul_neg_laplacian`), the
  modified metric has nonnegative scalar curvature;
* it is strictly superharmonic somewhere on a segment from a point where `h ≤ a` to a point where
  `h ≥ b` (`TauCeti.exists_mem_openSegment_laplacian_concaveTruncation_comp_neg`), so the scalar
  curvature becomes positive somewhere;
* it equals `h` where `h ≤ a`, which allows gluing to the unmodified metric along a collar, and is
  constant where `h ≥ b`, where the metric is a constant multiple of the Euclidean one.

`TauCeti.exists_concaveTruncation_comp_of_tendsto_one` chooses the levels and a radius for a given
compact collar, as in the proof of Proposition 5.4 of Schoen–Yau.

## References

* J. Lohkamp, *Scalar curvature and hammocks*, Math. Ann. 313 (1999), 385–407,
  Proposition 6.1.
* R. Schoen and S.-T. Yau, *Positive scalar curvature and minimal hypersurface singularities*,
  arXiv:1704.05490, Proposition 5.4 and its proof.
-/

public section

open Set Filter InnerProductSpace Laplacian Topology
open scoped Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ} {a b : ℝ}

/-- The concave truncation `F` composed with a function `h` harmonic at `x` has Laplacian
`F'' (h x) ‖∇h x‖²` at `x`. -/
theorem laplacian_concaveTruncation_comp {x : E} (hh : HarmonicAt h x) :
    Δ (concaveTruncation a b ∘ h) x =
      deriv (deriv (concaveTruncation a b)) (h x) * ‖∇ h x‖ ^ 2 :=
  hh.laplacian_comp (contDiff_concaveTruncation a b).contDiffAt

/-- **The concave truncation of a harmonic function is superharmonic.** For `a ≤ b` and `h`
harmonic at `x`, `Δ (concaveTruncation a b ∘ h) x ≤ 0`. -/
theorem laplacian_concaveTruncation_comp_nonpos (hab : a ≤ b) {x : E} (hh : HarmonicAt h x) :
    Δ (concaveTruncation a b ∘ h) x ≤ 0 :=
  hh.laplacian_comp_nonpos (contDiff_concaveTruncation a b).contDiffAt
    (deriv_deriv_concaveTruncation_nonpos hab _)

/-- **Strict superharmonicity of the concave truncation.** For `a < b` and `h` harmonic near a
segment `[p, q]` with `h p ≤ a` and `b ≤ h q`, the concave truncation of `h` has negative
Laplacian at some point of the open segment `(p, q)`. -/
theorem exists_mem_openSegment_laplacian_concaveTruncation_comp_neg (hab : a < b) {p q : E}
    (hh : HarmonicOnNhd h (segment ℝ p q)) (hp : h p ≤ a) (hq : b ≤ h q) :
    ∃ y ∈ openSegment ℝ p q, Δ (concaveTruncation a b ∘ h) y < 0 := by
  have hne : deriv (concaveTruncation a b) (h p) ≠ deriv (concaveTruncation a b) (h q) := by
    rw [deriv_concaveTruncation_of_le_left hab.le hp, deriv_concaveTruncation_of_right_le hab hq]
    exact one_ne_zero
  obtain ⟨y, hy, hne⟩ := hh.exists_mem_openSegment_laplacian_comp_ne_zero
    (fun _ _ ↦ (contDiff_concaveTruncation a b).contDiffAt) hne
  exact ⟨y, hy, (laplacian_concaveTruncation_comp_nonpos hab.le
    (hh y (openSegment_subset_segment ℝ p q hy))).lt_of_ne hne⟩

/-- **Lohkamp's choice of truncation levels.** Let `E` be nontrivial and let `h` be harmonic in a
neighbourhood of `{x | R₀ ≤ ‖x‖}`, with
`h < 1` there and `h → 1` at infinity, and let `K ⊆ {x | R₀ ≤ ‖x‖}` be compact, such as the
collar `{x | R₀ ≤ ‖x‖ ≤ R₀ + 1}`. Then there are levels `0 < a < b < 1` and a radius `R₁` such
that `F = concaveTruncation a b` satisfies `F ∘ h = h` on `K`, `F ∘ h` is the constant `F b` on
`{x | R₁ ≤ ‖x‖}`, and `Δ (F ∘ h) < 0` at some point `x` with `R₀ < ‖x‖ < R₁`. -/
theorem exists_concaveTruncation_comp_of_tendsto_one [Nontrivial E] {R₀ : ℝ}
    (hlt : ∀ x : E, R₀ ≤ ‖x‖ → h x < 1) (hh : HarmonicOnNhd h {x | R₀ ≤ ‖x‖})
    (hlim : Tendsto h (cocompact E) (𝓝 1)) {K : Set E} (hK : IsCompact K)
    (hKR : K ⊆ {x | R₀ ≤ ‖x‖}) :
    ∃ a b R₁ : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      (∀ x ∈ K, concaveTruncation a b (h x) = h x) ∧
      (∀ x : E, R₁ ≤ ‖x‖ → concaveTruncation a b (h x) = concaveTruncation a b b) ∧
      ∃ x : E, R₀ < ‖x‖ ∧ ‖x‖ < R₁ ∧ Δ (concaveTruncation a b ∘ h) x < 0 := by
  -- Anchor a radial segment at a point `p` of the region, and take `a ≥ max h` on `K ∪ {p}`.
  obtain ⟨p, hp⟩ := exists_norm_eq E (by positivity : (0 : ℝ) ≤ |R₀| + 1)
  have hp0 : 0 < ‖p‖ := by rw [hp]; positivity
  have hpR : R₀ < ‖p‖ := by rw [hp]; linarith [le_abs_self R₀]
  have hKpR : insert p K ⊆ {x | R₀ ≤ ‖x‖} := insert_subset hpR.le hKR
  obtain ⟨m, hm, hmax⟩ := (hK.insert p).exists_isMaxOn (insert_nonempty p K)
    (hh.continuousOn.mono hKpR)
  have hm1 : h m < 1 := hlt m (hKpR hm)
  set a := max (h m) (1 / 2)
  have ha0 : 0 < a := lt_max_of_lt_right (by norm_num)
  have ha1 : a < 1 := max_lt hm1 (by norm_num)
  have hab : a < (a + 1) / 2 := by linarith
  have hb1 : (a + 1) / 2 < 1 := by linarith
  have hle {x : E} (hx : x ∈ insert p K) : h x ≤ a := (hmax hx).trans (le_max_left _ _)
  -- Beyond some radius `R₂`, `h` exceeds the upper level `b = (a + 1) / 2`.
  obtain ⟨R₂, -, hR₂⟩ := hasBasis_cobounded_norm.eventually_iff.1
    (Metric.cobounded_eq_cocompact (α := E) ▸ hlim.eventually (lt_mem_nhds hb1))
  set R₁ := max R₂ (‖p‖ + 1)
  refine ⟨a, (a + 1) / 2, R₁, ha0, hab, hb1,
    fun x hx ↦ concaveTruncation_of_le_left hab.le (hle (mem_insert_of_mem p hx)),
    fun x hx ↦ concaveTruncation_of_right_le hab (hR₂ ((le_max_left _ _).trans hx)).le, ?_⟩
  -- The radial segment from `p` to `q = c • p`, `‖q‖ = R₁`, is the image of `[1, c]` under
  -- `f s = s • p`, so it stays in `‖p‖ ≤ ‖x‖ ≤ R₁`.
  set c := R₁ / ‖p‖
  have hc : 1 < c := (one_lt_div hp0).2 ((lt_add_one _).trans_le (le_max_right _ _))
  have hcp : c * ‖p‖ = R₁ := div_mul_cancel₀ _ hp0.ne'
  let f := (LinearMap.toSpanSingleton ℝ E p).toAffineMap
  have hf (s : ℝ) : f s = s • p := rfl
  have hsegf : segment ℝ p (c • p) = f '' Icc 1 c := by
    rw [← segment_eq_Icc hc.le, image_segment, hf, hf, one_smul]
  have hosegf : openSegment ℝ p (c • p) = f '' Ioo 1 c := by
    rw [← openSegment_eq_Ioo hc, image_openSegment, hf, hf, one_smul]
  have hfn {s : ℝ} (hs : 1 ≤ s) : ‖f s‖ = s * ‖p‖ := by
    rw [hf, norm_smul, Real.norm_of_nonneg (by linarith)]
  have hseg {y : E} (hy : y ∈ segment ℝ p (c • p)) : ‖p‖ ≤ ‖y‖ ∧ ‖y‖ ≤ R₁ := by
    rw [hsegf] at hy
    obtain ⟨s, ⟨hs1, hsc⟩, rfl⟩ := hy
    rw [hfn hs1, ← hcp]
    exact ⟨le_mul_of_one_le_left hp0.le hs1, mul_le_mul_of_nonneg_right hsc hp0.le⟩
  obtain ⟨y, hy, hneg⟩ := exists_mem_openSegment_laplacian_concaveTruncation_comp_neg hab
    (fun y hy ↦ hh y (hpR.le.trans (hseg hy).1)) (hle (mem_insert p K))
    (hR₂ ((le_max_left _ _).trans_eq ((hfn hc.le).trans hcp).symm)).le
  refine ⟨y, hpR.trans_le (hseg (openSegment_subset_segment ℝ _ _ hy)).1, ?_, hneg⟩
  rw [hosegf] at hy
  obtain ⟨s, ⟨hs1, hsc⟩, rfl⟩ := hy
  rw [hfn hs1.le, ← hcp]
  exact mul_lt_mul_of_pos_right hsc hp0

end TauCeti
