/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer

/-!
# Two atlases of the closed unit disc give equivalent Sobolev norms

This file works out the independence of `W^{k,p}` of the atlas on the closed unit disc
`Complex.UnitClosedDisc`, a surface with boundary whose charts are the Cayley charts, for the
trivial bundle with a finite-dimensional fibre `F`. It compares two finite bundle atlases:

* `Complex.UnitClosedDisc.fiveChartAtlas`: one interior chart, on the disc of radius `1/2` about
  `0`, and four half-disc charts, on the parts of the closed disc within distance `1` of the points
  `1`, `i`, `-1`, `-i` of the unit circle;
* `Complex.UnitClosedDisc.eightChartAtlas`: eight half-disc charts, on the parts of the closed disc
  within distance `6/5` of the points `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5` of the unit circle.

Sections transfer between any two finite bundle atlases
(`TauCeti.BorderedSobolevSection.transfersTo_of_contMDiff`), so the Sobolev spaces of sections of
the two atlases are isomorphic Banach spaces, an element corresponding to the element with the same
section (`Complex.UnitClosedDisc.fiveEightAtlasEquiv`), and their norms are equivalent
(`Complex.UnitClosedDisc.exists_norm_fiveEightAtlasEquiv_le`).

The atlases are instances of `Complex.UnitClosedDisc.ballAtlas`, whose chart domains are the parts
of the closed disc in open discs `‖z - c‖ < r`. Such a disc is a chart domain when its closure
avoids the one point of the closed disc missing from the source of the chart at its center, and
the discs must cover the closed disc.

## Main definitions

* `Complex.UnitClosedDisc.ballAtlas`: a finite bundle atlas of the trivial bundle with chart
  domains given by discs.
* `Complex.UnitClosedDisc.fiveChartAtlas`, `Complex.UnitClosedDisc.eightChartAtlas`: the two
  atlases above.
* `Complex.UnitClosedDisc.fiveEightAtlasEquiv`: the isomorphism of their Sobolev spaces.

## Main results

* `Complex.UnitClosedDisc.exists_norm_fiveEightAtlasEquiv_le`: the norms of the two atlases are
  equivalent.
-/

public section

noncomputable section

open Set Metric Bundle TauCeti
open scoped Manifold ENNReal Complex.UnitDisc

namespace Complex.UnitClosedDisc

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The finite bundle atlas of the trivial bundle over the closed unit disc whose `k`th chart is
the chart at the point `c k` of the closed disc, with domain the points of the closed disc at
distance less than `r k` from `c k`. The closure of each domain must avoid the point
`-chartCenter (c k)` missing from the source of the chart, and the domains must cover the closed
disc. -/
def ballAtlas (m : ℕ) (c : Fin m → 𝕔𝔻) (r : Fin m → ℝ)
    (hr : ∀ k, r k < ‖(c k : ℂ) + chartCenter (c k)‖)
    (hcov : ∀ z : 𝕔𝔻, ∃ k, ‖(z : ℂ) - c k‖ < r k) :
    FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F) where
  n := m
  center := c
  dom k := {z | ‖(z : ℂ) - c k‖ < r k}
  isOpen_dom k := isOpen_lt (continuous_coe.sub continuous_const).norm continuous_const
  isCompact_closure_dom _ := isClosed_closure.isCompact
  closure_dom_subset_source k := by
    refine (closure_lt_subset_le (continuous_coe.sub continuous_const).norm
      continuous_const).trans fun z (hz : ‖(z : ℂ) - c k‖ ≤ r k) ↦ ?_
    rw [chartAt_eq, cayleyChart_source]
    intro hzc
    rw [hzc, ← norm_neg, neg_sub, sub_neg_eq_add] at hz
    exact (hz.trans_lt (hr k)).false
  closure_dom_subset_baseSet _ := by simp
  iUnion_dom := eq_univ_of_forall fun z ↦ mem_iUnion.2 (hcov z)

/-- `r < ‖w‖` exactly when `r ^ 2 < re w ^ 2 + im w ^ 2`, for `0 ≤ r`. -/
private theorem lt_norm_iff {r : ℝ} (hr : 0 ≤ r) {w : ℂ} :
    r < ‖w‖ ↔ r ^ 2 < w.re ^ 2 + w.im ^ 2 := by
  rw [← pow_lt_pow_iff_left₀ hr (norm_nonneg w) two_ne_zero, Complex.sq_norm,
    Complex.normSq_apply, ← sq, ← sq]

/-- `‖z - c‖ < r` in coordinates, for `0 ≤ r`. -/
private theorem norm_sub_lt_iff {r : ℝ} (hr : 0 ≤ r) {z c : ℂ} :
    ‖z - c‖ < r ↔ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 < r ^ 2 := by
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero, Complex.sq_norm,
    Complex.normSq_apply, ← sq, ← sq, Complex.sub_re, Complex.sub_im]

/-- The squared coordinates of a point of the closed disc sum to at most `1`. -/
private theorem re_sq_add_im_sq_le_one (z : 𝕔𝔻) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 ≤ 1 := by
  have h := (sq_le_one_iff₀ (norm_nonneg _)).2 (norm_le_one z)
  rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at h

/-- A complex number whose squared coordinates sum to `1` lies in the closed unit disc. -/
private theorem norm_le_one_of_sq {w : ℂ} (h : w.re ^ 2 + w.im ^ 2 = 1) : ‖w‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg w), Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq, h]

/-- The centers of the five-chart atlas: `0`, `1`, `i`, `-1`, `-i`. -/
private def fiveCenter : Fin 5 → ℂ := ![0, 1, I, -1, -I]

private theorem norm_fiveCenter_le (k : Fin 5) : ‖fiveCenter k‖ ≤ 1 := by
  fin_cases k <;> simp [fiveCenter]

/-- The centers of the eight-chart atlas: `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5`. -/
private def eightCenter : Fin 8 → ℂ :=
  ![1, I, -1, -I, ⟨3 / 5, 4 / 5⟩, ⟨-3 / 5, 4 / 5⟩, ⟨-3 / 5, -4 / 5⟩, ⟨3 / 5, -4 / 5⟩]

private theorem norm_eightCenter_le (k : Fin 8) : ‖eightCenter k‖ ≤ 1 := by
  fin_cases k <;> first
    | exact norm_le_one_of_sq (by simp [eightCenter]; norm_num)
    | simp [eightCenter]

/-- Every point `x + iy` of the closed disc lies within distance `1` of one of `1`, `i`, `-1`,
`-i`, and strictly so when it lies outside the open disc of radius `1/2` about `0`: take the
point on the nearest half-axis, for which `x ^ 2 + y ^ 2 ≤ 2 |x|` (or `≤ 2 |y|`), strictly when
`1/4 ≤ x ^ 2 + y ^ 2`. -/
private theorem exists_axis_sq_lt (x y : ℝ) (hs : x ^ 2 + y ^ 2 ≤ 1) :
    ((x - 1) ^ 2 + y ^ 2 ≤ 1 ∧ (1 / 4 ≤ x ^ 2 + y ^ 2 → (x - 1) ^ 2 + y ^ 2 < 1)) ∨
    (x ^ 2 + (y - 1) ^ 2 ≤ 1 ∧ (1 / 4 ≤ x ^ 2 + y ^ 2 → x ^ 2 + (y - 1) ^ 2 < 1)) ∨
    ((x + 1) ^ 2 + y ^ 2 ≤ 1 ∧ (1 / 4 ≤ x ^ 2 + y ^ 2 → (x + 1) ^ 2 + y ^ 2 < 1)) ∨
    (x ^ 2 + (y + 1) ^ 2 ≤ 1 ∧ (1 / 4 ≤ x ^ 2 + y ^ 2 → x ^ 2 + (y + 1) ^ 2 < 1)) := by
  rcases le_total (|y|) (|x|) with hxy | hxy
  · rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx] at hxy
      have hy := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hxy 2
      refine Or.inl ⟨by nlinarith, fun h ↦ by nlinarith⟩
    · rw [abs_of_nonpos hx] at hxy
      have hy := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hxy 2
      refine Or.inr (Or.inr (Or.inl ⟨by nlinarith, fun h ↦ by nlinarith⟩))
  · rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy] at hxy
      have hx := sq_abs x ▸ pow_le_pow_left₀ (abs_nonneg x) hxy 2
      refine Or.inr (Or.inl ⟨by nlinarith, fun h ↦ by nlinarith⟩)
    · rw [abs_of_nonpos hy] at hxy
      have hx := sq_abs x ▸ pow_le_pow_left₀ (abs_nonneg x) hxy 2
      refine Or.inr (Or.inr (Or.inr ⟨by nlinarith, fun h ↦ by nlinarith⟩))

/-- The five-chart atlas of the closed disc: one interior chart, on the disc of radius `1/2` about
`0`, and four half-disc charts, on the parts of the closed disc within distance `1` of `1`, `i`,
`-1` and `-i`. -/
def fiveChartAtlas : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F) :=
  ballAtlas F 5 (fun k ↦ mk _ (norm_fiveCenter_le k)) ![1 / 2, 1, 1, 1, 1]
    (fun k ↦ by
      fin_cases k <;> simp only [coe_mk, chartCenter_def] <;>
        norm_num [fiveCenter, lt_norm_iff])
    fun z ↦ by
      have hs := re_sq_add_im_sq_le_one z
      generalize (z : ℂ) = w at hs ⊢
      by_cases h0 : w.re ^ 2 + w.im ^ 2 < 1 / 4
      · exact ⟨0, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [fiveCenter]; linarith)⟩
      · have h0' := not_lt.1 h0
        rcases exists_axis_sq_lt _ _ hs with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact ⟨1, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [fiveCenter]; linarith [h h0'])⟩
        · exact ⟨2, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [fiveCenter]; linarith [h h0'])⟩
        · exact ⟨3, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [fiveCenter]; linarith [h h0'])⟩
        · exact ⟨4, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [fiveCenter]; linarith [h h0'])⟩

/-- The eight-chart atlas of the closed disc: eight half-disc charts, on the parts of the closed
disc within distance `6/5` of `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5`. -/
def eightChartAtlas : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 F (Bundle.Trivial 𝕔𝔻 F) :=
  ballAtlas F 8 (fun k ↦ mk _ (norm_eightCenter_le k)) (fun _ ↦ 6 / 5)
    (fun k ↦ by
      fin_cases k <;> simp only [coe_mk, chartCenter_def] <;>
        norm_num [eightCenter, lt_norm_iff])
    fun z ↦ by
      have hs := re_sq_add_im_sq_le_one z
      generalize (z : ℂ) = w at hs ⊢
      rcases exists_axis_sq_lt _ _ hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨0, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [eightCenter]; linarith)⟩
      · exact ⟨1, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [eightCenter]; linarith)⟩
      · exact ⟨2, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [eightCenter]; linarith)⟩
      · exact ⟨3, (norm_sub_lt_iff (by norm_num)).2 (by norm_num [eightCenter]; linarith)⟩

variable [FiniteDimensional ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Independence of the atlas on the closed disc.** The Sobolev spaces of sections of the trivial
bundle for the five-chart atlas and the eight-chart atlas are isomorphic Banach spaces, an element
corresponding to the element with the same section. -/
def fiveEightAtlasEquiv : BorderedSobolevSection (fiveChartAtlas F) p k ≃L[ℝ]
    BorderedSobolevSection (eightChartAtlas F) p k :=
  BorderedSobolevSection.atlasEquiv
    (BorderedSobolevSection.transfersTo_of_contMDiff (n := k + 1) (by omega) (by omega) _)
    (BorderedSobolevSection.transfersTo_of_contMDiff (n := k + 1) (by omega) (by omega) _)

/-- The chart data of `fiveEightAtlasEquiv F p k w` are the readings in the charts of the
eight-chart atlas of any section whose readings in the charts of the five-chart atlas are the chart
data of `w`. -/
theorem fiveEightAtlasEquiv_apply (w : BorderedSobolevSection (fiveChartAtlas F) p k) :
    fiveEightAtlasEquiv F p k w = BorderedSobolevSection.changeAtlas
      (BorderedSobolevSection.transfersTo_of_contMDiff (n := k + 1) (by omega) (by omega) _) w :=
  BorderedSobolevSection.atlasEquiv_apply _ _ w

/-- **Equivalence of norms on the closed disc.** The Sobolev norms of the five-chart atlas and the
eight-chart atlas are equivalent: some constant `C > 0` bounds each by `C` times the other. -/
theorem exists_norm_fiveEightAtlasEquiv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : BorderedSobolevSection (fiveChartAtlas F) p k,
      ‖fiveEightAtlasEquiv F p k w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖fiveEightAtlasEquiv F p k w‖ := by
  simpa only [fiveEightAtlasEquiv_apply] using BorderedSobolevSection.exists_norm_changeAtlas_le
    (BorderedSobolevSection.transfersTo_of_contMDiff (n := k + 1) (by omega) (by omega) _)
    (BorderedSobolevSection.transfersTo_of_contMDiff (n := k + 1) (by omega) (by omega) _)

end Complex.UnitClosedDisc
