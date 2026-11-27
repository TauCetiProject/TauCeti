/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc.Centered
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Equiv
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer

/-!
# Half-disc atlases of the closed disc give equivalent Sobolev norms

This file works out the independence of `W^{k,p}` of the atlas on the closed unit disc, for the
trivial bundle with a finite-dimensional fibre `F`, on `TauCeti.CenteredClosedDisc`: the closed
disc with its Cayley charts, the preferred chart at a point `ζ` of the unit circle being the
Cayley chart `z ↦ I (ζ - z) / (ζ + z)` centered at `ζ`. This synonym has the same topology and the
same atlas of Cayley charts as `Complex.UnitClosedDisc`; only the preferred charts differ, so that
finite bundle atlases can use a chart centered at any boundary point. The file compares two finite
bundle atlases.

* `TauCeti.CenteredClosedDisc.fiveChartAtlas`: one interior chart, the Cayley chart centered at `1`
  on the disc of radius `1/2` about `0`, whose image lies in the open upper half-plane
  (`TauCeti.CenteredClosedDisc.fiveChartAtlas_image_zero_subset`), and four half-disc charts, the
  Cayley charts centered at `1`, `i`, `-1`, `-i`, each with image the half-disc
  `D⁺_1 = {w : ‖w‖ < 1, 0 ≤ im w}` (`TauCeti.CenteredClosedDisc.fiveChartAtlas_image_of_ne_zero`).
* `TauCeti.CenteredClosedDisc.eightChartAtlas`: eight half-disc charts, the Cayley charts centered
  at `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5`, each with image the half-disc `D⁺_2`
  (`TauCeti.CenteredClosedDisc.eightChartAtlas_image`).

The chart centered at `ζ` maps `{z : ‖ζ - z‖ < r ‖ζ + z‖}` onto `D⁺_r`
(`TauCeti.CenteredClosedDisc.cayleyChart_image_halfDiscDom`). For `r = 1` this is the half of the
disc where `0 < re (conj ζ z)`, so the four half-disc charts of the first atlas cover the disc minus
`0`; for `r = 2` the two charts centered at `±1` already cover the disc.

Sections transfer between any two finite bundle atlases
(`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`), so the Sobolev spaces of
sections of the two atlases are isomorphic Banach spaces, an element corresponding to the element
with the same section (`TauCeti.CenteredClosedDisc.fiveEightAtlasEquiv`), and their norms are
equivalent (`TauCeti.CenteredClosedDisc.exists_norm_fiveEightAtlasEquiv_le`). The norm of
`TauCeti.BorderedSobolevSection` is the maximum of the chartwise Sobolev norms rather than a sum
weighted by a partition of unity.

## Main definitions

* `TauCeti.CenteredClosedDisc.discAtlas`: a finite bundle atlas of the trivial bundle with
  prescribed centers and chart domains.
* `TauCeti.CenteredClosedDisc.fiveChartAtlas`, `TauCeti.CenteredClosedDisc.eightChartAtlas`: the two
  atlases above.
* `TauCeti.CenteredClosedDisc.fiveEightAtlasEquiv`: the isomorphism of their Sobolev spaces.

## Main results

* `TauCeti.CenteredClosedDisc.fiveChartAtlas_image_zero_subset`,
  `TauCeti.CenteredClosedDisc.fiveChartAtlas_image_of_ne_zero`,
  `TauCeti.CenteredClosedDisc.eightChartAtlas_image`: the chart images, an interior one and
  half-discs.
* `TauCeti.CenteredClosedDisc.exists_norm_fiveEightAtlasEquiv_le`: the norms of the two atlases
  are equivalent.
-/

public section

noncomputable section

open Set Bundle Complex
open scoped Manifold ENNReal

namespace TauCeti

namespace CenteredClosedDisc

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The finite bundle atlas of the trivial bundle over the closed disc with `k`th chart the
preferred chart at `c k`, on the open domain `D k`. The closure of each domain must avoid the point
`-chartCenter (c k)` missing from the source of the chart, and the domains must cover the disc. -/
@[expose, simps n center dom]
def discAtlas (m : ℕ) (c : Fin m → CenteredClosedDisc) (D : Fin m → Set CenteredClosedDisc)
    (hD : ∀ k, IsOpen (D k)) (hsrc : ∀ k, closure (D k) ⊆ {z | (z : ℂ) ≠ -chartCenter (c k)})
    (hcov : ∀ z, ∃ k, z ∈ D k) :
    FiniteBundleAtlas ClosedUpperHalfPlane CenteredClosedDisc F
      (Bundle.Trivial CenteredClosedDisc F) where
  n := m
  center := c
  dom := D
  isOpen_dom := hD
  isCompact_closure_dom _ := isClosed_closure.isCompact
  closure_dom_subset_source k := by
    rw [chartAt_eq, cayleyChart_source]
    exact hsrc k
  closure_dom_subset_baseSet _ := by simp
  iUnion_dom := eq_univ_of_forall fun z ↦ mem_iUnion.2 (hcov z)

/-- Membership in a half-disc domain in coordinates, for `0 < r`. -/
private theorem mem_halfDiscDom_iff {ζ : ℂ} {r : ℝ} (hr : 0 < r) {z : CenteredClosedDisc} :
    z ∈ halfDiscDom ζ r ↔ (ζ.re - (z : ℂ).re) ^ 2 + (ζ.im - (z : ℂ).im) ^ 2 <
      r ^ 2 * ((ζ.re + (z : ℂ).re) ^ 2 + (ζ.im + (z : ℂ).im) ^ 2) := by
  rw [mem_halfDiscDom, ← pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity)
    two_ne_zero, mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  ring_nf

/-- The points of the unit circle `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5`. -/
def circlePt : Fin 8 → ℂ :=
  ![1, I, -1, -I, ⟨3 / 5, 4 / 5⟩, ⟨-3 / 5, 4 / 5⟩, ⟨-3 / 5, -4 / 5⟩, ⟨3 / 5, -4 / 5⟩]

/-- The points `circlePt k` lie on the unit circle. -/
theorem norm_circlePt (k : Fin 8) : ‖circlePt k‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, Complex.sq_norm,
    Complex.normSq_apply]
  fin_cases k <;> norm_num [circlePt]

/-- The points `circlePt k` are nonzero. -/
theorem circlePt_ne_zero (k : Fin 8) : circlePt k ≠ 0 :=
  ne_zero_of_norm_ne_zero ((norm_circlePt k).symm ▸ one_ne_zero)

/-- The point `circlePt k` of the closed disc. -/
def circlePtDisc (k : Fin 8) : CenteredClosedDisc :=
  mk (circlePt k) (norm_circlePt k).le

@[simp]
theorem coe_circlePtDisc (k : Fin 8) : (circlePtDisc k : ℂ) = circlePt k :=
  coe_mk _ _

/-- The preferred chart at `circlePt k` is centered there. -/
@[simp]
theorem chartCenter_circlePtDisc (k : Fin 8) : chartCenter (circlePtDisc k) = circlePt k := by
  rw [chartCenter_of_norm_eq_one (by rw [coe_circlePtDisc, norm_circlePt]), coe_circlePtDisc]

/-- The domain `{‖z‖ < 1/2}` of the interior chart. -/
def innerDom : Set CenteredClosedDisc := {z | ‖(z : ℂ)‖ < 1 / 2}

@[simp]
theorem mem_innerDom {z : CenteredClosedDisc} : z ∈ innerDom ↔ ‖(z : ℂ)‖ < 1 / 2 :=
  Iff.rfl

/-- The domain of the interior chart is open. -/
theorem isOpen_innerDom : IsOpen innerDom :=
  isOpen_lt (continuous_norm.comp continuous_coe) continuous_const

/-- The centers of the five-chart atlas: `0`, then `1`, `i`, `-1`, `-i`. -/
def fiveCenter (k : Fin 5) : CenteredClosedDisc :=
  Fin.cases (mk 0 (by simp)) (fun j : Fin 4 ↦ circlePtDisc (Fin.castAdd 4 j)) k

@[simp]
theorem fiveCenter_zero : fiveCenter 0 = mk 0 (by simp) :=
  (rfl)

@[simp]
theorem fiveCenter_succ (j : Fin 4) : fiveCenter j.succ = circlePtDisc (Fin.castAdd 4 j) :=
  (rfl)

/-- The chart domains of the five-chart atlas: `{‖z‖ < 1/2}`, then the half-disc domains of radius
`1` centered at `1`, `i`, `-1`, `-i`. -/
def fiveDom (k : Fin 5) : Set CenteredClosedDisc :=
  Fin.cases innerDom (fun j : Fin 4 ↦ halfDiscDom (circlePt (Fin.castAdd 4 j)) 1) k

@[simp]
theorem fiveDom_zero : fiveDom 0 = innerDom :=
  (rfl)

@[simp]
theorem fiveDom_succ (j : Fin 4) : fiveDom j.succ = halfDiscDom (circlePt (Fin.castAdd 4 j)) 1 :=
  (rfl)

/-- The five-chart atlas: the interior chart on `{‖z‖ < 1/2}` and the half-disc charts centered at
`1`, `i`, `-1`, `-i`, with domains `{‖ζ - z‖ < ‖ζ + z‖}`. -/
@[expose] def fiveChartAtlas : FiniteBundleAtlas ClosedUpperHalfPlane CenteredClosedDisc F
    (Bundle.Trivial CenteredClosedDisc F) :=
  discAtlas F 5 fiveCenter fiveDom
    (fun k ↦ Fin.cases (by simpa using isOpen_innerDom)
      (fun j ↦ by simpa using isOpen_halfDiscDom _ _) k)
    (fun k ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · simp only [fiveDom_zero, fiveCenter_zero, chartCenter_mk_zero]
        refine (closure_lt_subset_le (continuous_norm.comp continuous_coe)
          continuous_const).trans fun z hz hz1 ↦ ?_
        -- `hz` is `‖z‖ ≤ 1/2`, stated with the composition `‖·‖ ∘ coe`.
        simp only [Function.comp_apply, mem_ofPred_eq, hz1, norm_neg, norm_one] at hz
        norm_num at hz
      · simpa [chartCenter_circlePtDisc] using
          closure_halfDiscDom_subset (circlePt_ne_zero (Fin.castAdd 4 j)) 1)
    fun z ↦ by
      by_cases h0 : ‖(z : ℂ)‖ < 1 / 2
      · exact ⟨0, by rw [fiveDom_zero, mem_innerDom]; exact h0⟩
      have hz : (z : ℂ) ≠ 0 := fun hz ↦ h0 (by simp [hz])
      have hxy : (z : ℂ).re ≠ 0 ∨ (z : ℂ).im ≠ 0 := by
        by_contra! h
        exact hz (Complex.ext h.1 h.2)
      rcases hxy with hx | hy
      · rcases hx.lt_or_gt with hx | hx
        -- The chart centered at `-1`.
        · refine ⟨(2 : Fin 4).succ, ?_⟩
          rw [fiveDom_succ]
          exact (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)
        -- The chart centered at `1`.
        · refine ⟨(0 : Fin 4).succ, ?_⟩
          rw [fiveDom_succ]
          exact (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)
      · rcases hy.lt_or_gt with hy | hy
        -- The chart centered at `-i`.
        · refine ⟨(3 : Fin 4).succ, ?_⟩
          rw [fiveDom_succ]
          exact (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)
        -- The chart centered at `i`.
        · refine ⟨(1 : Fin 4).succ, ?_⟩
          rw [fiveDom_succ]
          exact (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)

omit [NormedSpace ℝ F] in
@[simp]
theorem fiveChartAtlas_center (k : Fin 5) : (fiveChartAtlas F).center k = fiveCenter k :=
  (rfl)

omit [NormedSpace ℝ F] in
@[simp]
theorem fiveChartAtlas_dom (k : Fin 5) : (fiveChartAtlas F).dom k = fiveDom k :=
  (rfl)

/-- The eight-chart atlas: the half-disc charts centered at `1`, `i`, `-1`, `-i` and
`(±3 ± 4i)/5`, with domains `{‖ζ - z‖ < 2 ‖ζ + z‖}`. -/
@[expose] def eightChartAtlas : FiniteBundleAtlas ClosedUpperHalfPlane CenteredClosedDisc F
    (Bundle.Trivial CenteredClosedDisc F) :=
  discAtlas F 8 circlePtDisc (fun k ↦ halfDiscDom (circlePt k) 2)
    (fun _ ↦ isOpen_halfDiscDom _ _)
    (fun k ↦ by
      simpa [chartCenter_circlePtDisc] using
        closure_halfDiscDom_subset (circlePt_ne_zero k) 2)
    fun z ↦ by
      rcases le_or_gt 0 (z : ℂ).re with hx | hx
      · exact ⟨0, (mem_halfDiscDom_iff two_pos).2 (by norm_num [circlePt]; nlinarith)⟩
      · exact ⟨2, (mem_halfDiscDom_iff two_pos).2 (by norm_num [circlePt]; nlinarith)⟩

omit [NormedSpace ℝ F] in
@[simp]
theorem eightChartAtlas_center (k : Fin 8) : (eightChartAtlas F).center k = circlePtDisc k :=
  (rfl)

omit [NormedSpace ℝ F] in
@[simp]
theorem eightChartAtlas_dom (k : Fin 8) :
    (eightChartAtlas F).dom k = halfDiscDom (circlePt k) 2 :=
  (rfl)

/-- The preferred chart at `circlePt k` is the Cayley chart centered there. -/
@[simp]
theorem chartAt_circlePtDisc (k : Fin 8) :
    chartAt ClosedUpperHalfPlane (circlePtDisc k) = cayleyChart (circlePt k) (norm_circlePt k) :=
  chartAt_eq_cayleyChart _ (chartCenter_circlePtDisc k)

omit [NormedSpace ℝ F] in
/-- **The half-disc charts of the eight-chart atlas.** Each chart maps its domain onto the
half-disc `D⁺_2 = {w : ‖w‖ < 2}` of the closed upper half-plane. -/
theorem eightChartAtlas_image (k : Fin 8) :
    ((eightChartAtlas F).image k : Set ClosedUpperHalfPlane) =
      {w : ClosedUpperHalfPlane | ‖(w : ℂ)‖ < 2} := by
  ext w
  refine (FiniteBundleAtlas.mem_image (A := eightChartAtlas F) (i := k)).trans ?_
  simp only [FiniteBundleAtlas.chart, eightChartAtlas_center, eightChartAtlas_dom,
    chartAt_circlePtDisc, cayleyChart_image_halfDiscDom]

omit [NormedSpace ℝ F] in
/-- **The half-disc charts of the five-chart atlas.** The charts other than the first, centered at
`1`, `i`, `-1`, `-i`, map their domains onto the half-disc `D⁺_1 = {w : ‖w‖ < 1}` of the closed
upper half-plane. -/
theorem fiveChartAtlas_image_of_ne_zero (k : Fin 5) (hk : k ≠ 0) :
    ((fiveChartAtlas F).image k : Set ClosedUpperHalfPlane) =
      {w : ClosedUpperHalfPlane | ‖(w : ℂ)‖ < 1} := by
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hk
  ext w
  refine (FiniteBundleAtlas.mem_image (A := fiveChartAtlas F) (i := k)).trans ?_
  simp only [FiniteBundleAtlas.chart, fiveChartAtlas_center, fiveChartAtlas_dom]
  rw [← hj, fiveCenter_succ, fiveDom_succ, chartAt_circlePtDisc, cayleyChart_image_halfDiscDom]

omit [NormedSpace ℝ F] in
/-- **The interior chart of the five-chart atlas.** The first chart, the preferred chart at `0`,
maps its domain into the open upper half-plane, away from the boundary. -/
theorem fiveChartAtlas_image_zero_subset :
    ((fiveChartAtlas F).image (0 : Fin 5) : Set ClosedUpperHalfPlane) ⊆
      {w : ClosedUpperHalfPlane | 0 < (w : ℂ).im} := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ :=
    (FiniteBundleAtlas.mem_image (A := fiveChartAtlas F) (i := (0 : Fin 5))).1 hw
  simp only [fiveChartAtlas_dom, fiveDom_zero, mem_innerDom] at hz
  have hz1 : ‖(z : ℂ)‖ < 1 := hz.trans (by norm_num)
  have hc : chartAt ClosedUpperHalfPlane (mk 0 (by simp)) = cayleyChart 1 norm_one :=
    chartAt_eq_cayleyChart _ chartCenter_mk_zero
  simp only [FiniteBundleAtlas.chart, fiveChartAtlas_center, fiveCenter_zero, hc]
  exact im_cayleyChart_pos_iff.2 hz1

variable [FiniteDimensional ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- Sections transfer between any two finite bundle atlases of the trivial bundle over the closed
disc: every element of `W^{k,p}` for one atlas has a counterpart for the other, with the same
section. -/
theorem transfersTo_disc
    (A B : FiniteBundleAtlas ClosedUpperHalfPlane CenteredClosedDisc F
      (Bundle.Trivial CenteredClosedDisc F)) :
    BorderedSobolevSection.TransfersTo A B p k :=
  -- The closed disc is smooth, so the smoothness order `n = k + 1` meets `1 ≤ n` and `k ≤ n`,
  -- also for `k = 0`.
  BorderedSobolevSection.transfersTo_iff.2 fun w _ hs ↦
    BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord (n := k + 1) (by omega) (by omega)
      w hs B

/-- **Independence of the atlas on the closed disc.** The Sobolev spaces of sections of the
trivial bundle for the five-chart atlas and the eight-chart atlas are isomorphic Banach spaces,
an element corresponding to the element with the same section. -/
def fiveEightAtlasEquiv : BorderedSobolevSection (fiveChartAtlas F) p k ≃L[ℝ]
    BorderedSobolevSection (eightChartAtlas F) p k :=
  BorderedSobolevSection.atlasEquiv (transfersTo_disc F p k _ _) (transfersTo_disc F p k _ _)

/-- `fiveEightAtlasEquiv` acts as `TauCeti.BorderedSobolevSection.changeAtlas`; its chart data are
described by `TauCeti.BorderedSobolevSection.chartValueL_changeAtlas_ae`. -/
@[simp]
theorem fiveEightAtlasEquiv_apply (w : BorderedSobolevSection (fiveChartAtlas F) p k) :
    fiveEightAtlasEquiv F p k w =
      BorderedSobolevSection.changeAtlas (transfersTo_disc F p k _ _) w :=
  BorderedSobolevSection.atlasEquiv_apply _ _ w

/-- The inverse of `fiveEightAtlasEquiv` acts as `TauCeti.BorderedSobolevSection.changeAtlas`
from the eight-chart atlas back to the five-chart atlas. -/
@[simp]
theorem fiveEightAtlasEquiv_symm_apply (w : BorderedSobolevSection (eightChartAtlas F) p k) :
    (fiveEightAtlasEquiv F p k).symm w =
      BorderedSobolevSection.changeAtlas (transfersTo_disc F p k _ _) w :=
  BorderedSobolevSection.atlasEquiv_symm_apply _ _ w

/-- **Equivalence of norms on the closed disc.** The Sobolev norms of the five-chart atlas and the
eight-chart atlas are equivalent: some constant `C > 0` bounds each by `C` times the other, and
the identity map on sections is bounded both ways. -/
theorem exists_norm_fiveEightAtlasEquiv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : BorderedSobolevSection (fiveChartAtlas F) p k,
      ‖fiveEightAtlasEquiv F p k w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖fiveEightAtlasEquiv F p k w‖ := by
  simpa only [fiveEightAtlasEquiv_apply] using BorderedSobolevSection.exists_norm_changeAtlas_le
    (transfersTo_disc F p k _ _) (transfersTo_disc F p k _ _)

end CenteredClosedDisc

end TauCeti
