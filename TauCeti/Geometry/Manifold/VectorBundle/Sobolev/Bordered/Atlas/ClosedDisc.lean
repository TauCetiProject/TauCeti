/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc.Centred
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Equiv
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer

/-!
# Half-disc atlases of the closed disc give equivalent Sobolev norms

This file works out the independence of `W^{k,p}` of the atlas on the closed unit disc, for the
trivial bundle with a finite-dimensional fibre `F`, on `TauCeti.CentredClosedDisc`: the closed
disc with its Cayley charts, the preferred chart at a point `ζ` of the unit circle being the
Cayley chart `z ↦ I (ζ - z) / (ζ + z)` centred at `ζ`. This synonym has the same topology and the
same atlas of Cayley charts as `Complex.UnitClosedDisc`; only the preferred charts differ, so that
finite bundle atlases can use a chart centred at any boundary point. The file compares two finite
bundle atlases.

* `TauCeti.CentredClosedDisc.fiveChartAtlas`: one interior chart, the Cayley chart centred at `1`
  on the disc of radius `1/2` about `0`, whose image lies in the open upper half-plane
  (`TauCeti.CentredClosedDisc.image_fiveChartAtlas_zero_subset`), and four half-disc charts, the
  Cayley charts centred at `1`, `i`, `-1`, `-i`, each with image the half-disc
  `D⁺_1 = {w : ‖w‖ < 1, 0 ≤ im w}` (`TauCeti.CentredClosedDisc.image_fiveChartAtlas_of_ne`).
* `TauCeti.CentredClosedDisc.eightChartAtlas`: eight half-disc charts, the Cayley charts centred at
  `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5`, each with image the half-disc `D⁺_2`
  (`TauCeti.CentredClosedDisc.image_eightChartAtlas`).

The chart centred at `ζ` maps `{z : ‖ζ - z‖ < r ‖ζ + z‖}` onto `D⁺_r`
(`TauCeti.CentredClosedDisc.cayleyChart_image_setOf_lt`). For `r = 1` this is the half of the disc
where `0 < re (conj ζ z)`, so the four half-disc charts of the first atlas cover the disc minus
`0`; for `r = 2` the two charts centred at `±1` already cover the disc.

Sections transfer between any two finite bundle atlases
(`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`), so the Sobolev spaces of
sections of the two atlases are isomorphic Banach spaces, an element corresponding to the element
with the same section (`TauCeti.CentredClosedDisc.fiveEightAtlasEquiv`), and their norms are
equivalent (`TauCeti.CentredClosedDisc.exists_norm_fiveEightAtlasEquiv_le`). The norm of
`TauCeti.BorderedSobolevSection` is the maximum of the chartwise Sobolev norms rather than a sum
weighted by a partition of unity.

## Main definitions

* `TauCeti.CentredClosedDisc.discAtlas`: a finite bundle atlas of the trivial bundle with
  prescribed centres and chart domains.
* `TauCeti.CentredClosedDisc.fiveChartAtlas`, `TauCeti.CentredClosedDisc.eightChartAtlas`: the two
  atlases above.
* `TauCeti.CentredClosedDisc.fiveEightAtlasEquiv`: the isomorphism of their Sobolev spaces.

## Main results

* `TauCeti.CentredClosedDisc.image_fiveChartAtlas_zero_subset`,
  `TauCeti.CentredClosedDisc.image_fiveChartAtlas_of_ne`,
  `TauCeti.CentredClosedDisc.image_eightChartAtlas`: the chart images, an interior one and
  half-discs.
* `TauCeti.CentredClosedDisc.exists_norm_fiveEightAtlasEquiv_le`: the norms of the two atlases
  are equivalent.
-/

public section

noncomputable section

open Set Bundle Complex
open scoped Manifold ENNReal

namespace TauCeti

namespace CentredClosedDisc

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The finite bundle atlas of the trivial bundle over the closed disc with `k`th chart the
preferred chart at `c k`, on the open domain `D k`. The closure of each domain must avoid the point
`-centre (c k)` missing from the source of the chart, and the domains must cover the disc. -/
@[expose, simps n center dom]
def discAtlas (m : ℕ) (c : Fin m → CentredClosedDisc) (D : Fin m → Set CentredClosedDisc)
    (hD : ∀ k, IsOpen (D k)) (hsrc : ∀ k, closure (D k) ⊆ {z | (z : ℂ) ≠ -centre (c k)})
    (hcov : ∀ z, ∃ k, z ∈ D k) :
    FiniteBundleAtlas ClosedUpperHalfPlane CentredClosedDisc F (Bundle.Trivial CentredClosedDisc F)
    where
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

/-- The domain `{z : ‖ζ - z‖ < r ‖ζ + z‖}` of the half-disc chart centred at `ζ`. -/
def halfDiscDom (ζ : ℂ) (r : ℝ) : Set CentredClosedDisc := {z | ‖ζ - z‖ < r * ‖ζ + z‖}

/-- Half-disc domains are open. -/
theorem isOpen_halfDiscDom (ζ : ℂ) (r : ℝ) : IsOpen (halfDiscDom ζ r) :=
  isOpen_lt (continuous_const.sub continuous_coe).norm
    (continuous_const.mul (continuous_const.add continuous_coe).norm)

/-- The closure of a half-disc domain does not contain `-ζ`. -/
theorem closure_halfDiscDom_subset (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) :
    closure (halfDiscDom ζ r) ⊆ {z | (z : ℂ) ≠ -ζ} := by
  refine (closure_lt_subset_le (continuous_const.sub continuous_coe).norm
    (continuous_const.mul (continuous_const.add continuous_coe).norm)).trans fun z hz hzζ ↦ ?_
  -- `hz` is the inequality `‖ζ - z‖ ≤ r ‖ζ + z‖`, stated with pointwise operations on functions.
  replace hz : ‖ζ - (z : ℂ)‖ ≤ r * ‖ζ + z‖ := hz
  rw [hzζ, sub_neg_eq_add, add_neg_cancel, norm_zero, mul_zero, ← two_mul, norm_mul, hζ] at hz
  norm_num at hz

/-- `‖w‖ ^ 2` in coordinates. -/
private theorem sq_norm_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq]

/-- Membership in a half-disc domain in coordinates, for `0 < r`. -/
private theorem mem_halfDiscDom_iff {ζ : ℂ} {r : ℝ} (hr : 0 < r) {z : CentredClosedDisc} :
    z ∈ halfDiscDom ζ r ↔ (ζ.re - (z : ℂ).re) ^ 2 + (ζ.im - (z : ℂ).im) ^ 2 <
      r ^ 2 * ((ζ.re + (z : ℂ).re) ^ 2 + (ζ.im + (z : ℂ).im) ^ 2) := by
  rw [halfDiscDom, mem_ofPred_eq, ← pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity)
    two_ne_zero, mul_pow, sq_norm_eq, sq_norm_eq]
  simp

/-- The points of the unit circle `1`, `i`, `-1`, `-i` and `(±3 ± 4i)/5`. -/
def circlePt : Fin 8 → ℂ :=
  ![1, I, -1, -I, ⟨3 / 5, 4 / 5⟩, ⟨-3 / 5, 4 / 5⟩, ⟨-3 / 5, -4 / 5⟩, ⟨3 / 5, -4 / 5⟩]

/-- The points `circlePt k` lie on the unit circle. -/
theorem norm_circlePt (k : Fin 8) : ‖circlePt k‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, sq_norm_eq]
  fin_cases k <;> norm_num [circlePt]

/-- The point `circlePt k` of the closed disc. -/
def circlePtDisc (k : Fin 8) : CentredClosedDisc :=
  mk (circlePt k) (norm_circlePt k).le

/-- The preferred chart at `circlePt k` is centred there. -/
theorem centre_circlePtDisc (k : Fin 8) : centre (circlePtDisc k) = circlePt k := by
  rw [centre_of_norm_eq_one (by rw [circlePtDisc, coe_mk, norm_circlePt]), circlePtDisc, coe_mk]

/-- The domain `{‖z‖ < 1/2}` of the interior chart. -/
def innerDom : Set CentredClosedDisc := {z | ‖(z : ℂ)‖ < 1 / 2}

/-- The domain of the interior chart is open. -/
theorem isOpen_innerDom : IsOpen innerDom :=
  isOpen_lt (continuous_norm.comp continuous_coe) continuous_const

/-- The centres of the five-chart atlas: `0`, then `1`, `i`, `-1`, `-i`. -/
def fiveCentre (k : Fin 5) : CentredClosedDisc :=
  Fin.cases (mk 0 (by simp)) (fun j : Fin 4 ↦ circlePtDisc (Fin.castAdd 4 j)) k

/-- The five-chart atlas: the interior chart on `{‖z‖ < 1/2}` and the half-disc charts centred at
`1`, `i`, `-1`, `-i`, with domains `{‖ζ - z‖ < ‖ζ + z‖}`. -/
@[expose] def fiveChartAtlas : FiniteBundleAtlas ClosedUpperHalfPlane CentredClosedDisc F
    (Bundle.Trivial CentredClosedDisc F) :=
  discAtlas F 5 fiveCentre
    (Fin.cases innerDom fun j ↦ halfDiscDom (circlePt (Fin.castAdd 4 j)) 1)
    (fun k ↦ Fin.cases isOpen_innerDom (fun j ↦ isOpen_halfDiscDom _ _) k)
    (fun k ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · simp only [Fin.cases_zero, fiveCentre, centre_mk_zero, innerDom]
        refine (closure_lt_subset_le (continuous_norm.comp continuous_coe)
          continuous_const).trans fun z hz hz1 ↦ ?_
        replace hz : ‖(z : ℂ)‖ ≤ 1 / 2 := hz
        rw [hz1, norm_neg, norm_one] at hz
        norm_num at hz
      · simpa [fiveCentre, centre_circlePtDisc] using
          closure_halfDiscDom_subset _ (norm_circlePt _) 1)
    fun z ↦ by
      by_cases h0 : ‖(z : ℂ)‖ < 1 / 2
      · exact ⟨0, show z ∈ innerDom from h0⟩
      have hz : (z : ℂ) ≠ 0 := fun hz ↦ h0 (by simp [hz])
      have hxy : (z : ℂ).re ≠ 0 ∨ (z : ℂ).im ≠ 0 := by
        by_contra! h
        exact hz (Complex.ext h.1 h.2)
      rcases hxy with hx | hy
      · rcases hx.lt_or_gt with hx | hx
        · exact ⟨3, (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)⟩
        · exact ⟨1, (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)⟩
      · rcases hy.lt_or_gt with hy | hy
        · exact ⟨4, (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)⟩
        · exact ⟨2, (mem_halfDiscDom_iff one_pos).2 (by norm_num [circlePt]; nlinarith)⟩

/-- The eight-chart atlas: the half-disc charts centred at `1`, `i`, `-1`, `-i` and
`(±3 ± 4i)/5`, with domains `{‖ζ - z‖ < 2 ‖ζ + z‖}`. -/
@[expose] def eightChartAtlas : FiniteBundleAtlas ClosedUpperHalfPlane CentredClosedDisc F
    (Bundle.Trivial CentredClosedDisc F) :=
  discAtlas F 8 circlePtDisc (fun k ↦ halfDiscDom (circlePt k) 2)
    (fun _ ↦ isOpen_halfDiscDom _ _)
    (fun k ↦ by
      simpa [centre_circlePtDisc] using closure_halfDiscDom_subset _ (norm_circlePt k) 2)
    fun z ↦ by
      rcases le_or_gt 0 (z : ℂ).re with hx | hx
      · exact ⟨0, (mem_halfDiscDom_iff two_pos).2 (by norm_num [circlePt]; nlinarith)⟩
      · exact ⟨2, (mem_halfDiscDom_iff two_pos).2 (by norm_num [circlePt]; nlinarith)⟩

/-- The preferred chart at `circlePt k` is the Cayley chart centred there. -/
theorem chartAt_circlePtDisc (k : Fin 8) :
    chartAt ClosedUpperHalfPlane (circlePtDisc k) = cayleyChart (circlePt k) (norm_circlePt k) := by
  rw [chartAt_eq]
  congr 1
  exact centre_circlePtDisc k

omit [NormedSpace ℝ F] in
/-- **The half-disc charts of the eight-chart atlas.** Each chart maps its domain onto the
half-disc `D⁺_2 = {w : ‖w‖ < 2}` of the closed upper half-plane. -/
theorem image_eightChartAtlas (k : Fin 8) :
    ((eightChartAtlas F).image k : Set ClosedUpperHalfPlane) =
      {w : ClosedUpperHalfPlane | ‖(w : ℂ)‖ < 2} := by
  ext w
  refine (FiniteBundleAtlas.mem_image (A := eightChartAtlas F) (i := k)).trans ?_
  have hc : (eightChartAtlas F).chart k = cayleyChart (circlePt k) (norm_circlePt k) :=
    chartAt_circlePtDisc k
  rw [hc, show (eightChartAtlas F).dom k = halfDiscDom (circlePt k) 2 from rfl,
    halfDiscDom, cayleyChart_image_setOf_lt]

omit [NormedSpace ℝ F] in
/-- **The half-disc charts of the five-chart atlas.** The charts other than the first, centred at
`1`, `i`, `-1`, `-i`, map their domains onto the half-disc `D⁺_1 = {w : ‖w‖ < 1}` of the closed
upper half-plane. -/
theorem image_fiveChartAtlas_of_ne (k : Fin 5) (hk : k ≠ 0) :
    ((fiveChartAtlas F).image k : Set ClosedUpperHalfPlane) =
      {w : ClosedUpperHalfPlane | ‖(w : ℂ)‖ < 1} := by
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hk
  ext w
  refine (FiniteBundleAtlas.mem_image (A := fiveChartAtlas F) (i := k)).trans ?_
  -- The chart and domain with index `k` are read off `fiveCentre` and the domains by cases.
  have hc : (fiveChartAtlas F).chart k =
      cayleyChart (circlePt (Fin.castAdd 4 j)) (norm_circlePt _) := by
    rw [← chartAt_circlePtDisc]
    change chartAt _ (fiveCentre k) = _
    rw [← hj]
    rfl
  have hd : (fiveChartAtlas F).dom k = halfDiscDom (circlePt (Fin.castAdd 4 j)) 1 := by
    change @Fin.cases 4 (fun _ ↦ Set CentredClosedDisc) innerDom
      (fun j ↦ halfDiscDom (circlePt (Fin.castAdd 4 j)) 1) k = _
    rw [← hj]
    rfl
  rw [hc, hd, halfDiscDom, cayleyChart_image_setOf_lt]

omit [NormedSpace ℝ F] in
/-- **The interior chart of the five-chart atlas.** The first chart, the preferred chart at `0`,
maps its domain into the open upper half-plane, away from the boundary. -/
theorem image_fiveChartAtlas_zero_subset :
    ((fiveChartAtlas F).image (0 : Fin 5) : Set ClosedUpperHalfPlane) ⊆
      {w : ClosedUpperHalfPlane | 0 < (w : ℂ).im} := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ :=
    (FiniteBundleAtlas.mem_image (A := fiveChartAtlas F) (i := (0 : Fin 5))).1 hw
  replace hz : ‖(z : ℂ)‖ < 1 / 2 := hz
  have hc : (fiveChartAtlas F).chart (0 : Fin 5) = cayleyChart 1 norm_one := by
    change chartAt _ (fiveCentre 0) = _
    rw [chartAt_eq]
    congr 1
    exact centre_mk_zero
  have hz1 : ‖(z : ℂ)‖ < 1 := hz.trans (by norm_num)
  have hsrc : z ∈ (cayleyChart 1 norm_one).source := by
    rw [cayleyChart_source]
    intro h
    rw [h, norm_neg, norm_one] at hz1
    exact lt_irrefl _ hz1
  rw [hc]
  exact (Complex.UnitClosedDisc.im_cayleyChart_pos_iff (z := z) hsrc).2 hz1

variable [FiniteDimensional ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- Sections transfer between any two finite bundle atlases of the trivial bundle over the closed
disc (`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`, applied with
smoothness order `n = k + 1`, which meets `1 ≤ n` and `k ≤ n` also for `k = 0`). -/
theorem transfersTo_disc
    (A B : FiniteBundleAtlas ClosedUpperHalfPlane CentredClosedDisc F
      (Bundle.Trivial CentredClosedDisc F)) :
    BorderedSobolevSection.TransfersTo A B p k :=
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
theorem fiveEightAtlasEquiv_apply (w : BorderedSobolevSection (fiveChartAtlas F) p k) :
    fiveEightAtlasEquiv F p k w =
      BorderedSobolevSection.changeAtlas (transfersTo_disc F p k _ _) w :=
  BorderedSobolevSection.atlasEquiv_apply _ _ w

/-- **Equivalence of norms on the closed disc.** The Sobolev norms of the five-chart atlas and the
eight-chart atlas are equivalent: some constant `C > 0` bounds each by `C` times the other, and
the identity map on sections is bounded both ways. -/
theorem exists_norm_fiveEightAtlasEquiv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : BorderedSobolevSection (fiveChartAtlas F) p k,
      ‖fiveEightAtlasEquiv F p k w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖fiveEightAtlasEquiv F p k w‖ := by
  simpa only [fiveEightAtlasEquiv_apply] using BorderedSobolevSection.exists_norm_changeAtlas_le
    (transfersTo_disc F p k _ _) (transfersTo_disc F p k _ _)

end CentredClosedDisc

end TauCeti
