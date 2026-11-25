/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.AdmissibleBoundaryPart
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.Planar
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart

/-!
# Admissible and non-admissible boundary parts of the unit square

On the open unit square `Ω = (0, 1)²`, this file tests the notion of an admissible boundary part
(`Set.IsAdmissibleBoundaryPart`) on parts `{0} × S` of the left side
(`TauCeti.unitSquareLeftSide S`). For an open `S ⊆ (0, 1)` such a part is relatively open in the
frontier of `Ω`.

* The whole open left side `{0} × (0, 1)` is admissible. Along the open side the boundary charts
  of the square see either all of the part or none of it; at the corners `(0, 0)` and `(0, 1)` the
  charts are rotations by an odd multiple of `π / 4` with graph `|s|`, and the part is the half of
  the graph over one side of the base point.
* The oscillating part `{0} × ⋃_{k ≥ 1} (1 / (2k + 1), 1 / (2k))` is not admissible: in a chart at
  the corner `(0, 0)` it would lie over a half-line, all of the base, or none of it, but it
  alternates infinitely often near the corner.
* The punctured side `{0} × ((0, 1) ∖ {1/2})` is not admissible either: at `(0, 1/2)` it lies over
  both sides of the base point but not over the point itself. Yet it has the same closure as the
  whole open side, and hence the same space `W^{1,p}_Γ(Ω)`
  (`TauCeti.w1pVanishingOnSubmodule`). Admissibility is not a property of `closure Γ`.

The two negative results rest on `Set.IsBoundaryPartChart.ordConnected_inter_preimage`: in a
boundary-part chart of a planar domain, the parameters at which a frontier arc meets `Γ` form an
interval.

## Main declarations

* `TauCeti.unitSquareLeftSide`: the part `{0} × S` of the vertical axis.
* `TauCeti.exists_isOpen_frontier_openUnitSquare_inter_eq`: for open `S ⊆ (0, 1)`, the part is
  relatively open in the frontier of the square.
* `TauCeti.isAdmissibleBoundaryPart_unitSquareLeftSide_Ioo`: the open left side is admissible.
* `TauCeti.not_isAdmissibleBoundaryPart_unitSquareLeftSide_iUnion`: the oscillating part is not.
* `TauCeti.not_isAdmissibleBoundaryPart_unitSquareLeftSide_diff`: the punctured side is not.
* `TauCeti.w1pVanishingOnSubmodule_unitSquareLeftSide_diff`: the punctured side and the whole
  open side define the same space `W^{1,p}_Γ(Ω)`.

## References

* S. Bauer, D. Pauly and M. Schomburg, *The Maxwell compactness property in bounded weak
  Lipschitz domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), §2.1
  (strong Lipschitz pairs).
-/

public section

noncomputable section

open MeasureTheory Metric Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace TauCeti

/-! ### Parts of the left side -/

/-- The points `(0, t)` of the plane with `t ∈ S`. For `S ⊆ (0, 1)` this is a part of the open left
side of the frontier of the open unit square. -/
def unitSquareLeftSide (S : Set ℝ) : Set (WithLp 2 (ℝ × ℝ)) :=
  {x | x.fst = 0 ∧ x.snd ∈ S}

/-- Membership in a part of the left side. -/
@[simp]
theorem mem_unitSquareLeftSide {S : Set ℝ} {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ unitSquareLeftSide S ↔ x.fst = 0 ∧ x.snd ∈ S :=
  Iff.rfl

/-- The part `{0} × S` is the image of `S` under `t ↦ (0, t)`. -/
theorem unitSquareLeftSide_eq_image (S : Set ℝ) :
    unitSquareLeftSide S = (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) '' S := by
  ext x
  refine ⟨fun hx => ⟨x.snd, hx.2, (WithLp.ext_iff 2).2 (Prod.ext ?_ rfl)⟩, ?_⟩
  · simpa using hx.1.symm
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

/-- The closure of `{0} × S` is `{0} × closure S`. -/
theorem closure_unitSquareLeftSide (S : Set ℝ) :
    closure (unitSquareLeftSide S) = unitSquareLeftSide (closure S) := by
  rw [unitSquareLeftSide_eq_image, unitSquareLeftSide_eq_image,
    (WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)).isClosedEmbedding.closure_image_eq]

/-- The point `(0, t)` lies on the frontier of the open unit square for `t ∈ [0, 1]`. -/
theorem toLp_zero_prod_mem_frontier_openUnitSquare {t : ℝ} (ht : t ∈ Icc 0 1) :
    WithLp.toLp 2 ((0 : ℝ), t) ∈ frontier openUnitSquare :=
  mem_frontier_openUnitSquare.2 (Or.inr ⟨Or.inl rfl, ht⟩)

/-- For `S ⊆ (0, 1)`, the points of the frontier of the open unit square with first coordinate
below `1` and second coordinate in `S` are those of the left side over `S`. -/
theorem frontier_openUnitSquare_inter_eq_unitSquareLeftSide {S : Set ℝ} (hS : S ⊆ Ioo 0 1) :
    frontier openUnitSquare ∩ {x | x.fst < 1 ∧ x.snd ∈ S} = unitSquareLeftSide S := by
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_unitSquareLeftSide, mem_frontier_openUnitSquare]
  constructor
  · rintro ⟨⟨-, h0 | h1⟩ | ⟨h0 | h1, -⟩, hx1, hS'⟩
    · exact absurd h0 (hS hS').1.ne'
    · exact absurd h1 (hS hS').2.ne
    · exact ⟨h0, hS'⟩
    · exact absurd h1 hx1.ne
  · rintro ⟨h0, hS'⟩
    exact ⟨Or.inr ⟨Or.inl h0, Ioo_subset_Icc_self (hS hS')⟩, by rw [h0]; exact zero_lt_one, hS'⟩

/-- **Parts of the left side are relatively open.** For an open `S ⊆ (0, 1)`, the part `{0} × S`
is relatively open in the frontier of the open unit square. -/
theorem exists_isOpen_frontier_openUnitSquare_inter_eq {S : Set ℝ} (hSo : IsOpen S)
    (hS : S ⊆ Ioo 0 1) :
    ∃ U, IsOpen U ∧ frontier openUnitSquare ∩ U = unitSquareLeftSide S :=
  ⟨_, (isOpen_lt (WithLp.continuous_fst 2 ℝ ℝ) continuous_const).inter
    (hSo.preimage (WithLp.continuous_snd 2 ℝ ℝ)),
    frontier_openUnitSquare_inter_eq_unitSquareLeftSide hS⟩

/-! ### The open left side is admissible -/

/-- The corner chart of the open unit square at `(0, 0)` is a boundary-part chart of the open left
side over the half-line `(0, ∞)`: on the graph `u = |v|`, the left side is the branch `v > 0`. -/
private theorem isBoundaryPartChart_unitSquareLeftSide_zero :
    openUnitSquare.IsBoundaryPartChart (unitSquareLeftSide (Ioo 0 1))
      (prodRecentredRotation (√2)⁻¹ (√2)⁻¹ Real.inv_sqrt_two_sq_add_inv_sqrt_two_sq 0)
      (fun s => |s|) 1 (1 / 2) (1 / 2) (Ioi 0) := by
  refine isLipschitzChartWith_openUnitSquare_zero.toIsLipschitzChart
    |>.isBoundaryPartChart_of_forall_mem_iff fun z hz => ?_
  have hk0 : (0 : ℝ) < (√2)⁻¹ := by positivity
  have hk1 : (√2)⁻¹ < (1 : ℝ) := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
  set k : ℝ := (√2)⁻¹
  rw [mem_normalCylinder, Real.norm_eq_abs, abs_lt] at hz
  simp only [mem_unitSquareLeftSide, prodRecentredRotation_symm_apply_fst,
    prodRecentredRotation_symm_apply_snd, WithLp.zero_fst, WithLp.zero_snd, zero_add, mem_Ioo,
    mem_Ioi]
  constructor
  · rintro ⟨h1, h2, -⟩
    have huv : z.fst = z.snd := by
      rcases mul_eq_zero.1 (show k * (z.fst - z.snd) = 0 by linarith) with h | h
      · exact absurd h hk0.ne'
      · linarith
    have hv : 0 < z.snd := by nlinarith
    exact ⟨by rw [huv, abs_of_pos hv], hv⟩
  · rintro ⟨h1, hv⟩
    rw [abs_of_pos hv] at h1
    rw [h1]
    exact ⟨by ring, by positivity, by nlinarith⟩

/-- The corner chart at `(0, 1)` is a boundary-part chart of the open left side over the
half-line `(-∞, 0)`: on the graph `u = |v|`, the left side is the branch `v < 0`. -/
private theorem isBoundaryPartChart_unitSquareLeftSide_zero_one :
    openUnitSquare.IsBoundaryPartChart (unitSquareLeftSide (Ioo 0 1))
      (prodRecentredRotation (√2)⁻¹ (-(√2)⁻¹) (by rw [neg_sq]; exact
        Real.inv_sqrt_two_sq_add_inv_sqrt_two_sq) (WithLp.toLp 2 (0, 1)))
      (fun s => |s|) 1 (1 / 2) (1 / 2) (Iio 0) := by
  refine isLipschitzChartWith_openUnitSquare_zero_one.toIsLipschitzChart
    |>.isBoundaryPartChart_of_forall_mem_iff fun z hz => ?_
  have hk0 : (0 : ℝ) < (√2)⁻¹ := by positivity
  have hk1 : (√2)⁻¹ < (1 : ℝ) := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
  set k : ℝ := (√2)⁻¹
  rw [mem_normalCylinder, Real.norm_eq_abs, abs_lt] at hz
  simp only [mem_unitSquareLeftSide, prodRecentredRotation_symm_apply_fst,
    prodRecentredRotation_symm_apply_snd, WithLp.toLp_fst, WithLp.toLp_snd, zero_add, mem_Ioo,
    mem_Iio]
  constructor
  · rintro ⟨h1, -, h2⟩
    have huv : z.fst = -z.snd := by
      rcases mul_eq_zero.1 (show k * (z.fst + z.snd) = 0 by linarith) with h | h
      · exact absurd h hk0.ne'
      · linarith
    have hv : z.snd < 0 := by nlinarith
    exact ⟨by rw [huv, abs_of_neg hv], hv⟩
  · rintro ⟨h1, hv⟩
    rw [abs_of_neg hv] at h1
    rw [h1]
    exact ⟨by ring, by nlinarith, by nlinarith⟩

/-- **The open left side of the unit square is an admissible boundary part.** The interfaces in
the one-dimensional base are modelled on a zero-dimensional `E'`. -/
theorem isAdmissibleBoundaryPart_unitSquareLeftSide_Ioo {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [Subsingleton E'] :
    openUnitSquare.IsAdmissibleBoundaryPart (unitSquareLeftSide (Ioo 0 1)) ℝ E' := by
  obtain ⟨U, hU, hUΓ⟩ := exists_isOpen_frontier_openUnitSquare_inter_eq isOpen_Ioo subset_rfl
  refine isLipschitzDomainWith_openUnitSquare.isLipschitzDomain
    |>.isAdmissibleBoundaryPart_of_frontier_inter_eq hU hUΓ fun x hx => ?_
  -- Only the two corners `(0, 0)` and `(0, 1)` lie in the closure but not in the part.
  rw [closure_unitSquareLeftSide, closure_Ioo zero_ne_one] at hx
  obtain ⟨⟨hx0, hx1, hx2⟩, hxn⟩ := hx
  have hx' : x = WithLp.toLp 2 (0, x.snd) :=
    (WithLp.ext_iff 2).2 (Prod.ext (by simpa using hx0) rfl)
  rcases hx1.eq_or_lt with h | h
  · refine ⟨_, _, _, _, _, _, isBoundaryPartChart_unitSquareLeftSide_zero,
      isAdmissibleBaseRegion_Ioi 0, ?_⟩
    have hx0' : x = 0 := by
      rw [hx', ← h]
      simp
    rw [hx0', prodRecentredRotation_apply_self]
  rcases hx2.eq_or_lt with h' | h'
  · refine ⟨_, _, _, _, _, _, isBoundaryPartChart_unitSquareLeftSide_zero_one,
      isAdmissibleBaseRegion_Iio 0, ?_⟩
    rw [hx', h', prodRecentredRotation_apply_self]
  exact absurd ⟨hx0, h, h'⟩ hxn

/-! ### Two relatively open parts that are not admissible -/

/-- Near each point `(0, t₀)` of the closed left side, the parameters `t` at which `(0, t)` lies in
an admissible boundary part of the open unit square form an interval. -/
private theorem exists_ordConnected_of_isAdmissibleBoundaryPart {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Γ : Set (WithLp 2 (ℝ × ℝ))}
    (hΓ : openUnitSquare.IsAdmissibleBoundaryPart Γ ℝ E') {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 1) :
    ∃ ε > 0, (Ioo (t₀ - ε) (t₀ + ε) ∩ Icc 0 1 ∩
      (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹' Γ).OrdConnected := by
  obtain ⟨e, γ, K, h, r, B, hc, hB, hex⟩ :=
    hΓ.exists_isBoundaryPartChart _ (toLp_zero_prod_mem_frontier_openUnitSquare ht₀)
  have hcont := (WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)).continuous
  have hN : (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹' (e ⁻¹' normalCylinder h r) ∈ 𝓝 t₀ :=
    hcont.continuousAt.preimage_mem_nhds
      (((isOpen_normalCylinder h r).preimage e.continuous).mem_nhds (by
        rw [mem_preimage, hex]
        exact zero_mem_normalCylinder hc.isLipschitzChart.height_pos
          hc.isLipschitzChart.radius_pos))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, hc.ordConnected_inter_preimage hB.ordConnected
    (ordConnected_Ioo.inter ordConnected_Icc) hcont.continuousOn
    (WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)).injective.injOn
    (fun t ht => toLp_zero_prod_mem_frontier_openUnitSquare ht.2) fun t ht => hball ?_⟩
  rw [Real.ball_eq_Ioo]
  exact ht.1

/-- **An oscillating relatively open part that is not admissible.** The part
`{0} × ⋃_{k ≥ 1} (1 / (2k + 1), 1 / (2k))` of the left side, written here with `k` shifted to start
at `0`, alternates with its complement
infinitely often near the corner `(0, 0)`, so no boundary-part chart at the corner presents it as
the part of the graph over a half-line, all of the base, or none of it. It is relatively open in
the frontier by `TauCeti.exists_isOpen_frontier_openUnitSquare_inter_eq`. -/
theorem not_isAdmissibleBoundaryPart_unitSquareLeftSide_iUnion {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    ¬ openUnitSquare.IsAdmissibleBoundaryPart
      (unitSquareLeftSide (⋃ k : ℕ, Ioo (1 / (2 * k + 3 : ℝ)) (1 / (2 * k + 2)))) ℝ E' := by
  intro hΓ
  obtain ⟨ε, hε, hoc⟩ := exists_ordConnected_of_isAdmissibleBoundaryPart hΓ (t₀ := 0)
    ⟨le_rfl, zero_le_one⟩
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hkε : 1 < k * ε := by rwa [inv_lt_iff_one_lt_mul₀ hε] at hk
  -- The points `2 / (4k + 9) < 1 / (2k + 3) < 2 / (4k + 5)`: the outer two lie in the
  -- `(k + 1)`-st and `k`-th intervals, the middle one in the gap between them.
  have hmem (t : ℝ) (j : ℕ) (hj : t ∈ Ioo (1 / (2 * j + 3 : ℝ)) (1 / (2 * j + 2)))
      (ht : t < ε) :
      t ∈ Ioo (0 - ε) (0 + ε) ∩ Icc 0 1 ∩ (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹'
        unitSquareLeftSide (⋃ k : ℕ, Ioo (1 / (2 * k + 3 : ℝ)) (1 / (2 * k + 2))) := by
    have hj0 : 0 < 1 / (2 * j + 3 : ℝ) := by positivity
    have hj1 : 1 / (2 * j + 2 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    refine ⟨⟨⟨by linarith [hj.1], by linarith⟩, by linarith [hj.1], by linarith [hj.2]⟩, ?_⟩
    simp only [mem_preimage, mem_unitSquareLeftSide, WithLp.toLp_fst, WithLp.toLp_snd, true_and,
      mem_iUnion]
    exact ⟨j, hj⟩
  have hI₁ : (2 / (4 * k + 9) : ℝ) ∈
      Ioo (1 / (2 * ((k + 1 : ℕ) : ℝ) + 3)) (1 / (2 * (k + 1 : ℕ) + 2)) := by
    push_cast
    constructor <;> rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> linarith
  have hI₂ : (2 / (4 * k + 5) : ℝ) ∈ Ioo (1 / (2 * (k : ℝ) + 3)) (1 / (2 * k + 2)) := by
    constructor <;> rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> linarith
  have hε₁ : (2 / (4 * k + 9) : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hε₂ : (2 / (4 * k + 5) : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hgap₁ : (2 / (4 * k + 9) : ℝ) ≤ 1 / (2 * k + 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hgap₂ : (1 / (2 * k + 3) : ℝ) ≤ 2 / (4 * k + 5) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hgap := (hoc.out (hmem _ _ hI₁ hε₁) (hmem _ _ hI₂ hε₂) ⟨hgap₁, hgap₂⟩).2
  simp only [mem_preimage, mem_unitSquareLeftSide, WithLp.toLp_fst, WithLp.toLp_snd, true_and,
    mem_iUnion, mem_Ioo] at hgap
  obtain ⟨j, hj₁, hj₂⟩ := hgap
  rw [one_div_lt_one_div (by positivity) (by positivity)] at hj₁ hj₂
  have hkj : k < j := by exact_mod_cast (show (k : ℝ) < j by linarith)
  have hjk : 2 * j < 2 * k + 1 := by exact_mod_cast (show (2 * j : ℝ) < 2 * k + 1 by linarith)
  omega

/-- The open interval `(0, 1)` with its midpoint removed has closure `[0, 1]`. -/
private theorem closure_Ioo_diff_singleton :
    closure (Ioo (0 : ℝ) 1 \ {1 / 2}) = Icc 0 1 := by
  have h : Ioo (0 : ℝ) 1 \ {1 / 2} = Ioo 0 (1 / 2) ∪ Ioo (1 / 2) 1 := by
    ext t
    simp only [mem_sdiff, mem_Ioo, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨⟨h0, h1⟩, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨⟨h0, by linarith⟩, h.ne⟩
      · exact ⟨⟨by linarith, h1⟩, h.ne'⟩
  rw [h, closure_union, closure_Ioo (by norm_num), closure_Ioo (by norm_num),
    Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

/-- **A punctured side is not admissible.** The part `{0} × ((0, 1) ∖ {1/2})` lies over both
sides of the base point of any boundary-part chart at `(0, 1/2)`, but not over the point itself.
It is relatively open in the frontier by `TauCeti.exists_isOpen_frontier_openUnitSquare_inter_eq`,
and has the same closure as the admissible open side
(`TauCeti.closure_unitSquareLeftSide_diff`). -/
theorem not_isAdmissibleBoundaryPart_unitSquareLeftSide_diff {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    ¬ openUnitSquare.IsAdmissibleBoundaryPart (unitSquareLeftSide (Ioo 0 1 \ {1 / 2})) ℝ E' := by
  intro hΓ
  obtain ⟨ε, hε, hoc⟩ := exists_ordConnected_of_isAdmissibleBoundaryPart hΓ (t₀ := 1 / 2)
    ⟨by norm_num, by norm_num⟩
  set δ := min (ε / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have h₁ : 1 / 2 - δ ∈ Ioo (1 / 2 - ε) (1 / 2 + ε) ∩ Icc 0 1 ∩
      (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹' unitSquareLeftSide (Ioo 0 1 \ {1 / 2}) := by
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    simp only [mem_preimage, mem_unitSquareLeftSide, WithLp.toLp_fst, WithLp.toLp_snd, true_and,
      mem_sdiff, mem_Ioo, mem_singleton_iff]
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  have h₂ : 1 / 2 + δ ∈ Ioo (1 / 2 - ε) (1 / 2 + ε) ∩ Icc 0 1 ∩
      (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹' unitSquareLeftSide (Ioo 0 1 \ {1 / 2}) := by
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    simp only [mem_preimage, mem_unitSquareLeftSide, WithLp.toLp_fst, WithLp.toLp_snd, true_and,
      mem_sdiff, mem_Ioo, mem_singleton_iff]
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  have hhalf : (1 / 2 : ℝ) ∈ Icc (1 / 2 - δ) (1 / 2 + δ) := ⟨by linarith, by linarith⟩
  have hmid := (hoc.out h₁ h₂ hhalf).2
  simp at hmid

/-- The punctured side `{0} × ((0, 1) ∖ {1/2})` has the same closure as the open side
`{0} × (0, 1)`, namely the closed side `{0} × [0, 1]`. -/
theorem closure_unitSquareLeftSide_diff :
    closure (unitSquareLeftSide (Ioo 0 1 \ {1 / 2})) = closure (unitSquareLeftSide (Ioo 0 1)) := by
  rw [closure_unitSquareLeftSide, closure_unitSquareLeftSide, closure_Ioo_diff_singleton,
    closure_Ioo zero_ne_one]

/-- **Admissibility is not a property of `closure Γ`.** The non-admissible punctured side
`{0} × ((0, 1) ∖ {1/2})` and the admissible open side `{0} × (0, 1)` define the same space
`W^{1,p}_Γ` on the open unit square, since `W^{1,p}_Γ` depends on `Γ` only through its
closure. -/
theorem w1pVanishingOnSubmodule_unitSquareLeftSide_diff (mu : Measure (WithLp 2 (ℝ × ℝ)))
    [mu.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    w1pVanishingOnSubmodule mu ⟨openUnitSquare, isOpen_openUnitSquare⟩ p
        (unitSquareLeftSide (Ioo 0 1 \ {1 / 2})) =
      w1pVanishingOnSubmodule mu ⟨openUnitSquare, isOpen_openUnitSquare⟩ p
        (unitSquareLeftSide (Ioo 0 1)) := by
  rw [← w1pVanishingOnSubmodule_closure, closure_unitSquareLeftSide_diff,
    w1pVanishingOnSubmodule_closure]

end TauCeti
