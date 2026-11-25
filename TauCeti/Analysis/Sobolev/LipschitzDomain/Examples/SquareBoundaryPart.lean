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
# Boundary parts on the left side of the unit square

On the open unit square `(0, 1)²`, a set `S ⊆ (0, 1)` gives the part `{0} × S` of the left side
of the frontier (`TauCeti.squareLeftPart S`). For open `S` it is relatively open in the frontier.

* `{0} × (0, 1)` is an admissible boundary part
  (`TauCeti.isAdmissibleBoundaryPart_squareLeftPart_Ioo`): along the open left side every chart
  sees the whole base, away from the closed left side none of it, and at the corners `(0, 0)`
  and `(0, 1)` the charts are the rotations by `π / 4` and `-π / 4` with graph `|s|`, in which
  the side is the graph over one side of the base point.
* `{0} × ⋃ₖ (1/(2k+3), 1/(2k+2))` is not admissible
  (`TauCeti.not_isAdmissibleBoundaryPart_squareLeftPart_alternatingIntervals`): near the corner
  `(0, 0)` it alternates infinitely often.
* `{0} × ((0, 1) ∖ {1/2})` is not admissible
  (`TauCeti.not_isAdmissibleBoundaryPart_squareLeftPart_punctured`), although it has the closure
  of `{0} × (0, 1)` (as `TauCeti.closure_squareLeftPart` computes) and hence the same `W^{1,p}_Γ`
  (`TauCeti.w1pVanishingOnSubmodule_squareLeftPart_punctured`). Admissibility is not a property
  of `closure Γ`.

Both negative Checks come from `Set.IsAdmissibleBoundaryPart.exists_mem_nhds_forall_mem_of_mapsTo`:
along a segment of the frontier near a point, the parameters of the points of an admissible part
form an interval. The charts have the one-dimensional base `ℝ`, and the interfaces in the base are
points, modelled on any zero space such as `Fin 0 → ℝ`.
-/

public section

noncomputable section

open Metric Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace TauCeti

/-! ### The left side of the square -/

/-- The part `{0} × S` of the left side of the unit square. -/
def squareLeftPart (S : Set ℝ) : Set (WithLp 2 (ℝ × ℝ)) :=
  {x | x.fst = 0 ∧ x.snd ∈ S}

/-- Membership in `{0} × S`. -/
@[simp]
theorem mem_squareLeftPart {S : Set ℝ} {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ squareLeftPart S ↔ x.fst = 0 ∧ x.snd ∈ S :=
  Iff.rfl

/-- The point `(0, s)` lies in `{0} × S` exactly when `s ∈ S`. -/
theorem toLp_zero_prod_mem_squareLeftPart {S : Set ℝ} {s : ℝ} :
    WithLp.toLp 2 ((0 : ℝ), s) ∈ squareLeftPart S ↔ s ∈ S :=
  and_iff_right rfl

/-- The left side `{0} × S` is the image of `S` under `s ↦ (0, s)`. -/
theorem squareLeftPart_eq_image (S : Set ℝ) :
    squareLeftPart S = (fun s : ℝ => WithLp.toLp 2 ((0 : ℝ), s)) '' S := by
  ext x
  refine ⟨fun hx => ⟨x.snd, hx.2, WithLp.ofLp_injective 2 (Prod.ext (by simp [hx.1]) (by simp))⟩,
    ?_⟩
  rintro ⟨s, hs, rfl⟩
  exact toLp_zero_prod_mem_squareLeftPart.2 hs

/-- The closure of `{0} × S` is `{0} × closure S`. -/
theorem closure_squareLeftPart (S : Set ℝ) :
    closure (squareLeftPart S) = squareLeftPart (closure S) := by
  rw [squareLeftPart_eq_image, squareLeftPart_eq_image,
    (WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)).isClosedEmbedding.closure_image_eq]

/-- The path `s ↦ (0, s)` along the left side is continuous. -/
private theorem continuous_toLp_zero_prod : Continuous fun s : ℝ => WithLp.toLp 2 ((0 : ℝ), s) :=
  (WithLp.prod_continuous_toLp 2 ℝ ℝ).comp (continuous_const.prodMk continuous_id)

/-- `{0} × S` lies in the frontier of the open unit square when `S ⊆ [0, 1]`. -/
theorem squareLeftPart_subset_frontier {S : Set ℝ} (hS : S ⊆ Icc 0 1) :
    squareLeftPart S ⊆ frontier openUnitSquare :=
  fun _ hx => mem_frontier_openUnitSquare_of_fst_eq_zero hx.1 (hS hx.2)

/-- **`{0} × S` is relatively open** in the frontier of the open unit square, for open
`S ⊆ (0, 1)`. -/
theorem exists_isOpen_frontier_inter_eq_squareLeftPart {S : Set ℝ} (hSo : IsOpen S)
    (hS : S ⊆ Ioo 0 1) :
    ∃ U : Set (WithLp 2 (ℝ × ℝ)), IsOpen U ∧ frontier openUnitSquare ∩ U = squareLeftPart S := by
  refine ⟨{x | x.fst < 1 ∧ x.snd ∈ S},
    (isOpen_lt (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst continuous_const).inter
      (hSo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd), ?_⟩
  ext x
  refine ⟨fun hx => ⟨fst_eq_zero_of_mem_frontier_openUnitSquare hx.1 hx.2.1 (hS hx.2.2),
    hx.2.2⟩, fun hx => ⟨squareLeftPart_subset_frontier (hS.trans Ioo_subset_Icc_self) hx, ?_,
      hx.2⟩⟩
  rw [hx.1]
  exact zero_lt_one

/-! ### The negative Checks -/

/-- **A criterion for non-admissibility on the left side.** If, arbitrarily close to some `y`,
there are parameters `a ≤ t ≤ b` with `a, b ∈ S` and `t ∉ S`, then `{0} × S` is not an
admissible boundary part of the open unit square, whatever the interface model `E'`. -/
theorem not_isAdmissibleBoundaryPart_squareLeftPart {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {S : Set ℝ} {y : ℝ}
    (h : ∀ δ > 0, ∃ a t b : ℝ, a ≤ t ∧ t ≤ b ∧ y - δ < a ∧ b < y + δ ∧ a ∈ S ∧ b ∈ S ∧ t ∉ S) :
    ¬ openUnitSquare.IsAdmissibleBoundaryPart (squareLeftPart S) ℝ E' := by
  intro hΓ
  -- An admissible part lies in the frontier, so `S ⊆ [0, 1]`, and `y ∈ [0, 1]` is a limit of `S`.
  have hS (s : ℝ) (hs : s ∈ S) : s ∈ Icc 0 1 :=
    (mem_Icc_of_mem_frontier_openUnitSquare
      (hΓ.subset_frontier (toLp_zero_prod_mem_squareLeftPart.2 hs))).2
  have hy : y ∈ Icc 0 1 := by
    refine ⟨not_lt.1 fun hy0 => ?_, not_lt.1 fun hy1 => ?_⟩
    · obtain ⟨a, t, b, -, -, -, hb, -, hbS, -⟩ := h (-y) (by linarith)
      linarith [(hS b hbS).1]
    · obtain ⟨a, t, b, -, -, ha, -, haS, -, -⟩ := h (y - 1) (by linarith)
      linarith [(hS a haS).2]
  obtain ⟨U, hU, hmain⟩ := hΓ.exists_mem_nhds_forall_mem_of_mapsTo
    (squareLeftPart_subset_frontier subset_rfl (toLp_zero_prod_mem_squareLeftPart.2 hy))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨a, t, b, hat, htb, ha, hb, haS, hbS, htS⟩ := h ε hε
  have hab := hat.trans htb
  refine htS (toLp_zero_prod_mem_squareLeftPart.1 (hmain (fun s => WithLp.toLp 2 (0, s)) hab
    continuous_toLp_zero_prod.continuousOn
    (fun s _ u _ hsu => (Prod.mk.inj (WithLp.toLp_injective 2 hsu)).2)
    (fun s hs => ⟨?_, hball ?_⟩) (toLp_zero_prod_mem_squareLeftPart.2 haS)
    (toLp_zero_prod_mem_squareLeftPart.2 hbS) t ⟨hat, htb⟩))
  · exact squareLeftPart_subset_frontier subset_rfl (toLp_zero_prod_mem_squareLeftPart.2
      ⟨(hS a haS).1.trans hs.1, hs.2.trans (hS b hbS).2⟩)
  · rw [mem_ball, WithLp.prod_dist_eq_of_L2, Real.sqrt_lt' hε]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq]
    have : |s - y| < ε := abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    nlinarith [abs_nonneg (s - y)]

/-- The union `⋃ₖ (1/(2k+3), 1/(2k+2))` of the intervals `(1/3, 1/2), (1/5, 1/4), …`. -/
def alternatingIntervals : Set ℝ :=
  ⋃ k : ℕ, Ioo (1 / (2 * k + 3)) (1 / (2 * k + 2))

/-- Membership in `⋃ₖ (1/(2k+3), 1/(2k+2))`. -/
@[simp]
theorem mem_alternatingIntervals {x : ℝ} :
    x ∈ alternatingIntervals ↔ ∃ k : ℕ, x ∈ Ioo (1 / (2 * (k : ℝ) + 3)) (1 / (2 * k + 2)) :=
  mem_iUnion

/-- The intervals of `TauCeti.alternatingIntervals` lie in `(0, 1)`. -/
theorem alternatingIntervals_subset_Ioo : alternatingIntervals ⊆ Ioo 0 1 := by
  refine iUnion_subset fun k x hx => ⟨(by positivity : (0 : ℝ) < 1 / (2 * k + 3)).trans hx.1,
    hx.2.trans ?_⟩
  rw [div_lt_one (by positivity)]
  linarith [k.cast_nonneg (α := ℝ)]

/-- `TauCeti.alternatingIntervals` is open. -/
theorem isOpen_alternatingIntervals : IsOpen alternatingIntervals :=
  isOpen_iUnion fun _ => isOpen_Ioo

/-- The left endpoint `1/(2k+3)` of an interval of `TauCeti.alternatingIntervals` is not in it. -/
theorem one_div_notMem_alternatingIntervals (k : ℕ) :
    1 / (2 * (k : ℝ) + 3) ∉ alternatingIntervals := by
  simp only [mem_alternatingIntervals, mem_Ioo, not_exists, not_and]
  intro i h1 h2
  rw [one_div_lt_one_div (by positivity) (by positivity)] at h1 h2
  have hki : k < i := by exact_mod_cast (by linarith : (k : ℝ) < i)
  have : (k : ℝ) + 1 ≤ i := by exact_mod_cast hki
  linarith

/-- **`{0} × ⋃ₖ (1/(2k+3), 1/(2k+2))` is not admissible**: near the corner `(0, 0)` it
alternates infinitely often, so no chart at the corner sees it over all, none, or one side of
its base point. -/
theorem not_isAdmissibleBoundaryPart_squareLeftPart_alternatingIntervals {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    ¬ openUnitSquare.IsAdmissibleBoundaryPart (squareLeftPart alternatingIntervals) ℝ E' := by
  refine not_isAdmissibleBoundaryPart_squareLeftPart (y := 0) fun δ hδ => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  -- `a` lies in the interval of index `k + 1`, `b` in that of index `k`, and `t` between them.
  refine ⟨2 / (4 * k + 9), 1 / (2 * k + 3), 2 / (4 * k + 5), ?_, ?_, ?_, ?_, ?_, ?_,
    one_div_notMem_alternatingIntervals k⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · linarith [(by positivity : (0 : ℝ) < 2 / (4 * k + 9))]
  · refine lt_of_lt_of_le ?_ (by linarith : 1 / ((k : ℝ) + 1) ≤ 0 + δ)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  · refine mem_alternatingIntervals.2 ⟨k + 1, ?_, ?_⟩ <;> push_cast <;>
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> linarith
  · refine mem_alternatingIntervals.2 ⟨k, ?_, ?_⟩ <;>
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> linarith

/-- **`{0} × ((0, 1) ∖ {1/2})` is not admissible**: at `(0, 1/2)` it lies over both sides of the
base point but not over the point itself. -/
theorem not_isAdmissibleBoundaryPart_squareLeftPart_punctured {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    ¬ openUnitSquare.IsAdmissibleBoundaryPart (squareLeftPart (Ioo 0 1 \ {1 / 2})) ℝ E' := by
  refine not_isAdmissibleBoundaryPart_squareLeftPart (y := 1 / 2) fun δ hδ => ?_
  have hm : 0 < min δ (1 / 2) := lt_min hδ one_half_pos
  have hm' : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hmδ : min δ (1 / 2) ≤ δ := min_le_left _ _
  refine ⟨1 / 2 - min δ (1 / 2) / 2, 1 / 2, 1 / 2 + min δ (1 / 2) / 2, by linarith, by linarith,
    by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, ?_⟩, ⟨⟨by linarith, by linarith⟩, ?_⟩,
    fun h => h.2 rfl⟩
  · rw [mem_singleton_iff]
    linarith
  · rw [mem_singleton_iff]
    linarith

/-- `{0} × ((0, 1) ∖ {1/2})` and `{0} × (0, 1)` have the same closure. -/
theorem closure_squareLeftPart_punctured :
    closure (squareLeftPart (Ioo 0 1 \ {1 / 2})) = closure (squareLeftPart (Ioo 0 1)) := by
  have hsub : squareLeftPart (Ioo 0 1 \ {1 / 2}) ⊆ squareLeftPart (Ioo 0 1) :=
    fun x hx => ⟨hx.1, hx.2.1⟩
  refine (closure_mono hsub).antisymm (closure_minimal ?_ isClosed_closure)
  rw [squareLeftPart_eq_image, squareLeftPart_eq_image]
  refine (image_mono ?_).trans (image_closure_subset_closure_image continuous_toLp_zero_prod)
  simpa only [sdiff_eq] using (dense_compl_singleton (1 / 2 : ℝ)).open_subset_closure_inter
    isOpen_Ioo

/-- **The punctured side has the same `W^{1,p}_Γ` as the full side**, on every open set, since
`W^{1,p}_Γ` depends on `Γ` only through its closure. -/
theorem w1pVanishingOnSubmodule_squareLeftPart_punctured
    (mu : Measure (WithLp 2 (ℝ × ℝ))) [mu.IsAddHaarMeasure]
    (Omega : TopologicalSpace.Opens (WithLp 2 (ℝ × ℝ))) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    w1pVanishingOnSubmodule mu Omega p (squareLeftPart (Ioo 0 1 \ {1 / 2})) =
      w1pVanishingOnSubmodule mu Omega p (squareLeftPart (Ioo 0 1)) := by
  rw [← w1pVanishingOnSubmodule_closure, closure_squareLeftPart_punctured,
    w1pVanishingOnSubmodule_closure]

/-! ### The positive Check -/

/-- The side near the corner `(0, 0)` in the coordinates of the rotation by `π / 4`: with
`k = (√2)⁻¹`, the point `(k u - k v, k u + k v)` lies on `{0} × (0, 1)` exactly when `u = |v|` and
`0 < v`, for `|v| < 1 / 2`. -/
private theorem corner_mem_squareLeftPart_iff {u v : ℝ} (hv : |v| < 1 / 2) :
    ((√2)⁻¹ * u - (√2)⁻¹ * v = 0 ∧ (√2)⁻¹ * u + (√2)⁻¹ * v ∈ Ioo (0 : ℝ) 1) ↔
      u = |v| ∧ 0 < v := by
  have hk0 : (0 : ℝ) < (√2)⁻¹ := by positivity
  have hk1 : (√2)⁻¹ < (1 : ℝ) := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
  rw [abs_lt] at hv
  constructor
  · rintro ⟨h1, h2, -⟩
    have huv : u = v := by
      rw [← mul_sub, mul_eq_zero, sub_eq_zero] at h1
      exact h1.resolve_left hk0.ne'
    subst huv
    have hu : 0 < u := by nlinarith
    exact ⟨(abs_of_pos hu).symm, hu⟩
  · rintro ⟨rfl, hv0⟩
    rw [abs_of_pos hv0]
    exact ⟨sub_self _, by positivity, by nlinarith⟩

/-- The corner chart of `{0} × (0, 1)` at `(0, 0)`: the rotation by `π / 4` with graph `|s|`, in
which the side is the graph over `(0, ∞)`. -/
private theorem exists_isBoundaryPartChart_corner_zero :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (h r : ℝ),
      openUnitSquare.IsBoundaryPartChart (squareLeftPart (Ioo 0 1)) e (fun s => |s|) 1 h r
        (Ioi 0) ∧ e 0 = 0 := by
  refine ⟨_, _, _, isLipschitzChartWith_openUnitSquare_zero.toIsLipschitzChart
    |>.isBoundaryPartChart_of_forall_mem_iff fun z hz => ?_, prodRecentredRotation_apply_self ..⟩
  rw [mem_normalCylinder, Real.norm_eq_abs] at hz
  simp only [mem_squareLeftPart, prodRecentredRotation_symm_apply_fst,
    prodRecentredRotation_symm_apply_snd, WithLp.zero_fst, WithLp.zero_snd, zero_add, mem_Ioi]
  exact corner_mem_squareLeftPart_iff hz.2.2

/-- The corner chart of `{0} × (0, 1)` at `(0, 1)`: the rotation by `-π / 4` with graph `|s|`, in
which the side is the graph over `(-∞, 0)`. Its arithmetic is that of `(0, 0)` under `v ↦ -v`. -/
private theorem exists_isBoundaryPartChart_corner_one :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (h r : ℝ),
      openUnitSquare.IsBoundaryPartChart (squareLeftPart (Ioo 0 1)) e (fun s => |s|) 1 h r
        (Iio 0) ∧ e (WithLp.toLp 2 (0, 1)) = 0 := by
  refine ⟨_, _, _, isLipschitzChartWith_openUnitSquare_zero_one.toIsLipschitzChart
    |>.isBoundaryPartChart_of_forall_mem_iff fun z hz => ?_, prodRecentredRotation_apply_self ..⟩
  rw [mem_normalCylinder, Real.norm_eq_abs, ← abs_neg] at hz
  simp only [mem_squareLeftPart, prodRecentredRotation_symm_apply_fst,
    prodRecentredRotation_symm_apply_snd, WithLp.toLp_fst, WithLp.toLp_snd, mem_Iio]
  rw [← abs_neg z.snd, ← neg_pos]
  refine Iff.trans ?_ (corner_mem_squareLeftPart_iff hz.2.2)
  simp only [mem_Ioo]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **`{0} × (0, 1)` is an admissible boundary part of the open unit square**, with base `ℝ` and
point interfaces, modelled on any zero space `E'`. Away from the closed left side the charts see
none of the base, along the open side all of it, and at the corners `(0, 0)` and `(0, 1)` the
rotations by `± π / 4` see the side over one side of the base point. -/
theorem isAdmissibleBoundaryPart_squareLeftPart_Ioo {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [Subsingleton E'] :
    openUnitSquare.IsAdmissibleBoundaryPart (squareLeftPart (Ioo 0 1)) ℝ E' := by
  have hsub := squareLeftPart_subset_frontier (S := Ioo 0 1) Ioo_subset_Icc_self
  refine ⟨hsub, fun x hx => ?_⟩
  obtain ⟨⟨hs0, -⟩, ht0, ht1⟩ := mem_Icc_of_mem_frontier_openUnitSquare hx
  obtain ⟨e, φ, a, b, hex, hc⟩ := (Set.isLipschitzDomainAtWith_iff ..).1
    (((Set.isLipschitzDomainWith_iff ..).1 isLipschitzDomainWith_openUnitSquare).2 x hx)
  have hc := hc.toIsLipschitzChart
  rcases hs0.lt_or_eq with hs0 | hs0
  · -- Away from the left side, `Γ` misses the neighbourhood `{0 < x.fst}`.
    obtain ⟨ρ, hρ⟩ := hc.exists_isBoundaryPartChart_empty (Γ := squareLeftPart (Ioo 0 1)) hex
      ((isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).mem_nhds hs0)
      (disjoint_left.2 fun y hy hy' => (hy.1 ▸ hy' : (0 : ℝ) < 0).false)
    exact ⟨e, φ, 1, ρ, ρ, ∅, hρ, isAdmissibleBaseRegion_empty, hex⟩
  rcases ht0.lt_or_eq with ht0 | ht0
  · rcases ht1.lt_or_eq with ht1 | ht1
    · -- Along the open left side, `Γ` contains the frontier near `x`.
      have hm : 0 < min x.snd (1 - x.snd) := lt_min ht0 (by linarith)
      obtain ⟨ρ, hρ⟩ := hc.exists_isBoundaryPartChart_univ hex (ball_mem_nhds x hm) hsub
        fun y ⟨hy, hyx⟩ => by
          have h1 := (WithLp.dist_fst_le y x).trans_lt hyx
          have h2 := (WithLp.dist_snd_le y x).trans_lt hyx
          rw [Real.dist_eq, abs_lt] at h1 h2
          have hm1 := min_le_left x.snd (1 - x.snd)
          have hm2 := min_le_right x.snd (1 - x.snd)
          have hy2 : y.snd ∈ Ioo 0 1 := ⟨by linarith, by linarith⟩
          exact ⟨fst_eq_zero_of_mem_frontier_openUnitSquare hy (by linarith) hy2, hy2⟩
      exact ⟨e, φ, 1, ρ, ρ, univ, hρ, isAdmissibleBaseRegion_univ, hex⟩
    · obtain rfl : x = WithLp.toLp 2 (0, 1) :=
        WithLp.ofLp_injective 2 (Prod.ext (by simp [← hs0]) (by simp [ht1]))
      obtain ⟨e', h, r, hc', hex'⟩ := exists_isBoundaryPartChart_corner_one
      exact ⟨e', _, 1, h, r, _, hc', isAdmissibleBaseRegion_Iio 0, hex'⟩
  · obtain rfl : x = 0 := WithLp.ofLp_injective 2 (Prod.ext (by simp [← hs0]) (by simp [← ht0]))
    obtain ⟨e', h, r, hc', hex'⟩ := exists_isBoundaryPartChart_corner_zero
    exact ⟨e', _, 1, h, r, _, hc', isAdmissibleBaseRegion_Ioi 0, hex'⟩

end TauCeti
