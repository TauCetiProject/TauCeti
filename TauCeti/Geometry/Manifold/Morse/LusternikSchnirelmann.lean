/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann
import TauCeti.Geometry.Manifold.LocallyContractible
import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# The Lusternik–Schnirelmann bound on critical points

A smooth function `f` on a compact boundaryless manifold `M` has at least as many critical points
as the unnormalized Lusternik–Schnirelmann category of `M`:
`lsCategoryCount M univ ≤ totalCriticalCount I f`
(`TauCeti.lsCategoryCount_univ_le_totalCriticalCount`). No nondegeneracy is assumed. Points are
counted, not critical values, and an infinite critical set has count `⊤`. For nonempty `M`, whose
normalized category is `cat M = lsCategoryCount M univ - 1`, this says that `f` has at least
`cat M + 1` critical points.

The bound is proved on the sublevels `{f ≤ t}`, by induction over the critical values
(`TauCeti.lsCategoryCount_sublevel_le_encard`). Across a compact band without critical points the
count of the sublevel does not grow (`TauCeti.lsCategoryCount_sublevel_le_of_band`): a deformation
of `M` along a descending flow carries the upper sublevel into the lower one. Across a critical
level `c` the deformation of `TauCeti.exists_criticalLevelDeformation` carries `{f ≤ c + ε}` into
`{f < c - ε} ∪ U`, for any open `U` containing the critical points of a band around `c`. Since a
manifold is locally contractible, `U` can be taken to be a union of one categorical open set per
critical point, so the count grows by at most the number of critical points in the band
(`TauCeti.exists_lsCategoryCount_sublevel_le_add`).

## Main declarations

* `TauCeti.lsCategoryCount_sublevel_le_of_band`: the count of `{f ≤ b}` is at most that of
  `{f ≤ a}` when `f⁻¹[a, b]` is compact and has no critical points.
* `TauCeti.exists_lsCategoryCount_sublevel_le_add`: the count of `{f ≤ c + ε}` exceeds that of
  `{f ≤ c - ε}` by at most the number of critical points in a compact band around `c`.
* `TauCeti.lsCategoryCount_sublevel_le_encard`: the count of `{f ≤ t}` is at most the number of
  critical points in `{f ≤ t}`.
* `TauCeti.lsCategoryCount_univ_le_totalCriticalCount`: the Lusternik–Schnirelmann theorem on a
  compact manifold.

## References

* L. Lusternik and L. Schnirelmann, *Méthodes topologiques dans les problèmes variationnels*,
  Hermann, Paris, 1934.
* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

/-- If `f` has finitely many critical points in `{f ≤ b}` and `c < b`, then for some `δ > 0` with
`c + δ ≤ b` every critical point of `f` in the band `f⁻¹[c - δ, c + δ]` lies on the level `c`. -/
private theorem exists_pos_criticalPoints_inter_band_subset {b c : ℝ} (hcb : c < b)
    (hfin : (criticalPoints I f ∩ {x | f x ≤ b}).Finite) :
    ∃ δ > 0, c + δ ≤ b ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ f ⁻¹' {c} := by
  -- The critical values in `{f ≤ b}` other than `c` form a finite, hence closed, set.
  have hW : IsClosed (f '' (criticalPoints I f ∩ {x | f x ≤ b}) \ {c}) :=
    (hfin.image f).sdiff.isClosed
  obtain ⟨η, hη, hηW⟩ := Metric.mem_nhds_iff.mp (hW.isOpen_compl.mem_nhds fun h ↦ h.2 rfl)
  have hδη : min (η / 2) (b - c) ≤ η / 2 := min_le_left _ _
  have hδb : min (η / 2) (b - c) ≤ b - c := min_le_right _ _
  refine ⟨min (η / 2) (b - c), lt_min (half_pos hη) (sub_pos.mpr hcb), by linarith, ?_⟩
  rintro x ⟨hx, h₁, h₂⟩
  by_contra hxc
  refine hηW ?_ ⟨⟨x, ⟨hx, (by linarith : f x ≤ b)⟩, rfl⟩, hxc⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

variable [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M]

/-- **No growth across a band without critical points.** If `f` is smooth and the band
`f⁻¹[a, b]` is compact and contains no critical point of `f`, then the Lusternik–Schnirelmann count
of the sublevel `{f ≤ b}` is at most that of `{f ≤ a}`. -/
theorem lsCategoryCount_sublevel_le_of_band (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a b : ℝ}
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x, a ≤ f x → f x ≤ b → x ∉ criticalPoints I f) :
    lsCategoryCount M {x | f x ≤ b} ≤ lsCategoryCount M {x | f x ≤ a} := by
  obtain ⟨Φ, h0, -, h1⟩ := exists_ambientSublevelDeformation hf hcompact fun x ha hb ↦
    mt mem_criticalPoints_iff_mfderiv_eq_zero.mpr (hcrit x ha hb)
  exact lsCategoryCount_le_of_deformation Φ h0 fun x hx ↦ (h1 x hx).le

/-- **Crossing a critical level.** If `f` is smooth and the band `f⁻¹[c - δ, c + δ]`, `δ > 0`, is
compact, then for some `0 < ε < δ` the Lusternik–Schnirelmann count of `{f ≤ c + ε}` exceeds that
of `{f ≤ c - ε}` by at most the number of critical points of `f` in the band. The critical points
may be degenerate. -/
theorem exists_lsCategoryCount_sublevel_le_add (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ lsCategoryCount M {x | f x ≤ c + ε} ≤
      lsCategoryCount M {x | f x ≤ c - ε} +
        (criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ)).encard := by
  have := I.stronglyLocallyContractibleSpace
  obtain ⟨U, hUo, hSU, hU⟩ := exists_isOpen_superset_lsCategoryCount_le_encard
    (ChartedSpace.stronglyLocallyContractibleSpace H M).locallyContractible
    (criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ))
  obtain ⟨ε, hε, hεδ, Φ, h0, -, h1⟩ := exists_criticalLevelDeformation hf hδ hcompact hUo
    fun x h₁ h₂ h₀ ↦ hSU ⟨mem_criticalPoints_iff_mfderiv_eq_zero.mpr h₀, h₁, h₂⟩
  refine ⟨ε, hε, hεδ, ?_⟩
  calc lsCategoryCount M {x | f x ≤ c + ε}
      ≤ lsCategoryCount M ({x | f x < c - ε} ∪ U) :=
        lsCategoryCount_le_of_deformation Φ h0 fun x hx ↦ h1 x hx
    _ ≤ lsCategoryCount M {x | f x < c - ε} + lsCategoryCount M U := lsCategoryCount_union_le
    _ ≤ _ := add_le_add (lsCategoryCount_mono fun x (hx : f x < c - ε) ↦ hx.le) hU

/-- **The Lusternik–Schnirelmann bound on sublevels.** Let `f` be smooth and `t < b`, and suppose
that the sublevel `{f ≤ b}` is compact and contains only finitely many critical points of `f`. Then
the Lusternik–Schnirelmann count of `{f ≤ t}` is at most the number of critical points of `f` in
`{f ≤ t}`. The critical points may be degenerate. -/
theorem lsCategoryCount_sublevel_le_encard (hf : ContMDiff I 𝓘(ℝ) ∞ f) {t b : ℝ} (htb : t < b)
    (hb : IsCompact {x | f x ≤ b}) (hfin : (criticalPoints I f ∩ {x | f x ≤ b}).Finite) :
    lsCategoryCount M {x | f x ≤ t} ≤ (criticalPoints I f ∩ {x | f x ≤ t}).encard := by
  set C := criticalPoints I f
  -- Bands and sublevels below `b` are closed subsets of the compact sublevel `{f ≤ b}`.
  have hcpt {s : Set ℝ} (hs : IsClosed s) (hsb : s ⊆ Iic b) : IsCompact (f ⁻¹' s) :=
    hb.of_isClosed_subset (hs.preimage hf.continuous) fun x hx ↦ hsb hx
  -- Strong induction on the number of critical values in `{f ≤ t}`.
  induction hn : (f '' (C ∩ {x | f x ≤ t})).ncard using Nat.strong_induction_on generalizing t
    with | _ n ih =>
  rcases (C ∩ {x | f x ≤ t}).eq_empty_or_nonempty with hC | hC
  · -- Without critical points, the compact sublevel `{f ≤ t}` is empty.
    have hempty : {x | f x ≤ t} = ∅ := by
      by_contra hne
      obtain ⟨x, hx, hxt⟩ := exists_mem_criticalPoints_of_isCompact_sublevel (I := I)
        hf.continuous (hcpt isClosed_Iic (Iic_subset_Iic.mpr htb.le))
        (nonempty_iff_ne_empty.mpr hne)
      exact hC.subset ⟨hx, hxt⟩
    simp [hempty]
  -- Otherwise let `c = f p ≤ t` be the largest critical value in `{f ≤ t}`, and cross the level
  -- `c` between `c - ε` and `c + ε`.
  have hfinC : (C ∩ {x | f x ≤ t}).Finite :=
    hfin.subset (inter_subset_inter_right _ fun x (hx : f x ≤ t) ↦ hx.trans htb.le)
  obtain ⟨p, ⟨hp, hpt : f p ≤ t⟩, hmax⟩ := exists_max_image _ f hfinC hC
  obtain ⟨δ, hδ, hcδ, hband⟩ := exists_pos_criticalPoints_inter_band_subset (hpt.trans_lt htb) hfin
  obtain ⟨ε, hε, hεδ, hstep⟩ := exists_lsCategoryCount_sublevel_le_add hf hδ
    (hcpt isClosed_Icc fun y hy ↦ hy.2.trans hcδ)
  -- Below the level `c - ε` the critical values are those below `c`, by the induction hypothesis.
  have hlt : (f '' (C ∩ {x | f x ≤ f p - ε})).ncard < n := by
    rw [← hn]
    refine (ncard_le_ncard ?_ (hfinC.image f).sdiff).trans_lt
      (ncard_sdiff_singleton_lt_of_mem ⟨p, ⟨hp, hpt⟩, rfl⟩ (hfinC.image f))
    rintro _ ⟨x, ⟨hx, hxc : f x ≤ f p - ε⟩, rfl⟩
    exact ⟨⟨x, ⟨hx, (by linarith : f x ≤ t)⟩, rfl⟩, fun h ↦ by
      rw [mem_singleton_iff] at h
      linarith⟩
  have hbelow := ih _ hlt (by linarith) rfl
  -- Between `c + ε` and `t` there are no critical points.
  have habove : lsCategoryCount M {x | f x ≤ t} ≤ lsCategoryCount M {x | f x ≤ f p + ε} := by
    rcases le_or_gt t (f p + ε) with h | h
    · exact lsCategoryCount_mono fun x (hx : f x ≤ t) ↦ hx.trans h
    · refine lsCategoryCount_sublevel_le_of_band hf (hcpt isClosed_Icc fun y hy ↦ hy.2.trans htb.le)
        fun x hx₁ hx₂ hx ↦ ?_
      linarith [hmax x ⟨hx, hx₂⟩]
  -- The critical points below `c - ε` and those of the band are disjoint parts of `C ∩ {f ≤ t}`.
  have hcount : (C ∩ {x | f x ≤ f p - ε}).encard + (C ∩ f ⁻¹' Icc (f p - δ) (f p + δ)).encard ≤
      (C ∩ {x | f x ≤ t}).encard := by
    rw [← encard_union_eq]
    · refine encard_le_encard (union_subset ?_ fun x hx ↦ ⟨hx.1, (hband hx).le.trans hpt⟩)
      rintro x ⟨hx, hxc : f x ≤ f p - ε⟩
      exact ⟨hx, (by linarith : f x ≤ t)⟩
    · refine disjoint_left.mpr ?_
      rintro x ⟨-, hxc : f x ≤ f p - ε⟩ hx
      have hxp : f x = f p := hband hx
      linarith
  calc lsCategoryCount M {x | f x ≤ t} ≤ lsCategoryCount M {x | f x ≤ f p + ε} := habove
    _ ≤ lsCategoryCount M {x | f x ≤ f p - ε} + (C ∩ f ⁻¹' Icc (f p - δ) (f p + δ)).encard :=
      hstep
    _ ≤ _ := (add_le_add hbelow le_rfl).trans hcount

/-- **The Lusternik–Schnirelmann theorem.** On a compact boundaryless manifold `M`, the
Lusternik–Schnirelmann count of `M` is at most the number of critical points of any smooth
function on `M`. The critical points may be degenerate; if there are infinitely many, their count
is `⊤`. -/
theorem lsCategoryCount_univ_le_totalCriticalCount [CompactSpace M]
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : lsCategoryCount M univ ≤ totalCriticalCount I f := by
  cases (criticalPoints I f).finite_or_infinite with
  | inr hinf => simp [totalCriticalCount_def, hinf.encard_eq]
  | inl hfin =>
    obtain ⟨t, ht⟩ := (isCompact_range hf.continuous).bddAbove
    have hu : {x | f x ≤ t} = univ := eq_univ_of_forall fun x ↦ ht (mem_range_self x)
    simpa [hu, totalCriticalCount_def] using lsCategoryCount_sublevel_le_encard hf (lt_add_one t)
      (isClosed_le hf.continuous continuous_const).isCompact (hfin.subset inter_subset_left)

end TauCeti
