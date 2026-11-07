/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.HeightCompression
import TauCeti.Topology.ContinuousOn.ClosedGraph
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Straightening an ordered family of graphs

Let `E` be a real Hilbert space, with points `(u, t)` of the cylinder `E × ℝ` having base point `u`
and height `t`. Consider graphs of functions `φ ν : E → ℝ` over neighbourhoods `U ν` of a base point
`c`, indexed by `ν ∈ ℤ`, whose heights `φ ν c` over `c` are distinct and tend to `-∞` and `+∞` as
`ν` tends to `-∞` and `+∞`, and which form a locally finite family. Łojasiewicz straightens such a
family near the vertical line through `c`: after restricting every graph to a small ball around
`c`, an analytic automorphism `g` of the cylinder turns the restricted graphs into bounded,
pairwise disjoint graphs of uniformly Lipschitz functions, whose heights tend to `∓∞` with `ν`
uniformly over bounded parts of the base, while `g` pushes everything away from the line into the
strip `|t| < 1`.

`TauCeti.exists_straightening_graphOn` proves this, for any open set `G` containing the vertical
line through `c`. It provides radii `a ν > 0` with `closedBall c (a ν) ⊆ U ν` and an automorphism
`g` of `E × ℝ`, analytic with analytic inverse, such that the pieces
`ψ ν = g '' (ball c (a ν)).graphOn (φ ν)` satisfy:

1. `g` maps the complement of `G` into the strip `|t| < 1`;
2. every `ψ ν` is bounded, and the `ψ ν` are pairwise disjoint;
3. every bounded subset of `E` lies below all but finitely many of the `ψ ν`, that is, in their
   projections to `E`;
4. over every bounded subset of `E`, the heights of `ψ ν` tend to `+∞` as `ν → +∞` and to `-∞`
   as `ν → -∞`, uniformly;
5. the heights of any two points of one `ψ ν` differ by at most `3` times the distance of their
   base points;
6. the closure of `ψ ν` lies in the image of the whole graph of `φ ν` over `U ν`, and `g` maps
   the rest of that graph into the strip `|t| < 1`; consequently the part of `ψ ν` outside the
   strip is closed.

Only Lipschitz continuity of each `φ ν` near `c` is assumed. Analytic functions satisfy this
hypothesis, by `ContDiffAt.exists_lipschitzOnWith`.

The automorphism is `g = g₂ ∘ g₁ ∘ τ`, where `τ` translates `c` to the origin and `g₁` and `g₂` are
the base scaling and the height compression of `TauCeti.Analysis.Analytic.HeightCompression`. The
choices behind it are made in three steps. Disjoint compact height intervals `Δ ν` around the
heights `φ ν c` form a locally finite family
(`TauCeti.exists_closedBall_pairwiseDisjoint_locallyFinite`). The radii `a ν` are chosen so that
`φ ν` maps `closedBall c (a ν)` into `Δ ν` with a Lipschitz constant `K ν`. Finally a tube
`‖u - c‖ ≤ γ t` around the vertical line is chosen inside `G` and away from the parts of the graphs
outside these balls (`IsOpen.exists_tube_subset`). The scaling function `h` of `g₁` is then any
positive analytic function given by `TauCeti.exists_analyticOnNhd_sqrt_sq_sub_one_lt_mul` for the
intervals `Δ ν`, the tube radius `γ`, lower bounds depending on `K ν`, `a ν` and `|ν|`, and
Lipschitz constants `(K ν + 1)⁻¹`.

## Main results

* `TauCeti.exists_straightening_graphOn`: the straightening of the family of graphs.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 10.
-/

public section

open Set Filter Metric Topology Function Real Bornology
open scoped NNReal

namespace TauCeti

section Straightening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Łojasiewicz's straightening of an ordered family of graphs.** Let `φ ν : E → ℝ`, for `ν ∈ ℤ`,
be Lipschitz near `c`, with graphs over neighbourhoods `U ν` of `c` forming a locally finite family,
and with heights `φ ν c` which are distinct and tend to `-∞` and `+∞` as `ν` tends to `-∞` and `+∞`.
Let `G` be an open set containing the vertical line through `c`. Then there are radii `a ν > 0` with
`closedBall c (a ν) ⊆ U ν` and an automorphism `g` of `E × ℝ`, analytic with analytic inverse,
such that the images `ψ ν = g '' (ball c (a ν)).graphOn (φ ν)` of the graphs over the balls
satisfy:

* `g` maps the complement of `G` into the strip `|t| < 1`;
* every `ψ ν` is bounded, and the `ψ ν` are pairwise disjoint;
* every bounded set `B ⊆ E` lies in the projection of `ψ ν` for all but finitely many `ν`;
* over every bounded set `B ⊆ E`, the heights of the points of `ψ ν` exceed any given `R` for all
  large `ν`, and lie below it for all small `ν`;
* the points of each `ψ ν` satisfy `dist p.2 q.2 ≤ 3 * dist p.1 q.1`;
* the closure of `ψ ν` lies in the image under `g` of the graph of `φ ν` over `U ν`, the rest of
  which `g` maps into the strip `|t| < 1`, so that `ψ ν ∩ {p | 1 ≤ |p.2|}` is closed. -/
theorem exists_straightening_graphOn {φ : ℤ → E → ℝ} {U : ℤ → Set E} {c : E}
    {G : Set (E × ℝ)} (hU : ∀ ν, U ν ∈ 𝓝 c)
    (hφ : ∀ ν, ∃ K, ∃ s ∈ 𝓝 c, LipschitzOnWith K (φ ν) s) (hinj : Injective fun ν ↦ φ ν c)
    (htop : Tendsto (fun ν ↦ φ ν c) atTop atTop) (hbot : Tendsto (fun ν ↦ φ ν c) atBot atBot)
    (hlf : LocallyFinite fun ν ↦ (U ν).graphOn (φ ν)) (hG : IsOpen G) (hcG : ∀ t, (c, t) ∈ G) :
    ∃ (a : ℤ → ℝ) (g : E × ℝ ≃ E × ℝ) (ψ : ℤ → Set (E × ℝ)),
      (∀ ν, 0 < a ν ∧ closedBall c (a ν) ⊆ U ν ∧ ψ ν = g '' (ball c (a ν)).graphOn (φ ν)) ∧
      (∀ p, AnalyticAt ℝ g p) ∧ (∀ p, AnalyticAt ℝ g.symm p) ∧ MapsTo g Gᶜ {p | |p.2| < 1} ∧
      (∀ ν, IsBounded (ψ ν)) ∧ Pairwise (Disjoint on ψ) ∧
      (∀ B : Set E, IsBounded B → ∀ᶠ ν in cofinite, B ⊆ Prod.fst '' ψ ν) ∧
      (∀ B : Set E, IsBounded B → ∀ R, (∀ᶠ ν in atTop, ∀ p ∈ ψ ν, p.1 ∈ B → R ≤ p.2) ∧
        ∀ᶠ ν in atBot, ∀ p ∈ ψ ν, p.1 ∈ B → p.2 ≤ R) ∧
      (∀ ν, ∀ p ∈ ψ ν, ∀ q ∈ ψ ν, dist p.2 q.2 ≤ 3 * dist p.1 q.1) ∧
      (∀ ν, closure (ψ ν) ⊆ g '' (U ν).graphOn (φ ν)) ∧
      (∀ ν, MapsTo g ((U ν).graphOn (φ ν) \ (ball c (a ν)).graphOn (φ ν)) {p | |p.2| < 1}) ∧
      ∀ ν, IsClosed (ψ ν ∩ {p | 1 ≤ |p.2|}) := by
  -- We first reduce to `c = 0` by a translation. We then choose the height intervals `Δ ν`
  -- (step 1), the radii `a ν` (step 2), the tube radius `γ` (step 3) and the scaling function `h`
  -- (step 4), and finally verify the conclusions for `g = heightCompression E ∘ baseScaling hh`.
  wlog hc : c = 0 generalizing φ U c G
  · -- Translate the base point `c` to the origin by `T (u, t) = (u + c, t)`.
    set T : E × ℝ ≃ E × ℝ := (Equiv.addRight c).prodCongr (Equiv.refl ℝ) with hT
    have hTa : ⇑T = fun p : E × ℝ ↦ (p.1 + c, p.2) := by
      ext p <;> simp [hT]
    have hTsa : ⇑T.symm = fun p : E × ℝ ↦ (p.1 - c, p.2) := by
      ext p <;> simp [hT, sub_eq_add_neg]
    have hgraph (ν : ℤ) (s : Set E) :
        ((· + c) ⁻¹' s).graphOn (fun u ↦ φ ν (u + c)) = T ⁻¹' s.graphOn (φ ν) := by
      ext ⟨u, t⟩
      simp [hTa]
    have hball (r : ℝ) : (· + c) ⁻¹' ball c r = ball (0 : E) r := by
      ext u
      simp [dist_eq_norm]
    have hnhds {s : Set E} (hs : s ∈ 𝓝 c) : (· + c) ⁻¹' s ∈ 𝓝 (0 : E) :=
      (continuous_add_const (m := c)).continuousAt.preimage_mem_nhds (by rwa [zero_add])
    obtain ⟨a, g, ψ, h₀, hg, hgs, hG', hb, hd, hcov, hht, hlip, hcl, hstrip, hclosed⟩ :=
      this (φ := fun ν u ↦ φ ν (u + c)) (U := fun ν ↦ (· + c) ⁻¹' U ν) (c := 0) (G := T ⁻¹' G)
        (fun ν ↦ hnhds (hU ν))
        (fun ν ↦ by
          obtain ⟨K, s, hs, hK⟩ := hφ ν
          exact ⟨K, _, hnhds hs, fun u hu v hv ↦ (hK hu hv).trans_eq (by rw [edist_add_right])⟩)
        (by simpa only [zero_add] using hinj) (by simpa only [zero_add] using htop)
        (by simpa only [zero_add] using hbot)
        (by simpa only [hgraph] using hlf.preimage_continuous (by rw [hTa]; fun_prop))
        (hG.preimage (by rw [hTa]; fun_prop)) (fun t ↦ by simpa [hTa] using hcG t) rfl
    have hψ (ν : ℤ) : ψ ν = (T.symm.trans g) '' (ball c (a ν)).graphOn (φ ν) := by
      rw [(h₀ ν).2.2, Equiv.coe_trans, image_comp, Equiv.image_symm_eq_preimage, ← hgraph, hball]
    refine ⟨a, T.symm.trans g, ψ, fun ν ↦ ⟨(h₀ ν).1, fun u hu ↦ ?_, hψ ν⟩,
      fun p ↦ (hg _).comp (by
        rw [hTsa]; exact (analyticAt_fst.sub analyticAt_const).prod analyticAt_snd),
      fun p ↦ (by rw [hTa]; exact (analyticAt_fst.add analyticAt_const).prod analyticAt_snd :
        AnalyticAt ℝ T _).comp (hgs p),
      fun p hp ↦ hG' (by rwa [mem_compl_iff, mem_preimage, Equiv.apply_symm_apply]), hb, hd, hcov,
      hht, hlip, fun ν ↦ ?_, fun ν p hp ↦ hstrip ν ?_, hclosed⟩
    · have hu' : u - c ∈ closedBall (0 : E) (a ν) := by
        rwa [mem_closedBall, dist_zero_right, ← dist_eq_norm]
      simpa using (h₀ ν).2.1 hu'
    · rw [Equiv.coe_trans, image_comp, Equiv.image_symm_eq_preimage, ← hgraph]
      exact hcl ν
    · rw [← hball, hgraph, hgraph, ← preimage_sdiff, mem_preimage, Equiv.apply_symm_apply]
      exact hp
  subst hc
  -- Step 1: disjoint compact height intervals `Δ ν` around the heights `φ ν 0`.
  obtain ⟨ε, hε, hΔdisj, hΔlf⟩ := exists_closedBall_pairwiseDisjoint_locallyFinite _ hinj htop hbot
  set Δ : ℤ → Set ℝ := fun ν ↦ closedBall (φ ν 0) (ε ν)
  have hΔbd {ν : ℤ} {t : ℝ} (ht : t ∈ Δ ν) : φ ν 0 - 1 ≤ t ∧ t ≤ φ ν 0 + 1 := by
    have := (abs_le.1 ((Real.dist_eq _ _).symm.trans_le ht))
    constructor <;> linarith [(hε ν).2]
  -- Step 2: radii `a ν ≤ 1` such that `φ ν` is `K ν`-Lipschitz on `closedBall 0 (a ν) ⊆ U ν`,
  -- with values in `Δ ν` there.
  have hrad (ν : ℤ) : ∃ K : ℝ≥0, ∃ a > 0, a ≤ 1 ∧ closedBall 0 a ⊆ U ν ∧
      LipschitzOnWith K (φ ν) (closedBall 0 a) ∧ MapsTo (φ ν) (closedBall 0 a) (Δ ν) := by
    obtain ⟨K, s, hs, hK⟩ := hφ ν
    obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hs (hU ν))
    have ha₀ : 0 < min (min r 1) (ε ν / (K + 1)) :=
      lt_min (lt_min hr one_pos) (div_pos (hε ν).1 (by positivity))
    have hsub : closedBall (0 : E) (min (min r 1) (ε ν / (K + 1))) ⊆ s ∩ U ν :=
      (closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_left _ _))).trans hrs
    refine ⟨K, min (min r 1) (ε ν / (K + 1)), ha₀,
      (min_le_left _ _).trans (min_le_right _ _), hsub.trans inter_subset_right,
      hK.mono (hsub.trans inter_subset_left), fun u hu ↦ ?_⟩
    have hu' : ‖u‖ ≤ ε ν / (K + 1) := (mem_closedBall_zero_iff.1 hu).trans (min_le_right _ _)
    calc dist (φ ν u) (φ ν 0) ≤ K * dist u 0 :=
          hK.dist_le_mul u (hsub hu).1 0 (hsub (mem_closedBall_self ha₀.le)).1
      _ ≤ K * (ε ν / (K + 1)) := by rw [dist_zero_right]; gcongr
      _ ≤ ε ν := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [(hε ν).1]
  choose K a ha ha1 haU haL haΔ using hrad
  -- Step 3: a tube `‖u‖ ≤ γ t` around the vertical axis, inside `G` and away from the parts of
  -- the graphs outside the balls `ball 0 (a ν)`.
  set D : ℤ → Set (E × ℝ) := fun ν ↦ (U ν \ ball 0 (a ν)).graphOn (φ ν)
  have hDlf : LocallyFinite D := hlf.subset fun ν ↦ image_mono sdiff_subset
  have hDaxis (t : ℝ) : ((0 : E), t) ∉ closure (⋃ ν, D ν) := by
    rw [hDlf.closure_iUnion, mem_iUnion, not_exists]
    intro ν h
    have : closure (D ν) ⊆ (ball (0 : E) (a ν))ᶜ ×ˢ univ :=
      closure_minimal (by rintro _ ⟨u, hu, rfl⟩; exact ⟨hu.2, mem_univ _⟩)
        (isOpen_ball.isClosed_compl.prod isClosed_univ)
    exact (this h).1 (mem_ball_self (ha ν))
  obtain ⟨γ, hγ, hγW⟩ := (hG.inter isClosed_closure.isOpen_compl).exists_tube_subset
    fun t ↦ ⟨hcG t, hDaxis t⟩
  have hfar {p : E × ℝ} (hp : p ∉ G ∩ (closure (⋃ ν, D ν))ᶜ) : γ p.2 ≤ ‖p.1‖ := by
    by_contra! h
    exact hp (hγW p.1 p.2 (by rw [dist_zero_right]; exact h.le))
  -- Step 4: the scaling function `h` and the automorphism `g = g₂ ∘ g₁`.
  set M : ℤ → ℝ := fun ν ↦ 2 * K ν + 2 * (|(ν : ℝ)| + 1) / a ν + 1 with hM
  obtain ⟨h, hha, hpos, hhγ, hhΔ⟩ := exists_analyticOnNhd_sqrt_sq_sub_one_lt_mul (Δ := Δ)
    (fun ν ↦ isCompact_closedBall _ _) (fun ν ↦ convex_closedBall _ _) hΔdisj hΔlf hγ M
    (L := fun ν ↦ (K ν + 1)⁻¹) fun ν ↦ by positivity
  have hh (t : ℝ) : h t ≠ 0 := (hpos t).ne'
  set g : E × ℝ ≃ E × ℝ := (baseScaling hh).trans (heightCompression E) with hg
  have hstrip : MapsTo g {p | γ p.2 ≤ ‖p.1‖} {p | |p.2| < 1} :=
    mapsTo_heightCompression_comp_baseScaling hh fun t _ ↦ by
      rw [abs_of_pos (hpos t)]; exact hhγ t
  have hga (p : E × ℝ) : AnalyticAt ℝ g p :=
    (analyticAt_heightCompression _).comp (analyticAt_baseScaling (hha _ (mem_univ _)))
  have hgsa (p : E × ℝ) : AnalyticAt ℝ g.symm p :=
    (analyticAt_baseScaling_symm (hha _ (mem_univ _))).comp (analyticAt_heightCompression_symm p)
  have hgsymm : Continuous g.symm := continuous_iff_continuousAt.2 fun p ↦ (hgsa p).continuousAt
  -- The pieces `S ν` of the graphs over the balls `ball 0 (a ν)`.
  set S : ℤ → Set (E × ℝ) := fun ν ↦ (ball 0 (a ν)).graphOn (φ ν)
  have hSΔ {ν : ℤ} {p : E × ℝ} (hp : p ∈ S ν) : ‖p.1‖ ≤ a ν ∧ p.2 ∈ Δ ν := by
    obtain ⟨u, hu, rfl⟩ := hp
    exact ⟨(mem_ball_zero_iff.1 hu).le, haΔ ν (ball_subset_closedBall hu)⟩
  have hMK (ν : ℤ) : 2 * K ν + 1 ≤ M ν := by
    have : 0 ≤ 2 * (|(ν : ℝ)| + 1) / a ν := by have := ha ν; positivity
    simp only [hM]; linarith
  have hL1 (ν : ℤ) : (((K ν + 1)⁻¹ : ℝ≥0) : ℝ) * K ν ≤ 1 := by
    push_cast
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith [(K ν).coe_nonneg]
  have hL1' (ν : ℤ) : (((K ν + 1)⁻¹ : ℝ≥0) : ℝ) ≤ 1 := by
    push_cast
    exact inv_le_one_of_one_le₀ (by linarith [(K ν).coe_nonneg])
  have hclosure (ν : ℤ) : closure (g '' S ν) ⊆ g '' (U ν).graphOn (φ ν) := by
    rw [g.image_eq_preimage_symm, g.image_eq_preimage_symm]
    refine (hgsymm.closure_preimage_subset _).trans (preimage_mono ?_)
    have hcl : closure (S ν) ⊆ closure (S ν) ∩ closedBall 0 (a ν) ×ˢ univ :=
      subset_inter subset_rfl (closure_minimal (fun p hp ↦ ⟨mem_closedBall_zero_iff.2 (hSΔ hp).1,
        mem_univ _⟩) (isClosed_closedBall.prod isClosed_univ))
    rw [(haL ν).continuousOn.closure_graphOn_inter ball_subset_closedBall
      (closure_ball 0 (ha ν).ne').ge] at hcl
    exact hcl.trans (image_mono (haU ν))
  have hdiff (ν : ℤ) : MapsTo g ((U ν).graphOn (φ ν) \ S ν) {p | |p.2| < 1} := by
    rintro _ ⟨⟨u, hu, rfl⟩, hnot⟩
    refine hstrip (hfar fun hW ↦ hW.2 (subset_closure (mem_iUnion.2 ⟨ν, u, ⟨hu, fun hb ↦ ?_⟩,
      rfl⟩)))
    exact hnot ⟨u, hb, rfl⟩
  refine ⟨a, g, fun ν ↦ g '' S ν, fun ν ↦ ⟨ha ν, haU ν, rfl⟩, hga, hgsa,
    fun p hp ↦ hstrip (hfar fun hW ↦ hp hW.1), ?_, ?_, ?_, ?_, ?_, hclosure, hdiff, ?_⟩
  · -- boundedness
    exact fun ν ↦ isBounded_image_heightCompression_comp_baseScaling hh (fun p hp ↦ (hSΔ hp).1)
      (fun p hp ↦ (hSΔ hp).2) (isCompact_closedBall _ _) (hha.continuousOn.mono (subset_univ _))
  · -- disjointness
    intro ν μ hνμ
    refine (disjoint_image_iff g.injective).2 (Disjoint.mono ?_ ?_ (disjoint_prod.2
      (Or.inr (hΔdisj hνμ)) : Disjoint (univ ×ˢ Δ ν) (univ ×ˢ Δ μ))) <;>
    exact fun p hp ↦ ⟨mem_univ _, (hSΔ hp).2⟩
  · -- every bounded set of the base lies under all but finitely many pieces
    intro B hB
    obtain ⟨R, hR⟩ := hB.subset_closedBall 0
    have hcof : ∀ᶠ ν : ℤ in cofinite, R ≤ |(ν : ℝ)| := by
      rw [Int.cofinite_eq, eventually_sup]
      constructor
      · filter_upwards [eventually_le_atBot ⌊-R⌋] with ν hν
        have := Int.cast_le.2 hν |>.trans (Int.floor_le (-R) : ((⌊-R⌋ : ℤ) : ℝ) ≤ -R)
        linarith [neg_abs_le (ν : ℝ)]
      · filter_upwards [eventually_ge_atTop ⌈R⌉] with ν hν
        exact (Int.le_ceil R).trans ((Int.cast_le.2 hν).trans (le_abs_self _))
    filter_upwards [hcof] with ν hν
    have hsub : closedBall (0 : E) (a ν / 2) ⊆ closedBall 0 (a ν) :=
      closedBall_subset_closedBall (half_le_self (ha ν).le)
    have hball := closedBall_subset_fst_image_baseScaling_image_graphOn (hh := hh)
      (D := Δ ν) (c := M ν) (L := (K ν + 1)⁻¹) ((haL ν).mono hsub) ((haΔ ν).mono_left hsub)
      (hhΔ ν).2 (fun t ht ↦ ((hhΔ ν).1 t ht).le.trans (le_abs_self _))
      (by linarith [hMK ν, (K ν).coe_nonneg]) (by
        calc (((K ν + 1)⁻¹ : ℝ≥0) : ℝ) * (a ν / 2) * K ν
            = (((K ν + 1)⁻¹ : ℝ≥0) : ℝ) * K ν * (a ν / 2) := by ring
          _ ≤ 1 * (a ν / 2) := mul_le_mul_of_nonneg_right (hL1 ν) (by linarith [ha ν])
          _ < M ν := by linarith [ha1 ν, hMK ν, (K ν).coe_nonneg])
    refine hR.trans ((closedBall_subset_closedBall ?_).trans (hball.trans ?_))
    · have hMa : a ν / 2 * M ν = a ν * K ν + (|(ν : ℝ)| + 1) + a ν / 2 := by
        have := (ha ν).ne'
        simp only [hM]
        field_simp
      have : 0 ≤ a ν * K ν := by have := ha ν; positivity
      linarith [ha ν]
    · rintro _ ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      have hu' : u ∈ ball (0 : E) (a ν) :=
        mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hu).trans_lt (half_lt_self (ha ν)))
      refine ⟨g (u, φ ν u), ⟨(u, φ ν u), ⟨u, hu', rfl⟩, rfl⟩, ?_⟩
      simp only [hg, Equiv.trans_apply, heightCompression_apply]
  · -- heights
    intro B hB R
    obtain ⟨R₀, hR₀⟩ := hB.subset_closedBall 0
    have hT {x : E} (hx : x ∈ B) :
        |√(1 + ‖x‖ ^ 2) * (sinh R / sinh 1)| ≤ √(1 + R₀ ^ 2) * |sinh R / sinh 1| := by
      have hx' := mem_closedBall_zero_iff.1 (hR₀ hx)
      rw [abs_mul, abs_of_nonneg (sqrt_nonneg _)]
      gcongr
    have hpt {ν : ℤ} {p : E × ℝ} (hp : p ∈ g '' S ν) :
        ∃ t ∈ Δ ν, p.2 = (heightCompression E (p.1, t)).2 := by
      obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨q.2, (hSΔ hq).2, ?_⟩
      simp only [hg, Equiv.trans_apply, baseScaling_apply, heightCompression_apply]
    constructor
    · filter_upwards [htop.eventually_ge_atTop (√(1 + R₀ ^ 2) * |sinh R / sinh 1| + 1)]
        with ν hν p hp hpB
      obtain ⟨t, ht, hpt⟩ := hpt hp
      rw [hpt]
      exact le_heightCompression_snd_iff.2
        ((le_abs_self _).trans ((hT hpB).trans (by linarith [(hΔbd ht).1])))
    · filter_upwards [hbot.eventually_le_atBot (-(√(1 + R₀ ^ 2) * |sinh R / sinh 1|) - 1)]
        with ν hν p hp hpB
      obtain ⟨t, ht, hpt⟩ := hpt hp
      rw [hpt]
      exact heightCompression_snd_le_iff.2 (by
        linarith [(hΔbd ht).2, neg_abs_le (√(1 + ‖p.1‖ ^ 2) * (sinh R / sinh 1)), hT hpB])
  · -- Lipschitz bound
    intro ν
    refine dist_snd_le_three_mul_dist_fst_of_mem_image_heightCompression_comp_baseScaling hh
      (D := Δ ν) (a := a ν) (k := K ν) (L := (K ν + 1)⁻¹) (fun p hp ↦ (hSΔ hp).1)
      (fun p hp ↦ (hSΔ hp).2) ?_ (hhΔ ν).2 (fun t ht ↦ ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      exact (haL ν).dist_le_mul u (ball_subset_closedBall hu) v (ball_subset_closedBall hv)
    · rw [abs_of_pos (hpos t)]
      linarith [hMK ν, (hhΔ ν).1 t ht]
    · nlinarith [hL1' ν, ha1 ν, ha ν, NNReal.coe_nonneg ((K ν + 1)⁻¹)]
  · -- closedness of the parts outside the strip
    intro ν
    refine isClosed_of_closure_subset fun p hp ↦ ?_
    have hp' := closure_inter_subset_inter_closure _ _ hp
    rw [(isClosed_le continuous_const continuous_snd.abs).closure_eq] at hp'
    obtain ⟨q, hq, rfl⟩ := hclosure ν hp'.1
    by_cases hqS : q ∈ S ν
    · exact ⟨mem_image_of_mem g hqS, hp'.2⟩
    · exact absurd hp'.2 (not_le.2 (hdiff ν ⟨hq, hqS⟩))

end Straightening

end TauCeti
