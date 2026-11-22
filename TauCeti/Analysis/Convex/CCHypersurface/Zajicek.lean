/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Analysis.Convex.CCHypersurface.Basic
public import TauCeti.Analysis.Convex.Subdifferential
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Convex.Function.Topology
import TauCeti.Analysis.Convex.MeasurableSubgradient
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Countable coverings and Zajíček's theorem for `c - c` hypersurfaces

In any separable real inner product space, every `c - c` hypersurface is covered by countably many
Lipschitz hypersurfaces (`TauCeti.IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface`),
and in finite dimensions Zajíček's theorem characterizes subsets of convex nondifferentiability loci
as sets covered by countably many `c - c` hypersurfaces
(`TauCeti.exists_convexOn_subset_not_differentiableAt_iff`). Along the way we establish countable
`c - c` coverings of multivalued subdifferential loci, convex nondifferentiability loci of
extended-real convex functions, and frontiers of convex sets.

## Main declarations

* `TauCeti.IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface` — countable Lipschitz
  covering of any `c - c` hypersurface in a separable space.
* `TauCeti.exists_isCCHypersurface_of_subdifferential_separation`,
  `TauCeti.exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential`,
  `TauCeti.exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal`,
  `Convex.exists_countable_isCCHypersurface_cover_frontier` — countable `c - c` coverings.
* `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_add_sub_two_mul_eq`,
  `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne`,
  `TauCeti.exists_convexOn_subset_not_differentiableAt_iff`,
  `TauCeti.exists_convexOn_subset_not_differentiableAt_iff_nat` — Zajíček's theorem.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Theorem 1.24.
-/

public section

noncomputable section

open Set MeasureTheory Metric Submodule
open scoped NNReal

namespace TauCeti

section LipschitzCover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace.SeparableSpace E]

/-- Every `c - c` hypersurface in a separable real inner product space is covered by countably many
Lipschitz hypersurfaces. -/
theorem IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface {s : Set E}
    (hs : IsCCHypersurface s) :
    ∃ t : ℕ → Set E, (∀ n, IsLipschitzHypersurface (t n)) ∧ s ⊆ ⋃ n, t n := by
  obtain ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩ := isCCHypersurface_def.1 hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hloc_f := (hf.locallyLipschitzOn_iff_continuousOn isOpen_univ).2 hfc.continuousOn
  have hloc_g := (hg.locallyLipschitzOn_iff_continuousOn isOpen_univ).2 hgc.continuousOn
  choose Kf Uf hUf hLf using fun y => hloc_f (mem_univ y)
  choose Kg Ug hUg hLg using fun y => hloc_g (mem_univ y)
  have hU_nhds (y : ↥(ℝ ∙ e)ᗮ) : Uf y ∩ Ug y ∈ nhds y := by
    rw [← nhdsWithin_univ]
    exact Filter.inter_mem (hUf y) (hUg y)
  choose h hhLip hhEq using fun y =>
    (((hLf y).mono inter_subset_left).sub ((hLg y).mono inter_subset_right)).extend_real
  obtain ⟨C, hC_count, hC_cov⟩ := TopologicalSpace.countable_cover_nhds hU_nhds
  have hC_ne : C.Nonempty := by
    by_contra hC0
    rw [not_nonempty_iff_eq_empty.1 hC0, biUnion_empty] at hC_cov
    exact absurd hC_cov empty_ne_univ
  obtain ⟨y, rfl⟩ := hC_count.exists_eq_range hC_ne
  refine ⟨fun n => {x | inner ℝ x e = h (y n) (P x)},
    fun n => isLipschitzHypersurface_def.2
      ⟨e, he, Kf (y n) + Kg (y n), h (y n), hhLip (y n), rfl⟩,
    fun x hx => ?_⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := mem_iUnion₂.1 (hC_cov.symm ▸ mem_univ (P x))
  exact mem_iUnion.2 ⟨n, by simpa [← hhEq (y n) hn] using hx⟩

end LipschitzCover

section SubdifferentialSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Single-slice subdifferential separation lies in a `c - c` hypersurface.** In any real inner
product space `E`, for any `u : E → EReal`, unit vector `e`, `a < b`, and `M : ℝ`, the set of
points `x` admitting subgradients `p, q ∈ ∂u(x)` of norm at most `M` with `⟪p, e⟫ ≤ a` and
`b ≤ ⟪q, e⟫` is contained in a single `c - c` hypersurface. -/
theorem exists_isCCHypersurface_of_subdifferential_separation {u : E → EReal} {e : E}
    (he : ‖e‖ = 1) {a b : ℝ} (hab : a < b) (M : ℝ) :
    ∃ s : Set E, IsCCHypersurface s ∧
      {x : E | ∃ p ∈ subdifferential (innerₗ E) u x, ∃ q ∈ subdifferential (innerₗ E) u x,
          ‖p‖ ≤ M ∧ ‖q‖ ≤ M ∧ inner ℝ p e ≤ a ∧ b ≤ inner ℝ q e} ⊆ s := by
  set S := {x : E | ∃ p ∈ subdifferential (innerₗ E) u x, ∃ q ∈ subdifferential (innerₗ E) u x,
      ‖p‖ ≤ M ∧ ‖q‖ ≤ M ∧ inner ℝ p e ≤ a ∧ b ≤ inner ℝ q e}
  choose α hα using fun x : S => let ⟨_, hp, _, hq, hpM, hqM, hpa, hbq⟩ := x.property
    exists_mem_subdifferential_inner_eq hp hq hpM hqM hpa (hab.le.trans hbq)
  choose β hβ using fun x : S => let ⟨_, hp, _, hq, hpM, hqM, hpa, hbq⟩ := x.property
    exists_mem_subdifferential_inner_eq hp hq hpM hqM (hpa.trans hab.le) hbq
  obtain ⟨Fa, hFa_conv, hFa_lip, hFa⟩ :=
    exists_convexOn_lipschitzWith_eq_toReal_sub_mul_inner he a α hα
  obtain ⟨Fb, hFb_conv, hFb_lip, hFb⟩ :=
    exists_convexOn_lipschitzWith_eq_toReal_sub_mul_inner he b β hβ
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨_, isCCHypersurface_def.2 ⟨e, he, (b - a)⁻¹ • Fa, (b - a)⁻¹ • Fb,
    hFa_lip.continuous.const_smul _, hFb_lip.continuous.const_smul _,
    hFa_conv.smul (inv_nonneg.2 hba.le), hFb_conv.smul (inv_nonneg.2 hba.le), rfl⟩, fun x hx => ?_⟩
  simp only [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, hFa ⟨x, hx⟩, hFb ⟨x, hx⟩]
  field_simp [hba.ne']
  ring

/-- **Subdifferential singular locus is covered by countably many `c - c` hypersurfaces.** For any
extended-real function `u : E → EReal` on a separable real inner product space, the set of points
`x` at which `∂u(x)` has more than one element is covered by a countable family of `c - c`
hypersurfaces. -/
theorem exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential
    [TopologicalSpace.SeparableSpace E] (u : E → EReal) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧
      {x : E | ¬ (subdifferential (innerₗ E) u x).Subsingleton} ⊆ ⋃₀ C := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense E
  have hDsub : {d : E | d ∈ D ∧ d ≠ 0} ⊆ D := fun _ h => h.1
  have : Countable {d : E // d ∈ D ∧ d ≠ 0} := (hD_count.mono hDsub).to_subtype
  let I := {t : {d : E // d ∈ D ∧ d ≠ 0} × ℚ × ℚ × ℕ | t.2.1 < t.2.2.1}
  have : Countable I := Subtype.countable
  choose s hs hsub using fun t : I => exists_isCCHypersurface_of_subdifferential_separation (u := u)
    (e := ‖(t.val.1 : E)‖⁻¹ • (t.val.1 : E))
    (by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 t.val.1.property.2)])
    (Rat.cast_lt.2 t.property) (t.val.2.2.2 : ℝ)
  refine ⟨range s, countable_range s, forall_mem_range.2 hs, fun x hx => ?_⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.1 hx
  obtain ⟨d, hd_in, hdD⟩ := hD_dense.inter_open_nonempty {w : E | inner ℝ (p - q) w ≠ 0}
    (isOpen_ne.preimage (by fun_prop)) ⟨p - q, by simp [sub_ne_zero.2 hpq]⟩
  have hd0 : d ≠ 0 := fun h0 => by simp [h0] at hd_in
  let d' : {d : E // d ∈ D ∧ d ≠ 0} := ⟨d, hdD, hd0⟩
  let e : E := ‖(d' : E)‖⁻¹ • (d' : E)
  have hstep {p' q' : E} (hp' : p' ∈ subdifferential (innerₗ E) u x)
      (hq' : q' ∈ subdifferential (innerₗ E) u x) (hlt : inner ℝ p' e < inner ℝ q' e) :
      x ∈ ⋃₀ range s := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max ‖p'‖ ‖q'‖)
    obtain ⟨r₁, hr₁, hr₂⟩ := exists_rat_btwn hlt
    obtain ⟨r₂, hr₃, hr₄⟩ := exists_rat_btwn hr₂
    exact mem_sUnion.2 ⟨s ⟨(d', r₁, r₂, M), Rat.cast_lt.1 hr₃⟩, mem_range_self _, hsub _
      ⟨p', hp', q', hq', (le_max_left _ _).trans hM, (le_max_right _ _).trans hM, hr₁.le, hr₄.le⟩⟩
  refine (lt_or_gt_of_ne (fun heq => hd_in ?_)).elim (hstep hp hq) (hstep hq hp)
  have : inner ℝ (p - q) e = 0 := by rw [inner_sub_left, heq, sub_self]
  simpa [e, d', real_inner_smul_right, inv_eq_zero, norm_eq_zero, hd0] using this

end SubdifferentialSeparation

section FiniteDimensionalCovers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For any extended-real function `u : E → EReal` with convex real epigraph, the set of interior
points of its effective domain at which `u.toReal` is not differentiable is covered by countably
many `c - c` hypersurfaces. -/
theorem exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal
    {u : E → EReal} (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧
      {x : E | x ∈ interior {z | u z ≠ ⊤} ∧ ¬ DifferentiableAt ℝ (fun z => (u z).toReal) x} ⊆
        ⋃₀ C :=
  let ⟨C, hC, hs, h⟩ := exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential u
  ⟨C, hC, hs, fun _ ⟨hx, hnd⟩ => h <| by
    rwa [mem_ofPred_eq, ← differentiableAt_toReal_iff_subsingleton_subdifferential hu hx]⟩

private theorem exists_countable_isCCHypersurface_cover_closure_of_not_nonempty_interior {K : Set E}
    (hK : Convex ℝ K) (hint : ¬ (interior K).Nonempty) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ closure K ⊆ ⋃₀ C := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, countable_empty, by simp, by simp⟩
  have hdir : (affineSpan ℝ K).direction ≠ ⊤ :=
    mt (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x₀, subset_affineSpan ℝ K hx₀⟩).1
      (mt hK.interior_nonempty_iff_affineSpan_eq_top.2 hint)
  obtain ⟨v, hv_mem, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.1 hdir)
  let e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by simp [e, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
  refine ⟨{{x | inner ℝ x e = inner ℝ x₀ e}}, countable_singleton _,
    by simpa using isCCHypersurface_setOf_inner_eq he _, ?_⟩
  simpa using closure_minimal (fun x hx => by
    rw [mem_ofPred_eq, ← sub_eq_zero, ← inner_sub_left]
    exact (Submodule.mem_orthogonal _ _).1 (Submodule.smul_mem _ _ hv_mem) _
      (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx) (subset_affineSpan ℝ K hx₀)))
    (isClosed_eq (by fun_prop) continuous_const)

/-- **Frontier of a convex set is covered by countably many `c - c` hypersurfaces.** For any convex
subset `K` of a finite-dimensional real inner product space `E`, `frontier K` (and hence also
`K \ interior K`) is covered by a countable family of `c - c` hypersurfaces. -/
theorem _root_.Convex.exists_countable_isCCHypersurface_cover_frontier {K : Set E}
    (hK : Convex ℝ K) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ frontier K ⊆ ⋃₀ C := by
  by_cases hint : (interior K).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hint
    let K₀ : Set E := (z₀ + ·) ⁻¹' K
    have hK₀ : Convex ℝ K₀ := hK.translate_preimage_right z₀
    have hnhds : K₀ ∈ nhds (0 : E) := (continuous_const.add continuous_id).continuousAt
      |>.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hz₀)
    have hgc : ConvexOn ℝ univ (gauge K₀) := ⟨convex_univ, fun _ _ _ _ _ _ ha hb _ =>
      (gauge_add_le hK₀ (absorbent_nhds_zero hnhds) _ _).trans_eq
        (by rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul])⟩
    let u : E → ℝ := fun z => max (gauge K₀ (z - z₀)) 1
    have hu : ConvexOn ℝ univ u := ConvexOn.sup
      (by simpa [Function.comp_def, sub_eq_add_neg] using hgc.translate_left (-z₀))
      (convexOn_const 1 convex_univ)
    obtain ⟨C, hC, hs, hsub⟩ :=
      exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal
        (u := fun z => (u z : EReal)) (by simpa using convexOn_iff_convex_epigraph_ite.1 hu)
    refine ⟨C, hC, hs, fun x hx => hsub ⟨by simp, ?_⟩⟩
    simp only [EReal.toReal_coe]
    have hg1 : gauge K₀ (x - z₀) = 1 := (gauge_eq_one_iff_mem_frontier hK₀ hnhds).2 <| by
      dsimp only [K₀]
      rw [← Homeomorph.coe_addLeft z₀, ← (Homeomorph.addLeft z₀).preimage_frontier]
      simpa [add_sub_cancel] using hx
    refine not_differentiableAt_of_add_sub_two_mul_ge (v := x - z₀) zero_lt_one zero_lt_one
      fun t ht => ?_
    have hmul (s : ℝ) (hs : 0 ≤ 1 + s) : gauge K₀ (x + s • (x - z₀) - z₀) = 1 + s := by
      have hvec : x + s • (x - z₀) - z₀ = (1 + s) • (x - z₀) := by rw [add_smul, one_smul]; abel
      rw [hvec, gauge_smul_of_nonneg hs, smul_eq_mul, hg1, mul_one]
    have hm : gauge K₀ (x - t • (x - z₀) - z₀) = 1 - t := by
      simpa only [sub_eq_add_neg, neg_smul] using hmul (-t) (by linarith [ht.2])
    simp only [u, hmul t (by linarith [ht.1]), hm, hg1,
      max_eq_left (by linarith [ht.1] : (1 : ℝ) ≤ 1 + t),
      max_eq_right (by linarith [ht.1] : 1 - t ≤ 1), max_self]
    linarith
  · exact let ⟨C, hC, hs, hcl⟩ :=
      exists_countable_isCCHypersurface_cover_closure_of_not_nonempty_interior hK hint
      ⟨C, hC, hs, frontier_subset_closure.trans hcl⟩

end FiniteDimensionalCovers

section Zajicek

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_lipschitz_branch_data {s : Set E} (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (e : E) (_ : ‖e‖ = 1) (Lf Lg : ℝ≥0) (f' g' : ↥(ℝ ∙ e)ᗮ → ℝ),
      ConvexOn ℝ univ f' ∧ ConvexOn ℝ univ g' ∧ LipschitzWith Lf f' ∧ LipschitzWith Lg g' ∧
      ConvexOn ℝ univ (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
        (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
      LipschitzWith (max Lf (Lg + 1)) (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
        (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
      ∀ x ∈ s ∩ closedBall 0 R, g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e =
        f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) := by
  obtain ⟨e, he, f, g, -, -, hf, hg, hs_eq⟩ := isCCHypersurface_def.1 hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Lf, f', hf', hLf', hff'⟩ := hf.exists_convexOn_lipschitzWith_eqOn isOpen_univ
    (isCompact_closedBall 0 (max R 0)) (subset_univ _)
  obtain ⟨Lg, g', hg', hLg', hgg'⟩ := hg.exists_convexOn_lipschitzWith_eqOn isOpen_univ
    (isCompact_closedBall 0 (max R 0)) (subset_univ _)
  have hlip_in : LipschitzWith 1 (fun x : E => inner ℝ x e) := LipschitzWith.mk_one fun _ _ => by
    rw [Real.dist_eq, ← inner_sub_left, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he, mul_one])
  refine ⟨e, he, Lf, Lg, f', g', hf', hg', hLf', hLg',
    (hf'.comp_linearMap P.toLinearMap).sup ((hg'.comp_linearMap P.toLinearMap).add
      ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => by simp [inner_add_left, real_inner_smul_left]⟩),
    ((hLf'.comp (Submodule.lipschitzWith_orthogonalProjectionOnto _)).weaken (by simp)).max
      (((hLg'.comp (Submodule.lipschitzWith_orthogonalProjectionOnto _)).weaken (by simp) :
        LipschitzWith Lg (fun x => g' (P x))).add hlip_in),
    fun x ⟨hxs, hxR⟩ => ?_⟩
  have hPx : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0) := mem_closedBall_zero_iff.2 <|
    (norm_orthogonalProjectionOnto_apply_le _ x).trans <|
      (mem_closedBall_zero_iff.1 hxR).trans (le_max_left R 0)
  rw [hs_eq, mem_ofPred_eq] at hxs
  rw [← hff' hPx, ← hgg' hPx, hxs]
  ring

/-- **Lipschitz convex potential with unit second-difference slope along a `c - c` hypersurface.**
Given a `c - c` hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a unit vector `e : E`, and
a `K`-Lipschitz convex `ψ : E → ℝ` with `ψ 0 = 0` and
`ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t` for every `x ∈ s ∩ closedBall 0 R` and `t ≥ 0`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_add_sub_two_mul_eq {s : Set E}
    (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (e : E) (_ : ‖e‖ = 1) (ψ : E → ℝ),
      ConvexOn ℝ univ ψ ∧ ψ 0 = 0 ∧ LipschitzWith K ψ ∧
      ∀ x ∈ s ∩ closedBall 0 R, ∀ t : ℝ, 0 ≤ t →
        ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t := by
  obtain ⟨e, he, Lf, Lg, f', g', -, -, -, -, hconv₀, hlip₀, heq_on⟩ :=
    exists_lipschitz_branch_data hs R
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  let ψ : E → ℝ := fun x => max (f' (P x)) (g' (P x) + inner ℝ x e) - max (f' 0) (g' 0)
  refine ⟨max Lf (Lg + 1), e, he, ψ, hconv₀.add_const (-max (f' 0) (g' 0)), by simp [ψ, P],
    (hlip₀.sub (.const _)).weaken (by simp), fun x hx t ht => ?_⟩
  have hin (s : ℝ) : inner ℝ (x + s • e) e = inner ℝ x e + s := by
    simp [inner_add_left, real_inner_smul_left, he]
  have hin_sub : inner ℝ (x - t • e) e = inner ℝ x e - t := by
    simpa [sub_eq_add_neg, neg_smul] using hin (-t)
  simp only [ψ, P, map_add, map_sub, map_smul,
    orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero, sub_zero, hin t, hin_sub]
  rw [← add_assoc, ← add_sub_assoc (g' _), heq_on x hx,
    max_eq_right (le_add_of_nonneg_right ht),
    max_eq_left (sub_le_self _ ht), max_self]
  ring

/-- **Borel measurable subgradient splitting along a `c - c` hypersurface.** Given a `c - c`
hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a `K`-Lipschitz convex `ψ : E → ℝ`, and
Borel measurable maps `T₁, T₂ : E → E` bounded by `K` that are subgradients of `ψ` everywhere and
satisfy `T₁ x ≠ T₂ x` at every `x ∈ s ∩ closedBall 0 R`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne
    [MeasurableSpace E] [BorelSpace E] {s : Set E} (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (ψ : E → ℝ) (T₁ T₂ : E → E),
      ConvexOn ℝ univ ψ ∧ LipschitzWith K ψ ∧ Measurable T₁ ∧ Measurable T₂ ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₁ x) ≤ ψ z) ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₂ x) ≤ ψ z) ∧
      (∀ x, ‖T₁ x‖ ≤ K) ∧ (∀ x, ‖T₂ x‖ ≤ K) ∧
      (∀ x ∈ s ∩ closedBall 0 R, T₁ x ≠ T₂ x) := by
  obtain ⟨e, he, Lf, Lg, f', g', hf', hg', hLf', hLg', hconv, hlip, heq_on⟩ :=
    exists_lipschitz_branch_data hs R
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Gf, hGf_meas, hGf⟩ := hf'.exists_measurable_forall_add_inner_le isOpen_univ
  obtain ⟨Gg, hGg_meas, hGg⟩ := hg'.exists_measurable_forall_add_inner_le isOpen_univ
  have hsub₁ (x z : E) (hx : g' (P x) + inner ℝ x e ≤ f' (P x)) :
      max (f' (P x)) (g' (P x) + inner ℝ x e) + inner ℝ (z - x) (Gf (P x) : E) ≤
        max (f' (P z)) (g' (P z) + inner ℝ z e) := by
    rw [max_eq_left hx, ← inner_orthogonalProjectionOnto_eq_of_mem_right, map_sub]
    exact (hGf (P x) (mem_univ _) (P z) (mem_univ _)).trans (le_max_left _ _)
  have hsub₂ (x z : E) (hx : f' (P x) ≤ g' (P x) + inner ℝ x e) :
      max (f' (P x)) (g' (P x) + inner ℝ x e) + inner ℝ (z - x) ((Gg (P x) : E) + e) ≤
        max (f' (P z)) (g' (P z) + inner ℝ z e) := by
    rw [max_eq_right hx, inner_add_right, ← inner_orthogonalProjectionOnto_eq_of_mem_right,
      map_sub, inner_sub_left z x e]
    linarith [(add_le_add_left (hGg (P x) (mem_univ _) (P z) (mem_univ _)) (inner ℝ z e)).trans
      (le_max_right (f' (P z)) _)]
  obtain ⟨T₁, T₂, hT₁m, hT₂m, hT₁, hT₂, hTeq⟩ := exists_measurable_piecewise_subgradient_max
    (hLf'.continuous.comp P.continuous) ((hLg'.continuous.comp P.continuous).add (by fun_prop))
    (measurable_subtypeVal.comp (hGf_meas.comp P.measurable))
    ((measurable_subtypeVal.comp (hGg_meas.comp P.measurable)).add measurable_const) hsub₁ hsub₂
  refine ⟨max Lf (Lg + 1), _, T₁, T₂, hconv, hlip, hT₁m, hT₂m, hT₁, hT₂,
    fun x => hlip.norm_le_of_forall_add_inner_le (hT₁ x),
    fun x => hlip.norm_le_of_forall_add_inner_le (hT₂ x), fun x hx hEq => ?_⟩
  obtain ⟨h₁, h₂⟩ := hTeq x (heq_on x hx).symm
  have hin₁ : inner ℝ (T₁ x) e = 0 :=
    h₁ ▸ Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Gf (P x)).property
  have hin₂ : inner ℝ (T₂ x) e = 1 := by
    simp [h₂, inner_add_left,
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Gg (P x)).property, he]
  linarith [congrArg (inner ℝ · e) hEq]

private theorem exists_convexOn_subset_not_differentiableAt_of_seq (s : ℕ → Set E)
    (hs : ∀ n, IsCCHypersurface (s n)) :
    ∃ u : E → ℝ, ConvexOn ℝ univ u ∧ (⋃ n, s n) ⊆ {x | ¬ DifferentiableAt ℝ u x} := by
  choose K e _ ψ hconv hψ0 hlip hcorner using fun m : ℕ =>
    (hs m.unpair.1).exists_convexOn_lipschitzWith_add_sub_two_mul_eq (m.unpair.2 : ℝ)
  let w : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 1) / ((K m : ℝ) + 1)
  have hw_pos (m : ℕ) : 0 < w m := by positivity
  have hKw : Summable fun m => w m * (K m : ℝ) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hw_pos m).le (K m).coe_nonneg)
      (fun m => by
        have hK1 : (K m : ℝ) + 1 ≠ 0 := by positivity
        calc w m * (K m : ℝ)
            ≤ w m * ((K m : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (hw_pos m).le
          _ = (1 / 2 : ℝ) ^ (m + 1) := by dsimp [w]; field_simp [hK1])
      ((summable_geometric_two.mul_left (1 / 2 : ℝ)).congr fun m => by ring)
  obtain ⟨hsum, hu_conv⟩ :=
    summable_and_convexOn_tsum_weighted (fun m => (hw_pos m).le) hKw hconv hψ0 hlip
  refine ⟨fun x => ∑' m, w m * ψ m x, hu_conv, fun x hx => ?_⟩
  obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
  obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
  let m₀ := Nat.pair n R
  have hm₀ : x ∈ s m₀.unpair.1 ∩ closedBall 0 (m₀.unpair.2 : ℝ) := by
    simpa only [m₀, Nat.unpair_pair] using ⟨hxn, mem_closedBall_zero_iff.2 hR⟩
  refine not_differentiableAt_of_add_sub_two_mul_ge (v := e m₀) (hw_pos m₀) zero_lt_one
    fun t ht => ?_
  have hs₁ := hsum (x + t • e m₀)
  have hs₂ := hsum (x - t • e m₀)
  have hs₃ := (hsum x).mul_left 2
  have htsum_eq :
      (∑' m, w m * ψ m (x + t • e m₀)) + (∑' m, w m * ψ m (x - t • e m₀)) -
        2 * (∑' m, w m * ψ m x) =
        ∑' m, w m * (ψ m (x + t • e m₀) + ψ m (x - t • e m₀) - 2 * ψ m x) := by
    rw [← Summable.tsum_add hs₁ hs₂, ← tsum_mul_left, ← Summable.tsum_sub (hs₁.add hs₂) hs₃]
    congr 1
    ext m
    ring
  have hm₀_eq : w m₀ * t = w m₀ * (ψ m₀ (x + t • e m₀) + ψ m₀ (x - t • e m₀) - 2 * ψ m₀ x) := by
    rw [hcorner m₀ x hm₀ t ht.1.le]
  have hs_diff : Summable fun m => w m * (ψ m (x + t • e m₀) + ψ m (x - t • e m₀) - 2 * ψ m x) :=
    ((hs₁.add hs₂).sub hs₃).congr fun m => by dsimp only [w]; ring
  rw [htsum_eq, hm₀_eq]
  refine Summable.le_tsum hs_diff m₀ fun m _ => mul_nonneg (hw_pos m).le ?_
  have hmid := (hconv m).2 (mem_univ (x + t • e m₀)) (mem_univ (x - t • e m₀))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hxmid : (1 / 2 : ℝ) • (x + t • e m₀) + (1 / 2 : ℝ) • (x - t • e m₀) = x := by
    rw [smul_add, smul_sub]
    module
  rw [hxmid] at hmid
  simp only [smul_eq_mul] at hmid
  linarith

/-- **Zajíček's theorem.** In a finite-dimensional real inner product space `E`, a subset `A ⊆ E`
is contained in the nondifferentiability locus of some convex `u : E → ℝ` iff `A` can be covered by
countably many `c - c` hypersurfaces. -/
theorem exists_convexOn_subset_not_differentiableAt_iff {A : Set E} :
    (∃ u : E → ℝ, ConvexOn ℝ univ u ∧ A ⊆ {x | ¬ DifferentiableAt ℝ u x}) ↔
      ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ A ⊆ ⋃₀ C := by
  refine ⟨fun ⟨u, hu, hA⟩ => ?_, fun ⟨C, hC, hs, hA⟩ => ?_⟩
  · obtain ⟨C, hC, hs, hsub⟩ :=
      exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal
        (u := fun z => (u z : EReal)) (by simpa using convexOn_iff_convex_epigraph_ite.1 hu)
    exact ⟨C, hC, hs, hA.trans fun x hx => hsub ⟨by simp, by simpa using hx⟩⟩
  · rcases C.eq_empty_or_nonempty with rfl | hCne
    · simp only [sUnion_empty, subset_empty_iff] at hA
      exact ⟨0, convexOn_const 0 convex_univ, hA ▸ empty_subset _⟩
    · obtain ⟨s, rfl⟩ := hC.exists_eq_range hCne
      exact let ⟨u, hu, hsub⟩ :=
        exists_convexOn_subset_not_differentiableAt_of_seq s (forall_mem_range.1 hs)
        ⟨u, hu, hA.trans (sUnion_range s ▸ hsub)⟩

/-- **Zajíček's theorem (`ℕ`-indexed sequence form).** In a nontrivial finite-dimensional real inner
product space `E`, a subset `A ⊆ E` is contained in the nondifferentiability locus of some convex
`u : E → ℝ` iff `A` is covered by a sequence `s : ℕ → Set E` of `c - c` hypersurfaces. -/
theorem exists_convexOn_subset_not_differentiableAt_iff_nat [Nontrivial E] {A : Set E} :
    (∃ u : E → ℝ, ConvexOn ℝ univ u ∧ A ⊆ {x | ¬ DifferentiableAt ℝ u x}) ↔
      ∃ s : ℕ → Set E, (∀ n, IsCCHypersurface (s n)) ∧ A ⊆ ⋃ n, s n := by
  rw [exists_convexOn_subset_not_differentiableAt_iff]
  refine ⟨fun ⟨C, hC, hs, hA⟩ => ?_, fun ⟨s, hs, hA⟩ =>
    ⟨range s, countable_range s, forall_mem_range.2 hs, sUnion_range s ▸ hA⟩⟩
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · obtain ⟨e, he⟩ := exists_norm_eq E (zero_le_one (α := ℝ))
    exact ⟨fun _ => {x | inner ℝ x e = 0},
      fun _ => isCCHypersurface_setOf_inner_eq he 0, hA.trans (by simp)⟩
  · obtain ⟨s, rfl⟩ := hC.exists_eq_range hCne
    exact ⟨s, forall_mem_range.1 hs, sUnion_range s ▸ hA⟩

end Zajicek

end TauCeti
