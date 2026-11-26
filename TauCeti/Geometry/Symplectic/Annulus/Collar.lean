/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Annulus.PoincareBirkhoffLift
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.ContDiff.Periodization
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.InverseFunctionTheorem.DomRestrict
import TauCeti.Analysis.Sobolev.Trace.Reflection.Seeley

/-!
# Collars of diffeomorphisms of the closed strip

A smooth diffeomorphism `f` of the closed annulus `(ℝ / ℤ) × [0, 1]` lifts to a map of the closed
strip `ℝ × [0, 1]` commuting with the deck translation `(x, y) ↦ (x + 1, y)`. Such a lift is only
defined, and only smooth, on the closed strip, while the inverse function theorem, flows and the
predicate `TauCeti.IsPoincareBirkhoffLift` work with diffeomorphisms between open subsets of the
plane. This file extends the lift across the two boundary lines to an open collar.

Let `f, g : ℝ × ℝ → ℝ × ℝ` map the closed strip `S = ℝ × [0, 1]` into itself and be mutually
inverse there, with `f` of class `Cⁿ` (`n ≥ 1`) and `g` differentiable on `S`, and let `f` commute
with the deck translation on `S`. Then there are `ε > 0` and an open partial homeomorphism `F` of
the plane with source the open band `ℝ × (-ε, 1 + ε)`, which agrees with `f` on `S`, whose inverse
agrees with `g` on `S`, which is `Cⁿ` with `Cⁿ` inverse, and which commutes with the deck
translation on its whole source
(`TauCeti.exists_openPartialHomeomorph_eqOn_univ_prod_Icc`).

The construction has three steps.

* *Extension.* Seeley's extension (`TauCeti.HalfSpaceExtension.exists_contDiff_eqOn_prod_Icc`)
  extends the displacement `f - id`, which has period one in `x` on `S`, to a `Cⁿ` map on the
  plane, and periodizing in `x` (`TauCeti.exists_contDiff_eqOn_prod_univ_of_periodic`) makes the
  extension periodic everywhere. So the extension `Φ = id + u` of `f` commutes with the deck
  translation on the whole plane.
* *Invertible differential.* Differentiating `g ∘ f = id` and `f ∘ g = id` within `S`, which has
  unique derivatives (`HasFDerivWithinAt.isInvertible_of_invOn`), shows that the differential of
  `Φ` is invertible at every point of `S`. Invertibility is an open condition, so it holds on a
  thickening of the compact square `[0, 1] × [0, 1]`, and by periodicity on a band
  `ℝ × (-ε, 1 + ε)`.
* *Injectivity.* By the inverse function theorem `Φ` is injective near each point of `S`, and it is
  injective on `S`; so it is injective on an open neighbourhood of a compact rectangle
  `[-R, R] × [0, 1]` (`Set.InjOn.exists_isOpen_superset`), hence on a thickening of it. Two points
  of a thin band with the same image, translated by the same integer so that the first one lies in
  `[0, 1] × [-1, 2]`, lie in that thickening, because `Φ` moves points a bounded distance. So `Φ`
  is injective on a band `ℝ × (-ε, 1 + ε)`. There `Φ` is an injective local diffeomorphism, hence
  an open partial homeomorphism with `Cⁿ` inverse.

For a diffeomorphism of the closed strip preserving a smooth positive density `ρ dx ∧ dy`,
preserving both boundary lines and twisting them in opposite directions, the collar extension is a
Poincaré–Birkhoff lift for `ρ` (`TauCeti.exists_isPoincareBirkhoffLift_eqOn_univ_prod_Icc`). So
the strict annulus fixed-point theorem, stated for Poincaré–Birkhoff lifts, applies to every
smooth area-preserving diffeomorphism of the closed annulus which preserves each boundary circle
and twists the two in opposite directions.

## Main results

* `TauCeti.exists_openPartialHomeomorph_eqOn_univ_prod_Icc`: the collar extension of a
  diffeomorphism of the closed strip commuting with the deck translation.
* `TauCeti.exists_isPoincareBirkhoffLift_eqOn_univ_prod_Icc`: the collar extension of a twist map
  of the closed strip preserving `ρ dx ∧ dy` is a Poincaré–Birkhoff lift.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace TauCeti

/-! ### Bands around the strip -/

/-- The bands `(-ε, 1 + ε)` around `[0, 1]` grow with `ε`. -/
private theorem Ioo_neg_subset_Ioo_neg {ε ε' : ℝ} (h : ε ≤ ε') :
    Ioo (-ε) (1 + ε) ⊆ Ioo (-ε') (1 + ε') :=
  Ioo_subset_Ioo (neg_le_neg h) (add_le_add_right h 1)

/-- The band `(-ε, 1 + ε)` contains `[0, 1]` for `ε > 0`. -/
private theorem Icc_zero_one_subset_Ioo_neg {ε : ℝ} (hε : 0 < ε) :
    Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) :=
  Icc_subset_Ioo (neg_lt_zero.2 hε) (lt_add_of_pos_right 1 hε)

/-- The band `(-min ε 1, 1 + min ε 1)` lies in `[-1, 2]`. -/
private theorem Ioo_neg_min_one_subset_Icc (ε : ℝ) :
    Ioo (-min ε 1) (1 + min ε 1) ⊆ Icc (-1 : ℝ) 2 := fun _ hy ↦
  ⟨by linarith [hy.1, min_le_right ε 1], by linarith [hy.2, min_le_right ε 1]⟩

/-- A point of `[a, b] × (-δ, 1 + δ)` lies in the `δ`-thickening of `[a, b] × [0, 1]`. -/
private theorem mem_thickening_Icc_prod_Icc {a b δ : ℝ} (hδ : 0 < δ) {q : ℝ × ℝ}
    (hq₁ : q.1 ∈ Icc a b) (hq₂ : q.2 ∈ Ioo (-δ) (1 + δ)) :
    q ∈ Metric.thickening δ (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  refine Metric.mem_thickening_iff.2 ⟨(q.1, max 0 (min q.2 1)),
    ⟨hq₁, le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, ?_⟩
  simp only [Prod.dist_eq, dist_self, Real.dist_eq]
  refine max_lt hδ (abs_sub_lt_iff.2 ⟨?_, ?_⟩) <;> simp only [max_def, min_def] <;> split_ifs <;>
    linarith [hq₂.1, hq₂.2]

/-- Translating `p` by `-⌊p.1⌋` in `x` moves its first coordinate into `[0, 1]`. -/
private theorem fst_add_neg_floor_mem (p : ℝ × ℝ) :
    (p + (((-⌊p.1⌋ : ℤ) : ℝ), 0)).1 ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · simp [← sub_eq_add_neg]
  · simpa [← sub_eq_add_neg] using (Int.fract_lt_one p.1).le

/-- Translating `p` by `-⌊p.1⌋` in `x` moves it into `[0, 1] × [-1, 2]` when `p.2 ∈ [-1, 2]`. -/
private theorem add_neg_floor_mem {p : ℝ × ℝ} (hp : p.2 ∈ Icc (-1 : ℝ) 2) :
    p + (((-⌊p.1⌋ : ℤ) : ℝ), 0) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 2 :=
  ⟨fst_add_neg_floor_mem p, by simpa using hp⟩

/-! ### A periodic extension of a lift -/

/-- A map `Cⁿ` on the strip `ℝ × [0, 1]` and commuting with the deck translation there agrees on
the strip with `p ↦ p + u p` for a `Cⁿ` map `u` of period one in `x` on the whole plane. -/
private theorem exists_contDiff_add_eqOn {n : ℕ∞} {f : ℝ × ℝ → ℝ × ℝ}
    (hf : ContDiffOn ℝ n f (univ ×ˢ Icc 0 1))
    (hdeck : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, f (p + (1, 0)) = f p + (1, 0)) :
    ∃ u : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ n u ∧ EqOn (fun p ↦ p + u p) f (univ ×ˢ Icc 0 1) ∧
      ∀ (p : ℝ × ℝ) (k : ℤ), u (p + ((k : ℝ), 0)) = u p := by
  -- Extend the displacement `f - id` across the boundary lines.
  obtain ⟨G, hG, hGf⟩ := HalfSpaceExtension.exists_contDiff_eqOn_prod_Icc (hf.sub contDiffOn_id)
  -- Periodize the extension in `x`, written as the second variable.
  obtain ⟨v, hv, hvG, hvper⟩ := exists_contDiff_eqOn_prod_univ_of_periodic
    (hG.comp (contDiff_snd.prodMk contDiff_fst)) (s := Icc (0 : ℝ) 1) fun y hy x ↦ by
      have hp : ((x, y) : ℝ × ℝ) ∈ univ ×ˢ Icc (0 : ℝ) 1 := ⟨mem_univ _, hy⟩
      have hp' : ((x + 1, y) : ℝ × ℝ) ∈ univ ×ˢ Icc (0 : ℝ) 1 := ⟨mem_univ _, hy⟩
      have h := hdeck _ hp
      simp only [Prod.mk_add_mk, add_zero] at h
      simp only [comp_apply, hGf hp, hGf hp', id, h]
      ext <;> simp
  refine ⟨fun p ↦ v (p.2, p.1), hv.comp (contDiff_snd.prodMk contDiff_fst), fun p hp ↦ ?_,
    fun p k ↦ ?_⟩
  · have h := hvG (mk_mem_prod hp.2 (mem_univ p.1))
    simp only [comp_apply, hGf hp, id] at h
    simp [h]
  · simpa using (hvper p.2).int_mul k p.1

/-! ### Uniform bands -/

section Band

variable {Φ : ℝ × ℝ → ℝ × ℝ}

/-- The differential of a map commuting with the deck translation is periodic. -/
private theorem fderiv_add_mk
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), Φ (p + ((k : ℝ), 0)) = Φ p + ((k : ℝ), 0)) (p : ℝ × ℝ)
    (k : ℤ) : fderiv ℝ Φ (p + ((k : ℝ), 0)) = fderiv ℝ Φ p := by
  rw [← fderiv_comp_add_right, funext fun q ↦ hper q k, fderiv_add_const]

/-- If a `C¹` map commuting with the deck translation has invertible differential on the strip,
it has invertible differential on a band `ℝ × (-ε, 1 + ε)`. -/
private theorem exists_band_isInvertible_fderiv (hΦ : ContDiff ℝ 1 Φ)
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), Φ (p + ((k : ℝ), 0)) = Φ p + ((k : ℝ), 0))
    (hinv : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ Φ p).IsInvertible) :
    ∃ ε > 0, ∀ p : ℝ × ℝ, p.2 ∈ Ioo (-ε) (1 + ε) → (fderiv ℝ Φ p).IsInvertible := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).exists_thickening_subset_open
    (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
      (hΦ.continuous_fderiv one_ne_zero)) fun p hp ↦ hinv p ⟨mem_univ _, hp.2⟩
  refine ⟨δ, hδ, fun p hp ↦ ?_⟩
  have h : (fderiv ℝ Φ (p + (((-⌊p.1⌋ : ℤ) : ℝ), 0))).IsInvertible :=
    hsub (mem_thickening_Icc_prod_Icc hδ (fst_add_neg_floor_mem p) (by simpa using hp))
  rwa [fderiv_add_mk hper] at h

/-- A continuous map commuting with the deck translation moves the points of the band
`ℝ × [-1, 2]` a bounded distance. -/
private theorem exists_norm_sub_le (hΦ : Continuous Φ)
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), Φ (p + ((k : ℝ), 0)) = Φ p + ((k : ℝ), 0)) :
    ∃ M, ∀ q : ℝ × ℝ, q.2 ∈ Icc (-1 : ℝ) 2 → ‖Φ q - q‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun q : ℝ × ℝ ↦ Φ q - q) (hΦ.sub continuous_id).continuousOn
  refine ⟨M, fun q hq ↦ ?_⟩
  have h := hM _ (add_neg_floor_mem hq)
  rwa [hper, add_sub_add_right_eq_sub] at h

/-- If a `C¹` map commuting with the deck translation is injective on the strip and has invertible
differential there, it is injective on a band `ℝ × (-ε, 1 + ε)`. -/
private theorem exists_band_injOn (hΦ : ContDiff ℝ 1 Φ)
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), Φ (p + ((k : ℝ), 0)) = Φ p + ((k : ℝ), 0))
    (hinv : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ Φ p).IsInvertible)
    (hinj : InjOn Φ (univ ×ˢ Icc 0 1)) :
    ∃ ε > 0, InjOn Φ (univ ×ˢ Ioo (-ε) (1 + ε)) := by
  obtain ⟨M, hMp⟩ := exists_norm_sub_le hΦ.continuous hper
  set K := Icc (-(2 + 2 * M)) (2 + 2 * M) ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  -- `Φ` is injective on an open neighbourhood `t` of `K`: near each point of the strip by the
  -- inverse function theorem, and on the strip itself.
  obtain ⟨t, ht, hKt, htinj⟩ :=
    (hinj.mono (prod_mono (subset_univ _) subset_rfl)).exists_isOpen_superset hK
      (fun _ _ ↦ hΦ.continuous.continuousAt) fun p hp ↦ by
      obtain ⟨e, he⟩ := hinv p ⟨mem_univ _, hp.2⟩
      have hs : HasStrictFDerivAt Φ (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) p := by
        rw [he]
        exact hΦ.contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero
      exact ⟨_, (hs.toOpenPartialHomeomorph Φ).open_source.mem_nhds
        hs.mem_toOpenPartialHomeomorph_source, by simpa using (hs.toOpenPartialHomeomorph Φ).injOn⟩
  obtain ⟨δ, hδ, hδt⟩ := hK.exists_thickening_subset_open ht hKt
  refine ⟨min δ 1, lt_min hδ one_pos, fun p hp q hq hpq ↦ ?_⟩
  have hp' := Ioo_neg_min_one_subset_Icc δ hp.2
  have hq' := Ioo_neg_min_one_subset_Icc δ hq.2
  -- Translate both points by the same integer, so that the first one lies in `[0, 1] × [-1, 2]`.
  set v : ℝ × ℝ := (((-⌊p.1⌋ : ℤ) : ℝ), 0)
  have hpK := add_neg_floor_mem hp'
  have hΦv : Φ (p + v) = Φ (q + v) := by rw [hper, hper, hpq]
  have h₁ := hMp (p + v) (by simpa [v] using hp')
  have h₂ := hMp (q + v) (by simpa [v] using hq')
  have hM : 0 ≤ M := (norm_nonneg _).trans h₁
  -- The second point stays within `2 + 2 * M` of the origin.
  have hqv : ‖q + v‖ ≤ 2 + 2 * M := by
    have hpv : ‖p + v‖ ≤ 2 := norm_prod_le_iff.2
      ⟨by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hpK.1.1, hpK.1.2],
        by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hpK.2.1, hpK.2.2]⟩
    calc ‖q + v‖ = ‖(p + v) + (Φ (p + v) - (p + v)) - (Φ (q + v) - (q + v))‖ := by
          rw [hΦv]; abel_nf
      _ ≤ ‖p + v‖ + ‖Φ (p + v) - (p + v)‖ + ‖Φ (q + v) - (q + v)‖ := norm_sub_le_of_le
          (norm_add_le _ _) le_rfl
      _ ≤ 2 + 2 * M := by linarith
  have hqv₁ := (norm_fst_le (q + v)).trans hqv
  rw [Real.norm_eq_abs, abs_le] at hqv₁
  have hpt : p + v ∈ t := hδt (mem_thickening_Icc_prod_Icc hδ
    ⟨by linarith [hpK.1.1], by linarith [hpK.1.2]⟩
    (by simpa [v] using Ioo_neg_subset_Ioo_neg (min_le_left δ 1) hp.2))
  have hqt : q + v ∈ t := hδt (mem_thickening_Icc_prod_Icc hδ hqv₁
    (by simpa [v] using Ioo_neg_subset_Ioo_neg (min_le_left δ 1) hq.2))
  exact add_right_cancel (htinj hpt hqt hΦv)

end Band

/-! ### The collar extension -/

/-- **Collar extension of a diffeomorphism of the closed strip.** Let `f` and `g` be mutually
inverse maps of the closed strip `ℝ × [0, 1]` into itself, with `f` of class `Cⁿ`, `n ≥ 1`, and
`g` differentiable on the strip, and let `f` commute with the deck translation
`(x, y) ↦ (x + 1, y)` on the strip. Then for some `ε > 0`, `f` extends to an open partial
homeomorphism `F` of the plane with source the band `ℝ × (-ε, 1 + ε)`, whose target contains the
strip, which is `Cⁿ` with `Cⁿ` inverse, whose inverse extends `g`, and which commutes with the deck
translation on its source. -/
theorem exists_openPartialHomeomorph_eqOn_univ_prod_Icc {n : ℕ∞} (hn : 1 ≤ n)
    {f g : ℝ × ℝ → ℝ × ℝ} (hf : ContDiffOn ℝ n f (univ ×ˢ Icc 0 1))
    (hg : DifferentiableOn ℝ g (univ ×ˢ Icc 0 1))
    (hfS : MapsTo f (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hgS : MapsTo g (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hinv : InvOn g f (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hdeck : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, f (p + (1, 0)) = f p + (1, 0)) :
    ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), ∃ ε > 0,
      F.source = univ ×ˢ Ioo (-ε) (1 + ε) ∧ univ ×ˢ Icc 0 1 ⊆ F.target ∧
      ContDiffOn ℝ n F F.source ∧ ContDiffOn ℝ n F.symm F.target ∧
      EqOn F f (univ ×ˢ Icc 0 1) ∧ EqOn F.symm g (univ ×ˢ Icc 0 1) ∧
      ∀ p ∈ F.source, F (p + (1, 0)) = F p + (1, 0) := by
  obtain ⟨u, hu, huf, huper⟩ := exists_contDiff_add_eqOn hf hdeck
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p ↦ p + u p with hΦdef
  have hΦ : ContDiff ℝ n Φ := contDiff_id.add hu
  have hΦ₁ : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast hn)
  have hper : ∀ (p : ℝ × ℝ) (k : ℤ), Φ (p + ((k : ℝ), 0)) = Φ p + ((k : ℝ), 0) := fun p k ↦ by
    simp only [hΦdef, huper]
    abel
  have hU : UniqueDiffOn ℝ (univ ×ˢ Icc (0 : ℝ) 1) :=
    (uniqueDiffOn_univ (E := ℝ)).prod uniqueDiffOn_Icc_zero_one
  have hinvS : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ Φ p).IsInvertible := fun p hp ↦
    ((hΦ₁.differentiable one_ne_zero p).hasFDerivAt.hasFDerivWithinAt.congr huf.symm
      (huf hp).symm).isInvertible_of_invOn (hg _ (hfS hp)).hasFDerivWithinAt hfS hgS hinv
      (hU p hp) (hU _ (hfS hp)) hp
  obtain ⟨ε₁, hε₁, hband₁⟩ := exists_band_isInvertible_fderiv hΦ₁ hper hinvS
  obtain ⟨ε₂, hε₂, hband₂⟩ :=
    exists_band_injOn hΦ₁ hper hinvS (hinv.1.injOn.congr huf.symm)
  set ε := min ε₁ ε₂
  set B : Set (ℝ × ℝ) := univ ×ˢ Ioo (-ε) (1 + ε)
  have hB : IsOpen B := isOpen_univ.prod isOpen_Ioo
  have hB₁ : B ⊆ univ ×ˢ Ioo (-ε₁) (1 + ε₁) :=
    prod_mono subset_rfl (Ioo_neg_subset_Ioo_neg (min_le_left ε₁ ε₂))
  have hB₂ : B ⊆ univ ×ˢ Ioo (-ε₂) (1 + ε₂) :=
    prod_mono subset_rfl (Ioo_neg_subset_Ioo_neg (min_le_right ε₁ ε₂))
  have hSB : univ ×ˢ Icc (0 : ℝ) 1 ⊆ B :=
    prod_mono subset_rfl (Icc_zero_one_subset_Ioo_neg (lt_min hε₁ hε₂))
  have hinvB : ∀ p ∈ B, (fderiv ℝ Φ p).IsInvertible := fun p hp ↦ hband₁ p (hB₁ hp).2
  let F := OpenPartialHomeomorph.ofContinuousOpenRestrict ((hband₂.mono hB₂).toPartialEquiv Φ B)
    hΦ.continuous.continuousOn (isOpenMap_domRestrict_of_hasStrictFDerivAt_of_isInvertible hB
      (fun p _ ↦ hΦ₁.contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero) hinvB) hB
  have hFsource : F.source = B := by simp [F]
  have hFcoe : ⇑F = Φ := by simp [F]
  refine ⟨F, ε, lt_min hε₁ hε₂, hFsource, fun q hq ↦ ?_, hΦ.contDiffOn, ?_, huf,
    fun q hq ↦ ?_, fun p _ ↦ by rw [hFcoe]; simpa using hper p 1⟩
  · have h := F.map_source (hFsource ▸ hSB (hgS hq))
    rwa [hFcoe, huf (hgS hq), hinv.2 hq] at h
  · exact F.contDiffOn_symm_of_isInvertible_fderiv hΦ.contDiffOn hinvB
  · have h := F.left_inv (hFsource ▸ hSB (hgS hq))
    rwa [hFcoe, huf (hgS hq), hinv.2 hq] at h

/-- **Closed-strip twist maps are Poincaré–Birkhoff lifts.** Let `f` and `g` be mutually inverse
maps of the closed strip `ℝ × [0, 1]` into itself, with `f` smooth and `g` differentiable on the
strip, such that `f` commutes with the deck translation on the strip, preserves the area form
`ρ dx ∧ dy` of a smooth positive density `ρ` of period one in `x`, in the sense
`ρ(f p) det Df_p = ρ(p)` for the derivative `Df_p` within the strip, and preserves both boundary
lines, moving the lower one strictly to the left and the upper one strictly to the right. Then the
collar extension of `f` is a Poincaré–Birkhoff lift for `ρ` which agrees with `f` on the strip
and whose inverse agrees with `g` there. -/
theorem exists_isPoincareBirkhoffLift_eqOn_univ_prod_Icc {ρ : ℝ × ℝ → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (univ ×ˢ Icc 0 1)) (hρpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y))
    (hρper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    {f g : ℝ × ℝ → ℝ × ℝ} (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Icc 0 1))
    (hg : DifferentiableOn ℝ g (univ ×ˢ Icc 0 1))
    (hfS : MapsTo f (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hgS : MapsTo g (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hinv : InvOn g f (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hdeck : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, f (p + (1, 0)) = f p + (1, 0))
    (hdet : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ρ (f p) * (fderivWithin ℝ f (univ ×ˢ Icc 0 1) p).det = ρ p)
    (h₀ : ∀ x, (f (x, 0)).2 = 0) (h₀lt : ∀ x, (f (x, 0)).1 < x)
    (h₁ : ∀ x, (f (x, 1)).2 = 1) (h₁lt : ∀ x, x < (f (x, 1)).1) :
    ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), IsPoincareBirkhoffLift ρ F ∧
      EqOn F f (univ ×ˢ Icc 0 1) ∧ EqOn F.symm g (univ ×ˢ Icc 0 1) := by
  obtain ⟨F, ε, hε, hsrc, htgt, hFc, hFsc, hFf, hFg, hFdeck⟩ :=
    exists_openPartialHomeomorph_eqOn_univ_prod_Icc le_top hf hg hfS hgS hinv hdeck
  have hSsrc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ F.source :=
    hsrc ▸ prod_mono subset_rfl (Icc_zero_one_subset_Ioo_neg hε)
  have hmem (x : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : ((x, y) : ℝ × ℝ) ∈ univ ×ˢ Icc (0 : ℝ) 1 :=
    ⟨mem_univ x, hy⟩
  -- On the strip, the derivative of `F` is the derivative of `f` within the strip.
  have hderiv : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
      fderiv ℝ F p = fderivWithin ℝ f (univ ×ˢ Icc 0 1) p := fun p hp ↦ by
    have hd : DifferentiableAt ℝ F p :=
      (hFc.contDiffAt (F.open_source.mem_nhds (hSsrc hp))).differentiableAt (by simp)
    exact (hd.hasFDerivAt.hasFDerivWithinAt.congr hFf.symm (hFf hp).symm).fderivWithin
      (((uniqueDiffOn_univ (E := ℝ)).prod uniqueDiffOn_Icc_zero_one) p hp) |>.symm
  refine ⟨F, ⟨hρ, hρpos, hρper, hSsrc, htgt, hFc, hFsc, fun p hp ↦ hFf hp ▸ hfS hp,
    fun q hq ↦ hFg hq ▸ hgS hq, fun p hp ↦ hFdeck p (hSsrc hp), fun p hp ↦ ?_, fun x ↦ ?_,
    fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩, hFf, hFg⟩
  · rw [hderiv p hp, hFf hp, hdet p hp]
  · rw [hFf (hmem x (left_mem_Icc.2 zero_le_one)), h₀ x]
  · rw [hFf (hmem x (left_mem_Icc.2 zero_le_one))]
    exact h₀lt x
  · rw [hFf (hmem x (right_mem_Icc.2 zero_le_one)), h₁ x]
  · rw [hFf (hmem x (right_mem_Icc.2 zero_le_one))]
    exact h₁lt x

end TauCeti
