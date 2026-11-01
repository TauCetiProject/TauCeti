/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.Projection
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Trans
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Smooth arcs in dimension at least four are unknotted

Let `V` be a real normed space of dimension at least four, and let `γ : ℝ → V` be an injective
`C^n` immersion, `2 ≤ n ≤ ∞`, which agrees with the affine line `s ↦ p + s • e` outside a compact
set. Then `γ` is smoothly isotopic to that line, through injective immersions which all agree with
the line outside a fixed compact set (`TauCeti.exists_smoothIsotopy_line_of_four_le_finrank`).
Arcs cannot be knotted in dimension four and higher.

The isotopy is the concatenation of two explicit straight-line motions.

* **Projection.** Since `2 · 1 + 1 < dim V`, some direction `d` is neither on a secant line
  `ℝ • (γ s - γ s')` nor on a tangent line `ℝ • γ' s` of the arc
  (`ContDiff.exists_forall_smul_sub_ne_and_fderiv_ne`); the line direction `e` is a tangent
  vector of `γ`, so `d` and `e` are independent. Pick a linear form `φ` with `φ d = 1` and
  `φ e = 0`. The motion `γ - u • φ (γ - p) • d`, `u ∈ [0, 1]`, ends at the projection `π γ` of the
  arc to the hyperplane `p + ker φ` along `d`. Every stage is injective, because `γ s - γ s'` is
  never a multiple of `d`, and an immersion, because `γ' s` never is; the line is fixed throughout.
* **Straightening above the hyperplane.** Let `k` be a smooth function which is the identity on
  `[-L, L]` and vanishes outside `[-L - 1, L + 1]`. The motion
  `p + (1 - u) • (π γ - p) + (u * s) • e + (4 * u * (1 - u) * k s) • d` joins `π γ` to the line.
  The `φ`-coordinate `4 u (1 - u) k s` separates the parameters in `[-L, L]` at intermediate times,
  and for `L` large the hyperplane component keeps the parameters outside `[-L, L]` away from the
  others. The `φ`-coordinate `4 u (1 - u) k' s` of the velocity is nonzero on `(-L, L)` at
  intermediate times, and where the arc is the line the velocity is `e` plus a multiple of `d`.

The projection step is Whitney's projection argument (Hirsch, Chapter 1, §3). By the isotopy
extension theorem (`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`), the isotopy is realized on
every compact part of the line by a compactly supported ambient diffeotopy; this is how an arc in a
manifold of dimension at least four, read in a chart, is moved onto a straight arc. In dimension
three the theorem fails: an arc with a knot tied in a compact region is not isotopic to a straight
line by an isotopy fixed near infinity.

## Main results

* `TauCeti.exists_smoothIsotopy_line_of_four_le_finrank`: an injective `C^n` immersion of the
  line in a real normed space of dimension at least four, agreeing with an affine line outside a
  compact set, is smoothly isotopic to it by an isotopy fixed outside a compact set.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 1, §3 (projections of embeddings).
* H. Whitney, *Differentiable manifolds*, Ann. of Math. 37 (1936), 645–680.
-/

public section

noncomputable section

namespace TauCeti

open Function Module Set Topology Filter Manifold
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- An injective `C^n` immersion of the line, `1 ≤ n`, which is an affine line outside a compact
set, is a smooth embedding: it is proper, hence a closed embedding. -/
private theorem isSmoothEmbedding_of_eq_line {n : ℕ∞ω} (hn : 1 ≤ n) {f : ℝ → V}
    (hf : ContDiff ℝ n f) (hinj : Injective f) {f' : ℝ → V} (hder : ∀ s, HasDerivAt f (f' s) s)
    (hf' : ∀ s, f' s ≠ 0) {p e : V} (he : e ≠ 0) {R : ℝ}
    (hline : ∀ s, R ≤ |s| → f s = p + s • e) :
    IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, V) n f := by
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun s => ?_, ?_⟩
  · refine (hf.contDiffOn.isImmersionAt_iff_injective_fderiv isOpen_univ (mem_univ s) hn).2 ?_
    rw [(hder s).hasFDerivAt.fderiv]
    intro a b hab
    exact smul_left_injective ℝ (hf' s) (by simpa using hab)
  · have hproper : IsProperMap f := by
      rw [isProperMap_iff_isCompact_preimage]
      refine ⟨hf.continuous, fun K hK => ?_⟩
      obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
      refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage hf.continuous) ?_
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨max R ((C + ‖p‖) / ‖e‖), fun s hs => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      by_contra! hlt
      have hfs : ‖p + s • e‖ ≤ C := hline s ((le_max_left _ _).trans hlt.le) ▸ hC _ hs
      have hse : ‖s • e‖ ≤ ‖p + s • e‖ + ‖p‖ := by
        simpa using norm_sub_le (p + s • e) p
      rw [norm_smul, Real.norm_eq_abs] at hse
      have := (div_lt_iff₀ (norm_pos_iff.2 he)).1 ((le_max_right _ _).trans_lt hlt)
      linarith
    exact (IsClosedEmbedding.of_continuous_injective_isClosedMap hf.continuous hinj
      hproper.isClosedMap).isEmbedding

/-- The smooth isotopy given by a `C^n` map on `ℝ × ℝ`, read on `[0, 1] × ℝ`, whose time slices
in `[0, 1]` are smooth embeddings. -/
private def isotopyOfContDiff {n : ℕ∞ω} {f₀ f₁ : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯} (G : ℝ × ℝ → V)
    (hG : ContDiff ℝ n G) (h₀ : ∀ s, G (0, s) = f₀ s) (h₁ : ∀ s, G (1, s) = f₁ s)
    (hemb : ∀ u ∈ Icc (0 : ℝ) 1, IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, V) n fun s => G (u, s)) :
    SmoothIsotopy f₀ f₁ where
  toContMDiffMap := ⟨fun q => G ((q.1 : ℝ), q.2),
    (contMDiff_prod_modelWithCornersSelf_iff.2 hG.contMDiff).comp
      ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd)⟩
  map_zero_left s := by simpa using h₀ s
  map_one_left s := by simpa using h₁ s
  isSmoothEmbedding t := hemb t t.2

omit [FiniteDimensional ℝ V] in
/-- A map which is the affine line `s ↦ p + s • e` for `|s| ≥ R` has velocity `e` for `|s| > R`. -/
private theorem hasDerivAt_of_eq_line {f : ℝ → V} {p e : V} {R : ℝ}
    (hline : ∀ s, R ≤ |s| → f s = p + s • e) {s : ℝ} (hs : R < |s|) : HasDerivAt f e s := by
  have hl : HasDerivAt (fun s : ℝ => p + s • e) e s := by
    simpa using ((hasDerivAt_id s).smul_const e).const_add p
  refine hl.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with x hx
  exact hline x hx.le

/-- **The projection motion.** If `d` is on no secant line and no tangent line of the arc `γ`, and
`φ d = 1`, then `u ↦ γ - u • φ (γ - p) • d` is a smooth isotopy from `γ` to its projection `g`
along `d` onto the hyperplane `p + ker φ`. It fixes the parameters where `φ (γ s - p) = 0`. -/
private theorem exists_smoothIsotopy_projection {n : ℕ∞ω} (hn : 1 ≤ n)
    (γ g : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯) {p d e : V} (he : e ≠ 0) {φ : V →L[ℝ] ℝ}
    (hg : ∀ s, g s = γ s - φ (γ s - p) • d) (hsec : ∀ s s' (c : ℝ), γ s - γ s' = c • d → s = s')
    (htan : ∀ s (c : ℝ), deriv γ s ≠ c • d) {R : ℝ} (hline : ∀ s, R ≤ |s| → γ s = p + s • e)
    (hφline : ∀ s, R ≤ |s| → φ (γ s - p) = 0) :
    ∃ F : SmoothIsotopy γ g, ∀ (t : unitInterval) (s : ℝ), R ≤ |s| → F (t, s) = γ s := by
  have hγ : ContDiff ℝ n γ := contMDiff_iff_contDiff.1 γ.contMDiff
  have hγd : ∀ s, HasDerivAt γ (deriv γ s) s := fun s =>
    (hγ.differentiable (zero_lt_one.trans_le hn).ne' s).hasDerivAt
  let A : ℝ × ℝ → V := fun q => γ q.2 - (q.1 * φ (γ q.2 - p)) • d
  have hA : ContDiff ℝ n A := (hγ.comp contDiff_snd).sub ((contDiff_fst.mul
    (φ.contDiff.comp ((hγ.comp contDiff_snd).sub contDiff_const))).smul contDiff_const)
  have hAline : ∀ u s, R ≤ |s| → A (u, s) = γ s := by
    intro u s hs
    simp only [A]
    rw [hφline s hs, mul_zero, zero_smul, sub_zero]
  have hAemb : ∀ u ∈ Icc (0 : ℝ) 1, IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, V) n fun s => A (u, s) := by
    intro u _
    refine isSmoothEmbedding_of_eq_line hn (hA.comp (contDiff_const.prodMk contDiff_id))
      (fun s s' h => hsec s s' (u * φ (γ s - p) - u * φ (γ s' - p)) ?_)
      (f' := fun s => deriv γ s - (u * φ (deriv γ s)) • d) (fun s => ?_) (fun s h => ?_) he
      (fun s hs => (hAline u s hs).trans (hline s hs))
    · calc γ s - γ s' = A (u, s) - A (u, s') +
            (u * φ (γ s - p) - u * φ (γ s' - p)) • d := by
            simp only [A, sub_smul]
            abel
        _ = _ := by rw [h, sub_self, zero_add]
    · have h1 : HasDerivAt (fun s => φ (γ s - p)) (φ (deriv γ s)) s :=
        φ.hasFDerivAt.comp_hasDerivAt s ((hγd s).sub_const p)
      exact (hγd s).sub ((h1.const_mul u).smul_const d)
    · exact htan s _ (sub_eq_zero.1 h)
  exact ⟨isotopyOfContDiff A hA (fun s => by simp [A]) (fun s => by simp [A, hg]) hAemb,
    fun t s hs => hAline _ s hs⟩

/-- **Straightening an arc in a hyperplane.** Let `φ d = 1` and `φ e = 0`, and let `g` be an
injective `C^n` immersion of the line into the hyperplane `p + ker φ` which is the line `ℓ` for
`|s| ≥ R`. Then `g` is smoothly isotopic to `ℓ`, by
`p + (1 - u) • (g - p) + (u * s) • e + (4 * u * (1 - u) * k s) • d` with `k` a cutoff of the
identity, and the isotopy agrees with `ℓ` for `|s| ≥ R'`. -/
private theorem exists_smoothIsotopy_line_of_map_sub_eq_zero {n : ℕ∞ω} (hn₁ : 1 ≤ n)
    (hn : n ≤ ∞) (g ℓ : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯) {p d e : V} (hℓ : ∀ s, ℓ s = p + s • e)
    (he : e ≠ 0) {φ : V →L[ℝ] ℝ} (hφd : φ d = 1) (hφe : φ e = 0) (hinj : Injective g)
    (hg' : ∀ s, deriv g s ≠ 0) (hφg : ∀ s, φ (g s - p) = 0) {R : ℝ}
    (hline : ∀ s, R ≤ |s| → g s = p + s • e) :
    ∃ (F : SmoothIsotopy g ℓ) (R' : ℝ),
      ∀ (t : unitInterval) (s : ℝ), R' ≤ |s| → F (t, s) = ℓ s := by
  have hgc : ContDiff ℝ n g := contMDiff_iff_contDiff.1 g.contMDiff
  have hgd : ∀ s, HasDerivAt g (deriv g s) s := fun s =>
    (hgc.differentiable (zero_lt_one.trans_le hn₁).ne' s).hasDerivAt
  have hφg' : ∀ s, φ (deriv g s) = 0 := fun s =>
    (φ.hasFDerivAt.comp_hasDerivAt s ((hgd s).sub_const p)).unique
      ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq (Eventually.of_forall hφg))
  /- The constants: `‖g s - p‖ ≤ C` for `|s| ≤ R`, and `R < L` with `C ≤ L * ‖e‖`. -/
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hgc.continuous.sub continuous_const).continuousOn (s := Icc (-R) R))
  set L := max (max R 1) (C / ‖e‖) + 1 with hL
  have hL0 : 0 < L := by
    have := le_max_right R 1
    have := le_max_left (max R 1) (C / ‖e‖)
    linarith
  have hRL : R < L := by
    have := le_max_left R 1
    have := le_max_left (max R 1) (C / ‖e‖)
    linarith
  have hCL : C ≤ L * ‖e‖ := by
    have h1 : C / ‖e‖ ≤ L := by
      have := le_max_right (max R 1) (C / ‖e‖)
      linarith
    exact (div_le_iff₀ (norm_pos_iff.2 he)).1 h1
  /- The cutoff `k` of the identity: `k s = s` for `|s| ≤ L` and `k s = 0` for `|s| ≥ L + 1`. -/
  let χ : ContDiffBump (0 : ℝ) := ⟨L, L + 1, hL0, by linarith⟩
  let k : ℝ → ℝ := fun s => χ s * s
  have hk : ContDiff ℝ n k := (χ.contDiff.mul contDiff_id).of_le hn
  have hksmall : ∀ s, |s| ≤ L → k s = s := by
    intro s hs
    have : χ s = 1 := χ.one_of_mem_closedBall (by simpa [Real.dist_eq] using hs)
    simp [k, this]
  have hkbig : ∀ s, L + 1 ≤ |s| → k s = 0 := by
    intro s hs
    have : χ s = 0 := χ.zero_of_le_dist (by simpa [Real.dist_eq] using hs)
    simp [k, this]
  have hkd : ∀ s, |s| < L → HasDerivAt k 1 s := by
    intro s hs
    refine (hasDerivAt_id s).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hs] with x hx
    exact hksmall x hx.le
  /- The hyperplane component `H` of the motion. -/
  let H : ℝ → ℝ → V := fun u s => (1 - u) • (g s - p) + (u * s) • e
  have hφH : ∀ u s, φ (H u s) = 0 := by
    intro u s
    simp [H, hφg, hφe]
  have hHbig : ∀ u s, R ≤ |s| → H u s = s • e := by
    intro u s hs
    simp only [H]
    rw [hline s hs, add_sub_cancel_left, smul_smul, ← add_smul]
    congr 1
    ring
  have hHsmall : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s, |s| ≤ L → ‖H u s‖ ≤ L * ‖e‖ := by
    intro u hu s hs
    by_cases hRs : R ≤ |s|
    · rw [hHbig u s hRs, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg e)
    · have hsR : s ∈ Icc (-R) R := abs_le.1 (not_le.1 hRs).le
      have h1 : ‖(1 - u) • (g s - p)‖ ≤ (1 - u) * (L * ‖e‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2])]
        exact mul_le_mul_of_nonneg_left ((hC s hsR).trans hCL) (by linarith [hu.2])
      have h2 : ‖(u * s) • e‖ ≤ u * (L * ‖e‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.1, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (norm_nonneg e)) hu.1
      calc ‖H u s‖ ≤ ‖(1 - u) • (g s - p)‖ + ‖(u * s) • e‖ := norm_add_le _ _
        _ ≤ (1 - u) * (L * ‖e‖) + u * (L * ‖e‖) := add_le_add h1 h2
        _ = L * ‖e‖ := by ring
  /- The motion `B`, with `φ`-coordinate `4 u (1 - u) k s`. -/
  let B : ℝ × ℝ → V := fun q => p + H q.1 q.2 + (4 * q.1 * (1 - q.1) * k q.2) • d
  have hB : ContDiff ℝ n B := by
    refine (contDiff_const.add ?_).add ?_
    · exact ((contDiff_const.sub contDiff_fst).smul ((hgc.comp contDiff_snd).sub
        contDiff_const)).add ((contDiff_fst.mul contDiff_snd).smul contDiff_const)
    · exact (((contDiff_const.mul contDiff_fst).mul (contDiff_const.sub contDiff_fst)).mul
        (hk.comp contDiff_snd)).smul contDiff_const
  have hBline : ∀ u s, L + 1 ≤ |s| → B (u, s) = p + s • e := by
    intro u s hs
    simp only [B, hHbig u s (by linarith), hkbig s hs, mul_zero, zero_smul, add_zero]
  have hBemb : ∀ u ∈ Icc (0 : ℝ) 1, IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, V) n fun s => B (u, s) := by
    intro u hu
    have hderB : ∀ s, HasDerivAt (fun s => B (u, s))
        ((1 - u) • deriv g s + (u * 1) • e + (4 * u * (1 - u) * deriv k s) • d) s := by
      intro s
      have hkd' : HasDerivAt k (deriv k s) s :=
        (hk.differentiable (zero_lt_one.trans_le hn₁).ne' s).hasDerivAt
      exact ((((hgd s).sub_const p).const_smul (1 - u)).add
        (((hasDerivAt_id s).const_mul u).smul_const e)).const_add p |>.add
        ((hkd'.const_mul (4 * u * (1 - u))).smul_const d)
    refine isSmoothEmbedding_of_eq_line hn₁ (hB.comp (contDiff_const.prodMk contDiff_id))
      ?_ hderB (fun s h => ?_) he (hBline u)
    · -- Injectivity: compare the `φ`-coordinates, then the hyperplane components.
      intro s s' h
      simp only [B] at h
      have h1 := congrArg φ h
      simp only [map_add, map_smul, hφH, hφd, smul_eq_mul, mul_one, add_zero] at h1
      have h1' : 4 * u * (1 - u) * k s = 4 * u * (1 - u) * k s' := add_left_cancel h1
      rw [h1'] at h
      have hH : H u s = H u s' := add_left_cancel (add_right_cancel h)
      rcases eq_or_lt_of_le hu.1 with rfl | hu0
      · simp only [H, sub_zero, one_smul, zero_mul, zero_smul, add_zero, sub_left_inj] at hH
        exact hinj hH
      rcases eq_or_lt_of_le hu.2 with rfl | hu1
      · simp only [H, sub_self, zero_smul, one_mul, zero_add] at hH
        exact smul_left_injective ℝ he hH
      have hc : 4 * u * (1 - u) ≠ 0 := by
        have : 0 < 1 - u := by linarith
        positivity
      have hks : k s = k s' := mul_left_cancel₀ hc h1'
      -- Parameters beyond `L` lie on the line, far from the hyperplane component of the others.
      have hfar : ∀ a b, |a| ≤ L → L < |b| → H u a ≠ H u b := by
        intro a b ha hb hab
        have h2 := hHsmall u hu a ha
        rw [hab, hHbig u b (by linarith), norm_smul, Real.norm_eq_abs] at h2
        have := mul_lt_mul_of_pos_right hb (norm_pos_iff.2 he)
        linarith
      rcases le_or_gt |s| L with hs | hs <;> rcases le_or_gt |s'| L with hs' | hs'
      · rwa [hksmall s hs, hksmall s' hs'] at hks
      · exact absurd hH (hfar s s' hs hs')
      · exact absurd hH.symm (hfar s' s hs' hs)
      · rw [hHbig u s (by linarith), hHbig u s' (by linarith)] at hH
        exact smul_left_injective ℝ he hH
    · -- Immersion: the `φ`-coordinate of the velocity, then the hyperplane component.
      have h1 := congrArg φ h
      simp only [map_add, map_smul, hφg', hφd, hφe, smul_eq_mul, mul_one, mul_zero, zero_add,
        map_zero] at h1
      rw [h1, zero_smul, add_zero] at h
      by_cases hs : R < |s|
      · rw [(hasDerivAt_of_eq_line hline hs).deriv, mul_one, ← add_smul] at h
        exact he (by simpa using h)
      · rw [(hkd s (by linarith [not_lt.1 hs])).deriv, mul_one] at h1
        rcases mul_eq_zero.1 h1 with h2 | h2
        · have hu0 : u = 0 := by linarith [mul_eq_zero.1 h2]
          subst hu0
          simp only [sub_zero, one_smul, zero_mul, zero_smul, add_zero] at h
          exact hg' s h
        · have hu1 : u = 1 := by linarith
          subst hu1
          simp only [sub_self, zero_smul, mul_one, one_smul, zero_add] at h
          exact he h
  exact ⟨isotopyOfContDiff B hB (fun s => by simp [B, H]) (fun s => by simp [B, H, hℓ]) hBemb,
    L + 1, fun t s hs => (hBline _ s hs).trans (hℓ s).symm⟩

/-- **Smooth arcs in dimension at least four are unknotted.** Let `V` be a real normed space of
dimension at least four, `ℓ : s ↦ p + s • e` an affine line in `V`, and `γ : ℝ → V` an injective
`C^n` immersion, `2 ≤ n ≤ ∞`, which agrees with `ℓ` for `|s| ≥ R`. Then `γ` is smoothly isotopic
to `ℓ` by an isotopy which agrees with `ℓ` for `|s| ≥ R'`, for some `R'`. -/
theorem exists_smoothIsotopy_line_of_four_le_finrank {n : ℕ∞ω} (hn₂ : 2 ≤ n) (hn : n ≤ ∞)
    (hV : 4 ≤ finrank ℝ V) (γ ℓ : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯) {p e : V}
    (hℓ : ∀ s, ℓ s = p + s • e) (hinj : Injective γ) (hγ' : ∀ s, deriv γ s ≠ 0) {R : ℝ}
    (hline : ∀ s, R ≤ |s| → γ s = ℓ s) :
    ∃ (F : SmoothIsotopy γ ℓ) (R' : ℝ),
      ∀ (t : unitInterval) (s : ℝ), R' ≤ |s| → F (t, s) = ℓ s := by
  have hγ : ContDiff ℝ n γ := contMDiff_iff_contDiff.1 γ.contMDiff
  have hn₁ : (1 : ℕ∞ω) ≤ n := le_trans (by norm_num) hn₂
  have hγd : ∀ s, HasDerivAt γ (deriv γ s) s := fun s =>
    (hγ.differentiable (zero_lt_one.trans_le hn₁).ne' s).hasDerivAt
  have hline' : ∀ s, R ≤ |s| → γ s = p + s • e := fun s hs => (hline s hs).trans (hℓ s)
  have hRs : R < |(|R| + 1)| := by
    rw [abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  have he : e ≠ 0 := by
    have := hγ' (|R| + 1)
    rwa [(hasDerivAt_of_eq_line hline' hRs).deriv] at this
  /- A direction `d` off every secant and tangent line of the arc. -/
  obtain ⟨d, hsec, htan⟩ := (hγ.of_le hn₂).exists_forall_smul_sub_ne_and_fderiv_ne
    (by simp only [finrank_self]; omega)
  have hsec' : ∀ s s' (c : ℝ), γ s - γ s' = c • d → s = s' := by
    intro s s' c h
    by_contra hne
    have hc : c ≠ 0 := by
      rintro rfl
      exact sub_ne_zero.2 (hinj.ne hne) (by simpa using h)
    exact hsec s s' c⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul])
  have htan' : ∀ s (c : ℝ), deriv γ s ≠ c • d := by
    intro s c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact hγ' s (by simpa using h)
    refine htan s c⁻¹ ?_
    rw [(hγd s).hasFDerivAt.fderiv]
    simp [h, smul_smul, inv_mul_cancel₀ hc]
  /- A linear form `φ` with `φ d = 1` and `φ e = 0`. -/
  obtain ⟨φ, hφd, hφe⟩ : ∃ φ : V →L[ℝ] ℝ, φ d = 1 ∧ φ e = 0 := by
    have hdmem : d ∉ (ℝ ∙ e) := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, rfl⟩
      have ha : a ≠ 0 := by
        rintro rfl
        exact hsec 0 0 0 (by simp)
      refine htan' (|R| + 1) a⁻¹ ?_
      rw [(hasDerivAt_of_eq_line hline' hRs).deriv, smul_smul, inv_mul_cancel₀ ha, one_smul]
    obtain ⟨f, hfd, hfe⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hdmem inferInstance
    have hfe' : f e = 0 := by
      have : f e ∈ (ℝ ∙ e).map f := Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self e)
      rwa [hfe, Submodule.mem_bot] at this
    exact ⟨(f d)⁻¹ • LinearMap.toContinuousLinearMap f, by simp [hfd], by simp [hfe']⟩
  /- The projection `g` of the arc along `d` onto the hyperplane `p + ker φ`. -/
  have hφline : ∀ s, R ≤ |s| → φ (γ s - p) = 0 := by
    intro s hs
    rw [hline' s hs, add_sub_cancel_left, map_smul, hφe, smul_zero]
  let g : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯ := ⟨fun s => γ s - φ (γ s - p) • d,
    (hγ.sub ((φ.contDiff.comp (hγ.sub contDiff_const)).smul contDiff_const)).contMDiff⟩
  have hgd : ∀ s, HasDerivAt g (deriv γ s - φ (deriv γ s) • d) s := fun s =>
    (hγd s).sub ((φ.hasFDerivAt.comp_hasDerivAt s ((hγd s).sub_const p)).smul_const d)
  obtain ⟨F₁, hF₁⟩ := exists_smoothIsotopy_projection hn₁ γ g he (fun s => rfl) hsec' htan'
    hline' hφline
  obtain ⟨F₂, R', hF₂⟩ := exists_smoothIsotopy_line_of_map_sub_eq_zero hn₁ hn g ℓ hℓ he hφd hφe
    (fun s s' h => hsec' s s' (φ (γ s - p) - φ (γ s' - p)) (by
      have h' : γ s - φ (γ s - p) • d = γ s' - φ (γ s' - p) • d := h
      rw [sub_smul]
      calc γ s - γ s' = (γ s - φ (γ s - p) • d) - (γ s' - φ (γ s' - p) • d) +
            (φ (γ s - p) • d - φ (γ s' - p) • d) := by abel
        _ = _ := by rw [h', sub_self, zero_add]))
    (fun s h => htan' s (φ (deriv γ s)) (sub_eq_zero.1 ((hgd s).deriv ▸ h)))
    (fun s => by
      have : g s - p = (γ s - p) - φ (γ s - p) • d := by
        simp only [g, ContMDiffMap.coeFn_mk]
        abel
      rw [this, map_sub, map_smul, hφd, smul_eq_mul, mul_one, sub_self])
    (fun s hs => by
      simp only [g, ContMDiffMap.coeFn_mk]
      rw [hφline s hs, zero_smul, sub_zero, hline' s hs])
  refine ⟨F₁.trans F₂ hn, max R R', fun t s hs => ?_⟩
  refine SmoothIsotopy.trans_apply_mem F₁ F₂ hn (s := {ℓ s}) (fun t => ?_) (fun t => ?_) t
  · exact (hF₁ t s ((le_max_left _ _).trans hs)).trans (hline s ((le_max_left _ _).trans hs))
  · exact hF₂ t s ((le_max_right _ _).trans hs)

end TauCeti
