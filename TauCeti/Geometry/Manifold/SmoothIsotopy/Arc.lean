/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.Projection
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Trans
import TauCeti.Geometry.Manifold.SmoothIsotopy.Extension
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Deriv.Projection
import TauCeti.Analysis.Calculus.Deriv.EqLine
import TauCeti.Geometry.Manifold.SmoothEmbedding.EqLine
import TauCeti.Analysis.Normed.Module.Dual.Submodule
import TauCeti.LinearAlgebra.Projection

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
extension theorem, in the form keeping fixed the part of the line that the isotopy does not move
(`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem`), the isotopy is realized by a
compactly supported ambient diffeomorphism carrying the arc onto the line
(`TauCeti.exists_diffeomorph_apply_eq_line_of_four_le_finrank`); this is how an arc in a manifold
of dimension at least four, read in a chart, is moved onto a straight arc. In dimension three the
theorem fails: an arc with a knot tied in a compact region is not isotopic to a straight line by an
isotopy fixed near infinity.

## Main results

* `TauCeti.exists_smoothIsotopy_line_of_four_le_finrank`: an injective `C^n` immersion of the
  line in a real normed space of dimension at least four, agreeing with an affine line outside a
  compact set, is smoothly isotopic to it by an isotopy fixed outside a compact set.
* `TauCeti.exists_diffeomorph_apply_eq_line_of_four_le_finrank`: such an arc is carried onto the
  line by a diffeomorphism of the ambient space equal to the identity outside a compact set.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 1, §3 (projections of embeddings), and Chapter 8, §1 (isotopy extension).
* H. Whitney, *Differentiable manifolds*, Ann. of Math. 37 (1936), 645–680.
-/

public section

noncomputable section

open Function Module Set Topology Filter Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The projection motion.** If `d` is on no secant line and no tangent line of the arc `γ`, then
`u ↦ γ - u • φ (γ - p) • d` is a smooth isotopy from `γ` to its projection `g` along `d` onto the
hyperplane `p + ker φ` (when `φ d = 1`). It fixes the parameters where `φ (γ s - p) = 0`. -/
private theorem exists_smoothIsotopy_projection {n : ℕ∞ω} (hn : 1 ≤ n)
    (γ g : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯) {p d e : V} (he : e ≠ 0) {φ : V →L[ℝ] ℝ}
    (hg : ∀ s, g s = γ s - φ (γ s - p) • d) (hsec : ∀ s s' (c : ℝ), γ s - γ s' = c • d → s = s')
    (htan : ∀ s (c : ℝ), deriv γ s ≠ c • d) {R : ℝ} (hline : ∀ s, R ≤ |s| → γ s = p + s • e)
    (hφline : ∀ s, R ≤ |s| → φ (γ s - p) = 0) :
    ∃ F : SmoothIsotopy γ g, ∀ (t : unitInterval) (s : ℝ), R ≤ |s| → F (t, s) = γ s := by
  have hγ : ContDiff ℝ n γ := contMDiff_iff_contDiff.1 γ.contMDiff
  let A : ℝ × ℝ → V := fun q => γ q.2 - (q.1 * φ (γ q.2 - p)) • d
  have hA : ContDiff ℝ n A := (hγ.comp contDiff_snd).sub ((contDiff_fst.mul
    (φ.contDiff.comp ((hγ.comp contDiff_snd).sub contDiff_const))).smul contDiff_const)
  have hAline : ∀ u s, R ≤ |s| → A (u, s) = γ s := by
    intro u s hs
    simp only [A]
    rw [hφline s hs, mul_zero, zero_smul, sub_zero]
  have hAemb : ∀ u ∈ Icc (0 : ℝ) 1, IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, V) n fun s => A (u, s) := by
    intro u _
    have hAu : (fun s => A (u, s)) = fun s => γ s - (u • φ) (γ s - p) • d := by
      ext s
      simp [A]
    rw [hAu]
    refine isSmoothEmbedding_of_eq_line hn (hAu ▸ hA.comp (contDiff_const.prodMk contDiff_id))
      (injective_sub_smul hsec _)
      (fun s => (hγ.differentiable (zero_lt_one.trans_le hn).ne' s).hasDerivAt.sub_smul p d _)
      (fun s h => htan s _ (sub_eq_zero.1 h)) (p := p) he (R := R) (fun s hs => ?_)
    simp only [smul_apply, hφline s hs, smul_zero, zero_smul, sub_zero]
    exact hline s hs
  exact ⟨SmoothIsotopy.ofContDiff A hA (fun s => by simp [A]) (fun s => by simp [A, hg]) hAemb,
    fun t s hs => by rw [SmoothIsotopy.ofContDiff_apply]; exact hAline _ s hs⟩

omit [FiniteDimensional ℝ V] in
/-- **Injectivity of the straightening motion.** Let `H` be a map into `ker φ`, with `φ d = 1`,
which is the line `s ↦ s • e` for `|s| > L` and stays in the ball of radius `L * ‖e‖` for
`|s| ≤ L`, and let `k` be the identity on `[-L, L]`. Then `s ↦ p + H s + (c * k s) • d` is
injective, provided `H` is injective when `c = 0`: the `φ`-coordinate `c * k s` separates the
parameters in `[-L, L]`, and the ball keeps them away from the others. -/
private theorem injective_add_add_smul {H : ℝ → V} {k : ℝ → ℝ} {c : ℝ} {p d e : V}
    {φ : V →L[ℝ] ℝ} (hφd : φ d = 1) (hφH : ∀ s, φ (H s) = 0) (he : e ≠ 0) {L : ℝ}
    (hk : ∀ s, |s| ≤ L → k s = s) (hHbig : ∀ s, L < |s| → H s = s • e)
    (hHsmall : ∀ s, |s| ≤ L → ‖H s‖ ≤ L * ‖e‖) (hc : c = 0 → Injective H) :
    Injective fun s => p + H s + (c * k s) • d := by
  intro s s' h
  dsimp only at h
  -- Compare the `φ`-coordinates, then the components in `ker φ`.
  have h1 := congrArg φ h
  simp only [map_add, map_smul, hφH, hφd, smul_eq_mul, mul_one, add_zero] at h1
  have h1' : c * k s = c * k s' := add_left_cancel h1
  rw [h1'] at h
  have hH : H s = H s' := add_left_cancel (add_right_cancel h)
  rcases eq_or_ne c 0 with hc0 | hc0
  · exact hc hc0 hH
  have hks : k s = k s' := mul_left_cancel₀ hc0 h1'
  have hfar : ∀ a b, |a| ≤ L → L < |b| → H a ≠ H b := by
    intro a b ha hb hab
    have h2 := hHsmall a ha
    rw [hab, hHbig b hb, norm_smul, Real.norm_eq_abs] at h2
    have := mul_lt_mul_of_pos_right hb (norm_pos_iff.2 he)
    linarith
  rcases le_or_gt |s| L with hs | hs <;> rcases le_or_gt |s'| L with hs' | hs'
  · rwa [hk s hs, hk s' hs'] at hks
  · exact absurd hH (hfar s s' hs hs')
  · exact absurd hH.symm (hfar s' s hs' hs)
  · rw [hHbig s hs, hHbig s' hs'] at hH
    exact smul_left_injective ℝ he hH

omit [FiniteDimensional ℝ V] in
/-- **The velocity of the straightening motion vanishes nowhere.** Let `φ d = 1`, `φ e = 0`, and
let `g'` be a nonzero vector of `ker φ`. If `κ = 1` or `g' = e`, then
`(1 - u) • g' + (u * 1) • e + (4 * u * (1 - u) * κ) • d ≠ 0`. -/
private theorem straightening_velocity_ne_zero {g' d e : V} {φ : V →L[ℝ] ℝ} (he : e ≠ 0)
    (hφd : φ d = 1) (hφe : φ e = 0) (hφg' : φ g' = 0) (hg' : g' ≠ 0) {u κ : ℝ}
    (hκ : κ = 1 ∨ g' = e) :
    (1 - u) • g' + (u * 1) • e + (4 * u * (1 - u) * κ) • d ≠ 0 := by
  intro h
  -- The `φ`-coordinate, then the component in `ker φ`.
  have h1 := congrArg φ h
  simp only [map_add, map_smul, hφg', hφd, hφe, smul_eq_mul, mul_one, mul_zero, zero_add,
    map_zero] at h1
  rw [h1, zero_smul, add_zero] at h
  rcases hκ with rfl | rfl
  · rw [mul_one] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · have hu0 : u = 0 := by linarith [mul_eq_zero.1 h2]
      subst hu0
      simp only [sub_zero, one_smul, zero_mul, zero_smul, add_zero] at h
      exact hg' h
    · have hu1 : u = 1 := by linarith
      subst hu1
      simp only [sub_self, zero_smul, mul_one, one_smul, zero_add] at h
      exact he h
  · rw [mul_one, ← add_smul] at h
    exact hg' (by simpa using h)

/-- For `0 < r` there is a radius `L > 0` exceeding `R` with `C ≤ L * r`. -/
private theorem exists_radius_lt_and_le_mul {r : ℝ} (hr : 0 < r) (R C : ℝ) :
    ∃ L : ℝ, 0 < L ∧ R < L ∧ C ≤ L * r := by
  have h1 := le_max_left R 1
  have h2 := le_max_right R 1
  have h3 := le_max_left (max R 1) (C / r)
  have h4 := le_max_right (max R 1) (C / r)
  refine ⟨max (max R 1) (C / r) + 1, by linarith, by linarith, ?_⟩
  exact (div_le_iff₀ hr).1 (by linarith)

omit [FiniteDimensional ℝ V] in
/-- Away from the compact set where `g` leaves the line, the hyperplane component of the
straightening motion is `s • e`. -/
private theorem hyperplane_component_of_line {g : ℝ → V} {p e : V} {R : ℝ}
    (hline : ∀ s, R ≤ |s| → g s = p + s • e) (u s : ℝ) (hs : R ≤ |s|) :
    (1 - u) • (g s - p) + (u * s) • e = s • e := by
  rw [hline s hs, add_sub_cancel_left, smul_smul, ← add_smul]
  congr 1
  ring

omit [FiniteDimensional ℝ V] in
/-- The hyperplane component of the straightening motion at times `u ∈ [0, 1]` has norm at most
`L * ‖e‖` for `|s| ≤ L`, when `‖g s - p‖ ≤ C ≤ L * ‖e‖` on the compact set `[-R, R]`. -/
private theorem norm_hyperplane_component_le {g : ℝ → V} {p e : V} {R C L : ℝ}
    (hline : ∀ s, R ≤ |s| → g s = p + s • e) (hC : ∀ s ∈ Icc (-R) R, ‖g s - p‖ ≤ C)
    (hCL : C ≤ L * ‖e‖) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {s : ℝ} (hs : |s| ≤ L) :
    ‖(1 - u) • (g s - p) + (u * s) • e‖ ≤ L * ‖e‖ := by
  by_cases hRs : R ≤ |s|
  · rw [hyperplane_component_of_line hline u s hRs, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg e)
  · have hsR : s ∈ Icc (-R) R := abs_le.1 (not_le.1 hRs).le
    have h1 : ‖(1 - u) • (g s - p)‖ ≤ (1 - u) * (L * ‖e‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2])]
      exact mul_le_mul_of_nonneg_left ((hC s hsR).trans hCL) (by linarith [hu.2])
    have h2 : ‖(u * s) • e‖ ≤ u * (L * ‖e‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.1, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (norm_nonneg e)) hu.1
    calc ‖(1 - u) • (g s - p) + (u * s) • e‖
        ≤ ‖(1 - u) • (g s - p)‖ + ‖(u * s) • e‖ := norm_add_le _ _
      _ ≤ (1 - u) * (L * ‖e‖) + u * (L * ‖e‖) := add_le_add h1 h2
      _ = L * ‖e‖ := by ring

omit [FiniteDimensional ℝ V] in
/-- The hyperplane component of the straightening motion is injective at the times `u` where the
coefficient `4 * u * (1 - u)` of the `d`-component vanishes. -/
private theorem injective_hyperplane_component_of_eq_zero {g : ℝ → V} {p e : V} (he : e ≠ 0)
    (hinj : Injective g) {u : ℝ} (hc : 4 * u * (1 - u) = 0) :
    Injective fun s => (1 - u) • (g s - p) + (u * s) • e := by
  rcases mul_eq_zero.1 hc with h2 | h2
  · have hu0 : u = 0 := by linarith [mul_eq_zero.1 h2]
    subst hu0
    intro s s' h
    simp only [sub_zero, one_smul, zero_mul, zero_smul, add_zero, sub_left_inj] at h
    exact hinj h
  · have hu1 : u = 1 := by linarith
    subst hu1
    intro s s' h
    simp only [sub_self, zero_smul, one_mul, zero_add] at h
    exact smul_left_injective ℝ he h

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
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn₁).ne'
  have hgd : ∀ s, HasDerivAt g (deriv g s) s := fun s => (hgc.differentiable hn0 s).hasDerivAt
  have hφg' : ∀ s, φ (deriv g s) = 0 := fun s =>
    (φ.hasFDerivAt.comp_hasDerivAt s ((hgd s).sub_const p)).unique
      ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq (Eventually.of_forall hφg))
  /- The constants: `‖g s - p‖ ≤ C` for `|s| ≤ R`, and `R < L` with `C ≤ L * ‖e‖`. -/
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hgc.continuous.sub continuous_const).continuousOn (s := Icc (-R) R))
  obtain ⟨L, hL0, hRL, hCL⟩ := exists_radius_lt_and_le_mul (norm_pos_iff.2 he) R C
  obtain ⟨k, hk, hksmall, hkbig, hkd⟩ := exists_contDiff_cutoff_id hL0 (lt_add_one L)
  replace hk : ContDiff ℝ n k := hk.of_le hn
  /- The hyperplane component `H` of the motion. -/
  let H : ℝ → ℝ → V := fun u s => (1 - u) • (g s - p) + (u * s) • e
  have hφH : ∀ u s, φ (H u s) = 0 := by
    intro u s
    simp [H, hφg, hφe]
  have hHbig : ∀ u s, R ≤ |s| → H u s = s • e := fun u s hs =>
    hyperplane_component_of_line hline u s hs
  have hHsmall : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s, |s| ≤ L → ‖H u s‖ ≤ L * ‖e‖ := fun u hu s hs =>
    norm_hyperplane_component_le hline hC hCL hu hs
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
        ((1 - u) • deriv g s + (u * 1) • e + (4 * u * (1 - u) * deriv k s) • d) s := fun s =>
      ((((hgd s).sub_const p).const_smul (1 - u)).add
        (((hasDerivAt_id s).const_mul u).smul_const e)).const_add p |>.add
        (((hk.differentiable hn0 s).hasDerivAt.const_mul (4 * u * (1 - u))).smul_const d)
    refine isSmoothEmbedding_of_eq_line hn₁ (hB.comp (contDiff_const.prodMk contDiff_id))
      ?_ hderB (fun s => straightening_velocity_ne_zero he hφd hφe (hφg' s) (hg' s) ?_) he
      (hBline u)
    · simp only [B]
      refine injective_add_add_smul hφd (hφH u) he hksmall
        (fun s hs => hHbig u s (hRL.trans hs).le) (hHsmall u hu)
        (injective_hyperplane_component_of_eq_zero he hinj)
    · by_cases hs : R < |s|
      · exact Or.inr (hasDerivAt_of_eq_line hline hs).deriv
      · exact Or.inl (hkd s (by linarith [not_lt.1 hs])).deriv
  refine ⟨SmoothIsotopy.ofContDiff B hB (fun s => by simp [B, H]) (fun s => by simp [B, H, hℓ])
    hBemb, L + 1, fun t s hs => ?_⟩
  rw [SmoothIsotopy.ofContDiff_apply, hBline _ s hs, hℓ]

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
  /- A direction `d` off every secant and tangent line of the arc, and a linear form `φ` with
  `φ d = 1` and `φ e = 0`; `d` is off the line `ℝ ∙ e` since `e` is a velocity of the arc. -/
  obtain ⟨d, hd0, hsec, htan⟩ :=
    (hγ.of_le hn₂).exists_forall_sub_eq_smul_and_deriv_ne hV hinj hγ'
  have hde : d ∉ (ℝ ∙ e) := fun hd => by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hd
    have ha : a ≠ 0 := by
      rintro rfl
      exact hd0 (zero_smul ℝ e)
    refine htan (|R| + 1) a⁻¹ ?_
    rw [(hasDerivAt_of_eq_line hline' hRs).deriv, smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨f, hfe, hfd⟩ :=
    Submodule.exists_dual_forall_mem_eq_zero_ne_zero (Submodule.closed_of_finiteDimensional _) hde
  obtain ⟨φ, hφd, hφe⟩ : ∃ φ : V →L[ℝ] ℝ, φ d = 1 ∧ φ e = 0 :=
    ⟨(f d)⁻¹ • f, by simp [hfd], by simp [hfe e (Submodule.mem_span_singleton_self e)]⟩
  /- The projection `g` of the arc along `d` onto the hyperplane `p + ker φ`. -/
  have hφline : ∀ s, R ≤ |s| → φ (γ s - p) = 0 := by
    intro s hs
    rw [hline' s hs, add_sub_cancel_left, map_smul, hφe, smul_zero]
  let g : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯ := ⟨fun s => γ s - φ (γ s - p) • d,
    (hγ.sub ((φ.contDiff.comp (hγ.sub contDiff_const)).smul contDiff_const)).contMDiff⟩
  have hg : ⇑g = fun s => γ s - φ (γ s - p) • d := by
    ext s
    simp only [g, ContMDiffMap.coeFn_mk]
  obtain ⟨F₁, hF₁⟩ := exists_smoothIsotopy_projection hn₁ γ g he (congrFun hg) hsec htan
    hline' hφline
  obtain ⟨F₂, R', hF₂⟩ := exists_smoothIsotopy_line_of_map_sub_eq_zero hn₁ hn g ℓ hℓ he hφd hφe
    (hg ▸ injective_sub_smul hsec fun s => φ (γ s - p))
    (fun s h => htan s (φ (deriv γ s))
      (sub_eq_zero.1 (((hγd s).sub_smul p d φ).deriv ▸ hg ▸ h)))
    (fun s => by
      simp only [hg]
      rw [sub_right_comm, map_sub, map_smul, hφd, smul_eq_mul, mul_one, sub_self])
    (fun s hs => by simp only [hg]; rw [hφline s hs, zero_smul, sub_zero, hline' s hs])
  refine ⟨F₁.trans F₂ hn, max R R', fun t s hs => ?_⟩
  refine SmoothIsotopy.trans_apply_mem F₁ F₂ hn (s := {ℓ s}) (fun t => ?_) (fun t => ?_) t
  · exact (hF₁ t s ((le_max_left _ _).trans hs)).trans (hline s ((le_max_left _ _).trans hs))
  · exact hF₂ t s ((le_max_right _ _).trans hs)

/-- **Ambient unknotting of smooth arcs in dimension at least four.** Let `V` be a
finite-dimensional real normed space of dimension at least four, and `γ : ℝ → V` an injective `C^n`
immersion which agrees with the affine line `ℓ : s ↦ p + s • e` for `|s| ≥ R`. Then some `C^m`
diffeomorphism `Φ` of `V`, equal to the identity outside a compact set, carries `γ` onto `ℓ`:
`Φ (γ s) = p + s • e` for every `s`. Here `1 ≤ m` and `m + 1 ≤ n`.

The isotopy of `TauCeti.exists_smoothIsotopy_line_of_four_le_finrank` is extended to an ambient
diffeotopy by `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq_of_forall_notMem`, which keeps
the far part of the line, where the isotopy does not move, fixed. -/
theorem exists_diffeomorph_apply_eq_line_of_four_le_finrank {n m : ℕ∞} (hm : 1 ≤ m)
    (hmn : m + 1 ≤ n) (hV : 4 ≤ finrank ℝ V) (γ : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯) {p e : V}
    (hinj : Injective γ) (hγ' : ∀ s, deriv γ s ≠ 0) {R : ℝ}
    (hline : ∀ s, R ≤ |s| → γ s = p + s • e) :
    ∃ (Φ : V ≃ₘ^m⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (K : Set V), IsCompact K ∧ (∀ y ∉ K, Φ y = y) ∧
      ∀ s, Φ (γ s) = p + s • e := by
  have hn₂ : (2 : ℕ∞ω) ≤ n := by
    have h2 : (2 : ℕ∞) ≤ m + 1 := by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ m + 1 := by gcongr
    exact WithTop.coe_le_coe.mpr (h2.trans hmn)
  let ℓ : C^n⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, V), V⟯ :=
    ⟨fun s => p + s • e, (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff⟩
  have hℓ : ∀ s, ℓ s = p + s • e := fun s => rfl
  obtain ⟨H, R', hH⟩ := exists_smoothIsotopy_line_of_four_le_finrank hn₂
    (by exact_mod_cast le_top) hV γ ℓ hℓ hinj hγ' (R := R) fun s hs => hline s hs
  have hRs : R < |(|R| + 1)| := by
    rw [abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  have he : e ≠ 0 := by
    have := hγ' (|R| + 1)
    rwa [(hasDerivAt_of_eq_line hline hRs).deriv] at this
  -- Outside `[-c, c]` the isotopy is the line at all times, so `γ` is the line there too.
  set c := max R' 0
  have hHc : ∀ t s, c ≤ |s| → H (t, s) = p + s • e := fun t s hs =>
    hH t s ((le_max_left _ _).trans hs)
  have hγc : ∀ s, c ≤ |s| → γ s = p + s • e := fun s hs => by
    rw [← H.apply_zero]
    exact hHc 0 s hs
  /- Extend the isotopy, keeping fixed the part `C` of the line beyond `c + 1 / 2`, which the
  motion of `[-c, c]` never meets because every time slice is injective. -/
  have hC : IsClosed ((fun s : ℝ => p + s • e) '' {s | c + 1 / 2 ≤ |s|}) :=
    ((Homeomorph.addLeft p).isClosedMap.comp (isClosedEmbedding_smul_left he).isClosedMap) _
      (isClosed_le continuous_const continuous_abs)
  obtain ⟨Φ, K, hK, hΦK, hΦ, hΦC⟩ := H.exists_diffeotopy_apply_eq_of_forall_notMem
    (A₀ := Icc (-c) c) (A := Icc (-(c + 1)) (c + 1)) isCompact_Icc isCompact_Icc hC
    (fun t x hx => by
      rintro ⟨s, hs, hxs⟩
      have hs' : c ≤ |s| := by linarith [show c + 1 / 2 ≤ |s| from hs]
      have hxs' : x = s :=
        (H.isSmoothEmbedding t).isEmbedding.injective (hxs.symm.trans (hHc t s hs').symm)
      have : |x| ≤ c := abs_le.2 hx
      linarith [show c + 1 / 2 ≤ |x| from hxs' ▸ hs])
    (fun t x _ hx => by
      have hcx : c ≤ |x| := by
        by_contra h
        exact hx (abs_le.1 (not_le.1 h).le)
      rw [hHc t x hcx, hγc x hcx])
    hm hmn
  refine ⟨Φ.final, K, hK, fun y hy => by rw [Diffeotopy.final_apply, hΦK 1 y hy], fun s => ?_⟩
  rw [Diffeotopy.final_apply]
  by_cases hs : |s| ≤ c + 1
  · have h₁ : (⟨Real.smoothTransition ((1 : unitInterval) : ℝ), Real.smoothTransition.nonneg _,
        Real.smoothTransition.le_one _⟩ : unitInterval) = 1 := Subtype.ext (by simp)
    rw [hΦ 1 s (abs_le.1 hs), h₁, H.apply_one, hℓ]
  · have hcs : c ≤ |s| := by linarith
    rw [hγc s hcs]
    exact hΦC 1 _ ⟨s, (by linarith : c + 1 / 2 ≤ |s|), rfl⟩

end TauCeti
