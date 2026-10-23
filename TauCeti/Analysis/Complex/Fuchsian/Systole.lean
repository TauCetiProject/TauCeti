/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Thick
import TauCeti.Analysis.Complex.Fuchsian.Margulis
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Endpoint
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Hyperbolic elements of a cofinite Fuchsian group move every point far

Let `Γ ≤ PSL(2, ℝ)` be cofinite. Then there is `δ > 0` such that every hyperbolic element of `Γ`,
the class of a matrix `A` with `|tr A| > 2`, moves every point of `ℍ` a hyperbolic distance at
least `δ`. Equivalently, the translation lengths of the hyperbolic elements of `Γ`, the lengths
of the closed geodesics of `Γ \ ℍ`, are bounded below by a positive constant: the systole of
`Γ \ ℍ` is positive. Consequently an element of `Γ` moving some point less than `δ` fixes a point
of `ℍ` or is parabolic: for small `ε`, the `ε`-thin part of `Γ \ ℍ` comes only from elliptic and
parabolic elements.

The proof shows that a sufficiently short hyperbolic element moves some point exactly `1 / 4` and
that this point, which lies far from the axis, is `1 / 4`-thick. (The points on the axis itself
are moved less than `1 / 4`, so they are thin.) Conjugate a hyperbolic element to the dilation
`z ↦ exp s * z`, and among the dilations of `Γ` along the same axis take the one with the least
`s₀ > 0`. If `s₀` is small, choose `y` with `Im y = 1` so far from the imaginary axis that this
dilation moves it exactly `1 / 4`. Every
other dilation in `Γ` along the axis moves `y` at least as far, by minimality, and so does every
element exchanging the ends of the axis, because `y` is far from it. By the Margulis lemma
`Subgroup.conj_eq_or_conj_eq_inv_of_dist_le`, an element of `Γ` moving `y` less than `1 / 4`
preserves the axis, so it is one of these. Hence `y` lies in the `1 / 4`-thick part of `Γ`.

The thick part of a Dirichlet domain of a cofinite group is bounded
(`Subgroup.IsCofinite.isBounded_dirichletDomain_inter_thickPart`), so a translate of `y` lies in
a fixed ball `B`. The corresponding conjugate of the minimal dilation moves a point of `B` by
`1 / 4`, so it is one of the finitely many elements of `Γ` moving the slightly larger ball to meet
itself. Each of these that is hyperbolic moves every point by at least a fixed positive amount,
and this bounds `s₀` below.

## Main results

* `Subgroup.IsCofinite.exists_pos_le_dist_smul_of_two_lt_abs_trace`: the hyperbolic elements of a
  cofinite group move every point at least a fixed positive distance.
* `Subgroup.IsCofinite.exists_pos_exists_smul_eq_or_isParabolic_of_dist_smul_lt`: an element of a
  cofinite group moving some point a small distance fixes a point of `ℍ` or is parabolic.

## References

* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick-thin decomposition of a finite-volume hyperbolic
  manifold).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §5.4 (consequences of Jørgensen's inequality) and Chapter 7 (the displacement
  of a point by a Möbius transformation).
-/

public section

open Filter Metric TauCeti UpperHalfPlane Topology
open scoped MatrixGroups

open Matrix.SpecialLinearGroup (abs_le_dist_dilation_smul dilation dilation_inv
  dist_dilation_smul_I)
open Matrix.ProjectiveSpecialLinearGroup (IsParabolic)

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- If a conjugate `g = σ (z ↦ exp t * z) σ⁻¹` with `t ≠ 0` lies in `Γ`, then so does the
conjugate `σ (z ↦ exp |t| * z) σ⁻¹`, which is `g` or `g⁻¹`. -/
private theorem conj_dilation_abs_mem {g σ : PSL(2, ℝ)} {t : ℝ} (hg : g ∈ Γ)
    (h : g = σ * ((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) (ht : t ≠ 0) :
    σ * ((dilation |t| : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have : σ * ((dilation |t| : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ = g⁻¹ := by
      rw [h, abs_of_neg hneg, ← dilation_inv, QuotientGroup.mk_inv]
      group
    rw [this]
    exact Γ.inv_mem hg
  · rwa [abs_of_pos hpos, ← h]

/-- **A minimal dilation along an axis.** If `Γ` is discrete and contains the conjugate
`σ (z ↦ exp s * z) σ⁻¹` for some `s > 0`, then among the `t > 0` with
`σ (z ↦ exp t * z) σ⁻¹ ∈ Γ` there is a least one. -/
private theorem exists_min_dilation [DiscreteTopology Γ] (σ : PSL(2, ℝ)) {s : ℝ} (hs : 0 < s)
    (hmem : σ * ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ) :
    ∃ s₀, 0 < s₀ ∧ s₀ ≤ s ∧ σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ ∧
      ∀ t, 0 < t → σ * ((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ → s₀ ≤ t := by
  set T : Set ℝ := {t | 0 < t ∧ t ≤ s ∧ σ * ((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ}
  set K := closedBall (σ • I) s
  have hfinΓ : {γ : Γ | ((γ • ·) '' K ∩ K).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (isCompact_closedBall _ _)
      (isCompact_closedBall _ _)
  -- the elements `σ (z ↦ exp t * z) σ⁻¹` with `t ∈ T` move `σ • I` at most `s`, and are distinct
  have hfin : T.Finite := by
    refine Set.Finite.of_finite_image (f := fun t ↦ σ * ((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹)
      ((hfinΓ.image Subtype.val).subset ?_) ?_
    · rintro _ ⟨t, ⟨ht, hts, htΓ⟩, rfl⟩
      refine ⟨⟨_, htΓ⟩, ?_, rfl⟩
      refine ⟨_, ⟨σ • I, mem_closedBall_self hs.le, rfl⟩, ?_⟩
      dsimp only
      rw [mem_closedBall, Subgroup.mk_smul, dist_conj_smul, inv_smul_smul, pslMk_smul,
        dist_dilation_smul_I, abs_of_pos ht]
      exact hts
    · intro t ht t' ht' h
      have hD : ((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) = dilation t' := by
        simpa using h
      have := congrArg (fun g : PSL(2, ℝ) ↦ dist (g • I) I) hD
      simpa only [pslMk_smul, dist_dilation_smul_I, abs_of_pos ht.1, abs_of_pos ht'.1] using this
  obtain ⟨s₀, hs₀, hmin⟩ := Set.exists_min_image T id hfin ⟨s, hs, le_rfl, hmem⟩
  refine ⟨s₀, hs₀.1, hs₀.2.1, hs₀.2.2, fun t ht htΓ ↦ ?_⟩
  rcases le_total t s with hts | hst
  · exact hmin t ⟨ht, hts, htΓ⟩
  · exact hs₀.2.1.trans hst

/-- **A point far from the axis of a short dilation.** If `s₀ > 0` is small, there is a point of
`ℍ` moved exactly `1 / 4` by the dilation `z ↦ exp s₀ * z`, at least `1 / 4` by every dilation
`z ↦ exp t * z` with `|t| ≥ s₀`, and at least `1 / 4` by every antidiagonal matrix. -/
private theorem exists_dist_dilation_smul_eq {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hsmall : (Real.cosh s₀ - 1) * (2 + (Real.cosh (1 / 4) - 1)) ≤ Real.cosh (1 / 4) - 1) :
    ∃ y : ℍ, dist (((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) • y) y = 1 / 4 ∧
      (∀ t, s₀ ≤ |t| → 1 / 4 ≤ dist (((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) • y) y) ∧
      ∀ X : SL(2, ℝ), X 0 0 = 0 → X 1 1 = 0 → 1 / 4 ≤ dist (X • y) y := by
  set c₀ := Real.cosh (1 / 4) - 1
  have hc₀ : 0 < c₀ := sub_pos.2 (Real.one_lt_cosh.2 (by norm_num))
  have hk : 0 < Real.cosh s₀ - 1 := sub_pos.2 (Real.one_lt_cosh.2 hs₀.ne')
  have hkc : (Real.cosh s₀ - 1) * (c₀ / (Real.cosh s₀ - 1)) = c₀ := by field_simp
  have hck : 2 + c₀ ≤ c₀ / (Real.cosh s₀ - 1) := (le_div_iff₀ hk).2 (by linarith)
  -- the point `y = x + i`, with `x² = c₀ / (cosh s₀ - 1) - 1`
  set x := Real.sqrt (c₀ / (Real.cosh s₀ - 1) - 1)
  have hx : x ^ 2 = c₀ / (Real.cosh s₀ - 1) - 1 := Real.sq_sqrt (by linarith)
  set y : ℍ := ⟨x + Complex.I, by simp⟩
  have hy : (y.re / y.im) ^ 2 = c₀ / (Real.cosh s₀ - 1) - 1 := by
    simp [y, UpperHalfPlane.re, UpperHalfPlane.im, hx]
  have hcosh (t : ℝ) : Real.cosh (dist (((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) • y) y) =
      1 + (Real.cosh t - 1) * (c₀ / (Real.cosh s₀ - 1)) := by
    rw [pslMk_smul, Matrix.SpecialLinearGroup.cosh_dist_dilation_smul, hy]
    ring
  -- `cosh` is strictly increasing on `[0, ∞)`, where `1 / 4` and every distance lie
  have hle {d : ℝ} (hd : 0 ≤ d) : Real.cosh (1 / 4) ≤ Real.cosh d ↔ 1 / 4 ≤ d :=
    Real.cosh_strictMonoOn.le_iff_le (by norm_num) hd
  refine ⟨y, ?_, fun t ht ↦ (hle dist_nonneg).1 ?_, fun X h₀₀ h₁₁ ↦ (hle dist_nonneg).1 ?_⟩
  · have h : Real.cosh (dist (((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) • y) y) =
        Real.cosh (1 / 4) := by
      rw [hcosh, hkc]
      ring
    exact Real.cosh_strictMonoOn.injOn dist_nonneg (by norm_num) h
  · -- a dilation with `|t| ≥ s₀` moves `y` at least as far as the one with `t = s₀`
    have hst : Real.cosh s₀ ≤ Real.cosh t := Real.cosh_le_cosh.2 (by rwa [abs_of_pos hs₀])
    have hq : 0 ≤ c₀ / (Real.cosh s₀ - 1) := by positivity
    rw [hcosh]
    nlinarith
  · -- an antidiagonal matrix moves `y` far, since `y` is far from the imaginary axis
    refine le_trans ?_ (Matrix.SpecialLinearGroup.one_add_two_mul_sq_le_cosh_dist_smul h₀₀ h₁₁ y)
    rw [hy]
    linarith

/-- **A thick point near a short closed geodesic.** Let `Γ` be discrete, and let
`g = σ (z ↦ exp s₀ * z) σ⁻¹` lie in `Γ`, with `s₀ > 0` least among such dilations along the same
axis. If `s₀` is small, some point moved exactly `1 / 4` by `g` lies in the `1 / 4`-thick part
of `Γ`. -/
private theorem exists_mem_thickPart_dist_eq [DiscreteTopology Γ] (σ : PSL(2, ℝ)) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hmem : σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ)
    (hmin : ∀ t, 0 < t → σ * ((dilation t : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ → s₀ ≤ t)
    (hsmall : (Real.cosh s₀ - 1) * (2 + (Real.cosh (1 / 4) - 1)) ≤ Real.cosh (1 / 4) - 1) :
    ∃ y ∈ (thickPart Γ (1 / 4) : Set ℍ),
      dist ((σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) • y) y = 1 / 4 := by
  obtain ⟨y, hy₀, hyt, hyX⟩ := exists_dist_dilation_smul_eq hs₀ hsmall
  have hfix : ∀ w : ℍ, (σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) • w ≠ w := by
    intro w hw
    have h := abs_le_dist_dilation_smul s₀ (σ⁻¹ • w)
    rw [← pslMk_smul, ← dist_conj_smul, hw, dist_self, abs_of_pos hs₀] at h
    exact hs₀.not_ge h
  have hdist :
      dist ((σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) • σ • y) (σ • y) = 1 / 4 := by
    rw [dist_conj_smul, inv_smul_smul, hy₀]
  refine ⟨σ • y, mem_thickPart.2 fun γ hγ₁ ↦ ?_, hdist⟩
  by_contra! hlt
  rw [Subgroup.smul_def] at hlt
  -- by the Margulis lemma `σ⁻¹ γ σ` preserves the imaginary axis
  have hconj : (σ⁻¹ * γ * σ) * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * (σ⁻¹ * γ * σ)⁻¹ =
        dilation s₀ ∨
      (σ⁻¹ * γ * σ) * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * (σ⁻¹ * γ * σ)⁻¹ =
        ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ))⁻¹ := by
    have hc : (σ⁻¹ * γ * σ) * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * (σ⁻¹ * γ * σ)⁻¹ =
        σ⁻¹ * ((γ : PSL(2, ℝ)) * (σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) *
          (γ : PSL(2, ℝ))⁻¹) * σ := by
      group
    rw [hc]
    rcases conj_eq_or_conj_eq_inv_of_dist_le hmem γ.2 hfix hdist.le hlt.le with h | h <;>
      [left; right] <;> rw [h] <;> group
  have hγ : (γ : PSL(2, ℝ)) = σ * (σ⁻¹ * γ * σ) * σ⁻¹ := by group
  rw [hγ, dist_conj_smul, inv_smul_smul] at hlt
  rcases TauCeti.UpperHalfPlane.exists_eq_dilation_or_antidiag_of_conj_dilation hs₀.ne' hconj with
    ⟨t, ht⟩ | ⟨X, hX, h₀₀, h₁₁⟩
  · -- `γ` is a dilation along the axis, which moves `σ • y` at least `1 / 4` by minimality
    rw [ht] at hlt hγ
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hγ₁
      rw [← Subtype.coe_inj, hγ]
      simp
    exact (hyt t (hmin _ (abs_pos.2 ht0) (conj_dilation_abs_mem γ.2 hγ ht0))).not_gt hlt
  · -- `γ` exchanges the ends of the axis, and so moves `σ • y` at least `1 / 4`
    rw [← hX, pslMk_smul] at hlt
    exact (hyX X h₀₀ h₁₁).not_gt hlt

/-- **Dilations moving a thick point.** For a cofinite `Γ` there is `ε > 0` such that whenever a
conjugate `σ (z ↦ exp s₀ * z) σ⁻¹ ∈ Γ`, with `s₀ > 0`, moves some point of the `1 / 4`-thick part
at most `1 / 4`, then `s₀ ≥ ε`. Indeed, a translate of that point lies in a fixed ball, so a
conjugate of the dilation is one of finitely many elements of `Γ`. -/
private theorem IsCofinite.exists_pos_le_of_mem_thickPart (hΓ : Γ.IsCofinite) :
    ∃ ε > 0, ∀ (σ : PSL(2, ℝ)) (s₀ : ℝ), 0 < s₀ →
      σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹ ∈ Γ → ∀ y ∈ (thickPart Γ (1 / 4) : Set ℍ),
        dist ((σ * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) • y) y ≤ 1 / 4 → ε ≤ s₀ := by
  have := hΓ.discreteTopology
  -- the thick part of the Dirichlet domain at `I` lies in a ball `closedBall I R`
  obtain ⟨R, hR⟩ := (hΓ.isBounded_dirichletDomain_inter_thickPart I
    (by norm_num : (0 : ℝ) < 1 / 4)).subset_closedBall I
  set B := closedBall I (R + 1 / 4)
  set F := {γ : Γ | ((γ • ·) '' B ∩ B).Nonempty}
  have hF : F.Finite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (isCompact_closedBall _ _) (isCompact_closedBall _ _)
  -- choose `ε` small enough for the elements of `F` that move every point a positive distance
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧
      ∀ γ ∈ F, (∃ c > 0, ∀ z : ℍ, c ≤ dist (γ • z) z) → ∀ z : ℍ, ε ≤ dist (γ • z) z := by
    refine eventually_mem_nhdsWithin.and (hF.eventually_all.2 fun γ _ ↦ ?_)
    by_cases hP : ∃ c > 0, ∀ z : ℍ, c ≤ dist (γ • z) z
    · obtain ⟨c, hc, hcz⟩ := hP
      filter_upwards [(eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds] with ε hε _ z
      exact hε.le.trans (hcz z)
    · exact Eventually.of_forall fun _ h ↦ absurd h hP
  obtain ⟨ε, hε, hεF⟩ := hev.exists
  refine ⟨ε, hε, fun σ s₀ hs₀ hmem₀ y hythick hydist ↦ ?_⟩
  -- a translate of `y` lies in the ball, so the conjugate `f` of the dilation lies in `F`
  obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain (G := Γ) I y
  have hγR : γ • y ∈ closedBall I R := hR ⟨hγ, (smul_mem_thickPart_iff γ).2 hythick⟩
  set f : Γ := γ * ⟨_, hmem₀⟩ * γ⁻¹
  have hf : (f : PSL(2, ℝ)) =
      ((γ : PSL(2, ℝ)) * σ) * ((dilation s₀ : SL(2, ℝ)) : PSL(2, ℝ)) * ((γ : PSL(2, ℝ)) * σ)⁻¹ := by
    simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hfγy : dist (f • γ • y) (γ • y) ≤ 1 / 4 := by
    rwa [Subgroup.smul_def, Subgroup.smul_def, hf, dist_conj_smul, mul_inv_rev, mul_smul,
      inv_smul_smul, ← dist_conj_smul]
  have hfF : f ∈ F := by
    refine ⟨f • γ • y, ⟨γ • y, closedBall_subset_closedBall (by norm_num) hγR, rfl⟩, ?_⟩
    rw [mem_closedBall] at hγR ⊢
    linarith [dist_triangle (f • γ • y) (γ • y) I]
  -- `f` moves every point at least `s₀`, and moves `(γ σ) • I` exactly `s₀`
  have hP : ∃ c > 0, ∀ w : ℍ, c ≤ dist (f • w) w := by
    refine ⟨s₀, hs₀, fun w ↦ ?_⟩
    rw [Subgroup.smul_def, hf, dist_conj_smul]
    simpa only [pslMk_smul, abs_of_pos hs₀] using abs_le_dist_dilation_smul s₀ _
  have h := hεF f hfF hP (((γ : PSL(2, ℝ)) * σ) • I)
  rwa [Subgroup.smul_def, hf, dist_conj_smul, inv_smul_smul, pslMk_smul, dist_dilation_smul_I,
    abs_of_pos hs₀] at h

/-- **Hyperbolic elements of a cofinite group move every point far.** For a cofinite
`Γ ≤ PSL(2, ℝ)` there is `δ > 0` such that the class of every `A ∈ SL(2, ℝ)` with `|tr A| > 2`
lying in `Γ` moves every point of `ℍ` a hyperbolic distance at least `δ`. Equivalently, the
translation lengths of the hyperbolic elements of `Γ` are bounded below by `δ`. -/
theorem IsCofinite.exists_pos_le_dist_smul_of_two_lt_abs_trace (hΓ : Γ.IsCofinite) :
    ∃ δ > 0, ∀ A : SL(2, ℝ), (A : PSL(2, ℝ)) ∈ Γ →
      2 < |(A : Matrix (Fin 2) (Fin 2) ℝ).trace| → ∀ z : ℍ, δ ≤ dist (A • z) z := by
  have := hΓ.discreteTopology
  obtain ⟨ε, hε, hεs⟩ := hΓ.exists_pos_le_of_mem_thickPart
  set c₀ := Real.cosh (1 / 4) - 1
  have hc₀ : 0 < c₀ := sub_pos.2 (Real.one_lt_cosh.2 (by norm_num))
  -- choose `δ ≤ ε` so small that `exists_mem_thickPart_dist_eq` applies below `δ`
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ ε ∧ (Real.cosh δ - 1) * (2 + c₀) ≤ c₀ := by
    have h : Tendsto (fun δ ↦ (Real.cosh δ - 1) * (2 + c₀)) (𝓝 0) (𝓝 0) := by
      simpa using ((Real.continuous_cosh.sub continuous_const).mul continuous_const).tendsto
        (0 : ℝ) (f := fun δ ↦ (Real.cosh δ - 1) * (2 + c₀))
    exact eventually_mem_nhdsWithin.and <|
      ((eventually_le_nhds hε).and (h.eventually (ge_mem_nhds hc₀))).filter_mono
        nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδε, hδc⟩ := hev.exists
  refine ⟨δ, hδ, fun A hA htr z ↦ ?_⟩
  -- `A` is conjugate to a dilation, and some dilation along the same axis is minimal
  obtain ⟨σ, s, hs, hAeq⟩ := TauCeti.UpperHalfPlane.exists_eq_conj_dilation_of_two_lt_abs_trace htr
  obtain ⟨s₀, hs₀, hs₀s, hmem₀, hmin⟩ :=
    exists_min_dilation σ (abs_pos.2 hs) (conj_dilation_abs_mem hA hAeq hs)
  have hAz : |s| ≤ dist (A • z) z := by
    rw [← pslMk_smul, hAeq, dist_conj_smul, pslMk_smul]
    exact abs_le_dist_dilation_smul s _
  refine le_trans ?_ (hs₀s.trans hAz)
  by_contra! hlt
  -- otherwise `s₀` is small, so the minimal dilation moves a thick point exactly `1 / 4`
  have hsmall : (Real.cosh s₀ - 1) * (2 + c₀) ≤ c₀ := by
    refine le_trans ?_ hδc
    gcongr
    exact Real.cosh_le_cosh.2 (by rw [abs_of_pos hs₀, abs_of_pos hδ]; exact hlt.le)
  obtain ⟨y, hythick, hydist⟩ := exists_mem_thickPart_dist_eq σ hs₀ hmem₀ hmin hsmall
  exact (hεs σ s₀ hs₀ hmem₀ y hythick hydist.le).not_gt (hlt.trans_le hδε)

/-- **Short displacements in a cofinite group are elliptic or parabolic.** For a cofinite
`Γ ≤ PSL(2, ℝ)` there is `δ > 0` such that every element of `Γ` moving some point of `ℍ` a
hyperbolic distance less than `δ` fixes a point of `ℍ` or is parabolic. -/
theorem IsCofinite.exists_pos_exists_smul_eq_or_isParabolic_of_dist_smul_lt
    (hΓ : Γ.IsCofinite) :
    ∃ δ > 0, ∀ g ∈ Γ, ∀ z : ℍ, dist (g • z) z < δ → (∃ w : ℍ, g • w = w) ∨ IsParabolic g := by
  obtain ⟨δ, hδ, hδA⟩ := hΓ.exists_pos_le_dist_smul_of_two_lt_abs_trace
  refine ⟨δ, hδ, fun g hg z hz ↦ ?_⟩
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  rw [pslMk_smul] at hz
  rcases lt_trichotomy |(A : Matrix (Fin 2) (Fin 2) ℝ).trace| 2 with hlt | heq | hgt
  · -- an elliptic element fixes a point of `ℍ`
    have hell : (Matrix.SpecialLinearGroup.mapGL ℝ A).IsElliptic :=
      (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).2 hlt
    refine Or.inl ⟨UpperHalfPlane.fixedPt _ hell, ?_⟩
    rw [pslMk_smul]
    exact (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by simp) hell).2 rfl
  · have htr : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = 4 := by
      rw [← sq_abs, heq]
      norm_num
    rcases Matrix.ProjectiveSpecialLinearGroup.eq_one_or_isParabolic_of_trace_sq_eq_four htr with
      h | h
    · exact Or.inl ⟨z, by rw [h, one_smul]⟩
    · exact Or.inr h
  · exact absurd hz (hδA A hg hgt z).not_gt

end Subgroup
