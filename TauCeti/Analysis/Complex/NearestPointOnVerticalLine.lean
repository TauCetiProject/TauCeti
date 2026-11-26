/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Order.Interval.Set.Infinite
import TauCeti.Analysis.Complex.Basic
import TauCeti.Topology.Codiscrete
import TauCeti.Topology.MetricSpace.Pseudo.NearestPoint

/-!
# A point of a vertical line with a unique nearest point in a discrete set

Let `Z ⊆ ℂ` be closed and discrete in the half-plane `θ < re s`, in the sense
`Zᶜ ∈ Filter.codiscreteWithin {s | θ < s.re}`: every point of the half-plane has a neighbourhood
meeting `Z` in finitely many points (`codiscreteWithin_iff_locallyFiniteComplementWithin`). Let
every point of `Z` have real part `< σ`, and let some point of `Z` have real part `> θ`. Then a
ball of radius `r ≤ σ - θ` about a point of the vertical line `re s = σ` meets `Z` in a single
point, in one of two forms:

* (A) the ball about a point `σ + γ i` meets `Z` in a single point `ρ`, and the ball of the same
  radius about the real point `σ` does not meet `Z`; or
* (B) `Z` has a real point `β > θ` of largest real part, and the ball about `σ` meets `Z` in `β`
  alone.

This is the choice of the expansion point in the windowed form of Landau's theorem, where `Z` is
the set of poles of a meromorphic function in a half-plane: the ball of radius `r` about the
expansion point contains exactly one pole, so subtracting its principal part leaves a function
holomorphic on that ball.

The proof fixes a point `ρ₁ ∈ Z` with `θ < re ρ₁` and a radius `a` with
`σ - re ρ₁ < a < σ - θ`, and looks at `Z` in the closed ball of radius `a` about `σ`. If that
ball meets no point of `Z`, put `D = a`; otherwise let `w₀` be the point of `Z` in it nearest to
`σ` and put `D = dist σ w₀`. In both cases no point of `Z` is closer than `D` to `σ`. If some
point of `Z` (`ρ₁` itself when the ball is empty) is closer than `D` to the line `re s = σ`,
moving along the line to its height gives (A): the height `γ` is chosen off the finitely many
heights at which two distinct points of `Z` in a closed ball about `σ + (im ρ₁) i` are
equidistant from `σ + γ i` (`TauCeti.subsingleton_setOfPred_dist_eq_dist`). Otherwise `w₀` is real
and of largest real part, which is (B). Each closed ball used lies in the half-plane
(`Complex.closedBall_subset_setOfPred_lt_re`), so it meets `Z` in finitely many points
(`IsCompact.finite_inter_of_compl_mem_codiscreteWithin`, the local finiteness of `Z`).

## Main results

* `TauCeti.subsingleton_setOfPred_dist_eq_dist`: at most one point of a vertical line is
  equidistant from two distinct points that are not mirror images in that line (their real parts
  are not symmetric about the line, or their imaginary parts differ).
* `TauCeti.exists_ball_inter_eq_singleton_or_exists_real_ball_inter_eq_singleton`: the dichotomy
  (A)/(B).

## References

* The statements follow `Deduction.landau_finite`, `Deduction.landau_dichotomy` and
  `Deduction.landau_nearest` of L. Alpöge's Lean formalization of the Riemann hypothesis for
  Dirichlet L-functions, <https://github.com/leanprover-community/riemann-hypothesis>. That
  repository has no licence file and was not read; the proofs here are independent.
-/

public section

open Complex Filter Metric Set

namespace TauCeti

/-- At most one point `σ + γ i` of the vertical line `re s = σ` is equidistant from two distinct
points `p`, `q` that are not mirror images of each other in that line: either their real parts
are not symmetric about `σ` (`p.re + q.re ≠ 2 σ`) or their imaginary parts differ. -/
theorem subsingleton_setOfPred_dist_eq_dist {σ : ℝ} {p q : ℂ} (hpq : p ≠ q)
    (hσ : p.re + q.re ≠ 2 * σ ∨ p.im ≠ q.im) :
    {γ : ℝ | dist ((σ : ℂ) + γ * I) p = dist ((σ : ℂ) + γ * I) q}.Subsingleton := by
  have key : ∀ (γ : ℝ) (w : ℂ),
      dist ((σ : ℂ) + γ * I) w ^ 2 = (σ - w.re) ^ 2 + (γ - w.im) ^ 2 := fun γ w ↦ by
    simp [sq_dist_eq_re_im]
  intro γ₁ h₁ γ₂ h₂
  have k₁ := congrArg (· ^ 2) h₁.out
  have k₂ := congrArg (· ^ 2) h₂.out
  simp only [key] at k₁ k₂
  by_contra hne
  have him : p.im = q.im := by
    have : (γ₁ - γ₂) * (q.im - p.im) = 0 := by linear_combination (k₁ - k₂) / 2
    have := (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    linarith
  have hre : (q.re - p.re) * (2 * σ - p.re - q.re) = 0 := by
    rw [him] at k₁
    linear_combination k₁
  rcases mul_eq_zero.1 hre with h | h
  · exact hpq (Complex.ext (by linarith) him)
  · exact hσ.elim (fun h' ↦ h' (by linarith)) (fun h' ↦ h' him)

/-- If `Z` is discrete in the half-plane `θ < re s`, it meets every closed ball
`closedBall c R` with `θ + R < c.re` in finitely many points: the ball lies in the half-plane
(`Complex.closedBall_subset_setOfPred_lt_re`) and is compact. -/
private theorem finite_closedBall_inter {Z : Set ℂ} {θ : ℝ}
    (hZ : Zᶜ ∈ codiscreteWithin {s : ℂ | θ < s.re}) {c : ℂ} {R : ℝ} (hR : θ + R < c.re) :
    (closedBall c R ∩ Z).Finite :=
  (isCompact_closedBall c R).finite_inter_of_compl_mem_codiscreteWithin
    (closedBall_subset_setOfPred_lt_re hR) hZ

/-- Case (B) of the dichotomy. Let `w₀ ∈ Z` be at distance `< σ - θ` from `σ`, and let every
`w ∈ Z` satisfy the signed bound `dist σ w₀ ≤ σ - w.re`: it lies to the left of the line
`re s = σ`, at horizontal distance at least `dist σ w₀`. Then `w₀` is a real point `β > θ` of
largest real part, and a ball about `σ` of radius `r` with `σ - β < r ≤ σ - θ` meets `Z` in `β`
alone. -/
private theorem exists_real_ball_inter_eq_singleton {Z : Set ℂ} {θ σ : ℝ}
    (hZ : Zᶜ ∈ codiscreteWithin {s : ℂ | θ < s.re}) {w₀ : ℂ} (hw₀ : w₀ ∈ Z)
    (hθ : dist (σ : ℂ) w₀ < σ - θ) (hre : ∀ w ∈ Z, dist (σ : ℂ) w₀ ≤ σ - w.re) :
    ∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ (∀ ρ ∈ Z, ρ.re ≤ β) ∧
      ∃ r, σ - β < r ∧ r ≤ σ - θ ∧ ball (σ : ℂ) r ∩ Z = {(β : ℂ)} := by
  -- name the real part `β = σ - dist σ w₀` of the nearest point, with its defining equation
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = σ - dist (σ : ℂ) w₀ := ⟨_, rfl⟩
  -- a point of `Z` at distance at most `dist σ w₀` from `σ` is the real point `β`
  have hreal : ∀ w ∈ Z, dist (σ : ℂ) w ≤ dist (σ : ℂ) w₀ → w = β := fun w hw h ↦
    Complex.ext (by linarith [ofReal_re β, re_sub_re_le_dist σ w, ofReal_re σ, hre w hw])
      (by rw [ofReal_im, ← im_eq_im_of_dist_le_re_sub_re (z := (σ : ℂ)) (h.trans (hre w hw)),
        ofReal_im])
  have hw₀β := hreal w₀ hw₀ le_rfl
  obtain ⟨R, hR, hRθ⟩ := exists_between hθ
  obtain ⟨r, hr, hrR, hball⟩ := exists_ball_inter_eq_singleton_of_finite
    (finite_closedBall_inter hZ (c := σ) (R := R) (by rw [ofReal_re]; linarith)) hw₀ hR
    fun w hw h ↦ (hreal w hw h).trans hw₀β.symm
  exact ⟨β, hw₀β ▸ hw₀, by linarith, fun ρ hρ ↦ by linarith [hre ρ hρ], r, by linarith,
    by linarith, hw₀β ▸ hball⟩

/-- Case (A) of the dichotomy. Let every point of `Z` have real part `< σ`, let no point of `Z`
lie at distance `< D` from `σ`, with `D < σ - θ`, and let `ρ₁ ∈ Z` satisfy `σ - ρ₁.re < D`. Then
some point `σ + γ i` of the line `re s = σ` has a unique nearest point `ρ` in `Z`, with
`0 < dist (σ + γ i) ρ`, isolated by a ball of radius `r ≤ σ - θ` that `Z` meets in `ρ` alone; the
ball of radius `r` about `σ` does not meet `Z`. -/
private theorem exists_ball_inter_eq_singleton_of_re_lt {Z : Set ℂ} {θ σ D : ℝ}
    (hZ : Zᶜ ∈ codiscreteWithin {s : ℂ | θ < s.re}) (hσ : ∀ ρ ∈ Z, ρ.re < σ) {ρ₁ : ℂ}
    (hρ₁ : ρ₁ ∈ Z) (hD₁ : σ - ρ₁.re < D) (hDθ : D < σ - θ)
    (hD : ∀ w ∈ Z, D ≤ dist (σ : ℂ) w) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r, 0 < dist ((σ : ℂ) + γ * I) ρ ∧ dist ((σ : ℂ) + γ * I) ρ < r ∧
      r ≤ σ - θ ∧ ball ((σ : ℂ) + γ * I) r ∩ Z = {ρ} ∧ ball (σ : ℂ) r ∩ Z = ∅ := by
  have hre (t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  obtain ⟨ε, hε, hε₁, hε₂⟩ : ∃ ε > 0, σ - ρ₁.re + 2 * ε < D ∧ D + ε < σ - θ :=
    ⟨min (D - (σ - ρ₁.re)) (σ - θ - D) / 3, div_pos (lt_min (by linarith) (by linarith)) three_pos,
      by linarith [min_le_left (D - (σ - ρ₁.re)) (σ - θ - D)],
      by linarith [min_le_right (D - (σ - ρ₁.re)) (σ - θ - D)]⟩
  -- `F`: the finitely many points of `Z` near `σ + (im ρ₁) i`
  obtain ⟨F, hFdef⟩ : ∃ F, F = closedBall ((σ : ℂ) + ρ₁.im * I) (D + ε) ∩ Z := ⟨_, rfl⟩
  have hF : F.Finite := hFdef ▸ finite_closedBall_inter hZ (by rw [hre]; linarith)
  have hρ₁c : dist ((σ : ℂ) + ρ₁.im * I) ρ₁ = σ - ρ₁.re := by
    -- `σ + (im ρ₁) i - ρ₁` is the nonnegative real number `σ - re ρ₁`
    have hdiff : (σ : ℂ) + ρ₁.im * I - ρ₁ = ((σ - ρ₁.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp)
    rw [dist_eq, hdiff, Complex.norm_of_nonneg (sub_nonneg.2 (hσ ρ₁ hρ₁).le)]
  have hF₁ : ρ₁ ∈ F := hFdef ▸ ⟨mem_closedBall'.2 (by linarith), hρ₁⟩
  -- the heights at which two points of `F` are equidistant
  have hB : (⋃ p ∈ F, ⋃ q ∈ F,
      {γ : ℝ | p ≠ q ∧ dist ((σ : ℂ) + γ * I) p = dist ((σ : ℂ) + γ * I) q}).Finite :=
    hF.biUnion fun p hp ↦ hF.biUnion fun q hq ↦ by
      by_cases hpq : p = q
      · simp [hpq]
      · rw [hFdef] at hp hq
        exact (subsingleton_setOfPred_dist_eq_dist hpq
          (Or.inl (by linarith [hσ p hp.2, hσ q hq.2]))).finite.subset fun γ h ↦ h.2
  obtain ⟨γ, hγ, hγB⟩ := ((Ioo_infinite (by linarith : ρ₁.im - ε < ρ₁.im + ε)).sdiff hB).nonempty
  -- name the centre `z = σ + γ i`; `subst` restores it before the final `exact`
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = σ + γ * I := ⟨_, rfl⟩
  have hzc : dist ((σ : ℂ) + ρ₁.im * I) z < ε := by
    -- both points lie on the line `re s = σ`, at heights `im ρ₁` and `γ`
    have hsame : ((σ : ℂ) + ρ₁.im * I).re = z.re := by simp [hz]
    have hheight : ((σ : ℂ) + ρ₁.im * I).im - z.im = ρ₁.im - γ := by simp [hz]
    rw [dist_of_re_eq hsame, Real.dist_eq, hheight, abs_sub_lt_iff]
    constructor <;> linarith [hγ.1, hγ.2]
  -- `ρ`: the point of `F` nearest to `z = σ + γ i`, unique by the choice of `γ`
  obtain ⟨ρ, hρ, hmin⟩ := exists_min_image F (dist z) hF ⟨ρ₁, hF₁⟩
  have hρZ : ρ ∈ Z := (hFdef ▸ hρ).2
  have hρD : dist z ρ < D - ε :=
    (hmin ρ₁ hF₁).trans_lt <| (dist_triangle_left _ _ _).trans_lt (by linarith)
  obtain ⟨r, hr, hrD, hball⟩ := exists_ball_inter_eq_singleton_of_finite
    (finite_closedBall_inter hZ (c := z) (R := D) (by rw [hz, hre]; linarith)) hρZ
    (by linarith) fun w hw h ↦ by
      have hwF : w ∈ F :=
        hFdef ▸ ⟨mem_closedBall'.2 ((dist_triangle _ z w).trans (by linarith)), hw⟩
      by_contra hne
      exact hγB (mem_biUnion hwF (mem_biUnion hρ ⟨hne, hz ▸ le_antisymm h (hmin w hwF)⟩))
  have hpos : 0 < dist z ρ := by linarith [re_sub_re_le_dist z ρ, hσ ρ hρZ, hz ▸ hre γ]
  subst hz
  exact ⟨γ, ρ, hρZ, r, hpos, hr, by linarith, hball,
    eq_empty_of_forall_notMem fun w hw ↦ by linarith [mem_ball'.1 hw.1, hD w hw.2]⟩

/-- **Choosing the expansion point.** Let `Z ⊆ ℂ` be closed and discrete in the half-plane
`θ < re s` (`Zᶜ ∈ codiscreteWithin {s | θ < s.re}`), let every point of `Z` have real part `< σ`,
and let some point of `Z` have real part `> θ`. Then either
* (A) there are a real `γ`, a point `ρ ∈ Z` and a radius `r ≤ σ - θ` with
  `0 < dist (σ + γ i) ρ < r`, such that the ball of radius `r` about `σ + γ i` meets `Z` in `ρ`
  alone and the ball of radius `r` about `σ` does not meet `Z`; or
* (B) there are a real `β > θ` in `Z`, of largest real part among the points of `Z`, and a radius
  `r` with `σ - β < r ≤ σ - θ` such that the ball of radius `r` about `σ` meets `Z` in `β`
  alone.

The conjuncts `0 < dist (σ + γ i) ρ` of (A) (a consequence of `ρ.re < σ`) and `θ < β` of (B) (a
consequence of `σ - β < r ≤ σ - θ`) follow from the others and are stated for convenience. -/
theorem exists_ball_inter_eq_singleton_or_exists_real_ball_inter_eq_singleton {Z : Set ℂ}
    {θ σ : ℝ} (hZ : Zᶜ ∈ codiscreteWithin {s : ℂ | θ < s.re}) (hσ : ∀ ρ ∈ Z, ρ.re < σ)
    (hθ : ∃ ρ ∈ Z, θ < ρ.re) :
    (∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r, 0 < dist ((σ : ℂ) + γ * I) ρ ∧ dist ((σ : ℂ) + γ * I) ρ < r ∧
      r ≤ σ - θ ∧ ball ((σ : ℂ) + γ * I) r ∩ Z = {ρ} ∧ ball (σ : ℂ) r ∩ Z = ∅) ∨
    ∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ (∀ ρ ∈ Z, ρ.re ≤ β) ∧
      ∃ r, σ - β < r ∧ r ≤ σ - θ ∧ ball (σ : ℂ) r ∩ Z = {(β : ℂ)} := by
  obtain ⟨ρ₁, hρ₁, hρ₁θ⟩ := hθ
  obtain ⟨a, ha₁, ha₂⟩ := exists_between (by linarith : σ - ρ₁.re < σ - θ)
  have hF := finite_closedBall_inter hZ (c := σ) (R := a) (by rw [ofReal_re]; linarith)
  rcases (closedBall (σ : ℂ) a ∩ Z).eq_empty_or_nonempty with h | h
  · -- no point of `Z` within `a` of `σ`: case (A) with `D = a`
    refine Or.inl (exists_ball_inter_eq_singleton_of_re_lt hZ hσ hρ₁ ha₁ ha₂ fun w hw ↦ ?_)
    exact le_of_not_gt fun hlt ↦ (eq_empty_iff_forall_notMem.1 h) w ⟨mem_closedBall'.2 hlt.le, hw⟩
  · -- `w₀` is a point of `Z` nearest to `σ`
    obtain ⟨w₀, hw₀, hmin⟩ := exists_min_image _ (dist (σ : ℂ)) hF h
    have hw₀a := mem_closedBall'.1 hw₀.1
    have hnear : ∀ w ∈ Z, dist (σ : ℂ) w₀ ≤ dist (σ : ℂ) w := fun w hw ↦
      (le_total (dist (σ : ℂ) w) a).elim (fun h' ↦ hmin w ⟨mem_closedBall'.2 h', hw⟩) hw₀a.trans
    by_cases hA : ∃ ρ ∈ Z, σ - ρ.re < dist (σ : ℂ) w₀
    · obtain ⟨ρ, hρ, hlt⟩ := hA
      exact Or.inl (exists_ball_inter_eq_singleton_of_re_lt hZ hσ hρ hlt (hw₀a.trans_lt ha₂) hnear)
    · push Not at hA
      exact Or.inr (exists_real_ball_inter_eq_singleton hZ hw₀.2 (hw₀a.trans_lt ha₂) hA)

end TauCeti
