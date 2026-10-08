/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.Basic
public import TauCeti.Analysis.Polynomial.Conjugation

/-!
# Conjugation-compatible nonmonic Puiseux branches

An analytic polynomial family whose coefficients respect conjugation admits nonmonic
Puiseux branches with one involutive permutation implementing conjugation. After multiplying
by the power that removes their poles, the analytic extensions respect the same permutation
on the full product, including the exceptional hyperplane. Extended roots may collide there,
and the original fibers may drop degree or be nullified.

The branches, pole removal, and permutation are constructed from coefficient hypotheses.
No root labels or symmetry of a supplied splitting are assumed. The distinguished power
substitution can be any positive multiple of the factorial of the punctured-fiber degree.
The parameter involution may conjugate several base coordinates; continuity suffices for it.
The leading-coefficient unit need not itself be assumed conjugation-compatible.

The construction uses `exists_analyticOnNhd_nonmonic_powerSubstitution` and the unique
conjugation permutation of a complete distinct root labelling
`TauCeti.existsUnique_root_conj_perm_of_subset_closure`.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 4, Corollary 4.2.
-/

public section

open Function Metric Polynomial Set ComplexConjugate

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E} [SimplyConnectedSpace U] {F : E × ℂ → ℂ[X]} {u : E × ℂ → ℂ}
  {d n a : ℕ} {R R' : ℝ} {τ : E → E}

/-- Construct nonmonic Puiseux branches and their pole-removed analytic extensions together
with the unique involutive conjugation permutation. Coefficient symmetry is needed only off
the distinguished hyperplane. The same labels act on the full-disc extensions, where roots
may collide. No nonvanishing condition on the constant coefficient is imposed;
degree zero is included. -/
theorem exists_analyticOnNhd_nonmonic_powerSubstitution_conj
    (hU : IsOpen U) (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hdiscr : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr ≠ 0)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hlc : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).coeff d = b.2 ^ a * u b)
    (hτ : ContinuousOn τ U) (hτU : MapsTo τ U U) (hττ : ∀ x ∈ U, τ (τ x) = x)
    (hconj : ∀ b ∈ U ×ˢ (ball 0 R \ {0}),
      F (τ b.1, conj b.2) = (F b).map (starRingEnd ℂ)) :
    ∃ r g : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
      (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ ball 0 R') ∧
        EqOn (g i) (fun b ↦ b.2 ^ (n * a) * r i b) (U ×ˢ (ball 0 R' \ {0}))) ∧
      (∀ b ∈ U ×ˢ (ball 0 R' \ {0}), Injective (fun i ↦ r i b) ∧
        F (b.1, b.2 ^ n) = C ((F (b.1, b.2 ^ n)).coeff d) * ∏ i, (X - C (r i b))) ∧
      ∃! σ : Equiv.Perm (Fin d), Involutive σ ∧
        (∀ i b, b ∈ U ×ˢ (ball 0 R' \ {0}) →
          r (σ i) b = conj (r i (τ b.1, conj b.2))) ∧
        ∀ i b, b ∈ U ×ˢ ball 0 R' → g (σ i) b = conj (g i (τ b.1, conj b.2)) := by
  obtain ⟨r, g, hra, hga, hfac⟩ := exists_analyticOnNhd_nonmonic_powerSubstitution
    hU hR' hn hR hdvd hF hdeg hdiscr hu hu0 hlc
  let S := U ×ˢ (ball (0 : ℂ) R' \ {0})
  let T := U ×ˢ ball (0 : ℂ) R'
  let κ : E × ℂ → E × ℂ := fun b ↦ (τ b.1, conj b.2)
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hST : S ⊆ T := prod_mono subset_rfl sdiff_subset
  have hq : MapsTo q S (U ×ˢ (ball 0 R \ {0})) := by
    intro b hb
    refine ⟨hb.1, ?_, pow_ne_zero n hb.2.2⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2.1) (norm_nonneg _) hn).trans_le hR
  have hconjBall : MapsTo conj (ball (0 : ℂ) R') (ball 0 R') := by
    intro z hz
    simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
  have hκ : ContinuousOn κ T := hτ.prodMap Complex.continuous_conj.continuousOn
  have hκT : MapsTo κ T T := hτU.prodMap hconjBall
  have hκS : MapsTo κ S S :=
    hτU.prodMap (fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩)
  have hκκ : ∀ b ∈ S, κ (κ b) = b :=
    fun b hb ↦ Prod.ext (hττ b.1 hb.1) (Complex.conj_conj b.2)
  have hroot (b : E × ℂ) (hb : b ∈ S) (z : ℂ) :
      (F (q b)).IsRoot z ↔ ∃ i, r i b = z := by
    have hl : (F (q b)).coeff d ≠ 0 := by
      rw [hlc _ (hq hb)]
      exact mul_ne_zero (pow_ne_zero _ (hq hb).2.2) (hu0 _ ⟨(hq hb).1, (hq hb).2.1⟩)
    rw [(hfac b hb).2, root_mul, iff_false_intro (not_isRoot_C _ z hl),
      false_or, isRoot_prod]
    simp [sub_eq_zero, eq_comm]
  have hsymm (b : E × ℂ) (hb : b ∈ S) :
      F (q (κ b)) = (F (q b)).map (starRingEnd ℂ) := by
    simpa only [q, κ, map_pow] using hconj _ (hq hb)
  -- Distinct punctured roots determine the permutation, without requiring extensions there.
  let := pathConnectedSpace_ball_diff_singleton (0 : ℂ) hR'
  have hSc : IsPreconnected S :=
    (isPreconnected_iff_preconnectedSpace.2 inferInstance).prod
      (isPreconnected_iff_preconnectedSpace.2 inferInstance)
  obtain ⟨x₀⟩ : Nonempty U := inferInstance
  obtain ⟨t₀⟩ : Nonempty ↥(ball (0 : ℂ) R' \ {0}) := inferInstance
  let b₀ : S := ⟨(x₀, t₀), x₀.property, t₀.property⟩
  obtain ⟨σ, ⟨hσσ, hσ⟩, huniq⟩ := TauCeti.existsUnique_root_conj_perm_of_subset_closure
    hSc subset_rfl subset_closure (fun i ↦ (hra i).continuousOn)
    (fun b hb ↦ (hfac b hb).1) hroot (hκ.mono hST) hκS hκS hκκ hsymm b₀
  -- The removed pole is a real monomial, so scaling commutes with conjugation.
  -- Continuity then carries the identity through the exceptional hyperplane.
  have hgconj (i : Fin d) : EqOn (g (σ i)) (fun b ↦ conj (g i (κ b))) S := by
    intro b hb
    simp only [(hga (σ i)).2 hb, (hga i).2 (hκS hb), hσ i b hb,
      κ, map_mul, map_pow, Complex.conj_conj]
  have hgfull (i : Fin d) : EqOn (g (σ i)) (fun b ↦ conj (g i (κ b))) T :=
    TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton isOpen_ball (hga (σ i)).1.continuousOn
      (Complex.continuous_conj.comp_continuousOn ((hga i).1.continuousOn.comp hκ hκT))
      (hgconj i)
  refine ⟨r, g, hra, hga, hfac, σ, ⟨hσσ, hσ, hgfull⟩, ?_⟩
  intro σ' hσ'
  exact huniq σ' ⟨hσ'.1, hσ'.2.1⟩

end TauCeti.Polynomial
