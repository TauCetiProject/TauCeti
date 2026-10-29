/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.RootDifference
public import TauCeti.Analysis.Polynomial.Conjugation
public import TauCeti.Analysis.Analytic.Laurent.Conjugation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Global conjugation symmetry of nonmonic root differences

Construct nonmonic Puiseux branches together with global Laurent unit forms for their
pairwise differences and a single involution implementing conjugation. Conjugate pairs of
labels have equal integer difference exponents and conjugate units on the whole product,
including the exceptional hyperplane. The parameter involution need not fix base points.

The branches and difference units come from
`TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_root_sub_eq_zpow_mul_unit`.
The conjugation permutation comes from the complete distinct punctured root labelling;
`AnalyticAt.laurent_eq_of_conj` identifies the difference exponents at paired parameters.
Cancellation away from the hyperplane and continuity extend unit symmetry across it.
No condition on the constant coefficient is needed, and individual branches may vanish
identically or have poles.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Function Metric Polynomial Set Topology ComplexConjugate

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E} [SimplyConnectedSpace U] {F : E × ℂ → ℂ[X]} {d n a c : ℕ} {R R' : ℝ}
  {u v : E × ℂ → ℂ} {τ : E → E}

/-- Construct nonmonic Puiseux branches with global Laurent difference units respecting
conjugation. The unique conjugation permutation preserves the difference exponents and
interchanges their units on the full product. Exponents and units are indexed only by
unequal labels. Poles, collisions on the hyperplane, degree drops, nullified central fibers,
and degrees zero and one are allowed. -/
theorem exists_analyticOnNhd_nonmonic_root_sub_eq_zpow_mul_unit_conj
    (hU : IsOpen U) (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hv : AnalyticOnNhd ℂ v (U ×ˢ ball 0 R))
    (hv0 : ∀ b ∈ U ×ˢ ball 0 R, v b ≠ 0)
    (hlead : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).coeff d = b.2 ^ a * u b)
    (hdiscr : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr = b.2 ^ c * v b)
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
        (∀ i b, b ∈ U ×ˢ ball 0 R' → g (σ i) b = conj (g i (τ b.1, conj b.2))) ∧
        ∃ (e : (i j : Fin d) → i ≠ j → ℤ)
          (w : (i j : Fin d) → i ≠ j → E × ℂ → ℂ),
          ∀ i j hij,
            AnalyticOnNhd ℂ (w i j hij) (U ×ˢ ball 0 R') ∧
            (∀ b ∈ U ×ˢ ball 0 R', w i j hij b ≠ 0) ∧
            (∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
              r i b - r j b = b.2 ^ e i j hij * w i j hij b) ∧
            e (σ i) (σ j) (σ.injective.ne hij) = e i j hij ∧
            ∀ b ∈ U ×ˢ ball 0 R',
              w (σ i) (σ j) (σ.injective.ne hij) b =
                conj (w i j hij (τ b.1, conj b.2)) := by
  obtain ⟨r, g, hra, hg, hr, hdiff⟩ :=
    exists_analyticOnNhd_nonmonic_root_sub_eq_zpow_mul_unit
      hU hR' hn hR hdvd hF hdeg hu hu0 hv hv0 hlead hdiscr
  choose e w hwa hw0 hwform using hdiff
  let S := U ×ˢ (ball (0 : ℂ) R' \ {0})
  let T := U ×ˢ ball (0 : ℂ) R'
  let κ : E × ℂ → E × ℂ := fun b ↦ (τ b.1, conj b.2)
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hST : S ⊆ T := prod_mono subset_rfl sdiff_subset
  have hq : MapsTo q S (U ×ˢ (ball 0 R \ {0})) :=
    (mapsTo_id U).prodMap (mapsTo_pow_ball_zero_diff_singleton hn hR)
  have hconjBall : MapsTo conj (ball (0 : ℂ) R') (ball 0 R') := by
    intro z hz
    simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
  have hκ : ContinuousOn κ T := hτ.prodMap Complex.continuous_conj.continuousOn
  have hκT : MapsTo κ T T := hτU.prodMap hconjBall
  have hκS : MapsTo κ S S :=
    hτU.prodMap fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩
  have hroot (b : E × ℂ) (hb : b ∈ S) (z : ℂ) :
      (F (q b)).IsRoot z ↔ ∃ i, r i b = z := by
    have hl : (F (q b)).coeff d ≠ 0 := by
      rw [hlead _ (hq hb)]
      exact mul_ne_zero (pow_ne_zero _ (hq hb).2.2) (hu0 _ ⟨(hq hb).1, (hq hb).2.1⟩)
    rw [(hr b hb).2, root_mul, iff_false_intro (not_isRoot_C _ z hl),
      false_or, isRoot_prod]
    simp [sub_eq_zero, eq_comm]
  -- The punctured product is connected, so conjugation uses one permutation of all labels.
  let := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex])
      (0 : ℂ) hR')
  have hSc : IsPreconnected S :=
    (isPreconnected_iff_preconnectedSpace.2 inferInstance).prod
      (isPreconnected_iff_preconnectedSpace.2 inferInstance)
  obtain ⟨x₀⟩ : Nonempty U := inferInstance
  obtain ⟨t₀⟩ : Nonempty ↥(ball (0 : ℂ) R' \ {0}) := inferInstance
  obtain ⟨σ, ⟨hσσ, hσ⟩, huniq⟩ := TauCeti.existsUnique_root_conj_perm_of_subset_closure
    hSc subset_rfl subset_closure (fun i ↦ (hra i).continuousOn)
    (fun b hb ↦ (hr b hb).1) hroot (hκ.mono hST) hκS hκS
    (fun b hb ↦ Prod.ext (hττ b.1 hb.1) (Complex.conj_conj b.2))
    (fun b hb ↦ by simpa only [q, κ, map_pow] using hconj _ (hq hb))
    ⟨(x₀, t₀), x₀.2, t₀.2⟩
  have hgfull (i : Fin d) : EqOn (g (σ i)) (fun b ↦ conj (g i (κ b))) T := by
    refine TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton (c := (0 : ℂ)) isOpen_ball
      (hg (σ i)).1.continuousOn
      (Complex.continuous_conj.comp_continuousOn ((hg i).1.continuousOn.comp hκ hκT)) ?_
    intro b hb
    simp only [(hg (σ i)).2 hb, (hg i).2 (hκS hb), hσ i b hb,
      κ, map_mul, map_pow, Complex.conj_conj]
  -- Compare Laurent forms at x₀ and τ x₀. Neither parameter must be fixed by τ.
  have heq (i j : Fin d) (hij : i ≠ j) (b : E × ℂ) (hb : b ∈ S) :
      b.2 ^ e (σ i) (σ j) (σ.injective.ne hij) * w (σ i) (σ j) (σ.injective.ne hij) b =
        conj ((conj b.2) ^ e i j hij * w i j hij (κ b)) := by
    rw [← hwform (σ i) (σ j) (σ.injective.ne hij) b hb,
      ← hwform i j hij (κ b) (hκS hb), hσ i b hb, hσ j b hb, map_sub]
  have hexp (i j : Fin d) (hij : i ≠ j) :
      e (σ i) (σ j) (σ.injective.ne hij) = e i j hij := by
    apply (AnalyticAt.laurent_eq_of_conj
      ((hwa (σ i) (σ j) (σ.injective.ne hij) _ ⟨x₀.2, mem_ball_self hR'⟩).restrictScalars
        (𝕜 := ℝ)) (hw0 _ _ _ _ ⟨x₀.2, mem_ball_self hR'⟩)
      ((hwa i j hij _ ⟨hτU x₀.2, mem_ball_self hR'⟩).restrictScalars (𝕜 := ℝ))
      (hw0 _ _ _ _ ⟨hτU x₀.2, mem_ball_self hR'⟩)
      (hτ.continuousAt (hU.mem_nhds x₀.2)) ?_).1
    filter_upwards [(hU.prod isOpen_ball).mem_nhds
      (x := (x₀.1, (0 : ℂ))) ⟨x₀.2, mem_ball_self hR'⟩] with b hb hb0
    exact heq i j hij b ⟨hb.1, hb.2, hb0⟩
  have hwfull (i j : Fin d) (hij : i ≠ j) :
      EqOn (w (σ i) (σ j) (σ.injective.ne hij))
        (fun b ↦ conj (w i j hij (κ b))) T := by
    refine TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton (c := (0 : ℂ)) isOpen_ball
      (hwa _ _ _).continuousOn
      (Complex.continuous_conj.comp_continuousOn ((hwa i j hij).continuousOn.comp hκ hκT)) ?_
    intro b hb
    have h := heq i j hij b hb
    rw [hexp i j hij, map_mul, map_zpow₀, Complex.conj_conj] at h
    exact mul_left_cancel₀ (zpow_ne_zero _ hb.2.2) h
  refine ⟨r, g, hra, hg, hr, σ, ⟨hσσ, hσ, hgfull, e, w, ?_⟩, ?_⟩
  · exact fun i j hij ↦ ⟨hwa i j hij, hw0 i j hij, hwform i j hij,
      hexp i j hij, hwfull i j hij⟩
  · intro σ' hσ'
    exact huniq σ' ⟨hσ'.1, hσ'.2.1⟩

end TauCeti.Polynomial
