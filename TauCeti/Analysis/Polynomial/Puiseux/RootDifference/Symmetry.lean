/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.RootDifference
public import TauCeti.Analysis.Polynomial.Conjugation
public import TauCeti.Analysis.Analytic.Laurent.Conjugation
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Polynomial.Puiseux.RootPermutation

/-!
# Global conjugation symmetry of nonmonic root differences

Construct nonmonic Puiseux branches together with global Laurent unit forms for their
pairwise differences and a single involution implementing conjugation. Conjugate pairs of
labels have equal integer difference exponents and conjugate units on the whole product,
including the exceptional hyperplane. The parameter involution need not fix base points.

The branches and difference units come from
`TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_root_sub_eq_zpow_mul_unit`.
The conjugation permutation comes from the complete distinct punctured root labelling, by
`TauCeti.Polynomial.existsUnique_root_conj_perm_of_powerSubstitution`;
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
  obtain ⟨σ, ⟨hσσ, hσ⟩, huniq⟩ := existsUnique_root_conj_perm_of_powerSubstitution hR' hn hR
    (fun b hb ↦ hlead b hb ▸ mul_ne_zero (pow_ne_zero _ hb.2.2) (hu0 b ⟨hb.1, hb.2.1⟩))
    hτ hτU hττ hconj (fun i ↦ (hra i).continuousOn) hr
  obtain ⟨hκ, hκT, hκS⟩ := TauCeti.continuousOn_mapsTo_prodMap_conj hτ hτU
  have hgfull (i : Fin d) : EqOn (g (σ i)) (fun b ↦ conj (g i (τ b.1, conj b.2)))
      (U ×ˢ ball 0 R') :=
    TauCeti.eqOn_conj_extension (τ := τ) (fun i ↦ (hg i).1.continuousOn) (fun i ↦ (hg i).2) hσ
      hκ hκT i
  have hsymm (i j : Fin d) (hij : i ≠ j) :
      e (σ i) (σ j) (σ.injective.ne hij) = e i j hij ∧
        ∀ b ∈ U ×ˢ ball 0 R',
          w (σ i) (σ j) (σ.injective.ne hij) b =
            conj (w i j hij (τ b.1, conj b.2)) := by
    obtain ⟨x₀⟩ : Nonempty U := inferInstance
    refine AnalyticOnNhd.laurent_eq_of_conj hU hR' ⟨x₀, x₀.property⟩ hτ hτU
      ((hwa _ _ _).restrictScalars (𝕜 := ℝ)) (hw0 _ _ _) ((hwa i j hij).restrictScalars (𝕜 := ℝ))
      (hw0 i j hij) fun b hb ↦ ?_
    rw [← hwform (σ i) (σ j) (σ.injective.ne hij) b hb,
      ← hwform i j hij (τ b.1, conj b.2) (hκS hb), hσ i b hb, hσ j b hb, map_sub]
  refine ⟨r, g, hra, hg, hr, σ, ⟨hσσ, hσ, hgfull, e, w, fun i j hij ↦ ?_⟩, ?_⟩
  · exact ⟨hwa i j hij, hw0 i j hij, hwform i j hij, (hsymm i j hij).1, (hsymm i j hij).2⟩
  · intro σ' hσ'
    exact huniq σ' ⟨hσ'.1, hσ'.2.1⟩

end TauCeti.Polynomial
