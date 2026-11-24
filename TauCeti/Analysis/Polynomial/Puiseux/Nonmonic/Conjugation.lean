/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.Basic
public import TauCeti.Analysis.Polynomial.Conjugation

import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Polynomial.Puiseux.RootPermutation

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

The construction uses `exists_analyticOnNhd_nonmonic_powerSubstitution` and
`existsUnique_root_conj_perm_of_powerSubstitution`, the unique conjugation permutation of
continuous punctured root labels of a power-substituted family.

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
    hU hn hR hdvd hF hdeg hdiscr hu hu0 hlc
  obtain ⟨σ, ⟨hσσ, hσ⟩, huniq⟩ := existsUnique_root_conj_perm_of_powerSubstitution hR' hn hR
    (fun b hb ↦ hlc b hb ▸ mul_ne_zero (pow_ne_zero _ hb.2.2) (hu0 b ⟨hb.1, hb.2.1⟩))
    hτ hτU hττ hconj (fun i ↦ (hra i).continuousOn) hfac
  obtain ⟨hκ, hκT, -⟩ := TauCeti.continuousOn_mapsTo_prodMap_conj hτ hτU
  have hgfull := fun i ↦ TauCeti.eqOn_conj_extension (fun i ↦ (hga i).1.continuousOn)
    (fun i ↦ (hga i).2) hσ hκ hκT i
  refine ⟨r, g, hra, hga, hfac, σ, ⟨hσσ, hσ, hgfull⟩, ?_⟩
  intro σ' hσ'
  exact huniq σ' ⟨hσ'.1, hσ'.2.1⟩

end TauCeti.Polynomial
