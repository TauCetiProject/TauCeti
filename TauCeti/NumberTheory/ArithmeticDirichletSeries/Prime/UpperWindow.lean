/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Windows
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.ErrorTransform
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Rat
import TauCeti.Analysis.LaplaceTransform.WindowedLandau
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
import TauCeti.NumberTheory.LFunctions.Zeros.RiemannHypotheses.HalfPlane
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# Upper Chebyshev bounds on scale windows

An upper bound for the prime ideal counting error `ψ_K(x) - x` on arbitrarily far-out
power windows leaves at most the obstruction of a rightmost real zero of Dedekind zeta.
For the rational field there are no real zeros in the relevant interval. The proof uses
windowed Landau for the continued Laplace transform of the error in the variable `log x`.
-/

public section

open Complex Filter MeasureTheory Set
open scoped ComplexOrder

namespace TauCeti

open LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- An upper bound of order `x ^ θ` for `ψ_K(x) - x` on arbitrarily far-out power windows
implies either zero-freeness in `Re s > θ` or a rightmost real zero of `ζ_K` in `(θ, 1)`. -/
theorem zeroFreeRightOf_or_exists_rightmost_real_zero_of_hasWindows_primePsi_sub_le_rpow
    {θ C L : ℝ} (hθ : 0 ≤ θ) (hL : 1 < L)
    (hwin : HasWindows {x | primePsi K univ x - x ≤ C * x ^ θ} L) :
    ZeroFreeRightOf θ (dedekindZetaC K) ∨
      ∃ β ∈ Ioo θ 1, 0 < meromorphicOrderAt (dedekindZetaC K) (β : ℂ) ∧
        ZeroFreeRightOf β (dedekindZetaC K) := by
  rw [zeroFreeRightOf_dedekindZetaC_iff_forall_meromorphicOrderAt_primePsiErrorTransform_nonneg
    K hθ]
  by_cases hp : ∃ ρ : ℂ,
      θ < ρ.re ∧ meromorphicOrderAt (primePsiErrorTransform K) ρ < 0
  · obtain ⟨B, hB₀, hB⟩ := exists_primePsi_univ_le_mul K
    have hg : ∀ᵐ u ∂volume.restrict (Ioi 0),
        max (primePsi K univ (Real.exp u) - Real.exp u) 0 ≤ B * Real.exp (1 * u) := by
      refine Eventually.of_forall fun u ↦ ?_
      rw [one_mul]
      refine max_le ?_ (mul_nonneg hB₀ (Real.exp_pos u).le)
      exact (sub_le_self _ (Real.exp_pos u).le).trans (hB _ (Real.exp_pos u).le)
    have hw (η : ℝ) (hη : 0 < η) :=
      (frequently_integral_mul_rpow_le_rpow_iff (fun x ↦ max (primePsi K univ x - x) 0) L θ η).mp
        (hwin.frequently_integral_mul_rpow_le_rpow hη)
    obtain ⟨β, hβ, hβpole, hmax, -⟩ :=
      exists_rightmost_real_pole_of_hasLaplace_window_of_ae_le_exp hL hg
        ((meromorphicNFOn_primePsiErrorTransform K).meromorphicOn.mono_set (subset_univ _))
        (fun _ hs ↦ hasLaplace_primePsi_sub_exp K hs) hw hp
    have hβ₀ := hθ.trans_lt hβ.1
    have hβne : β ≠ 1 := by
      rintro rfl
      exact hβpole.not_ge (by simpa using
        (analyticAt_primePsiErrorTransform_one K).meromorphicOrderAt_nonneg)
    exact .inr ⟨β, ⟨hβ.1, hβ.2.lt_of_ne hβne⟩,
      (meromorphicOrderAt_primePsiErrorTransform_neg_iff K (ofReal_ne_zero.mpr hβ₀.ne')).mp hβpole,
      (zeroFreeRightOf_dedekindZetaC_iff_forall_meromorphicOrderAt_primePsiErrorTransform_nonneg
        K hβ₀.le).mpr hmax⟩
  · exact .inl fun ρ hρ ↦ le_of_not_gt fun h ↦ hp ⟨ρ, hρ, h⟩

/-- For the rational field, an upper bound of order `x ^ θ` for `ψ(x) - x` on arbitrarily
far-out power windows excludes zeros of Riemann zeta to the right of `θ`. -/
theorem zeroFreeRightOf_riemannZeta_of_hasWindows_psi_sub_le_rpow {θ C L : ℝ}
    (hθ : 0 ≤ θ) (hL : 1 < L) (hwin : HasWindows {x | Chebyshev.psi x - x ≤ C * x ^ θ} L) :
    ZeroFreeRightOf θ riemannZeta := by
  rcases zeroFreeRightOf_or_exists_rightmost_real_zero_of_hasWindows_primePsi_sub_le_rpow ℚ hθ hL
    (by simpa only [primePsi_rat_univ] using hwin) with h | ⟨β, hβ, hz, -⟩
  · exact zeroFreeRightOf_dedekindZetaC_rat_iff.mp h
  rw [meromorphicOrderAt_congr (dedekindZetaC_rat_eventuallyEq_riemannZeta β)] at hz
  exact ((riemannZeta_lt_zero (hθ.trans_lt hβ.1) hβ.2).ne
    (meromorphicOrderAt_riemannZeta_pos_iff.mp hz)).elim

end TauCeti
