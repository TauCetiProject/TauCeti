/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
import TauCeti.Analysis.LaplaceTransform.WindowedLandau
import TauCeti.Analysis.MellinTransform.Windows
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.ErrorTransform
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed

/-!
# Windowed lower bounds for the prime ideal counting error

A one-sided lower bound for `ψ_K(x) - x` on arbitrarily far-out power windows implies
zero-freeness of the Dedekind zeta function. The mean version controls only the weighted
negative part of the error on those windows. The sign matters: the transform of
`x - ψ_K(x)` has positive residues at real poles, as required by the windowed Landau theorem
of Levent Alpöge (`Deduction.landau_window`).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Interval

namespace TauCeti

open LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- If the negative part of `ψ_K(x) - x`, weighted by `x ^ (-θ - 1)`, has integral at most
`Y ^ η` on arbitrarily far-out windows `[Y, Y ^ L]` for each `η > 0`, then the Dedekind
zeta function has no zeros to the right of `θ`. -/
theorem zeroFreeRightOf_dedekindZetaC_of_primePsi_window_integral_lower {θ L : ℝ}
    (hθ : 0 ≤ θ) (hL : 1 < L)
    (hwin : ∀ η : ℝ, 0 < η → ∃ᶠ Y in atTop,
      (∫ x in Y..(Y ^ L), max (x - primePsi K univ x) 0 * x ^ (-(θ + 1))) ≤ Y ^ η) :
    ZeroFreeRightOf θ (dedekindZetaC K) := by
  let F := primePsiErrorTransform K
  have hpole {s : ℂ} (hs : 0 < s.re) (hp : meromorphicOrderAt F s < 0) :
      ∃ m : ℤ, 0 < m ∧ meromorphicOrderAt F s = -1 ∧
        meromorphicTrailingCoeffAt F s = -(m : ℂ) / s := by
    have hs₀ := ne_zero_of_re_pos hs
    have hz := (meromorphicOrderAt_primePsiErrorTransform_neg_iff K hs₀).mp hp
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (meromorphicOrderAt_dedekindZetaC_ne_top K s)
    have h := primePsiErrorTransform_simplePole K hs₀ hz
    rw [← hm] at hz h
    exact ⟨m, WithTop.coe_lt_coe.mp hz, h.1, by rw [h.2, WithTop.untop₀_coe]⟩
  have hF : MeromorphicOn (-F) {s | θ < s.re} := fun s _ ↦
    ((meromorphicNFOn_primePsiErrorTransform K) (mem_univ s)).meromorphicAt.neg
  rw [zeroFreeRightOf_iff]
  intro s hs
  suffices hn : 0 ≤ meromorphicOrderAt (-F) s by
    exact le_of_not_gt fun hz ↦ hn.not_gt <| by
      rw [← meromorphicOrderAt_neg]
      exact (meromorphicOrderAt_primePsiErrorTransform_neg_iff K
        (ne_zero_of_re_pos (hθ.trans_lt hs))).mpr hz
  refine meromorphicOrderAt_nonneg_of_hasLaplace_window_of_simple_poles
    (g := fun u ↦ Real.exp u - primePsi K univ (Real.exp u)) (A := 1) (B := 1) hL
    (Eventually.of_forall fun u ↦ ?_) hF (fun z hz ↦ ?_) ?_ ?_ (fun η hη ↦ ?_) s hs
  · simpa only [one_mul] using max_le (sub_le_self _ (primePsi_nonneg _ _)) (Real.exp_pos u).le
  · exact (hasLaplace_primePsi_sub_exp K hz).neg.congr_ae
      (Eventually.of_forall fun _ ↦ by simp [neg_sub])
  · intro s hs hp
    rw [← meromorphicOrderAt_neg] at hp ⊢
    exact (hpole (hθ.trans_lt hs) hp).choose_spec.2.1
  · intro β hβ h
    have hβ₀ := hθ.trans_lt hβ
    have hp : meromorphicOrderAt F (β : ℂ) < 0 := by
      rw [meromorphicOrderAt_neg, h]
      exact WithTop.coe_lt_coe.mpr (neg_one_lt_zero : (-1 : ℤ) < 0)
    obtain ⟨m, hm, _, hc⟩ := hpole (by simpa only [ofReal_re] using hβ₀) hp
    rw [Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one h,
      meromorphicTrailingCoeffAt_neg, hc, neg_div, neg_neg]
    rw [← ofReal_intCast, ← ofReal_div, ofReal_re]
    exact div_pos (Int.cast_pos.mpr hm) hβ₀
  · exact (frequently_integral_mul_rpow_le_rpow_iff
      (fun x ↦ max (x - primePsi K univ x) 0) L θ η).mp (hwin η hη)

/-- A lower bound `ψ_K(x) - x ≥ -C * x ^ θ` on windows `[Y, Y ^ L]` at arbitrarily large
scales `Y`, for a fixed exponent `L > 1`, gives a zero-free half-plane `Re s > θ` for the
Dedekind zeta function. -/
theorem zeroFreeRightOf_dedekindZetaC_of_primePsi_hasWindows_lower {θ L C : ℝ}
    (hθ : 0 ≤ θ) (hL : 1 < L)
    (hwin : HasWindows {x | -(C * x ^ θ) ≤ primePsi K univ x - x} L) :
    ZeroFreeRightOf θ (dedekindZetaC K) := by
  have hw : HasWindows {x | x - primePsi K univ x ≤ C * x ^ θ} L :=
    hwin.mono fun _ hx ↦ by
      rw [mem_ofPred_eq] at hx ⊢
      linarith
  exact zeroFreeRightOf_dedekindZetaC_of_primePsi_window_integral_lower K hθ hL
    (fun _ hη ↦ hw.frequently_integral_mul_rpow_le_rpow hη)

end TauCeti
