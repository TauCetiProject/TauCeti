/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.LaplaceTransform.WindowedLandau
public import TauCeti.Analysis.MellinTransform.Windows
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.Analysis.LaplaceTransform.Window.Landau
import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Windowed Landau theorem for upper Mellin transforms

A bound on the positive part on arbitrarily far-out power windows `[Y, Y ^ L]` excludes
poles of an upper Mellin transform if they are simple with positive residue at real poles.
This is the Mellin form of the windowed Laplace criterion, using `y = exp u` to transfer
both the transform and the window integrals. In particular, a pointwise upper power bound
on those windows suffices. Without the sign and simplicity assumptions, the same windows
force any nonempty set of poles in the half-plane to have a real rightmost pole with negative
leading coefficient. The latter form assumes only absolute convergence on the initial
half-plane.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Interval

namespace TauCeti

/-- An upper Mellin transform continued meromorphically to `re z > θ` has no poles there if
all poles there are simple, all real poles there have positive real part of the residue, and
the positive-part Mellin integral on `[Y, Y ^ L]` is at most `Y ^ η` for arbitrarily large `Y`
for each `η > 0`. The integral representing `F` on `re z > A` must converge absolutely;
the upper growth bound on `G` is needed only almost everywhere. -/
theorem meromorphicOrderAt_nonneg_of_mellin_window_of_simple_poles
    {G : ℝ → ℝ} {F : ℂ → ℂ} {A θ L B : ℝ} (hL : 1 < L)
    (hG : ∀ᵐ y ∂volume.restrict (Ioi 1), max (G y) 0 ≤ B * y ^ A)
    (hF : MeromorphicOn F {z | θ < z.re})
    (hM : ∀ z : ℂ, A < z.re →
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) = F z)
    (hsimple : ∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → meromorphicOrderAt F z = -1)
    (hres : ∀ β : ℝ, θ < β → meromorphicOrderAt F (β : ℂ) = -1 → 0 < (Contour.residue F β).re)
    (hwin : ∀ η : ℝ, 0 < η → ∃ᶠ Y in atTop,
      (∫ y in Y..(Y ^ L), max (G y) 0 * y ^ (-(θ + 1))) ≤ Y ^ η) :
    ∀ ρ : ℂ, θ < ρ.re → 0 ≤ meromorphicOrderAt F ρ := by
  refine meromorphicOrderAt_nonneg_of_hasLaplace_window_of_simple_poles
    (g := G ∘ Real.exp) (A := A) (B := B) hL ?_ hF (fun z hz ↦ ?_) hsimple hres fun η hη ↦ ?_
  · have hg := (ae_restrict_iff' measurableSet_Ioi).mp hG
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [quasiMeasurePreserving_exp.ae (hg.filter_mono ae_restrict_le)] with u hu hu₀
    simpa only [Function.comp_apply, ← Real.exp_mul, mul_comm u A] using
      hu (Real.one_lt_exp_iff.mpr hu₀)
  · exact (hasLaplace_comp_exp_iff (fun y ↦ (G y : ℂ)) z (F z) 0).mpr
      (by simpa only [Real.exp_zero, smul_eq_mul] using hM z hz)
  · exact (frequently_integral_mul_rpow_le_rpow_iff (fun y ↦ max (G y) 0) L θ η).mp (hwin η hη)

/-- A pointwise upper power bound on arbitrarily far-out power windows suffices for the
windowed Landau criterion for a continued upper Mellin transform with simple poles. -/
theorem meromorphicOrderAt_nonneg_of_mellin_hasWindows_of_simple_poles
    {G : ℝ → ℝ} {F : ℂ → ℂ} {A θ L B C : ℝ} (hL : 1 < L)
    (hG : ∀ᵐ y ∂volume.restrict (Ioi 1), max (G y) 0 ≤ B * y ^ A)
    (hF : MeromorphicOn F {z | θ < z.re})
    (hM : ∀ z : ℂ, A < z.re →
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) = F z)
    (hsimple : ∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → meromorphicOrderAt F z = -1)
    (hres : ∀ β : ℝ, θ < β → meromorphicOrderAt F (β : ℂ) = -1 → 0 < (Contour.residue F β).re)
    (hwin : HasWindows {y | G y ≤ C * y ^ θ} L) :
    ∀ ρ : ℂ, θ < ρ.re → 0 ≤ meromorphicOrderAt F ρ := by
  exact meromorphicOrderAt_nonneg_of_mellin_window_of_simple_poles hL hG hF hM hsimple hres
    (fun _ hη ↦ hwin.frequently_integral_mul_rpow_le_rpow hη)

/-- **Windowed Landau theorem for the upper Mellin transform.** Suppose `F` continues the
absolutely convergent upper Mellin transform of `G` from `Re z > A` to `Re z > θ`. If for each
`η > 0` there are arbitrarily far-out power windows `[Y, Y ^ L]` on which the positive-part
integral at exponent `θ` is at most `Y ^ η`, then either there are no poles in `Re z > θ` or
there is a real rightmost pole there with a strictly negative real leading Laurent coefficient.
No pointwise growth bound on `G` is required. -/
theorem meromorphicOrderAt_nonneg_or_exists_rightmost_real_pole_of_mellin_window
    {G : ℝ → ℝ} {F : ℂ → ℂ} {A θ L : ℝ} (hL : 1 < L)
    (hF : MeromorphicOn F {z | θ < z.re})
    (hM : ∀ z : ℂ, A < z.re →
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) = F z)
    (hwin : ∀ η : ℝ, 0 < η → ∃ᶠ Y in atTop,
      (∫ y in Y..(Y ^ L), max (G y) 0 * y ^ (-(θ + 1))) ≤ Y ^ η) :
    (∀ z : ℂ, θ < z.re → 0 ≤ meromorphicOrderAt F z) ∨
      ∃ β ∈ Ioc θ A, meromorphicOrderAt F (β : ℂ) < 0 ∧
        (∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → z.re ≤ β) ∧
        (meromorphicTrailingCoeffAt F (β : ℂ)).re < 0 ∧
        (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 := by
  refine meromorphicOrderAt_nonneg_or_exists_rightmost_real_pole_of_hasLaplace_window
    (g := G ∘ Real.exp) hL hF (fun z hz ↦ ?_) fun η hη ↦ ?_
  · exact (hasLaplace_comp_exp_iff (fun y ↦ (G y : ℂ)) z (F z) 0).mpr
      (by simpa only [Real.exp_zero, smul_eq_mul] using hM z hz)
  · exact (frequently_integral_mul_rpow_le_rpow_iff (fun y ↦ max (G y) 0) L θ η).mp (hwin η hη)

/-- A pointwise upper power bound on arbitrarily far-out power windows forces a real rightmost
pole with negative leading Laurent coefficient, if the continued upper Mellin transform has
any pole to the right of the exponent. -/
theorem meromorphicOrderAt_nonneg_or_exists_rightmost_real_pole_of_mellin_hasWindows
    {G : ℝ → ℝ} {F : ℂ → ℂ} {A θ L C : ℝ} (hL : 1 < L)
    (hF : MeromorphicOn F {z | θ < z.re})
    (hM : ∀ z : ℂ, A < z.re →
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, (y : ℂ) ^ (-(z + 1)) * (G y : ℂ)) = F z)
    (hwin : HasWindows {y | G y ≤ C * y ^ θ} L) :
    (∀ z : ℂ, θ < z.re → 0 ≤ meromorphicOrderAt F z) ∨
      ∃ β ∈ Ioc θ A, meromorphicOrderAt F (β : ℂ) < 0 ∧
        (∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → z.re ≤ β) ∧
        (meromorphicTrailingCoeffAt F (β : ℂ)).re < 0 ∧
        (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 :=
  meromorphicOrderAt_nonneg_or_exists_rightmost_real_pole_of_mellin_window hL hF hM
    (fun _ hη ↦ hwin.frequently_integral_mul_rpow_le_rpow hη)

end TauCeti
