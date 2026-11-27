/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Polar
import TauCeti.Analysis.ODE.DiracSystem.ZeroFree

/-!
# The argument of the Dirac Hermite–Biehler function as a function of `(t, x)`

Let `q` be a potential, locally integrable on `[0, ∞)`, with Dirac fundamental matrix
`M_q(t, z)` (`TauCeti.diracFundamentalMatrix`) and Hermite–Biehler function
`E(t, z) = A(t, z) - i C(t, z)` (`TauCeti.diracHermiteBiehler`).

## Main results

* `TauCeti.exists_continuousOn_diracHermiteBiehler_eq_norm_mul_exp_prod`: `E(t, x)` has an
  argument `φ(t, x)`, jointly continuous on `[0, ∞) × ℝ`, with `φ(0, x) = 0` and
  `E(t, x) = |E(t, x)| e^{iφ(t, x)}`.
* `TauCeti.eqOn_of_diracHermiteBiehler_eq_norm_mul_exp_prod`: this argument is unique.

## Implementation notes

`E(t, z)` is jointly continuous in `(t, z)` (`TauCeti.continuousOn_diracHermiteBiehler_prod`)
and does not vanish for real `z = x` (`TauCeti.diracHermiteBiehler_ne_zero`), so
the continuous function `(t, x) ↦ E(max t 0, x)` on the simply connected plane has a continuous
logarithm `L` (`Complex.exists_continuousOn_eqOn_exp_comp`). As `E(0, x) = 1`, the imaginary part
of `L(t, x) - L(0, x)` is the argument, by the polar form `exp w = ‖exp w‖ e^{i Im w}`
(`Complex.norm_exp_mul_exp_im_mul_I`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix Complex Filter Topology

namespace TauCeti

variable {q : ℝ → ℂ}

/-- The function `(t, x) ↦ E(max t 0, x)` is continuous on the plane. -/
private theorem continuous_diracHermiteBiehler_max (hq : LocallyIntegrableOn q (Ici 0)) :
    Continuous fun p : ℝ × ℝ ↦ diracHermiteBiehler q (max p.1 0) p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  set T := max p₀.1 0 + 1
  have hqT : IntegrableOn q (Icc 0 T) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have hon : ContinuousOn (fun p : ℝ × ℝ ↦ diracHermiteBiehler q (max p.1 0) p.2)
      {p | p.1 < T} :=
    (continuousOn_diracHermiteBiehler_prod hqT).comp
      (f := fun p : ℝ × ℝ ↦ (max p.1 0, (p.2 : ℂ)))
      ((continuous_fst.max continuous_const).prodMk
        (continuous_ofReal.comp continuous_snd)).continuousOn fun p hp ↦
      ⟨⟨le_max_right _ _, max_le hp.le (by positivity)⟩, mem_univ _⟩
  refine hon.continuousAt (isOpen_lt continuous_fst continuous_const |>.mem_nhds ?_)
  simp only [mem_ofPred_eq, T]
  linarith [le_max_left p₀.1 0]

/-- **A jointly continuous argument of `E` on the real axis.** For `q` locally integrable on
`[0, ∞)`, there is `φ : ℝ × ℝ → ℝ`, continuous on `[0, ∞) × ℝ`, with `φ(0, x) = 0` and
`E(t, x) = |E(t, x)| e^{iφ(t, x)}` for `t ≥ 0` and real `x`. -/
theorem exists_continuousOn_diracHermiteBiehler_eq_norm_mul_exp_prod
    (hq : LocallyIntegrableOn q (Ici 0)) :
    ∃ φ : ℝ × ℝ → ℝ, ContinuousOn φ (Ici 0 ×ˢ univ) ∧ (∀ x, φ (0, x) = 0) ∧
      ∀ t, 0 ≤ t → ∀ x : ℝ,
        diracHermiteBiehler q t x = ‖diracHermiteBiehler q t x‖ * exp (I * φ (t, x)) := by
  set g : ℝ × ℝ → ℂ := fun p ↦ diracHermiteBiehler q (max p.1 0) p.2
  have hg0 : 0 ∉ g '' univ := by
    rintro ⟨p, -, hp⟩
    exact diracHermiteBiehler_ne_zero hq (le_max_right p.1 0) (z := p.2) (by simp) hp
  obtain ⟨L, hLc, hLg⟩ := exists_continuousOn_eqOn_exp_comp
    (convex_univ.isSimplyConnected univ_nonempty)
    isOpen_univ (continuous_diracHermiteBiehler_max hq).continuousOn hg0
  have hLc' : Continuous L := continuousOn_univ.1 hLc
  have hexp (p : ℝ × ℝ) : exp (L p) = g p := hLg (mem_univ p)
  refine ⟨fun p ↦ (L p).im - (L (0, p.2)).im, (Complex.continuous_im.comp hLc' |>.sub
    (Complex.continuous_im.comp (hLc'.comp (by fun_prop)))).continuousOn, fun x ↦ sub_self _,
    fun t ht x ↦ ?_⟩
  -- `exp (L (0, x)) = E(0, x) = 1`, so the polar form of `exp (L (0, x))` gives
  -- `exp (i Im L (0, x)) = 1`.
  have h0 : exp (L (0, x)) = 1 := by simp [hexp, g, diracHermiteBiehler_zero]
  have hI0 : exp (I * (L (0, x)).im) = 1 := by
    have := norm_exp_mul_exp_im_mul_I (L (0, x))
    rwa [h0, norm_one, ofReal_one, one_mul, mul_comm] at this
  have hgt : g (t, x) = diracHermiteBiehler q t x := by simp [g, max_eq_left ht]
  have hshift : exp (I * ((L (t, x)).im - (L (0, x)).im : ℝ)) = exp (I * (L (t, x)).im) := by
    rw [ofReal_sub, mul_sub, exp_sub, hI0, div_one]
  rw [hshift, ← hgt, ← hexp, mul_comm I]
  exact (norm_exp_mul_exp_im_mul_I _).symm

/-- **Uniqueness of the argument.** For `q` locally integrable on `[0, ∞)`, two functions
continuous on `[0, ∞) × ℝ`, vanishing at `t = 0` and arguments of `E(t, x)` there, agree on
`[0, ∞) × ℝ`. -/
theorem eqOn_of_diracHermiteBiehler_eq_norm_mul_exp_prod (hq : LocallyIntegrableOn q (Ici 0))
    {φ ψ : ℝ × ℝ → ℝ} (hφ : ContinuousOn φ (Ici 0 ×ˢ univ)) (hψ : ContinuousOn ψ (Ici 0 ×ˢ univ))
    (hφ0 : ∀ x, φ (0, x) = 0) (hψ0 : ∀ x, ψ (0, x) = 0)
    (hφE : ∀ t, 0 ≤ t → ∀ x : ℝ,
      diracHermiteBiehler q t x = ‖diracHermiteBiehler q t x‖ * exp (I * φ (t, x)))
    (hψE : ∀ t, 0 ≤ t → ∀ x : ℝ,
      diracHermiteBiehler q t x = ‖diracHermiteBiehler q t x‖ * exp (I * ψ (t, x))) :
    EqOn φ ψ (Ici 0 ×ˢ univ) := by
  intro p hp
  have h := Contour.sub_eq_sub_of_eq_norm_mul_exp (s := Ici 0 ×ˢ univ)
    (f := fun r : ℝ × ℝ ↦ diracHermiteBiehler q r.1 r.2) (x := (0, p.2))
    ((convex_Ici 0).prod convex_univ).isPreconnected ⟨le_rfl, mem_univ _⟩ hp
    (fun r hr ↦ diracHermiteBiehler_ne_zero hq hr.1 (by simp)) hφ hψ
    (fun r hr ↦ hφE r.1 hr.1 r.2) (fun r hr ↦ hψE r.1 hr.1 r.2)
  simpa [hφ0, hψ0] using h

end TauCeti
