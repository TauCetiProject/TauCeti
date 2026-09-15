/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Injectivity
public import TauCeti.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# Analytic rank and conductor of a newform

For a positive-weight newform, its coefficient Dirichlet series has the entire continuation
`ModularForm.L`.  This file defines the analytic rank to be the order of vanishing of that
continuation at the central point `k / 2`.  The continuation is not identically zero, because
its Dirichlet coefficients have first coefficient one.  Consequently the order is finite and
is faithfully represented by a natural number.

The analytic conductor is stated in the arithmetic `s`-coordinate.  If
`s_an = s - (k - 1) / 2` is the analytic normalization, its two archimedean parameters are
`s_an + (k - 1) / 2` and `s_an + (k + 1) / 2`.  Thus

`q(f, s) = N (|s_an + (k - 1) / 2| + 3) (|s_an + (k + 1) / 2| + 3)`.

The constant `3` and this normalization follow Iwaniec--Kowalski, §5.1 and (5.7).

## Main definitions

* `HeckeRing.GL2.Newform.analyticRank`: the order of vanishing at `k / 2`.
* `HeckeRing.GL2.Newform.analyticConductorAt`: the analytic conductor at `s`.
* `HeckeRing.GL2.Newform.analyticConductor`: the conductor at the central point.

## Main results

* `HeckeRing.GL2.Newform.L_ne_zero`: the entire continuation is not identically zero.
* `HeckeRing.GL2.Newform.analyticOrderAt_L_ne_top`: its order is finite at every point.
* `HeckeRing.GL2.Newform.analyticRank_eq_analyticOrderNatAt`: any entire continuation agreeing
  with the coefficient series on its convergence half-plane gives the same analytic rank.
* `HeckeRing.GL2.Newform.analyticRank_eq_zero_iff`: rank zero is equivalent to nonvanishing at
  the central point.
* `HeckeRing.GL2.Newform.analyticConductorAt_eq`: the conductor in the arithmetic coordinate.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1, especially (5.7).
-/

public section

noncomputable section

open Filter LSeries UpperHalfPlane

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The entire continuation of the L-function of a newform is not identically zero.

Indeed, were it zero, the coefficient L-series would vanish for all sufficiently large real
arguments.  Injectivity of Dirichlet series would then force every positive-index coefficient
to vanish, contradicting the normalization `a₁ = 1`. -/
theorem L_ne_zero (f : Newform N k) (hk : 0 < k) :
    ModularForm.L hk f.toCuspForm ≠ 0 := by
  intro hL
  have hzero :
      (fun x : ℝ ↦ LSeries (fun n ↦
        (qExpansion ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty f.toCuspForm).coeff n) x)
          =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop ((k : ℝ) / 2 + 2)] with x hx
    have hs : (k : ℝ) / 2 + 1 < x := by linarith
    simpa [hL] using CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  rcases LSeries_eventually_eq_zero_iff'.mp hzero with hcoeff | habscissa
  · have h := hcoeff 1 one_ne_zero
    have hnorm :
        (qExpansion ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty f.toCuspForm).coeff 1 = 1 := by
      simpa only [strictWidthInfty_Gamma1] using f.isNorm
    rw [hnorm] at h
    exact one_ne_zero h
  · have hfinite :=
      (CuspForm.hasEntireExtension_qExpansion_coeff hk f.toCuspForm).abscissa_lt_top
    rw [habscissa] at hfinite
    exact (lt_irrefl ⊤ hfinite).elim

/-- The analytic order of the entire L-function of a newform is finite at every point. -/
theorem analyticOrderAt_L_ne_top (f : Newform N k) (hk : 0 < k) (s : ℂ) :
    analyticOrderAt (ModularForm.L hk f.toCuspForm) s ≠ ⊤ := by
  intro htop
  apply f.L_ne_zero hk
  exact (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s fun _ ↦
    (CuspForm.differentiable_L hk f.toCuspForm).analyticAt _).mp htop

/-- The **analytic rank** of a positive-weight newform is the order of vanishing of its entire
L-function at the central point `s = k / 2`. -/
def analyticRank (f : Newform N k) (hk : 0 < k) : ℕ :=
  analyticOrderNatAt (ModularForm.L hk f.toCuspForm) ((k : ℂ) / 2)

/-- The defining equation for the analytic rank. -/
lemma analyticRank_def (f : Newform N k) (hk : 0 < k) :
    f.analyticRank hk =
      analyticOrderNatAt (ModularForm.L hk f.toCuspForm) ((k : ℂ) / 2) :=
  (rfl)

/-- Any entire continuation agreeing with the coefficient Dirichlet series on the known
convergence half-plane computes the analytic rank.  In particular, the definition is independent
of the chosen construction of analytic continuation. -/
theorem analyticRank_eq_analyticOrderNatAt (f : Newform N k) (hk : 0 < k)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFL : ∀ {s : ℂ}, (k : ℝ) / 2 + 1 < s.re →
      F s = LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) :
    f.analyticRank hk = analyticOrderNatAt F ((k : ℂ) / 2) := by
  have hEq : F = ModularForm.L hk f.toCuspForm := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (CuspForm.differentiable_L hk f.toCuspForm)) (by
          refine Filter.eventuallyEq_iff_exists_mem.mpr
            ⟨{s : ℂ | (k : ℝ) / 2 + 1 < s.re}, ?_, ?_⟩
          · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
              simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
              linarith : (((k : ℝ) / 2 + 2 : ℝ) : ℂ) ∈
                {s : ℂ | (k : ℝ) / 2 + 1 < s.re})
          · intro s hs
            exact hFL hs |>.trans (by
                simpa using CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs))
  rw [analyticRank_def, hEq]

/-- A newform has analytic rank zero exactly when its entire L-function does not vanish at the
central point. -/
theorem analyticRank_eq_zero_iff (f : Newform N k) (hk : 0 < k) :
    f.analyticRank hk = 0 ↔ ModularForm.L hk f.toCuspForm ((k : ℂ) / 2) ≠ 0 := by
  rw [analyticRank_def, ← Nat.cast_inj (R := ℕ∞), Nat.cast_analyticOrderNatAt
    (f.analyticOrderAt_L_ne_top hk ((k : ℂ) / 2)), Nat.cast_zero]
  exact ((CuspForm.differentiable_L hk f.toCuspForm).analyticAt ((k : ℂ) / 2))
    |>.analyticOrderAt_eq_zero

/-- A newform has positive analytic rank exactly when its entire L-function vanishes at the
central point. -/
theorem analyticRank_pos_iff (f : Newform N k) (hk : 0 < k) :
    0 < f.analyticRank hk ↔ ModularForm.L hk f.toCuspForm ((k : ℂ) / 2) = 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, f.analyticRank_eq_zero_iff hk, not_not]

/-- The analytic conductor of a newform at an arithmetic parameter `s`.

Writing `s_an = s - (k - 1) / 2`, the two norm factors are the archimedean parameters
`s_an + (k - 1) / 2` and `s_an + (k + 1) / 2`. -/
def analyticConductorAt (_f : Newform N k) (s : ℂ) : ℝ :=
  let s_an := s - ((k : ℂ) - 1) / 2
  (N : ℝ) * (‖s_an + ((k : ℂ) - 1) / 2‖ + 3) *
    (‖s_an + ((k : ℂ) + 1) / 2‖ + 3)

/-- In the arithmetic `s`-coordinate, the two archimedean parameters simplify to `s` and
`s + 1`. -/
theorem analyticConductorAt_eq (f : Newform N k) (s : ℂ) :
    f.analyticConductorAt s =
      (N : ℝ) * (‖s‖ + 3) * (‖s + 1‖ + 3) := by
  simp only [analyticConductorAt]
  congr 2 <;> congr 1 <;> ring_nf

/-- The analytic conductor of a newform is its analytic conductor at the central point
`s = k / 2`. -/
def analyticConductor (f : Newform N k) : ℝ :=
  f.analyticConductorAt ((k : ℂ) / 2)

/-- The defining equation for the central analytic conductor. -/
lemma analyticConductor_def (f : Newform N k) :
    f.analyticConductor = f.analyticConductorAt ((k : ℂ) / 2) :=
  (rfl)

/-- The central analytic conductor in the arithmetic coordinate. -/
theorem analyticConductor_eq (f : Newform N k) :
    f.analyticConductor =
      (N : ℝ) * (‖(k : ℂ) / 2‖ + 3) * (‖(k : ℂ) / 2 + 1‖ + 3) := by
  rw [analyticConductor_def, analyticConductorAt_eq]

/-- The analytic conductor at every parameter is strictly positive. -/
theorem analyticConductorAt_pos (f : Newform N k) (s : ℂ) :
    0 < f.analyticConductorAt s := by
  rw [f.analyticConductorAt_eq s]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  positivity

/-- The central analytic conductor is strictly positive. -/
theorem analyticConductor_pos (f : Newform N k) : 0 < f.analyticConductor := by
  rw [analyticConductor_def]
  exact f.analyticConductorAt_pos _

end HeckeRing.GL2.Newform
