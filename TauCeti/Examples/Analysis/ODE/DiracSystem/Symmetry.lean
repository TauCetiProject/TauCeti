/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Symmetry

/-!
# Checks for the conjugation of the Dirac system by `Ω`

* **A real constant potential.** For `q = c` real at `z = 0`, conjugating
  `M_c(t, 0) = diag(e^{ct}, e^{-ct})` by `Ω` gives `diag(e^{-ct}, e^{ct})`, which is the matrix of
  the potential `-c` (`TauCeti.Examples.DiracSystem.diracFundamentalMatrix_neg_const_zero`), in
  agreement with `TauCeti.diracFundamentalMatrix_ofReal_const_zero` at `-c`.
* **The free case.** For `q = 0` the fundamental matrix is a rotation and commutes with `Ω`, as
  `-0 = 0` requires (`TauCeti.Examples.DiracSystem.commute_diracFundamentalMatrix_zero_potential`).
  Reading the sign change as `M_{-q} = M_q⁻¹` would give the inverse rotation
  `[[cos tz, sin tz], [-sin tz, cos tz]]` at `q = 0`, which is a different matrix whenever
  `sin tz ≠ 0` (`TauCeti.Examples.DiracSystem.diracFundamentalMatrix_neg_zero_ne_inverse`).
-/

public section

open MeasureTheory Set Matrix Complex

namespace TauCeti.Examples.DiracSystem

/-- **Conjugation by `Ω` for a real constant potential.** At `z = 0`, the fundamental matrix of
the potential `-c` is `Ω diag(e^{ct}, e^{-ct}) Ω⁻¹ = diag(e^{-ct}, e^{ct})`. -/
theorem diracFundamentalMatrix_neg_const_zero (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    diracFundamentalMatrix (-fun _ ↦ (c : ℂ)) t 0 =
      !![(Real.exp (-(c * t)) : ℂ), 0; 0, (Real.exp (c * t) : ℂ)] := by
  rw [diracFundamentalMatrix_neg_potential
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) ht,
    diracFundamentalMatrix_ofReal_const_zero]
  simp

/-- The two computations of the fundamental matrix of the potential `-c` at `z = 0` agree: by
conjugation by `Ω` (`diracFundamentalMatrix_neg_const_zero`) and directly from the formula for a
real constant potential at `-c`. -/
example (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    diracFundamentalMatrix (-fun _ ↦ (c : ℂ)) t 0 =
      diracFundamentalMatrix (fun _ ↦ ((-c : ℝ) : ℂ)) t 0 := by
  rw [diracFundamentalMatrix_neg_const_zero c ht, diracFundamentalMatrix_ofReal_const_zero]
  simp

/-- **The free fundamental matrix commutes with `Ω`.** For the zero potential, `-0 = 0`, so the
sign-of-the-potential symmetry says that `M_0(t, z)` commutes with `Ω`. -/
theorem commute_diracFundamentalMatrix_zero_potential {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Commute !![0, 1; -1, 0] (diracFundamentalMatrix 0 t z) := by
  have h := mul_diracFundamentalMatrix_neg_potential
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) ht z (q := 0)
  rwa [neg_zero] at h

/-- **The sign change is not inversion.** At `q = 0`, `M_{-q}(t, z)` is the rotation
`M_0(t, z)`, not its inverse `[[cos tz, sin tz], [-sin tz, cos tz]]`, as soon as `sin tz ≠ 0`. -/
theorem diracFundamentalMatrix_neg_zero_ne_inverse {t : ℝ} (z : ℂ) (hs : sin (t * z) ≠ 0) :
    diracFundamentalMatrix (-0) t z ≠
      !![cos (t * z), sin (t * z); -sin (t * z), cos (t * z)] := by
  rw [neg_zero, diracFundamentalMatrix_zero_potential]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at h01
  exact hs (by linear_combination -h01 / 2)

end TauCeti.Examples.DiracSystem
