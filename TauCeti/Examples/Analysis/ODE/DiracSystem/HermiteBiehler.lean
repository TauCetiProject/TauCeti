/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Reflection
public import TauCeti.Analysis.ODE.DiracSystem.RealPotential

/-!
# Checks for the Hermite–Biehler functions of a Dirac system

* **The free case.** For `q = 0`, `E = e^{-itz}` and `E~ = -i e^{-itz}`, so `E# = e^{itz}` and
  `E~# = i e^{itz}` (`TauCeti.Examples.DiracSystem.conj_diracHermiteBiehler_zero_potential_conj`,
  `TauCeti.Examples.DiracSystem.conj_diracHermiteBiehlerDirichlet_zero_potential_conj`), and
  `E E~# - E~ E# = e^{-itz} (i e^{itz}) + i e^{-itz} e^{itz} = 2i`
  (`TauCeti.Examples.DiracSystem.diracHermiteBiehler_zero_potential_mul_conj_sub_mul_conj`).
* **A real constant potential at `z = 0`.** For `q = c` real, `E(t, 0) = e^{ct}` and
  `E~(t, 0) = -i e^{-ct}`
  (`TauCeti.Examples.DiracSystem.diracHermiteBiehler_ofReal_const_spectralParam_zero`,
  `TauCeti.Examples.DiracSystem.diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero`).
* **The sign of the potential at `z = 0`.** For `t ≥ 0`, `E_{-c}(t, 0) = e^{-ct} = i E~_c(t, 0)` and
  `E~_{-c}(t, 0) = -i e^{ct} = -i E_c(t, 0)`
  (`TauCeti.Examples.DiracSystem.diracHermiteBiehler_neg_const_spectralParam_zero`,
  `TauCeti.Examples.DiracSystem.diracHermiteBiehlerDirichlet_neg_const_spectralParam_zero`); the
  relation without the factor `i`, `E_{-q} = E~_q`, would give `-i e^{-ct}`.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate

namespace TauCeti.Examples.DiracSystem

/-! ### The free case -/

/-- In the free case, `E#(t, z) = e^{itz}`. -/
theorem conj_diracHermiteBiehler_zero_potential_conj (t : ℝ) (z : ℂ) :
    conj (diracHermiteBiehler 0 t (conj z)) = exp (I * (t * z)) := by
  rw [diracHermiteBiehler_zero_potential, ← exp_conj]
  congr 1
  simp

/-- In the free case, `E~#(t, z) = i e^{itz}`. -/
theorem conj_diracHermiteBiehlerDirichlet_zero_potential_conj (t : ℝ) (z : ℂ) :
    conj (diracHermiteBiehlerDirichlet 0 t (conj z)) = I * exp (I * (t * z)) := by
  rw [diracHermiteBiehlerDirichlet_zero_potential, map_mul, ← exp_conj]
  congr 1
  · simp
  · congr 1
    simp

/-- **The free-case determinant**, computed directly:
`E E~# - E~ E# = e^{-itz} (i e^{itz}) + i e^{-itz} e^{itz} = 2i`. -/
theorem diracHermiteBiehler_zero_potential_mul_conj_sub_mul_conj (t : ℝ) (z : ℂ) :
    diracHermiteBiehler 0 t z * conj (diracHermiteBiehlerDirichlet 0 t (conj z)) -
      diracHermiteBiehlerDirichlet 0 t z * conj (diracHermiteBiehler 0 t (conj z)) = 2 * I := by
  rw [conj_diracHermiteBiehler_zero_potential_conj,
    conj_diracHermiteBiehlerDirichlet_zero_potential_conj, diracHermiteBiehler_zero_potential,
    diracHermiteBiehlerDirichlet_zero_potential]
  have h : exp (-I * (t * z)) * exp (I * (t * z)) = 1 := by
    rw [← exp_add, neg_mul, neg_add_cancel, exp_zero]
  linear_combination (2 * I) * h

/-- The free-case determinant agrees with the general identity
`TauCeti.diracHermiteBiehler_mul_conj_sub_mul_conj`. -/
example {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    diracHermiteBiehler 0 t z * conj (diracHermiteBiehlerDirichlet 0 t (conj z)) -
      diracHermiteBiehlerDirichlet 0 t z * conj (diracHermiteBiehler 0 t (conj z)) = 2 * I :=
  diracHermiteBiehler_mul_conj_sub_mul_conj
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) ht z

/-! ### A real constant potential at `z = 0` -/

/-- For a real constant potential `c`, `E(t, 0) = e^{ct}`. -/
theorem diracHermiteBiehler_ofReal_const_spectralParam_zero (c t : ℝ) :
    diracHermiteBiehler (fun _ ↦ (c : ℂ)) t 0 = Real.exp (c * t) := by
  rw [diracHermiteBiehler_def, diracFundamentalMatrix_ofReal_const_spectralParam_zero]
  simp

/-- For a real constant potential `c`, `E~(t, 0) = -i e^{-ct}`. -/
theorem diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero (c t : ℝ) :
    diracHermiteBiehlerDirichlet (fun _ ↦ (c : ℂ)) t 0 = -I * Real.exp (-(c * t)) := by
  rw [diracHermiteBiehlerDirichlet_def, diracFundamentalMatrix_ofReal_const_spectralParam_zero]
  simp

/-! ### The sign of the potential at `z = 0` -/

/-- `E_{-c}(t, 0) = e^{-ct} = i E~_c(t, 0)`, by the sign-of-the-potential relation and by the
formula for the constant `-c`. -/
theorem diracHermiteBiehler_neg_const_spectralParam_zero (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    diracHermiteBiehler (-fun _ ↦ (c : ℂ)) t 0 = Real.exp (-(c * t)) ∧
      diracHermiteBiehler (-fun _ ↦ (c : ℂ)) t 0 =
        I * diracHermiteBiehlerDirichlet (fun _ ↦ (c : ℂ)) t 0 := by
  have h := diracHermiteBiehler_neg_potential
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) ht 0 (q := fun _ ↦ (c : ℂ))
  refine ⟨?_, h⟩
  rw [h, diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero]
  linear_combination (-(Real.exp (-(c * t)) : ℂ)) * I_sq

/-- `E~_{-c}(t, 0) = -i e^{ct} = -i E_c(t, 0)`. -/
theorem diracHermiteBiehlerDirichlet_neg_const_spectralParam_zero (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    diracHermiteBiehlerDirichlet (-fun _ ↦ (c : ℂ)) t 0 = -I * Real.exp (c * t) ∧
      diracHermiteBiehlerDirichlet (-fun _ ↦ (c : ℂ)) t 0 =
        -I * diracHermiteBiehler (fun _ ↦ (c : ℂ)) t 0 := by
  have h := diracHermiteBiehlerDirichlet_neg_potential
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) ht 0 (q := fun _ ↦ (c : ℂ))
  refine ⟨?_, h⟩
  rw [h, diracHermiteBiehler_ofReal_const_spectralParam_zero]

/-- The sign relation needs the factor `i`: `E_{-c}(t, 0) ≠ E~_c(t, 0)`, since `e^{-ct}` is real
and nonzero while `E~_c(t, 0) = -i e^{-ct}` is purely imaginary. -/
theorem diracHermiteBiehler_neg_const_spectralParam_zero_ne (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    diracHermiteBiehler (-fun _ ↦ (c : ℂ)) t 0 ≠
      diracHermiteBiehlerDirichlet (fun _ ↦ (c : ℂ)) t 0 := by
  rw [(diracHermiteBiehler_neg_const_spectralParam_zero c ht).1,
    diracHermiteBiehlerDirichlet_ofReal_const_spectralParam_zero]
  intro h
  simpa [exp_re, exp_im] using congrArg re h

end TauCeti.Examples.DiracSystem
