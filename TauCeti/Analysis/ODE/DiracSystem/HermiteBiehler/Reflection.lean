/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Basic
public import TauCeti.Analysis.ODE.DiracSystem.Symmetry
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Reflections of the Hermite–Biehler functions of a Dirac system

Let `M_q(t, z) = [[A, B], [C, D]]` be the fundamental matrix of the Dirac system with potential `q`,
locally integrable on `[0, ∞)`, and let `E = A - iC` and `E~ = B - iD` be its Hermite–Biehler
functions (`TauCeti.diracHermiteBiehler`, `TauCeti.diracHermiteBiehlerDirichlet`). Write
`H#(z) = conj H(conj z)` for the reflection of an entire function `H`. For `t ≥ 0`, the entries of
`M_q(t, ·)` are real entire functions (`TauCeti.diracFundamentalMatrix_conj`), so:

* `E# = A + iC` and `E~# = B + iD` (`TauCeti.conj_diracHermiteBiehler_conj`,
  `TauCeti.conj_diracHermiteBiehlerDirichlet_conj`), hence
  `A = (E + E#) / 2`, `C = (E# - E) / (2i)`, `B = (E~ + E~#) / 2` and `D = (E~# - E~) / (2i)`
  (`TauCeti.diracFundamentalMatrix_zero_zero_eq_diracHermiteBiehler` and its three companions);
* `det [[E, E~], [E#, E~#]] = E E~# - E~ E# = 2i`
  (`TauCeti.diracHermiteBiehler_mul_conj_sub_mul_conj`), from `det M = 1`;
* the integral equations take the form `E(t, z) = 1 + ∫₀ᵗ (-iz E(s, z) + q(s) E#(s, z)) ds` and
  `E~(t, z) = -i + ∫₀ᵗ (-iz E~(s, z) + q(s) E~#(s, z)) ds`
  (`TauCeti.diracHermiteBiehler_eq_one_add_integral_conj`,
  `TauCeti.diracHermiteBiehlerDirichlet_eq_neg_I_add_integral_conj`).

**Sign of the potential.** Conjugation by `Ω` changes the sign of the potential
(`TauCeti.diracFundamentalMatrix_neg_potential`), so `E_{-q} = i E~_q` and `E~_{-q} = -i E_q`
(`TauCeti.diracHermiteBiehler_neg_potential`, `TauCeti.diracHermiteBiehlerDirichlet_neg_potential`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  §3.1.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

section Reflection

variable (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t) (z : ℂ)
include hq ht

/-- **The reflection of `E`.** `E#(t, z) = conj E(t, conj z) = A(t, z) + i C(t, z)`. -/
theorem conj_diracHermiteBiehler_conj :
    conj (diracHermiteBiehler q t (conj z)) =
      diracFundamentalMatrix q t z 0 0 + I * diracFundamentalMatrix q t z 1 0 := by
  rw [diracHermiteBiehler_def, map_sub, map_mul, conj_I, conj_diracFundamentalMatrix_conj hq ht,
    conj_diracFundamentalMatrix_conj hq ht]
  ring

/-- **The reflection of `E~`.** `E~#(t, z) = conj E~(t, conj z) = B(t, z) + i D(t, z)`. -/
theorem conj_diracHermiteBiehlerDirichlet_conj :
    conj (diracHermiteBiehlerDirichlet q t (conj z)) =
      diracFundamentalMatrix q t z 0 1 + I * diracFundamentalMatrix q t z 1 1 := by
  rw [diracHermiteBiehlerDirichlet_def, map_sub, map_mul, conj_I,
    conj_diracFundamentalMatrix_conj hq ht, conj_diracFundamentalMatrix_conj hq ht]
  ring

/-- `A = (E + E#) / 2`. -/
theorem diracFundamentalMatrix_zero_zero_eq_diracHermiteBiehler :
    diracFundamentalMatrix q t z 0 0 =
      (diracHermiteBiehler q t z + conj (diracHermiteBiehler q t (conj z))) / 2 := by
  rw [conj_diracHermiteBiehler_conj hq ht, diracHermiteBiehler_def]
  ring

/-- `C = (E# - E) / (2i)`. -/
theorem diracFundamentalMatrix_one_zero_eq_diracHermiteBiehler :
    diracFundamentalMatrix q t z 1 0 =
      (conj (diracHermiteBiehler q t (conj z)) - diracHermiteBiehler q t z) / (2 * I) := by
  rw [conj_diracHermiteBiehler_conj hq ht, diracHermiteBiehler_def, eq_div_iff (by simp)]
  ring

/-- `B = (E~ + E~#) / 2`. -/
theorem diracFundamentalMatrix_zero_one_eq_diracHermiteBiehlerDirichlet :
    diracFundamentalMatrix q t z 0 1 =
      (diracHermiteBiehlerDirichlet q t z + conj (diracHermiteBiehlerDirichlet q t (conj z))) /
        2 := by
  rw [conj_diracHermiteBiehlerDirichlet_conj hq ht, diracHermiteBiehlerDirichlet_def]
  ring

/-- `D = (E~# - E~) / (2i)`. -/
theorem diracFundamentalMatrix_one_one_eq_diracHermiteBiehlerDirichlet :
    diracFundamentalMatrix q t z 1 1 =
      (conj (diracHermiteBiehlerDirichlet q t (conj z)) - diracHermiteBiehlerDirichlet q t z) /
        (2 * I) := by
  rw [conj_diracHermiteBiehlerDirichlet_conj hq ht, diracHermiteBiehlerDirichlet_def,
    eq_div_iff (by simp)]
  ring

/-- **The determinant identity.** `E E~# - E~ E# = 2i`, that is
`det [[E, E~], [E#, E~#]] = 2i`, from `det M_q(t, z) = 1`. -/
theorem diracHermiteBiehler_mul_conj_sub_mul_conj :
    diracHermiteBiehler q t z * conj (diracHermiteBiehlerDirichlet q t (conj z)) -
      diracHermiteBiehlerDirichlet q t z * conj (diracHermiteBiehler q t (conj z)) = 2 * I := by
  have hdet := det_diracFundamentalMatrix (hq.integrableOn_uIcc_of_Ici ht) z
  rw [det_fin_two] at hdet
  rw [conj_diracHermiteBiehler_conj hq ht, conj_diracHermiteBiehlerDirichlet_conj hq ht,
    diracHermiteBiehler_def, diracHermiteBiehlerDirichlet_def]
  linear_combination (2 * I) * hdet

end Reflection

/-- **The integral equation of `E` with the reflection.** For `q` locally integrable on `[0, ∞)`
and `t ≥ 0`, `E(t, z) = 1 + ∫₀ᵗ (-iz E(s, z) + q(s) E#(s, z)) ds`. -/
theorem diracHermiteBiehler_eq_one_add_integral_conj (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (z : ℂ) :
    diracHermiteBiehler q t z =
      1 + ∫ s in (0 : ℝ)..t, (-I * z * diracHermiteBiehler q s z +
        q s * conj (diracHermiteBiehler q s (conj z))) := by
  rw [diracHermiteBiehler_eq_one_add_integral (hq.integrableOn_uIcc_of_Ici ht) z]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht] at hs
  simp only [conj_diracHermiteBiehler_conj hq hs.1]

/-- **The integral equation of `E~` with the reflection.** For `q` locally integrable on
`[0, ∞)` and `t ≥ 0`, `E~(t, z) = -i + ∫₀ᵗ (-iz E~(s, z) + q(s) E~#(s, z)) ds`. -/
theorem diracHermiteBiehlerDirichlet_eq_neg_I_add_integral_conj
    (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t) (z : ℂ) :
    diracHermiteBiehlerDirichlet q t z =
      -I + ∫ s in (0 : ℝ)..t, (-I * z * diracHermiteBiehlerDirichlet q s z +
        q s * conj (diracHermiteBiehlerDirichlet q s (conj z))) := by
  rw [diracHermiteBiehlerDirichlet_eq_neg_I_add_integral (hq.integrableOn_uIcc_of_Ici ht) z]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht] at hs
  simp only [conj_diracHermiteBiehlerDirichlet_conj hq hs.1]

/-- **The sign of the potential for `E`.** For `q` locally integrable on `[0, ∞)` and `t ≥ 0`,
`E_{-q}(t, z) = i E~_q(t, z)`. -/
theorem diracHermiteBiehler_neg_potential (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (z : ℂ) : diracHermiteBiehler (-q) t z = I * diracHermiteBiehlerDirichlet q t z := by
  have h00 : diracFundamentalMatrix (-q) t z 0 0 = diracFundamentalMatrix q t z 1 1 := by
    simp [diracFundamentalMatrix_neg_potential hq ht]
  have h10 : diracFundamentalMatrix (-q) t z 1 0 = -diracFundamentalMatrix q t z 0 1 := by
    simp [diracFundamentalMatrix_neg_potential hq ht]
  rw [diracHermiteBiehler_def, diracHermiteBiehlerDirichlet_def]
  linear_combination h00 - I * h10 + diracFundamentalMatrix q t z 1 1 * I_sq

/-- **The sign of the potential for `E~`.** For `q` locally integrable on `[0, ∞)` and `t ≥ 0`,
`E~_{-q}(t, z) = -i E_q(t, z)`. -/
theorem diracHermiteBiehlerDirichlet_neg_potential (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (z : ℂ) :
    diracHermiteBiehlerDirichlet (-q) t z = -I * diracHermiteBiehler q t z := by
  have h01 : diracFundamentalMatrix (-q) t z 0 1 = -diracFundamentalMatrix q t z 1 0 := by
    simp [diracFundamentalMatrix_neg_potential hq ht]
  have h11 : diracFundamentalMatrix (-q) t z 1 1 = diracFundamentalMatrix q t z 0 0 := by
    simp [diracFundamentalMatrix_neg_potential hq ht]
  rw [diracHermiteBiehlerDirichlet_def, diracHermiteBiehler_def]
  linear_combination h01 - I * h11 - diracFundamentalMatrix q t z 1 0 * I_sq

end TauCeti
