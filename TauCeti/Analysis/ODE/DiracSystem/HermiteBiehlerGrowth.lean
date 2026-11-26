/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler
public import TauCeti.Analysis.ODE.DiracSystem.Norm

/-!
# Growth of the Hermite–Biehler functions of a Dirac system

For a potential `q` integrable on `[0, t]` with `t ≥ 0`, the fundamental matrix satisfies
`‖M_q(t, z)‖ ≤ exp(t|z| + ∫₀ᵗ |q|)` in the Euclidean operator norm
(`TauCeti.norm_toEuclideanCLM_diracFundamentalMatrix_le`). Hence every entry of `M_q(t, z)` is
bounded by the same exponential (`TauCeti.norm_diracFundamentalMatrix_apply_le`), and the
Hermite–Biehler functions `E = A - iC` and `E~ = B - iD` satisfy
`|E(t, z)|, |E~(t, z)| ≤ 2 exp(t|z| + ∫₀ᵗ |q|)`
(`TauCeti.norm_diracHermiteBiehler_le`, `TauCeti.norm_diracHermiteBiehlerDirichlet_le`). So
`E(t, ·)` and `E~(t, ·)` are entire functions of order at most one and exponential type at most
`t`: `|E(t, z)| ≤ C e^{t|z|}` for a constant `C`
(`TauCeti.exists_norm_diracHermiteBiehler_le_mul_exp`,
`TauCeti.exists_norm_diracHermiteBiehlerDirichlet_le_mul_exp`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix Complex

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- **Entries of the fundamental matrix.** If `q` is integrable on `[0, t]` and `t ≥ 0`, every
entry of `M_q(t, z)` has modulus at most `exp(t|z| + ∫₀ᵗ |q|)`. -/
theorem norm_diracFundamentalMatrix_apply_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) (i j : Fin 2) :
    ‖diracFundamentalMatrix q t z i j‖ ≤ Real.exp (t * ‖z‖ + ∫ s in (0 : ℝ)..t, ‖q s‖) := by
  set M := diracFundamentalMatrix q t z
  have h := (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M).le_opNorm (EuclideanSpace.single j 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ (h.trans (norm_toEuclideanCLM_diracFundamentalMatrix_le hq ht z))
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ i)
  clear_value M
  simp

/-- **Growth of `E`.** If `q` is integrable on `[0, t]` and `t ≥ 0`, then
`|E(t, z)| ≤ 2 exp(t|z| + ∫₀ᵗ |q|)`. -/
theorem norm_diracHermiteBiehler_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (z : ℂ) :
    ‖diracHermiteBiehler q t z‖ ≤ 2 * Real.exp (t * ‖z‖ + ∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [diracHermiteBiehler_def]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_I, one_mul, two_mul]
  exact add_le_add (norm_diracFundamentalMatrix_apply_le hq ht z 0 0)
    (norm_diracFundamentalMatrix_apply_le hq ht z 1 0)

/-- **Growth of `E~`.** If `q` is integrable on `[0, t]` and `t ≥ 0`, then
`|E~(t, z)| ≤ 2 exp(t|z| + ∫₀ᵗ |q|)`. -/
theorem norm_diracHermiteBiehlerDirichlet_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) :
    ‖diracHermiteBiehlerDirichlet q t z‖ ≤
      2 * Real.exp (t * ‖z‖ + ∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [diracHermiteBiehlerDirichlet_def]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_I, one_mul, two_mul]
  exact add_le_add (norm_diracFundamentalMatrix_apply_le hq ht z 0 1)
    (norm_diracFundamentalMatrix_apply_le hq ht z 1 1)

/-- **`E(t, ·)` has exponential type at most `t`**: `|E(t, z)| ≤ C e^{t|z|}` for a constant `C`;
in particular `E(t, ·)` is entire of order at most one. -/
theorem exists_norm_diracHermiteBiehler_le_mul_exp (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) :
    ∃ C, ∀ z, ‖diracHermiteBiehler q t z‖ ≤ C * Real.exp (t * ‖z‖) :=
  ⟨2 * Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖), fun z ↦ by
    rw [mul_assoc, ← Real.exp_add, add_comm (∫ s in (0 : ℝ)..t, ‖q s‖)]
    exact norm_diracHermiteBiehler_le hq ht z⟩

/-- **`E~(t, ·)` has exponential type at most `t`**: `|E~(t, z)| ≤ C e^{t|z|}` for a constant `C`;
in particular `E~(t, ·)` is entire of order at most one. -/
theorem exists_norm_diracHermiteBiehlerDirichlet_le_mul_exp (hq : IntegrableOn q (Icc 0 t))
    (ht : 0 ≤ t) : ∃ C, ∀ z, ‖diracHermiteBiehlerDirichlet q t z‖ ≤ C * Real.exp (t * ‖z‖) :=
  ⟨2 * Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖), fun z ↦ by
    rw [mul_assoc, ← Real.exp_add, add_comm (∫ s in (0 : ℝ)..t, ‖q s‖)]
    exact norm_diracHermiteBiehlerDirichlet_le hq ht z⟩

end TauCeti
