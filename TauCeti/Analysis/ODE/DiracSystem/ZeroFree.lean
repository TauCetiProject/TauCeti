/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HermiteBiehler
public import TauCeti.Analysis.ODE.DiracSystem.ChristoffelDarboux
public import TauCeti.Analysis.ODE.DiracSystem.Symmetry
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The Hermite–Biehler property of the Dirac system

For a potential `q` and the fundamental matrix `M_q(t, z) = [[A, B], [C, D]]` of the Dirac system
`Ω X' = z X - Q_q X` (`TauCeti.diracFundamentalMatrix`), write `X = (X₀, X₁)` for its `j`-th
column: the Neumann solution `Θ = (A, C)` for `j = 0` and the Dirichlet solution `Φ = (B, D)` for
`j = 1`. The functions `X₀ - i X₁`, that is `E = A - iC` and `F = B - iD` (the latter is often
written with a tilde over `E`), are the Hermite–Biehler functions of the system, from which its
scattering data and de Branges spaces are built.

* `TauCeti.norm_sub_I_mul_sq_sub_norm_add_I_mul_sq_diracFundamentalMatrix`:
  `|X₀ - iX₁|² - |X₀ + iX₁|² = 4 Im z ∫₀ᵗ |X(s, z)|² ds`, from the kernel identity on the diagonal
  (`TauCeti.im_conj_mul_diracFundamentalMatrix`) and `|u - iv|² - |u + iv|² = 4 Im (conj u v)`.
* `TauCeti.conj_diracFundamentalMatrix_sub_I_mul_conj`: since `A, B, C, D` are real entire
  functions (`TauCeti.diracFundamentalMatrix_conj`), `X₀ + iX₁` is the reflection
  `z ↦ conj ((X₀ - iX₁)(conj z))`; for `j = 0` this is `E# = A + iC`. In this form the identity
  above reads `|E|² - |E#|² = 4 Im z ∫₀ᵗ |Θ(s, z)|² ds`
  (`TauCeti.norm_sub_I_mul_sq_sub_norm_conj_sq_diracFundamentalMatrix`).
* `TauCeti.isHermiteBiehler_diracFundamentalMatrix`: for `t > 0`, `E(t, ·)` and `F(t, ·)` are
  Hermite–Biehler functions (`TauCeti.IsHermiteBiehler`), because the integral
  `∫₀ᵗ |X(s, z)|² ds` is positive (`TauCeti.integral_norm_sq_diracFundamentalMatrix_pos`).
* `TauCeti.diracFundamentalMatrix_sub_I_mul_ne_zero`: for `t ≥ 0`, `E(t, ·)` and `F(t, ·)` have
  no zeros in the closed upper half-plane. In the open half-plane this is the Hermite–Biehler
  property; on the real axis `X₀` and `X₁` are real and do not vanish together.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  Lemma 13.
* R. Romanov, *Canonical systems and de Branges spaces*, arXiv:1408.6022, Proposition 4.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- If `q` is integrable on `[0, t]` (or `[t, 0]`), the `j`-th column `X = (X₀, X₁)` of the
fundamental matrix satisfies `|X₀ - iX₁|² - |X₀ + iX₁|² = 4 Im z ∫₀ᵗ |X(s, z)|² ds`. For `j = 0`
this is `|E(t, z)|² - |E#(t, z)|² = 4 Im z ∫₀ᵗ |Θ(s, z)|² ds` with `E = A - iC`, and for `j = 1`
the same identity for `F = B - iD` and `Φ`. -/
theorem norm_sub_I_mul_sq_sub_norm_add_I_mul_sq_diracFundamentalMatrix
    (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) (j : Fin 2) :
    ‖diracFundamentalMatrix q t z 0 j - I * diracFundamentalMatrix q t z 1 j‖ ^ 2 -
        ‖diracFundamentalMatrix q t z 0 j + I * diracFundamentalMatrix q t z 1 j‖ ^ 2 =
      4 * z.im * ∫ s in (0 : ℝ)..t,
        (‖diracFundamentalMatrix q s z 0 j‖ ^ 2 + ‖diracFundamentalMatrix q s z 1 j‖ ^ 2) := by
  rw [mul_assoc, ← im_conj_mul_diracFundamentalMatrix hq]
  -- `|u - iv|² - |u + iv|² = 4 Im (conj u v)`.
  generalize diracFundamentalMatrix q t z 0 j = u
  generalize diracFundamentalMatrix q t z 1 j = v
  simp only [← normSq_eq_norm_sq, normSq_apply, sub_re, add_re, sub_im, add_im, mul_re, mul_im,
    I_re, I_im, conj_re, conj_im]
  ring

/-- **The reflection of `X₀ - iX₁` is `X₀ + iX₁`.** For a potential `q` locally integrable on
`[0, ∞)` and `t ≥ 0`, the entries of the fundamental matrix are real entire functions
(`TauCeti.diracFundamentalMatrix_conj`), so the `j`-th column `X` satisfies
`conj (X₀(t, conj z) - iX₁(t, conj z)) = X₀(t, z) + iX₁(t, z)`. For `j = 0` this is
`E#(t, z) = A(t, z) + iC(t, z)`, and for `j = 1` the same for `F = B - iD`. -/
theorem conj_diracFundamentalMatrix_sub_I_mul_conj (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (z : ℂ) (j : Fin 2) :
    conj (diracFundamentalMatrix q t (conj z) 0 j - I * diracFundamentalMatrix q t (conj z) 1 j) =
      diracFundamentalMatrix q t z 0 j + I * diracFundamentalMatrix q t z 1 j := by
  simp [diracFundamentalMatrix_conj hq ht]

/-- The identity `|E(t, z)|² - |E#(t, z)|² = 4 Im z ∫₀ᵗ |X(s, z)|² ds` in reflection form: for a
potential `q` locally integrable on `[0, ∞)`, `t ≥ 0` and the `j`-th column `X` of the fundamental
matrix, with `E(t, z) = X₀(t, z) - iX₁(t, z)` and `E#(t, z) = conj (E(t, conj z))`. -/
theorem norm_sub_I_mul_sq_sub_norm_conj_sq_diracFundamentalMatrix
    (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t) (z : ℂ) (j : Fin 2) :
    ‖diracFundamentalMatrix q t z 0 j - I * diracFundamentalMatrix q t z 1 j‖ ^ 2 -
        ‖conj (diracFundamentalMatrix q t (conj z) 0 j -
          I * diracFundamentalMatrix q t (conj z) 1 j)‖ ^ 2 =
      4 * z.im * ∫ s in (0 : ℝ)..t,
        (‖diracFundamentalMatrix q s z 0 j‖ ^ 2 + ‖diracFundamentalMatrix q s z 1 j‖ ^ 2) := by
  rw [conj_diracFundamentalMatrix_sub_I_mul_conj hq ht]
  exact norm_sub_I_mul_sq_sub_norm_add_I_mul_sq_diracFundamentalMatrix
    (hq.integrableOn_uIcc_of_Ici ht) z j

/-- **The Hermite–Biehler property of the Dirac system.** For a potential `q` locally integrable on
`[0, ∞)` and `t > 0`, the function `z ↦ X₀(t, z) - i X₁(t, z)` built from the `j`-th column of the
fundamental matrix is Hermite–Biehler: for `j = 0` this is `E(t, ·) = A(t, ·) - iC(t, ·)`, and for
`j = 1` it is `F(t, ·) = B(t, ·) - iD(t, ·)`. -/
theorem isHermiteBiehler_diracFundamentalMatrix (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 < t)
    (j : Fin 2) :
    IsHermiteBiehler fun z ↦
      diracFundamentalMatrix q t z 0 j - I * diracFundamentalMatrix q t z 1 j := by
  have hqt' : IntegrableOn q (uIcc 0 t) := hq.integrableOn_uIcc_of_Ici ht.le
  have hqt : IntegrableOn q (Icc 0 t) := hqt'.mono_set Icc_subset_uIcc
  refine isHermiteBiehler_iff.2 ⟨(differentiable_diracFundamentalMatrix_apply hqt' 0 j).sub
    ((differentiable_diracFundamentalMatrix_apply hqt' 1 j).const_mul I), fun z hz ↦ ?_⟩
  have key := norm_sub_I_mul_sq_sub_norm_conj_sq_diracFundamentalMatrix hq ht.le z j
  rw [RCLike.norm_conj] at key
  have hpos := mul_pos (mul_pos four_pos hz)
    (integral_norm_sq_diracFundamentalMatrix_pos hqt ht z j)
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith)

/-- **The Hermite–Biehler functions have no zeros in the closed upper half-plane.** For a potential
`q` locally integrable on `[0, ∞)`, `t ≥ 0` and `Im z ≥ 0`, the `j`-th column `X` of the
fundamental matrix satisfies `X₀(t, z) - i X₁(t, z) ≠ 0`: neither `E(t, ·)` nor `F(t, ·)` vanishes
in the closed upper half-plane. -/
theorem diracFundamentalMatrix_sub_I_mul_ne_zero (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    {z : ℂ} (hz : 0 ≤ z.im) (j : Fin 2) :
    diracFundamentalMatrix q t z 0 j - I * diracFundamentalMatrix q t z 1 j ≠ 0 := by
  rcases hz.lt_or_eq with hz | hz
  · rcases ht.lt_or_eq with ht | rfl
    · exact (isHermiteBiehler_diracFundamentalMatrix hq ht j).ne_zero hz
    · fin_cases j <;> simp
  -- On the real axis `X₀` and `X₁` are real, so `X₀ - iX₁ = 0` forces `X₀ = X₁ = 0`.
  have hx : z = (z.re : ℂ) := ext rfl (by simp [hz])
  have hreal (i : Fin 2) : (diracFundamentalMatrix q t z i j).im = 0 := by
    rw [hx, ← conj_eq_iff_im]
    exact conj_diracFundamentalMatrix_ofReal hq ht z.re i j
  intro h
  have hre := congrArg re h
  have him := congrArg im h
  simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, zero_re, zero_im, hreal] at hre him
  have := norm_sq_add_norm_sq_diracFundamentalMatrix_pos (hq.integrableOn_uIcc_of_Ici ht) z j
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply, hreal, hreal] at this
  nlinarith

end TauCeti
