/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import Mathlib.Topology.Algebra.Module.Star
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Symmetries of the Dirac fundamental matrix

For a potential `q`, locally integrable on `[0, ∞)`, the fundamental matrix
`M_q(t, z) = [[A, B], [C, D]]` of the Dirac system `Ω X' = z X - Q_q X`
(`TauCeti.diracFundamentalMatrix`) has three symmetries, all consequences of the uniqueness of
solutions (`TauCeti.IsDiracSolution.eq_diracFundamentalMatrix_mulVec`).

* **Reflection.** `Q_q` has real entries, so `M_q(t, conj z) = conj M_q(t, z)` entrywise for every
  complex potential: `A, B, C, D` are real entire functions
  (`TauCeti.diracFundamentalMatrix_conj`, `TauCeti.conj_diracFundamentalMatrix_conj`,
  `TauCeti.conj_diracFundamentalMatrix_ofReal`).
* **Sign of the potential.** `Ω Q_q Ω⁻¹ = -Q_q = Q_{-q}`, so conjugation by `Ω` carries solutions
  for `q` to solutions for `-q`, and `Ω M_q(t, z) = M_{-q}(t, z) Ω`
  (`TauCeti.mul_diracFundamentalMatrix_neg_potential`). In entries, `A_{-q} = D_q`,
  `B_{-q} = -C_q`, `C_{-q} = -B_q` and `D_{-q} = A_q`
  (`TauCeti.diracFundamentalMatrix_neg_potential`).
* **Parity.** Conjugation by `diag(1, -1)` changes the sign of the spectral parameter and replaces
  `q` by `conj q`, so `M_{conj q}(t, -z) = diag(1, -1) M_q(t, z) diag(1, -1)`
  (`TauCeti.diracFundamentalMatrix_neg_of_eqOn_conj`). For a real potential, `A` and `D` are even
  and `B` and `C` are odd in `z` (`TauCeti.diracFundamentalMatrix_neg_of_im_eq_zero`).

All three are instances of a general principle: a continuous `ℝ`-linear equivalence of `ℂ²`
intertwining the Dirac coefficients carries solutions to solutions
(`TauCeti.IsDiracSolution.continuousLinearEquiv_comp`). In particular an invertible constant
matrix `S` with `S (-Ω(z - Q_q(s))) = (-Ω(z' - Q_{q'}(s))) S` for every `s ≥ 0` intertwines the
fundamental matrices, `S M_q(t, z) = M_{q'}(t, z') S`
(`TauCeti.mul_diracFundamentalMatrix_of_mul_eq`); if `S S' = 1`, then
`M_{q'}(t, z') = S M_q(t, z) S'` (`TauCeti.diracFundamentalMatrix_eq_mul_mul_of_mul_eq`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  §3.1.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate

namespace TauCeti

variable {q q' : ℝ → ℂ} {z z' : ℂ} {t : ℝ}

/-- A continuous `ℝ`-linear equivalence `L` of `ℂ²` with
`L (-Ω(z - Q_q(s)) v) = -Ω(z' - Q_{q'}(s)) L v` for every `s ≥ 0` carries solutions of the Dirac
system for `(q, z)` to solutions for `(q', z')`. -/
theorem IsDiracSolution.continuousLinearEquiv_comp {X : ℝ → Fin 2 → ℂ}
    (hX : IsDiracSolution q z X) (L : (Fin 2 → ℂ) ≃L[ℝ] (Fin 2 → ℂ))
    (h : ∀ s ∈ Ici 0, ∀ v, L (diracCoeff q z s *ᵥ v) = diracCoeff q' z' s *ᵥ L v) :
    IsDiracSolution q' z' fun t ↦ L (X t) := by
  refine isDiracSolution_iff.2 ⟨L.continuous.comp_continuousOn hX.continuousOn, fun t ht ↦ ?_⟩
  have hint : ∫ s in (0 : ℝ)..t, diracCoeff q' z' s *ᵥ L (X s) =
      ∫ s in (0 : ℝ)..t, L (diracCoeff q z s *ᵥ X s) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht] at hs
    exact (h s hs.1 (X s)).symm
  rw [hint, L.intervalIntegral_comp_comm, hX.eq_add_integral ht, map_add]

/-- An invertible constant matrix `S` intertwining the Dirac coefficients of `(q, z)` and
`(q', z')` on `[0, ∞)` carries solutions of the Dirac system for `(q, z)` to solutions for
`(q', z')`. -/
theorem IsDiracSolution.mulVec_of_mul_eq {X : ℝ → Fin 2 → ℂ} (hX : IsDiracSolution q z X)
    {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : IsUnit S)
    (h : ∀ s ∈ Ici 0, S * diracCoeff q z s = diracCoeff q' z' s * S) :
    IsDiracSolution q' z' fun t ↦ S *ᵥ X t := by
  have := hS.invertible
  let L : (Fin 2 → ℂ) ≃L[ℝ] (Fin 2 → ℂ) :=
    (toLinearEquiv' S this).toContinuousLinearEquiv.restrictScalars ℝ
  have hL (v : Fin 2 → ℂ) : L v = S *ᵥ v :=
    (LinearMap.congr_fun (toLinearEquiv'_apply S this) v).trans (toLin'_apply S v)
  simpa only [hL] using
    hX.continuousLinearEquiv_comp L fun s hs v ↦ by simp only [hL, mulVec_mulVec, h s hs]

/-- **Intertwining the fundamental matrices.** If `q` and `q'` are locally integrable on
`[0, ∞)` and an invertible constant matrix `S` satisfies
`S (-Ω(z - Q_q(s))) = (-Ω(z' - Q_{q'}(s))) S` for every `s ≥ 0`, then
`S M_q(t, z) = M_{q'}(t, z') S` for `t ≥ 0`. -/
theorem mul_diracFundamentalMatrix_of_mul_eq (hq : LocallyIntegrableOn q (Ici 0))
    (hq' : LocallyIntegrableOn q' (Ici 0)) {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : IsUnit S)
    (h : ∀ s ∈ Ici 0, S * diracCoeff q z s = diracCoeff q' z' s * S) (ht : 0 ≤ t) :
    S * diracFundamentalMatrix q t z = diracFundamentalMatrix q' t z' * S := by
  have hq't : IntegrableOn q' (Icc 0 t) :=
    hq'.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have key (v : Fin 2 → ℂ) :
      (S * diracFundamentalMatrix q t z) *ᵥ v = (diracFundamentalMatrix q' t z' * S) *ᵥ v := by
    have := ((isDiracSolution_diracFundamentalMatrix_mulVec hq z v).mulVec_of_mul_eq hS
      h).eq_diracFundamentalMatrix_mulVec hq't ht
    simpa [mulVec_mulVec] using this
  ext i j
  simpa [mulVec_single] using congrFun (key (Pi.single j 1)) i

/-- If `q` and `q'` are locally integrable on `[0, ∞)` and a constant matrix `S` with right
inverse `S'` satisfies `S (-Ω(z - Q_q(s))) = (-Ω(z' - Q_{q'}(s))) S` for every `s ≥ 0`, then
`M_{q'}(t, z') = S M_q(t, z) S'` for `t ≥ 0`. -/
theorem diracFundamentalMatrix_eq_mul_mul_of_mul_eq (hq : LocallyIntegrableOn q (Ici 0))
    (hq' : LocallyIntegrableOn q' (Ici 0)) {S S' : Matrix (Fin 2) (Fin 2) ℂ} (hSS' : S * S' = 1)
    (h : ∀ s ∈ Ici 0, S * diracCoeff q z s = diracCoeff q' z' s * S) (ht : 0 ≤ t) :
    diracFundamentalMatrix q' t z' = S * diracFundamentalMatrix q t z * S' := by
  rw [mul_diracFundamentalMatrix_of_mul_eq hq hq'
    ((isUnit_iff_isUnit_det S).2 (isUnit_det_of_right_inverse hSS')) h ht, Matrix.mul_assoc,
    hSS', Matrix.mul_one]

/-- Complex conjugation of the entries of a solution of the Dirac system for `(q, z)` gives a
solution for `(q, conj z)`: the matrix `Q_q` has real entries. -/
theorem IsDiracSolution.star {X : ℝ → Fin 2 → ℂ} (hX : IsDiracSolution q z X) :
    IsDiracSolution q (conj z) fun t ↦ star (X t) := by
  have hc (s : ℝ) : (diracCoeff q z s).map (starRingEnd ℂ) = diracCoeff q (conj z) s := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracCoeff_def]
  simpa only [starL'_apply] using hX.continuousLinearEquiv_comp (starL' ℝ) fun s _ v ↦ by
    ext i
    rw [starL'_apply, starL'_apply, ← hc]
    exact RingHom.map_mulVec (starRingEnd ℂ) (diracCoeff q z s) v i

/-- **Reflection symmetry.** For a potential `q` locally integrable on `[0, ∞)` and `t ≥ 0`,
`M_q(t, conj z) = conj M_q(t, z)` entrywise. In particular the entries `A, B, C, D` of the
fundamental matrix are real entire functions, for every complex potential. -/
theorem diracFundamentalMatrix_conj (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t) (z : ℂ) :
    diracFundamentalMatrix q t (conj z) = (diracFundamentalMatrix q t z).map (starRingEnd ℂ) := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  ext i j
  have := congrFun ((isDiracSolution_diracFundamentalMatrix_mulVec hq z
    (Pi.single j 1)).star.eq_diracFundamentalMatrix_mulVec hqt ht) i
  rw [diracFundamentalMatrix_zero, one_mulVec, ← Pi.single_star, star_one, mulVec_single] at this
  simpa using this.symm

/-- The entries of the fundamental matrix are real entire functions: for `q` locally integrable on
`[0, ∞)` and `t ≥ 0`, `conj M_q(t, conj z) = M_q(t, z)` entrywise. -/
theorem conj_diracFundamentalMatrix_conj (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (z : ℂ) (i j : Fin 2) :
    conj (diracFundamentalMatrix q t (conj z) i j) = diracFundamentalMatrix q t z i j := by
  rw [diracFundamentalMatrix_conj hq ht z, map_apply, conj_conj]

/-- On the real axis the entries of the fundamental matrix are real: for `x : ℝ`,
`conj M_q(t, x) = M_q(t, x)` entrywise. -/
theorem conj_diracFundamentalMatrix_ofReal (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (x : ℝ) (i j : Fin 2) :
    conj (diracFundamentalMatrix q t x i j) = diracFundamentalMatrix q t x i j := by
  have := congrFun (congrFun (diracFundamentalMatrix_conj hq ht (x : ℂ)) i) j
  rw [conj_ofReal] at this
  exact this.symm

/-- **The sign of the potential.** For `q` locally integrable on `[0, ∞)` and `t ≥ 0`, the
fundamental matrix of `-q` is `M_{-q}(t, z) = Ω M_q(t, z) Ω⁻¹`: with `M_q = [[A, B], [C, D]]`,
`A_{-q} = D_q`, `B_{-q} = -C_q`, `C_{-q} = -B_q` and `D_{-q} = A_q`. Hence `Θ_{-q} = Ω Φ_q` and
`Φ_{-q} = -Ω Θ_q` for the columns `Θ = (A, C)` and `Φ = (B, D)`. -/
theorem diracFundamentalMatrix_neg_potential (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (z : ℂ) :
    diracFundamentalMatrix (-q) t z =
      !![diracFundamentalMatrix q t z 1 1, -diracFundamentalMatrix q t z 1 0;
        -diracFundamentalMatrix q t z 0 1, diracFundamentalMatrix q t z 0 0] := by
  rw [diracFundamentalMatrix_eq_mul_mul_of_mul_eq (S := !![0, 1; -1, 0]) (S' := !![0, -1; 1, 0])
    hq hq.neg ?_ (fun s _ ↦ ?_) ht, eta_fin_two (diracFundamentalMatrix q t z)]
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [diracCoeff_def, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

/-- **The sign of the potential, as an intertwining.** For `q` locally integrable on `[0, ∞)`
and `t ≥ 0`, `Ω M_q(t, z) = M_{-q}(t, z) Ω` with `Ω = [[0, 1], [-1, 0]]`: conjugation by `Ω`
changes the sign of the potential, `Ω Q_q Ω⁻¹ = Q_{-q}`. -/
theorem mul_diracFundamentalMatrix_neg_potential (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (z : ℂ) :
    !![0, 1; -1, 0] * diracFundamentalMatrix q t z =
      diracFundamentalMatrix (-q) t z * !![0, 1; -1, 0] := by
  rw [diracFundamentalMatrix_neg_potential hq ht z, eta_fin_two (diracFundamentalMatrix q t z)]
  simp

/-- **Parity.** For `q` locally integrable on `[0, ∞)`, a potential `q'` equal to `conj q` on
`[0, ∞)`, and `t ≥ 0`, conjugation by `diag(1, -1)` changes the sign of the spectral parameter:
`M_{q'}(t, -z) = diag(1, -1) M_q(t, z) diag(1, -1)`. So `A_{q'}(t, -z) = A_q(t, z)`,
`B_{q'}(t, -z) = -B_q(t, z)`, `C_{q'}(t, -z) = -C_q(t, z)` and `D_{q'}(t, -z) = D_q(t, z)`. -/
theorem diracFundamentalMatrix_neg_of_eqOn_conj (hq : LocallyIntegrableOn q (Ici 0))
    (hconj : EqOn q' (fun s ↦ conj (q s)) (Ici 0)) (ht : 0 ≤ t) (z : ℂ) :
    diracFundamentalMatrix q' t (-z) =
      !![diracFundamentalMatrix q t z 0 0, -diracFundamentalMatrix q t z 0 1;
        -diracFundamentalMatrix q t z 1 0, diracFundamentalMatrix q t z 1 1] := by
  have hqc : LocallyIntegrableOn q' (Ici 0) := by
    refine LocallyIntegrableOn.congr ((ae_restrict_mem measurableSet_Ici).mono
      fun s hs ↦ (hconj hs).symm) fun x hx ↦ ?_
    obtain ⟨U, hU, hi⟩ := hq x hx
    exact ⟨U, hU, conjCLE.toContinuousLinearMap.integrable_comp hi⟩
  rw [diracFundamentalMatrix_eq_mul_mul_of_mul_eq (S := !![1, 0; 0, -1]) (S' := !![1, 0; 0, -1])
    hq hqc ?_ (fun s hs ↦ ?_) ht, eta_fin_two (diracFundamentalMatrix q t z)]
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diracCoeff_def, Matrix.mul_apply, Fin.sum_univ_two, hconj hs] <;> ring

/-- **Parity for real potentials.** For a potential `q`, locally integrable and real on
`[0, ∞)`, and `t ≥ 0`, `A` and `D` are even and `B` and `C` are odd in `z`:
`M_q(t, -z) = diag(1, -1) M_q(t, z) diag(1, -1)`. -/
theorem diracFundamentalMatrix_neg_of_im_eq_zero (hq : LocallyIntegrableOn q (Ici 0))
    (hre : ∀ s ∈ Ici 0, (q s).im = 0) (ht : 0 ≤ t) (z : ℂ) :
    diracFundamentalMatrix q t (-z) =
      !![diracFundamentalMatrix q t z 0 0, -diracFundamentalMatrix q t z 0 1;
        -diracFundamentalMatrix q t z 1 0, diracFundamentalMatrix q t z 1 1] :=
  diracFundamentalMatrix_neg_of_eqOn_conj hq (fun s hs ↦ (conj_eq_iff_im.2 (hre s hs)).symm) ht z

end TauCeti
