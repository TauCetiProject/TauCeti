/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.FiniteSum

/-!
# The Mellin transform of a Dirichlet theta series

The Gaussian theta series of a nonprincipal Dirichlet character, expressed by summing the
Hurwitz theta kernels of the residue classes, gives its completed L-function by an absolutely
convergent Mellin integral. The two endpoint corrections
of Mathlib's even Hurwitz kernels cancel in the character sum; the odd kernels already have
no corrections. Primitivity is not needed.

The normalization is that of `New.hasMellin_thetaSeries_char` in `Lib/Analytic/DirichletTheta`
of lsernau/grh-lean at `72fead1`, with the factor `√u` absorbed into the Mellin exponent.
-/

public section

open Complex Finset Filter HurwitzZeta MeasureTheory Set

namespace DirichletCharacter

private theorem hasMellin_even_hurwitz_sum {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (s : ℂ) :
    HasMellin (fun x ↦ ∑ a : ZMod N, χ a * (evenKernel (ZMod.toAddCircle a) x : ℂ)) (s / 2)
      (∑ a : ZMod N, χ a * (2 * completedHurwitzZetaEven (ZMod.toAddCircle a) s)) := by
  have hN : N ≠ 1 := by
    rintro rfl
    exact hχ χ.level_one
  let P (a : ZMod N) := hurwitzEvenFEPair (ZMod.toAddCircle a)
  have hsum : ∑ a : ZMod N, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hconst : ∑ a : ZMod N, χ a * (P a).f₀ = 0 := by
    simp [P, hurwitzEvenFEPair, ZMod.toAddCircle_eq_zero, mul_ite, χ.map_zero' hN]
  have hmod (a : ZMod N) : HasMellin (fun x ↦ χ a * (P a).f_modif x) (s / 2)
      (χ a * (P a).Λ₀ (s / 2)) := by
    have h := (P a).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)
    exact hasMellin_const_smul h.1 (χ a)
  have h := HasMellin.finsetSum (t := univ) (fun a _ ↦ hmod a)
  have hvalue : ∑ a : ZMod N, χ a * (P a).Λ₀ (s / 2) =
      ∑ a : ZMod N, χ a * (2 * completedHurwitzZetaEven (ZMod.toAddCircle a) s) := by
    have hterm (a : ZMod N) : χ a * (P a).Λ₀ (s / 2) =
        χ a * (2 * completedHurwitzZetaEven (ZMod.toAddCircle a) s) +
          (χ a * (P a).f₀) * (1 / (s / 2)) + χ a * (1 / ((1 / 2 : ℂ) - s / 2)) := by
      rw [WeakFEPair.Λ₀_eq, completedHurwitzZetaEven]
      -- These projections are the common weight and the constant term of the cosine kernel.
      have hk : (↑(P a).k : ℂ) = 1 / 2 := by simp [P, hurwitzEvenFEPair]
      have he : (P a).ε = 1 := rfl
      have hg : (P a).g₀ = 1 := rfl
      rw [hk, he, hg]
      simp only [smul_eq_mul, mul_one]
      have hP : (hurwitzEvenFEPair (ZMod.toAddCircle a)).Λ (s / 2) = (P a).Λ (s / 2) := rfl
      rw [hP]
      ring
    simp only [hterm, sum_add_distrib, ← sum_mul, hconst, hsum, zero_mul, add_zero]
  have hae : (fun x ↦ ∑ a : ZMod N, χ a * (P a).f_modif x) =ᵐ[volume.restrict (Ioi 0)]
      (fun x ↦ ∑ a : ZMod N, χ a * (evenKernel (ZMod.toAddCircle a) x : ℂ)) := by
    have hne : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), x ≠ 1 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with x hx hx1
    rcases lt_or_gt_of_ne hx1 with hl | hr
    · have hm : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, hl⟩
      simp [WeakFEPair.f_modif, P, hurwitzEvenFEPair, hm, hl.le, mul_sub,
        sum_sub_distrib, ← sum_mul, hsum]
    · simp [WeakFEPair.f_modif, P, hurwitzEvenFEPair, hr, hr.le, mul_sub,
        sum_sub_distrib, χ.map_zero' hN]
  rw [hvalue] at h
  have hweight := hae.mono fun x hx ↦ congrArg (fun z : ℂ ↦ (x : ℂ) ^ (s / 2 - 1) • z) hx
  exact ⟨(integrable_congr hweight).mp h.1, (integral_congr_ae hweight).symm.trans h.2⟩

private theorem hasMellin_odd_hurwitz_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    HasMellin (fun x ↦ ∑ a : ZMod N, χ a * (oddKernel (ZMod.toAddCircle a) x : ℂ)) ((s + 1) / 2)
      (∑ a : ZMod N, χ a * (2 * completedHurwitzZetaOdd (ZMod.toAddCircle a) s)) := by
  refine HasMellin.finsetSum fun a _ ↦ ?_
  have h := (isStrong_hurwitzOddFEPair (ZMod.toAddCircle a)).hasMellin ((s + 1) / 2)
  have hm := hasMellin_const_smul h.1 (χ a)
  rw [h.2] at hm
  simpa [completedHurwitzZetaOdd, smul_eq_mul, mul_div_cancel₀] using hm

/-- In its residue-class expression, the Gaussian theta kernel of a nonprincipal Dirichlet
character has Mellin transform equal to half the completed L-function. The degree `j` is the
parity of the character. The integral converges for all Mellin parameters; the character need
not be primitive. -/
theorem hasMellin_gaussianTheta_residue_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {j : ℕ} (hj : (j = 0 ∧ χ.Even) ∨ (j = 1 ∧ χ.Odd)) (s : ℂ) :
    HasMellin (fun u : ℝ ↦ ((((N : ℝ) * u) ^ j : ℝ) : ℂ) / 2 *
      ∑ a : ZMod N, χ a * ((if j = 0 then evenKernel else oddKernel)
        (ZMod.toAddCircle a) ((N * u) ^ 2) : ℂ)) s (χ.completedLFunction s / 2) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  let F (x : ℝ) := ∑ a : ZMod N, χ a * ((if j = 0 then evenKernel else oddKernel)
    (ZMod.toAddCircle a) x : ℂ)
  have hcore : HasMellin F ((s + j) / 2) (2 * (N : ℂ) ^ s * χ.completedLFunction s) := by
    have hcancel (z : ℂ) : (N : ℂ) ^ s * ((N : ℂ) ^ (-s) * z) = z := by
      rw [cpow_neg, ← mul_assoc, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hNc)), one_mul]
    rcases hj with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · simpa [F, DirichletCharacter.completedLFunction, ZMod.completedLFunction_def_even hp.to_fun,
        hcancel, mul_left_comm (χ _) 2, ← mul_sum, mul_assoc] using hasMellin_even_hurwitz_sum hχ s
    · simpa [F, DirichletCharacter.completedLFunction, ZMod.completedLFunction_def_odd hp.to_fun,
        hcancel, mul_left_comm (χ _) 2, ← mul_sum, mul_assoc] using hasMellin_odd_hurwitz_sum χ s
  have hsquare : MellinConvergent (fun u : ℝ ↦ F (u ^ (2 : ℝ))) (s + j) :=
    (MellinConvergent.comp_rpow (by norm_num : (2 : ℝ) ≠ 0)).mpr (by simpa using hcore.1)
  have hscaled := ((MellinConvergent.comp_mul_left (s := s + j) hN).mpr hsquare)
  let G (u : ℝ) := (u : ℂ) ^ (j : ℂ) • F (((N : ℝ) * u) ^ (2 : ℝ))
  have hg : MellinConvergent G s := MellinConvergent.cpow_smul.mpr hscaled
  have hm := hasMellin_const_smul hg ((N : ℂ) ^ j / 2)
  have hval : ((N : ℂ) ^ j / 2) • mellin G s = χ.completedLFunction s / 2 := by
    have hdilation := mellin_comp_mul_left (fun u ↦ F (u ^ (2 : ℝ))) (s + j) hN
    rw [mellin_cpow_smul, hdilation, mellin_comp_rpow]
    norm_num only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2), ofReal_ofNat]
    rw [hcore.2]
    simp only [ofReal_natCast, smul_eq_mul, real_smul, ofReal_div, ofReal_one, ofReal_ofNat,
      neg_add, cpow_add _ _ hNc, cpow_neg, cpow_natCast]
    field_simp [cpow_ne_zero_iff.mpr (Or.inl hNc) (b := s)]
    rw [mul_comm, mul_div_cancel_right₀ _ (cpow_ne_zero_iff.mpr (Or.inl hNc))]
  rw [hval] at hm
  refine (TauCeti.hasMellin_congr (fun u _ ↦ ?_)).mp hm
  simp only [G, F, Real.rpow_two, smul_eq_mul, cpow_natCast, ofReal_pow, ofReal_mul,
    ofReal_natCast, mul_pow]
  ring

end DirichletCharacter
