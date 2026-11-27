/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
public import TauCeti.NumberTheory.LSeries.GaussianTheta
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Uniqueness
import TauCeti.NumberTheory.LSeries.HurwitzZeta.Basic

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
  have hconst : ∑ a : ZMod N, χ a * (if ZMod.toAddCircle a = 0 then 1 else 0) = 0 := by
    simp [ZMod.toAddCircle_eq_zero, mul_ite, χ.map_zero' hN]
  have hmod (a : ZMod N) : HasMellin (fun x ↦ χ a * (P a).f_modif x) (s / 2)
      (χ a * (P a).Λ₀ (s / 2)) := by
    have h := (P a).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)
    exact hasMellin_const_smul h.1 (χ a)
  have h := HasMellin.finsetSum (t := univ) (fun a _ ↦ hmod a)
  have hvalue : ∑ a : ZMod N, χ a * (P a).Λ₀ (s / 2) =
      ∑ a : ZMod N, χ a * (2 * completedHurwitzZetaEven (ZMod.toAddCircle a) s) := by
    have hΛ₀ (a : ZMod N) : (P a).Λ₀ (s / 2) =
        2 * completedHurwitzZetaEven₀ (ZMod.toAddCircle a) s := by
      rw [completedHurwitzZetaEven₀, mul_div_cancel₀ _ two_ne_zero]
    simp_rw [hΛ₀, completedHurwitzZetaEven_eq]
    simp only [mul_left_comm (χ _) 2, ← mul_sum, mul_sub, sum_sub_distrib,
      ← mul_div_assoc, ← sum_div, ← sum_mul, mul_one, hconst, hsum, mul_zero, zero_mul,
      zero_div, sub_zero]
  have hae : (fun x ↦ ∑ a : ZMod N, χ a * (P a).f_modif x) =ᵐ[volume.restrict (Ioi 0)]
      (fun x ↦ ∑ a : ZMod N, χ a * (evenKernel (ZMod.toAddCircle a) x : ℂ)) := by
    have hne : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), x ≠ 1 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with x hx hx1
    rcases lt_or_gt_of_ne hx1 with hl | hr
    · simp only [P, hurwitzEvenFEPair_f_modif_of_mem_Ioo _ ⟨hx, hl⟩, mul_sub,
        sum_sub_distrib, ← sum_mul, hsum, zero_mul, sub_zero]
    · simp only [P, hurwitzEvenFEPair_f_modif_of_one_lt _ hr, mul_sub, sum_sub_distrib,
        hconst, sub_zero]
  rw [hvalue] at h
  exact (TauCeti.hasMellin_congr_ae hae).mp h

private theorem hasMellin_odd_hurwitz_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    HasMellin (fun x ↦ ∑ a : ZMod N, χ a * (oddKernel (ZMod.toAddCircle a) x : ℂ)) ((s + 1) / 2)
      (∑ a : ZMod N, χ a * (2 * completedHurwitzZetaOdd (ZMod.toAddCircle a) s)) := by
  refine HasMellin.finsetSum fun a _ ↦ ?_
  have h := (isStrong_hurwitzOddFEPair (ZMod.toAddCircle a)).hasMellin ((s + 1) / 2)
  rw [completedHurwitzZetaOdd, mul_div_cancel₀ _ two_ne_zero, ← h.2]
  simpa only [smul_eq_mul, hurwitzOddFEPair_f, Function.comp_apply] using
    hasMellin_const_smul h.1 (χ a)

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
  have hNs : (N : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  let F (x : ℝ) := ∑ a : ZMod N, χ a * ((if j = 0 then evenKernel else oddKernel)
    (ZMod.toAddCircle a) x : ℂ)
  have hcore : HasMellin F ((s + j) / 2) (2 * (N : ℂ) ^ s * χ.completedLFunction s) := by
    have hcancel (z : ℂ) : (N : ℂ) ^ s * ((N : ℂ) ^ (-s) * z) = z := by
      rw [cpow_neg, ← mul_assoc, mul_inv_cancel₀ hNs, one_mul]
    rcases hj with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · rw [mul_assoc, completedLFunction, ZMod.completedLFunction_def_even hp.to_fun, hcancel,
        mul_sum]
      simpa only [F, Nat.cast_zero, add_zero, ite_true,
        mul_left_comm (χ _) 2] using hasMellin_even_hurwitz_sum hχ s
    · rw [mul_assoc, completedLFunction, ZMod.completedLFunction_def_odd hp.to_fun, hcancel,
        mul_sum]
      simpa only [F, Nat.cast_one, ite_eq_right Nat.one_ne_zero, mul_left_comm (χ _) 2] using
        hasMellin_odd_hurwitz_sum χ s
  have hsquare : HasMellin (fun u : ℝ ↦ F (u ^ (2 : ℝ))) (s + j)
      ((N : ℂ) ^ s * χ.completedLFunction s) := by
    have h := HasMellin.comp_rpow (a := 2) (s := s + j)
      (by simpa only [ofReal_ofNat] using hcore) (by norm_num)
    simpa only [abs_two, real_smul, ofReal_inv, ofReal_ofNat, mul_assoc,
      inv_mul_cancel_left₀ (two_ne_zero : (2 : ℂ) ≠ 0)] using h
  -- Apply the power weight before dilation so the dilation factor only involves `s`.
  have hd := (hsquare.cpow_smul (s := s) (a := (j : ℂ))).comp_mul_right hN
  have hvalue := hd.2
  simp only [ofReal_natCast, smul_eq_mul, cpow_neg, inv_mul_cancel_left₀ hNs] at hvalue
  have hm := hasMellin_const_smul hd.1 (1 / 2 : ℂ)
  simp only [smul_eq_mul, one_div, inv_mul_eq_div] at hm
  rw [hvalue] at hm
  refine (TauCeti.hasMellin_congr (fun u _ ↦ ?_)).mp hm
  simp only [F, mul_comm u (N : ℝ), Real.rpow_two, cpow_natCast, ofReal_pow]
  ring

/-- The normalized Gaussian theta series of a nonprincipal character, at its matching
parity, has absolutely convergent Mellin transform `Λ(s, χ) / 2` at `s - 1/2`. -/
theorem hasMellin_gaussianThetaSeries_completedLFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {j : Fin 2}
    (hpar : χ (-1) = (-1) ^ j.val) (s : ℂ) :
    HasMellin (TauCeti.gaussianThetaSeries j (fun n ↦ χ n)) (s - 1 / 2)
      (χ.completedLFunction s / 2) := by
  let G (u : ℝ) := ((((N : ℝ) * u) ^ j.val : ℝ) : ℂ) / 2 *
    ∑ a : ZMod N, χ a * ((if j.val = 0 then evenKernel else oddKernel)
      (ZMod.toAddCircle a) ((N * u) ^ 2) : ℂ)
  have hj : (j.val = 0 ∧ χ.Even) ∨ (j.val = 1 ∧ χ.Odd) := by
    fin_cases j
    · exact Or.inl ⟨rfl, by simpa [Even] using hpar⟩
    · exact Or.inr ⟨rfl, by simpa [Odd] using hpar⟩
  have hG (z : ℂ) : HasMellin G z (χ.completedLFunction z / 2) :=
    χ.hasMellin_gaussianTheta_residue_sum hχ hj z
  have hθ {z : ℂ} (hz : 1 < z.re) :
      HasMellin (TauCeti.gaussianTheta j (fun n ↦ χ n)) z (χ.completedLFunction z / 2) := by
    rw [funext (TauCeti.gaussianTheta_eq_gaussianDirichletTheta j _)]
    have hΓ : Gammaℝ (z + j.val) = χ.gammaFactor z := by
      rcases hj with ⟨h, he⟩ | ⟨h, ho⟩
      · simp [h, he.gammaFactor_def]
      · simp [h, ho.gammaFactor_def]
    have h := TauCeti.hasMellin_gaussianDirichletTheta j.val (χ.LSeriesSummable_of_one_lt_re hz)
      (by linarith [Nat.cast_nonneg (α := ℝ) j.val])
    rw [hΓ, ← mul_div_assoc, mul_comm (_root_.LSeries (fun n ↦ χ n) z),
      ← χ.completedLFunction_eq_gammaFactor_mul_LSeries hz] at h
    exact h
  -- Compare on an absolutely convergent line, then transfer the entire Mellin representation.
  have hae := (hθ (z := 2) (by norm_num)).1.ae_eq_of_mellin_eq_on_verticalLine (c := 2)
    (by simpa using (hG 2).1) fun z hz ↦
      (hθ (by rw [mem_ofPred_eq.mp hz]; norm_num)).2.trans (hG z).2.symm
  have h := HasMellin.cpow_smul (s := s - 1 / 2) (a := 1 / 2)
    (by rw [sub_add_cancel]; exact (TauCeti.hasMellin_congr_ae hae).mpr (hG s))
  refine (TauCeti.hasMellin_congr (fun u (hu : 0 < u) ↦ ?_)).mp h
  simp only [TauCeti.gaussianThetaSeries_def, smul_eq_mul, Real.sqrt_eq_rpow,
    ofReal_cpow hu.le, ofReal_div, ofReal_one, ofReal_ofNat]

end DirichletCharacter
