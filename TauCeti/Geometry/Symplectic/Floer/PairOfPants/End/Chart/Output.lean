/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# The positive end chart of the output end

The positive end chart `φ'_∞` (`TauCeti.Floer.positiveEndChart inf`) of the output end of the pair
of pants `S = ℂ ∖ {0, 1}` sends `(s, t)` to `2 exp (2π (s + i t))`, read in real coordinates. This
file records its norm and direction, and how it moves under a translation of the plane.

## Main results

* `TauCeti.Floer.norm_equivRealProdCLM_symm_positiveEndChart_inf`,
  `TauCeti.Floer.equivRealProdCLM_symm_positiveEndChart_inf_div_norm`: the output end, read in
  the positive end chart at `(s, t)`, lies at the norm `2 exp (2πs)` in the direction
  `exp (2π i t)`; so beyond the height `max R 0` it lies at distance at least `R` from `0`
  (`TauCeti.Floer.le_norm_equivRealProdCLM_symm_positiveEndChart_inf`).
* `TauCeti.Floer.mem_image_positiveEndChart_inf_of_two_lt_norm`: off the disc `‖w‖ ≤ 2` the plane
  lies in the image of the band `(0, ∞) × [0, 1)` under `φ'_∞`.
* `TauCeti.Floer.exists_positiveEndChart_inf_eq_add`: a point beyond the height `T + 1` of `φ'_∞`
  lies beyond the height `T` of the end chart `c + φ'_∞` recentred at `c`, for `|c| ≤ 1`.
  Whenever `φ'_∞(ζ) = φ'_∞(ζ') + c`, read in `ℂ` the point `φ'_∞(ζ')` is `φ'_∞(ζ) - c`
  (`TauCeti.Floer.equivRealProdCLM_symm_positiveEndChart_inf_eq_sub`).
* `TauCeti.Floer.positiveEndChart_inf_add_mem_thricePuncturedSphereReal`: beyond the height `1`,
  the output end translated by `c` with `|c| ≤ 1` stays in `S`.
-/

public section

open Set Real TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

/-- The output end, read in the positive end chart `φ'_∞`, lies at the norm `2 exp (2πs)`. -/
theorem norm_equivRealProdCLM_symm_positiveEndChart_inf (s t : ℝ) :
    ‖Complex.equivRealProdCLM.symm (positiveEndChart inf (s, t))‖ = 2 * exp (2 * π * s) := by
  have h := norm_cylindricalEndLift_sub_endCenter inf
    (Complex.equivRealProdCLM.symm (inf.endSign • (s, t)))
  rw [positiveEndChart_apply, equivRealProdCLM_symm_endChart]
  simpa using h

/-- The output end, read in the positive end chart `φ'_∞` at `ζ`, lies at the norm `2 exp (2π ζ₁)`:
the form of `norm_equivRealProdCLM_symm_positiveEndChart_inf` for a point `ζ` of the strip. -/
theorem norm_equivRealProdCLM_symm_positiveEndChart_inf' (ζ : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)‖ = 2 * exp (2 * π * ζ.1) := by
  rw [← norm_equivRealProdCLM_symm_positiveEndChart_inf ζ.1 ζ.2, Prod.mk.eta]

/-- Beyond the height `max R 0` of the output end, points are at distance at least `R` from `0`. -/
theorem le_norm_equivRealProdCLM_symm_positiveEndChart_inf {R : ℝ} {ζ : ℝ × ℝ}
    (hζ : max R 0 ≤ ζ.1) : R ≤ ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)‖ := by
  rw [norm_equivRealProdCLM_symm_positiveEndChart_inf']
  have := add_one_le_exp (2 * π * ζ.1)
  nlinarith [le_max_left R 0, le_max_right R 0, two_le_pi]

/-- The output end, read in the positive end chart `φ'_∞` at `(s, t)`, lies in the direction
`exp (2π i t)`. -/
theorem equivRealProdCLM_symm_positiveEndChart_inf_div_norm (ζ : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) /
        ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)‖ =
      Complex.exp ((2 * π * ζ.2 : ℝ) * Complex.I) := by
  obtain ⟨s, t⟩ := ζ
  have h : Complex.equivRealProdCLM.symm (positiveEndChart inf (s, t)) =
      (2 * Real.exp (2 * π * s) : ℝ) * Complex.exp ((2 * π * t : ℝ) * Complex.I) := by
    rw [positiveEndChart_apply, equivRealProdCLM_symm_endChart, cylindricalEndLift_inf,
      endSign_inf]
    simp only [neg_smul, one_smul, Prod.neg_mk, Complex.equivRealProdCLM_symm_apply,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [norm_equivRealProdCLM_symm_positiveEndChart_inf, h]
  have h2 : ((2 * Real.exp (2 * π * s) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  field_simp

/-- A point at distance more than `2` from `0` lies in the image of the band `(0, ∞) × [0, 1)`
under the positive end chart of the output end. -/
theorem mem_image_positiveEndChart_inf_of_two_lt_norm {v : ℝ × ℝ}
    (hv : 2 < ‖Complex.equivRealProdCLM.symm v‖) :
    v ∈ positiveEndChart inf '' (Ioi 0 ×ˢ Ico 0 1) := by
  have hv0 : Complex.equivRealProdCLM.symm v ≠ 0 := norm_pos_iff.1 (by linarith)
  refine ⟨endBandCoord inf v, ⟨?_, (endBandCoord_mem inf v).2⟩,
    positiveEndChart_endBandCoord inf (by rwa [endCenter_inf])⟩
  rw [endBandCoord_apply, mem_Ioi, lt_fst_positiveEndCoord_inf_iff hv0, mul_zero, exp_zero,
    mul_one]
  exact hv

/-- A point beyond the height `T + 1` of the standard end chart `φ'_∞` of the output end, with
`T ≥ 0`, lies beyond the height `T` of the end chart `c + φ'_∞` recentred at `c`, for `|c| ≤ 1`:
it is `φ'_∞(ζ') + c` for some `ζ' = (s, t)` with `s > T` and `t ∈ [0, 1)`. -/
theorem exists_positiveEndChart_inf_eq_add {c : ℝ} (hc : |c| ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    {ζ : ℝ × ℝ} (hζ : T + 1 < ζ.1) :
    ∃ ζ' : ℝ × ℝ, T < ζ'.1 ∧ ζ'.2 ∈ Ico (0 : ℝ) 1 ∧
      positiveEndChart inf ζ = positiveEndChart inf ζ' + (c, 0) := by
  set w := positiveEndChart inf ζ - (c, 0)
  have hz0 := equivRealProdCLM_symm_positiveEndChart_ne_endCenter inf ζ
  rw [endCenter_inf] at hz0
  have hz := (lt_fst_positiveEndCoord_inf_iff hz0).1 (by
    rwa [fst_positiveEndCoord_positiveEndChart])
  have hcn : ‖(c : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  -- `|w| ≥ |φ'_∞(ζ)| - 1 > 2 exp (2π (T + 1)) - 1 ≥ 2 exp (2π T)`.
  have hw : 2 * exp (2 * π * T) < ‖Complex.equivRealProdCLM.symm w‖ := by
    have hsub : Complex.equivRealProdCLM.symm w =
        Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) - c :=
      TauCeti.Complex.equivRealProdCLM_symm_sub_prodMk_zero _ c
    have hexp : 2 * exp (2 * π * T) + 1 ≤ 2 * exp (2 * π * (T + 1)) := by
      rw [mul_add, mul_one, exp_add]
      nlinarith [fourteen_le_two_mul_exp_two_pi, one_le_exp (by positivity : 0 ≤ 2 * π * T)]
    rw [hsub]
    linarith [norm_sub_norm_le (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)) (c : ℂ)]
  have hw0 : Complex.equivRealProdCLM.symm w ≠ 0 :=
    norm_pos_iff.1 ((by positivity : 0 < 2 * exp (2 * π * T)).trans hw)
  refine ⟨endBandCoord inf w, ?_, (endBandCoord_mem inf w).2, ?_⟩
  · rw [endBandCoord_apply]
    exact (lt_fst_positiveEndCoord_inf_iff hw0).2 hw
  · rw [positiveEndChart_endBandCoord inf (by rwa [endCenter_inf]), sub_add_cancel]

/-- If `φ'_∞(ζ) = φ'_∞(ζ') + c`, then, read in `ℂ`, the point `φ'_∞(ζ')` is `φ'_∞(ζ) - c`. -/
theorem equivRealProdCLM_symm_positiveEndChart_inf_eq_sub {c : ℝ} {ζ ζ' : ℝ × ℝ}
    (hζζ' : positiveEndChart inf ζ = positiveEndChart inf ζ' + (c, 0)) :
    Complex.equivRealProdCLM.symm (positiveEndChart inf ζ') =
      Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) - c := by
  rw [hζζ', TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero, add_sub_cancel_right]

/-- A point beyond the height `1` of the output end, translated by `c` with `|c| ≤ 1`, lies on
the pair of pants `S`: it is at distance at least `2` from `0`. -/
theorem positiveEndChart_inf_add_mem_thricePuncturedSphereReal {c : ℝ} (hc : |c| ≤ 1)
    {ζ : ℝ × ℝ} (hζ : 1 ≤ ζ.1) : positiveEndChart inf ζ + (c, 0) ∈ thricePuncturedSphereReal := by
  set Z := Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)
  have hn : ‖Z‖ = 2 * exp (2 * π * ζ.1) := norm_equivRealProdCLM_symm_positiveEndChart_inf' ζ
  have h2π : 2 * π ≤ 2 * π * ζ.1 := le_mul_of_one_le_right (by positivity) hζ
  have h14 : (14 : ℝ) ≤ 2 * exp (2 * π * ζ.1) :=
    fourteen_le_two_mul_exp_two_pi.trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.2 h2π) zero_le_two)
  have hcn : ‖(c : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  refine mem_thricePuncturedSphereReal_of_two_le_norm ?_
  rw [TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero]
  have := norm_sub_norm_le Z (-(c : ℂ))
  rw [sub_neg_eq_add, norm_neg] at this
  linarith

end TauCeti.Floer
