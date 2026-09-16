/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Wishart.Nonsingular

/-!
# The scale of the nonsingular Wishart law

Congruence `A ↦ C * A * Cᵀ` by an invertible matrix carries the nonsingular Wishart law of scale
`S` to the one of scale `C * S * Cᵀ`, because the density and the congruence Jacobian cancel
exactly. Substituting `C⁻¹ B C⁻ᵀ` for the argument multiplies the determinant factor
`(det A) ^ ((n - p - 1) / 2)` of the density by `|det C| ^ (p + 1 - n)`, and reading the density
at the scale `S` rather than at `C * S * Cᵀ` multiplies it by a further `|det C| ^ n`, since the
scale enters the normalizing constant through `(det S) ^ (n / 2)`. Their product `|det C| ^ (p + 1)`
is exactly the factor by which congruence rescales `TauCeti.symmetricLebesgue`.

This makes the scale parameter inessential where the law is not the zero measure: a nonsingular
Wishart law of positive-definite scale is a congruence image of the standard one, whose scale is
the identity matrix, so any property preserved by congruence pushforward transfers from the
standard scale to every positive-definite one. The total mass is such a property. At the scale
`2⁻¹ • 1` the exponential weight of the density is `exp (-trace A)` and the normalizing constant
collapses to `Γ_p (n / 2)`, so the mass is the multivariate Gamma integral
`TauCeti.lintegral_posDef_multivariateGamma` divided by that constant, namely `1`, and congruence
spreads this to every positive-definite scale.

## Main results

* `TauCeti.map_symmetricCongruence_nonsingularWishartMeasure` — congruence by an invertible
  matrix carries the law of scale `S` to the law of scale `C * S * Cᵀ`;
* `TauCeti.nonsingularWishartMeasure_eq_map_sqrt` — a nonsingular Wishart law of positive-definite
  scale is the standard one transported by the congruence with the square root of that scale;
* `TauCeti.isProbabilityMeasure_nonsingularWishartMeasure` — the law is a probability measure at
  exactly the parameters where a density defines it.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapters 2 and 3.
* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes 53,
  chapter 8.
-/

public section

noncomputable section

open MeasureTheory

open scoped Matrix MatrixOrder

namespace TauCeti

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-! ### Congruence -/

/-- **The substituted Wishart density.** Undoing congruence by `C` in the density of scale `S`
gives the density of scale `C * S * Cᵀ`, times the Jacobian factor `|det C| ^ (p + 1)` that the
change of variables contributes. -/
private theorem nonsingularWishartPDFReal_symmetricCongruence_inv (hS : S.PosDef)
    (C : Matrix.GeneralLinearGroup (Fin p) ℝ)
    {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hB : (B : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    nonsingularWishartPDFReal n S (Matrix.GeneralLinearGroup.symmetricCongruence C⁻¹ B) =
      |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) *
        nonsingularWishartPDFReal n
          ((C : Matrix (Fin p) (Fin p) ℝ) * S * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ) B := by
  set Cm : Matrix (Fin p) (Fin p) ℝ := (C : Matrix (Fin p) (Fin p) ℝ) with hCm
  set Bm : Matrix (Fin p) (Fin p) ℝ := (B : Matrix (Fin p) (Fin p) ℝ)
  have hd : Cm.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero C
  have hCu : IsUnit Cm := (Matrix.isUnit_iff_isUnit_det Cm).2 (isUnit_iff_ne_zero.2 hd)
  have hdinv : (Cm⁻¹).det = (Cm.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hA : ((Matrix.GeneralLinearGroup.symmetricCongruence C⁻¹ B :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : Matrix (Fin p) (Fin p) ℝ) =
      Cm⁻¹ * Bm * (Cm⁻¹)ᵀ := by
    rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, hCm, Matrix.coe_units_inv]
  -- over `ℝ` the star of a matrix is its transpose, so the conjugation criterion applies as is
  have hApos : (Cm⁻¹ * Bm * (Cm⁻¹)ᵀ).PosDef :=
    (Matrix.IsUnit.posDef_star_right_conjugate_iff (Matrix.isUnit_nonsing_inv_iff.2 hCu)).2 hB
  have hdetA : (Cm⁻¹ * Bm * (Cm⁻¹)ᵀ).det = (Cm.det ^ 2)⁻¹ * Bm.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdinv, sq, mul_inv]
    ring
  have hdetT : (Cm * S * Cmᵀ).det = Cm.det ^ 2 * S.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  -- cyclicity of the trace moves the two inverse factors onto the scale matrix
  have htrace : Matrix.trace (S⁻¹ * (Cm⁻¹ * Bm * (Cm⁻¹)ᵀ)) =
      Matrix.trace ((Cm * S * Cmᵀ)⁻¹ * Bm) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
  rw [nonsingularWishartPDFReal_of_posDef n S (hA ▸ hApos),
    nonsingularWishartPDFReal_of_posDef n _ hB, hA, hdetA, hdetT, htrace]
  set d : ℝ := Cm.det ^ 2 with hdsq
  have hdpos : 0 < d := by positivity
  have hsplit : ((d⁻¹ * Bm.det) : ℝ) ^ ((n - (p : ℝ) - 1) / 2) =
      (d ^ ((n - (p : ℝ) - 1) / 2))⁻¹ * Bm.det ^ ((n - (p : ℝ) - 1) / 2) := by
    rw [Real.mul_rpow (inv_nonneg.2 hdpos.le) hB.det_pos.le, Real.inv_rpow hdpos.le]
  have hconst : ((d * S.det) : ℝ) ^ (n / 2) = d ^ (n / 2) * S.det ^ (n / 2) :=
    Real.mul_rpow hdpos.le hS.det_pos.le
  have hfac : |Cm.det| ^ (p + 1) = d ^ (n / 2) / d ^ ((n - (p : ℝ) - 1) / 2) := by
    rw [← Real.rpow_sub hdpos, hdsq, ← sq_abs Cm.det, ← Real.rpow_natCast |Cm.det| 2,
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_natCast |Cm.det| (p + 1)]
    congr 1
    push_cast
    ring
  rw [hsplit, hconst, hfac]
  have h1 : d ^ ((n - (p : ℝ) - 1) / 2) ≠ 0 := (Real.rpow_pos_of_pos hdpos _).ne'
  have h2 : d ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hdpos _).ne'
  field_simp
  ring

/-- **Congruence carries the nonsingular Wishart law of scale `S` to the one of scale
`C * S * Cᵀ`.** No hypothesis is needed: congruence by an invertible matrix preserves positive
definiteness, so the two sides are zero together outside the classical parameter range. -/
theorem map_symmetricCongruence_nonsingularWishartMeasure (n : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    (nonsingularWishartMeasure n S).map
        (Matrix.GeneralLinearGroup.symmetricCongruence C) =
      nonsingularWishartMeasure n
        ((C : Matrix (Fin p) (Fin p) ℝ) * S * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ) := by
  have hCu : IsUnit (C : Matrix (Fin p) (Fin p) ℝ) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_ne_zero.2 (Matrix.GeneralLinearGroup.det_ne_zero C))
  rcases le_or_gt n ((p : ℝ) - 1) with hn | hn
  · rw [nonsingularWishartMeasure_of_le S hn, nonsingularWishartMeasure_of_le _ hn,
      Measure.map_zero]
  by_cases hS : S.PosDef
  · have hT : ((C : Matrix (Fin p) (Fin p) ℝ) * S * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ).PosDef :=
      (Matrix.IsUnit.posDef_star_right_conjugate_iff hCu).2 hS
    rw [nonsingularWishartMeasure_of_posDef hS hn, nonsingularWishartMeasure_of_posDef hT hn]
    have hfun : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (0 : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) +
          Matrix.GeneralLinearGroup.symmetricCongruence C A) =
        ⇑(Matrix.GeneralLinearGroup.symmetricCongruence C) := funext fun A => zero_add _
    have hmap := Measure.map_affine_withDensity (symmetricLebesgue p)
      (Matrix.GeneralLinearGroup.symmetricCongruence C) 0 (nonsingularWishartPDF n S)
    rw [hfun] at hmap
    rw [hmap]
    refine congrArg _ (funext fun B => ?_)
    simp only [sub_zero, Matrix.GeneralLinearGroup.symmetricCongruence_symm,
      Matrix.GeneralLinearGroup.det_symmetricCongruence]
    by_cases hB : (B : Matrix (Fin p) (Fin p) ℝ).PosDef
    · rw [nonsingularWishartPDF_def, nonsingularWishartPDF_def,
        nonsingularWishartPDFReal_symmetricCongruence_inv hS C hB,
        ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, abs_pow]
      refine congrArg ENNReal.ofReal ?_
      have hdne : |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) ≠ 0 :=
        pow_ne_zero _ (abs_ne_zero.2 (Matrix.GeneralLinearGroup.det_ne_zero C))
      rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
    · have hBc : ¬ ((Matrix.GeneralLinearGroup.symmetricCongruence C⁻¹ B :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
            Matrix (Fin p) (Fin p) ℝ).PosDef := by
        rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply]
        exact fun h => hB ((Matrix.IsUnit.posDef_star_right_conjugate_iff
          ((Matrix.isUnit_iff_isUnit_det _).2
            (isUnit_iff_ne_zero.2 (Matrix.GeneralLinearGroup.det_ne_zero C⁻¹)))).1 h)
      rw [nonsingularWishartPDF_of_not_posDef _ _ hBc,
        nonsingularWishartPDF_of_not_posDef _ _ hB, mul_zero]
  · have hT : ¬ ((C : Matrix (Fin p) (Fin p) ℝ) * S * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ).PosDef :=
      fun h => hS ((Matrix.IsUnit.posDef_star_right_conjugate_iff hCu).1 h)
    rw [nonsingularWishartMeasure_of_not_posDef n hS, Measure.map_zero,
      nonsingularWishartMeasure_of_not_posDef n hT]

/-! ### The standard scale -/

/-- At the scale `2⁻¹ • 1` the exponential weight of the Wishart density is `exp (-trace A)` and
the normalizing constant is `Γ_p (n / 2)`, so its total mass is the multivariate Gamma integral
divided by that constant. -/
private theorem isProbabilityMeasure_nonsingularWishartMeasure_inv_two_smul_one
    (hn : (p : ℝ) - 1 < n) :
    IsProbabilityMeasure
      (nonsingularWishartMeasure n ((2 : ℝ)⁻¹ • (1 : Matrix (Fin p) (Fin p) ℝ))) := by
  set S₀ : Matrix (Fin p) (Fin p) ℝ := (2 : ℝ)⁻¹ • 1 with hS₀def
  have hS₀ : S₀.PosDef := Matrix.PosDef.smul Matrix.PosDef.one (by norm_num)
  have hinv : S₀⁻¹ = (2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hS₀def, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    norm_num
  have hdet : S₀.det = ((2 : ℝ)⁻¹) ^ p := by
    rw [hS₀def, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hΓ : 0 < multivariateGamma p (n / 2) := multivariateGamma_pos (by linarith)
  -- the two powers of two in the normalizing constant cancel
  have hnorm : (2 : ℝ) ^ (n * (p : ℝ) / 2) * S₀.det ^ (n / 2) * multivariateGamma p (n / 2) =
      multivariateGamma p (n / 2) := by
    have hpow : (((2 : ℝ)⁻¹ ^ p) ^ (n / 2) : ℝ) = (2 : ℝ) ^ (-(n * (p : ℝ) / 2)) := by
      rw [← Real.rpow_natCast ((2 : ℝ)⁻¹) p, ← Real.rpow_neg_one (2 : ℝ),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hdet, hpow, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
  -- off the positive-definite cone the density vanishes
  have hcone : ∫⁻ A, nonsingularWishartPDF n S₀ A ∂symmetricLebesgue p =
      ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}, nonsingularWishartPDF n S₀ A
          ∂symmetricLebesgue p := by
    rw [← lintegral_add_compl _ (measurableSet_posDefMatrix p),
      setLIntegral_eq_zero (measurableSet_posDefMatrix p).compl
        (fun A hA => nonsingularWishartPDF_of_not_posDef n S₀ hA), add_zero]
  -- on the cone the density is the multivariate Gamma integrand over its own constant
  have hpt : ∀ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef →
      nonsingularWishartPDF n S₀ A =
        ENNReal.ofReal (multivariateGamma p (n / 2))⁻¹ *
          ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (n / 2 - ((p : ℝ) + 1) / 2) *
            Real.exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace)) := by
    intro A hA
    rw [nonsingularWishartPDF_of_posDef n S₀ hA, hnorm, hinv,
      ← ENNReal.ofReal_mul (by positivity)]
    refine congrArg ENNReal.ofReal ?_
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
    ring_nf
  constructor
  rw [nonsingularWishartMeasure_of_posDef hS₀ hn, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hcone,
    setLIntegral_congr_fun (measurableSet_posDefMatrix p) hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_posDef_multivariateGamma (by linarith : ((p : ℝ) - 1) / 2 < n / 2),
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hΓ.ne', ENNReal.ofReal_one]

/-! ### Reduction to a scalar scale -/

/-- A nonsingular Wishart law of positive-definite scale is a congruence image of one whose scale
is a positive multiple of the identity: for positive `c`, the congruence with the square root of
`c⁻¹ • S` carries the law of scale `c • 1` to the law of scale `S`. -/
private theorem nonsingularWishartMeasure_eq_map_sqrt_smul_one (n : ℝ) (hS : S.PosDef) {c : ℝ}
    (hc : 0 < c) :
    nonsingularWishartMeasure n S =
      (nonsingularWishartMeasure n (c • (1 : Matrix (Fin p) (Fin p) ℝ))).map
        (Matrix.symmetricCongruenceLinearMap (CFC.sqrt (c⁻¹ • S))) := by
  have hT : (c⁻¹ • S).PosDef := Matrix.PosDef.smul hS (inv_pos.2 hc)
  have hsq : CFC.sqrt (c⁻¹ • S) * CFC.sqrt (c⁻¹ • S) = c⁻¹ • S :=
    CFC.sqrt_mul_sqrt_self _ hT.posSemidef.nonneg
  have hherm : (CFC.sqrt (c⁻¹ • S))ᵀ = CFC.sqrt (c⁻¹ • S) := by
    have h := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (c⁻¹ • S))).1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hCu : IsUnit (CFC.sqrt (c⁻¹ • S)) := hT.isStrictlyPositive.isUnit_cfcSqrt _
  have hcoe : ((hCu.unit : Matrix.GeneralLinearGroup (Fin p) ℝ) :
      Matrix (Fin p) (Fin p) ℝ) = CFC.sqrt (c⁻¹ • S) := hCu.unit_spec
  have hscale : ((hCu.unit : Matrix.GeneralLinearGroup (Fin p) ℝ) :
        Matrix (Fin p) (Fin p) ℝ) * (c • 1) *
      ((hCu.unit : Matrix.GeneralLinearGroup (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ)ᵀ = S := by
    rw [hcoe, hherm, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hsq, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul]
  have hmap := map_symmetricCongruence_nonsingularWishartMeasure n (c • 1)
    (hCu.unit : Matrix.GeneralLinearGroup (Fin p) ℝ)
  rw [hscale] at hmap
  have hfun : ⇑(Matrix.GeneralLinearGroup.symmetricCongruence
        (hCu.unit : Matrix.GeneralLinearGroup (Fin p) ℝ)) =
      ⇑(Matrix.symmetricCongruenceLinearMap (CFC.sqrt (c⁻¹ • S))) :=
    funext fun A => Subtype.ext (by
      rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply,
        Matrix.coe_symmetricCongruenceLinearMap_apply, hcoe])
  rw [← hmap, hfun]

/-- **A nonsingular Wishart law of positive-definite scale is the standard one transported by a
congruence.** The congruence with the square root of the scale carries the law of scale `1` to the
law of scale `S`. This is the density-family analogue of
`TauCeti.wishartGramMeasure_eq_map_sqrt`. -/
theorem nonsingularWishartMeasure_eq_map_sqrt (n : ℝ) (hS : S.PosDef) :
    nonsingularWishartMeasure n S =
      (nonsingularWishartMeasure n 1).map
        (Matrix.symmetricCongruenceLinearMap (CFC.sqrt S)) := by
  have h := nonsingularWishartMeasure_eq_map_sqrt_smul_one n hS one_pos
  rwa [inv_one, one_smul, one_smul] at h

/-- **The nonsingular Wishart law is a probability measure** at exactly the parameters where a
density defines it: a positive-definite scale and a degree above `p - 1`. -/
theorem isProbabilityMeasure_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    IsProbabilityMeasure (nonsingularWishartMeasure n S) := by
  have := isProbabilityMeasure_nonsingularWishartMeasure_inv_two_smul_one (p := p) hn
  rw [nonsingularWishartMeasure_eq_map_sqrt_smul_one n hS (by norm_num : (0 : ℝ) < 2⁻¹)]
  infer_instance

end TauCeti
