/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.TristramLevine.Averaged
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Tristram--Levine signature near one

For a real matrix `V` with nonsingular skew part `V - Vᵀ`, the Tristram--Levine signature
vanishes on a neighbourhood of `1` in the unit circle. This applies to knot Seifert matrices,
whose skew parts are unimodular, and includes the empty matrix. It need not hold for link
Seifert matrices with singular skew part.

Although the Hermitian form itself is zero at `1`, dividing its value at `exp(iθ)` by `θ`
gives a family converging to the nonsingular Hermitian matrix `i(Vᵀ - V)`. Conjugation
negates the limiting matrix, so its signature is zero. Local constancy of the Hermitian
signature at a nonsingular matrix, from
`Matrix.IsHermitian.eventually_signature_eq`, then gives the vanishing result on both
sides. Consequently the averaged signature is also zero at `1`.

## References

* A. Conway, [*The Levine--Tristram signature: a survey*](https://arxiv.org/abs/1903.04477),
  Remark 2.2 (vanishing near one for knots) and Section 2.4 (averaged signatures).
-/

public section

open Filter Topology Matrix
open scoped ComplexConjugate

namespace TauCeti.KnotTheory

variable {ι : Type*}

private theorem inv_smul_tristramLevineForm_exp (V : Matrix ι ι ℝ) (θ : ℝ) :
    θ⁻¹ • tristramLevineForm V (Circle.exp θ) =
      ((1 - Real.cos θ) / θ) • (V + Vᵀ).map ((↑) : ℝ → ℂ) +
        (Real.sin θ / θ) • (Complex.I • (Vᵀ - V).map ((↑) : ℝ → ℂ)) := by
  ext i j
  simp [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The rescaled Tristram--Levine forms at `exp(iθ)` tend to `i(Vᵀ - V)` as `θ → 0`,
with `θ ≠ 0`. Thus the singularity of the rescaled family at zero is removable. -/
theorem tendsto_inv_smul_tristramLevineForm_exp_nhdsNE_zero (V : Matrix ι ι ℝ) :
    Tendsto (fun θ : ℝ => θ⁻¹ • tristramLevineForm V (Circle.exp θ)) (𝓝[≠] 0)
      (𝓝 (Complex.I • (Vᵀ - V).map ((↑) : ℝ → ℂ))) := by
  have h := (Real.tendsto_one_sub_cos_div_nhdsNE_zero.smul_const
      ((V + Vᵀ).map ((↑) : ℝ → ℂ))).add
    (Real.tendsto_sin_div_nhdsNE_zero.smul_const
      (Complex.I • (Vᵀ - V).map ((↑) : ℝ → ℂ)))
  simpa only [zero_smul, one_smul, zero_add, inv_smul_tristramLevineForm_exp] using h

variable [Fintype ι] [DecidableEq ι]

/-- If the skew part of `V` is nonsingular, its signature vanishes at every sufficiently
small angle, on both sides of zero and at zero itself. -/
theorem eventually_tristramLevineSignature_exp_eq_zero (V : Matrix ι ι ℝ)
    (hV : (V - Vᵀ).det ≠ 0) :
    ∀ᶠ θ : ℝ in 𝓝 0, tristramLevineSignature V (Circle.exp θ) = 0 := by
  let A := Complex.I • (Vᵀ - V).map ((↑) : ℝ → ℂ)
  have hA : A.IsHermitian := by
    ext i j
    simp [A, Matrix.conjTranspose_apply, smul_eq_mul]
    ring
  have hstar : A.map (starRingEnd ℂ) = -A := by
    ext i j
    simp [A, smul_eq_mul]
  have hsig : hA.signature = 0 := by
    have h : hA.neg.signature = hA.signature := by
      convert hA.signature_map_starRingEnd using 2
      exact hstar.symm
    rw [hA.signature_neg] at h
    omega
  have hskew : (Vᵀ - V).det ≠ 0 := by
    rw [← neg_sub V Vᵀ, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hV
  have hmap : IsUnit ((Vᵀ - V).map ((↑) : ℝ → ℂ)).det :=
    RingHom.map_det Complex.ofRealHom (Vᵀ - V) ▸
      (isUnit_iff_ne_zero.mpr hskew).map Complex.ofRealHom
  have hdet : IsUnit A.det := by
    dsimp only [A]
    rw [det_smul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ Complex.I_ne_zero)).mul hmap
  have hlim := tendsto_inv_smul_tristramLevineForm_exp_nhdsNE_zero V
  have hev := hlim.eventually (hA.eventually_signature_eq hdet)
  have hzero : ∀ᶠ θ : ℝ in 𝓝[≠] 0, tristramLevineSignature V (Circle.exp θ) = 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with θ hθ hθ0
    have hs := hθ ((isHermitian_tristramLevineForm V (Circle.exp θ)).smul
      (isSelfAdjoint_iff.mpr (star_trivial (θ⁻¹))))
    rw [hsig] at hs
    rcases lt_or_gt_of_ne hθ0 with hneg | hpos
    · rw [(isHermitian_tristramLevineForm V _).signature_smul_of_neg (inv_lt_zero'.mpr hneg)] at hs
      simpa only [tristramLevineSignature_def] using neg_eq_zero.mp hs
    · rw [(isHermitian_tristramLevineForm V _).signature_smul_of_pos (inv_pos.mpr hpos)] at hs
      simpa only [tristramLevineSignature_def] using hs
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hzero (by simp)

/-- For a real Seifert matrix with nonsingular skew part, the raw signature vanishes on a
neighbourhood of `1` in the circle. No unimodularity or prescribed matrix size is needed. -/
theorem eventually_tristramLevineSignature_eq_zero_nhds_one (V : Matrix ι ι ℝ)
    (hV : (V - Vᵀ).det ≠ 0) :
    ∀ᶠ ω : Circle in 𝓝 1, tristramLevineSignature V ω = 0 := by
  rw [← Circle.exp_zero, ← isLocalHomeomorph_circleExp.map_nhds_eq 0]
  exact eventually_tristramLevineSignature_exp_eq_zero V hV

/-- The averaged signature at `1` is zero whenever the skew part of the Seifert matrix is
nonsingular, so there it agrees with the raw signature, which is zero by
`tristramLevineSignature_one`. -/
@[simp]
theorem averagedTristramLevineSignature_one (V : Matrix ι ι ℝ)
    (hV : (V - Vᵀ).det ≠ 0) : averagedTristramLevineSignature V 1 = 0 := by
  have h := eventually_tristramLevineSignature_exp_eq_zero V hV
  rw [averagedTristramLevineSignature_eq_of_eventually (a := 0) (b := 0)
    (by simpa using h.filter_mono nhdsWithin_le_nhds)
    (by simpa using h.filter_mono nhdsWithin_le_nhds)]
  norm_num

end TauCeti.KnotTheory
