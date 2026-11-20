/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Basic
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype
public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

import TauCeti.Analysis.Normed.Module.GaussianSum.Comparison
import TauCeti.Probability.Distributions.Gaussian.L2
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Gaussian cotype and the `2`-summing norm of maps out of a Euclidean space

A real normed space `Y` has *Gaussian cotype `q` with constant `C`* if every finite family `y`
in `Y` satisfies `‖y‖_q ≤ C G₂(y)`, where `G₂(y) = (𝔼_g ‖∑ i, gᵢ yᵢ‖²)^(1/2)` is the Gaussian
second moment, the `gᵢ` being independent real standard Gaussians. This is Rademacher cotype
with the random signs replaced by Gaussian coefficients.

Rademacher cotype `2` with constant `C` implies Gaussian cotype `2` with the same constant:
apply the cotype inequality to the family `(gᵢ yᵢ)ᵢ` for each value of the Gaussian vector `g`
and integrate. Since every coefficient has second moment `1`, the left side integrates to
`‖y‖₂²`, and since the Gaussian law is invariant under sign changes, the right side integrates
to `C² G₂(y)²`.

Gaussian cotype `2` bounds the `2`-summing norm of every operator `U` from a finite-dimensional
real inner product space with orthonormal basis `(eᵢ)` into `Y`: `π₂(U) ≤ C G₂(U eᵢ)`. Indeed,
for a family `x` of weak `ℓ²` norm `w`, every functional `f` satisfies
`∑ₖ f(U xₖ)² ≤ w² ‖f ∘ U‖² = ∑ᵢ f(w U eᵢ)²`, so Gaussian comparison under weak quadratic
domination gives `G₂(U xₖ) ≤ w G₂(U eᵢ)`, and Gaussian cotype bounds `‖(U xₖ)‖₂` by `C` times
the former. This is the first step of the proof that the `2`-summing norm of such an operator
into a space of cotype `2` is controlled by the Rademacher average of the `U eᵢ` alone.

## Main declarations

* `TauCeti.HasGaussianCotype`: Gaussian cotype `q` with constant `C`.
* `TauCeti.HasGaussianCotype.norm_toLp_le`: the defining inequality for families indexed by any
  finite type.
* `TauCeti.HasCotype.hasGaussianCotype_two`: Rademacher cotype `2` implies Gaussian cotype `2`
  with the same constant.
* `ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype`,
  `ContinuousLinearMap.summingENorm_two_le_of_hasCotype`: `π₂(U) ≤ C G₂(U eᵢ)` for an operator
  `U` out of a finite-dimensional real inner product space with orthonormal basis `(eᵢ)`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*, CBMS Regional
  Conference Series in Mathematics 60, AMS, 1986, §3, pp. 33–37.
* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012), §9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (Y) in
/-- `Y` has *Gaussian cotype `q` with constant `C`* if every finite family `y` in `Y` satisfies
`‖y‖_q ≤ C G₂(y)`, where `‖y‖_q = ‖WithLp.toLp q y‖` is the `ℓ^q` norm of the family and
`G₂(y) = (𝔼_g ‖∑ i, gᵢ yᵢ‖²)^(1/2)` is its Gaussian second moment, with independent real standard
Gaussian coefficients `gᵢ`. -/
def HasGaussianCotype (q : ℝ≥0∞) (C : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (y : Fin n → Y), ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y

variable {q : ℝ≥0∞} {C C' : ℝ≥0}

/-- The defining inequality of Gaussian cotype `q` with constant `C`, for families indexed by
`Fin n`. -/
theorem hasGaussianCotype_iff :
    HasGaussianCotype Y q C ↔
      ∀ (n : ℕ) (y : Fin n → Y), ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y :=
  Iff.rfl

/-- A Gaussian cotype constant may be enlarged. -/
theorem HasGaussianCotype.mono_const (h : HasGaussianCotype Y q C) (hC : C ≤ C') :
    HasGaussianCotype Y q C' :=
  fun n y ↦ (h n y).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hC) (gaussianSecondMoment_nonneg _))

/-- The Gaussian cotype inequality holds for families indexed by any finite type. -/
theorem HasGaussianCotype.norm_toLp_le {ι : Type*} [Fintype ι] (h : HasGaussianCotype Y q C)
    (y : ι → Y) : ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y := by
  let e := Fintype.equivFin ι
  have hy := h _ (y ∘ e.symm)
  rwa [gaussianSecondMoment_comp_equiv, PiLp.norm_toLp_comp_equiv] at hy

/-- **Gaussian cotype from Rademacher cotype.** Rademacher cotype `2` with constant `C` implies
Gaussian cotype `2` with the same constant. -/
theorem HasCotype.hasGaussianCotype_two (h : HasCotype Y 2 C) : HasGaussianCotype Y 2 C := by
  intro n y
  refine (sq_le_sq₀ (by positivity)
    (mul_nonneg C.2 (gaussianSecondMoment_nonneg _))).1 ?_
  -- For each value `g` of the Gaussian vector, the cotype inequality for `(gᵢ yᵢ)ᵢ`.
  have hpt (g : EuclideanSpace ℝ (Fin n)) :
      ‖WithLp.toLp 2 (fun i ↦ g i • y i)‖ ^ 2 ≤
        (C : ℝ) ^ 2 * Finset.univ.expect fun ε : Fin n → ℤˣ ↦ ‖∑ i, g i • ε i • y i‖ ^ 2 := by
    calc ‖WithLp.toLp 2 (fun i ↦ g i • y i)‖ ^ 2
        ≤ (C * rademacherSecondMoment fun i ↦ g i • y i) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h.norm_toLp_le _) 2
      _ = _ := by
          rw [mul_pow, rademacherSecondMoment_sq]
          simp_rw [smul_comm (g _)]
  have hint (ε : Fin n → ℤˣ) :
      Integrable (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖∑ i, g i • ε i • y i‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    integrable_norm_sq_gaussianSum fun i ↦ ε i • y i
  calc ‖WithLp.toLp 2 y‖ ^ 2
      = ∫ g : EuclideanSpace ℝ (Fin n), ‖WithLp.toLp 2 (fun i ↦ g i • y i)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        -- Each Gaussian coefficient `gᵢ = ⟪eᵢ, g⟫` has second moment `1`.
        have hg (i : Fin n) (g : EuclideanSpace ℝ (Fin n)) :
            g i = inner ℝ (EuclideanSpace.single i 1) g := by
          simp [EuclideanSpace.inner_single_left]
        simp_rw [PiLp.norm_sq_eq_of_L2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hg]
        rw [integral_finsetSum _ fun i _ ↦
          ((Probability.memLp_inner_stdGaussian _ 2 (by simp)).integrable_sq).mul_const _]
        simp [integral_mul_const, Probability.integral_sq_inner_stdGaussian]
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin n), (C : ℝ) ^ 2 *
          Finset.univ.expect fun ε : Fin n → ℤˣ ↦ ‖∑ i, g i • ε i • y i‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity) ?_
        (.of_forall hpt)
      simp_rw [Finset.expect_eq_sum_div_card]
      exact ((integrable_finsetSum _ fun ε _ ↦ hint ε).div_const _).const_mul _
    _ = (C : ℝ) ^ 2 * gaussianSecondMoment y ^ 2 := by
      simp_rw [integral_const_mul, Finset.expect_eq_sum_div_card]
      rw [integral_div, integral_finsetSum _ fun ε _ ↦ hint ε]
      simp_rw [← gaussianSecondMoment_sq, gaussianSecondMoment_units_smul]
      simp
    _ = (C * gaussianSecondMoment y) ^ 2 := by ring

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {ι E Y : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}

/-- **The `2`-summing norm under Gaussian cotype.** If `Y` has Gaussian cotype `2` with constant
`C`, then every operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into
`Y` satisfies `π₂(U) ≤ C G₂(U eᵢ)`. -/
theorem summingENorm_two_le_of_hasGaussianCotype (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E)
    (h : HasGaussianCotype Y 2 C) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment fun i ↦ U (b i)) := by
  refine (summingENorm_le_ofReal_iff (mul_nonneg C.2 (gaussianSecondMoment_nonneg _))).2 ?_
  intro n x
  set w := weakLpNorm (𝕜 := ℝ) 2 x
  have hw : 0 ≤ w := apply_nonneg _ _
  -- Every functional has a smaller square sum on `(U xₖ)ₖ` than on `(w • U eᵢ)ᵢ`.
  have hdom (f : StrongDual ℝ Y) :
      ∑ k, |f (U (x k))| ^ 2 ≤ ∑ i, |f (w • U (b i))| ^ 2 := by
    have hf := sum_norm_eval_rpow_le_weakLpNorm (𝕜 := ℝ) 2 (by simp) x (f.comp U)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, comp_apply, Real.norm_eq_abs] at hf
    refine hf.trans_eq ?_
    rw [mul_pow, b.norm_dual, Finset.mul_sum]
    simp [w, mul_pow]
  calc ‖WithLp.toLp 2 fun k ↦ U (x k)‖
      ≤ C * gaussianSecondMoment fun k ↦ U (x k) := h.norm_toLp_le _
    _ ≤ C * gaussianSecondMoment fun i ↦ w • U (b i) := by
      gcongr
      exact gaussianSecondMoment_le_of_weakTwo_le _ _ hdom
    _ = C * gaussianSecondMoment (fun i ↦ U (b i)) * w := by
      rw [gaussianSecondMoment_smul, abs_of_nonneg hw]
      ring

/-- **The `2`-summing norm under cotype `2`.** If `Y` has Rademacher cotype `2` with constant
`C`, then every operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into
`Y` satisfies `π₂(U) ≤ C G₂(U eᵢ)`. -/
theorem summingENorm_two_le_of_hasCotype (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E)
    (h : HasCotype Y 2 C) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment fun i ↦ U (b i)) :=
  U.summingENorm_two_le_of_hasGaussianCotype b h.hasGaussianCotype_two

end ContinuousLinearMap
