/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype
public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Analysis.Normed.Module.GaussianSum.Comparison
import TauCeti.Analysis.Normed.Module.RademacherSum.Contraction
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.Distributions.Gaussian.TailMoment

/-!
# Cotype-2 comparison and `2`-summing bounds on finite-dimensional Hilbert spaces

This file proves Pisier's Gaussian comparison and `2`-summing bounds for operators from a
finite-dimensional Hilbert space (or more generally, any space carrying a finite Parseval lower
frame) into a real or complex normed space of Gaussian or Rademacher cotype `2`, without any
completeness hypothesis on the target space `Y`.

1. **Proposition 3.7 (Gaussian cotype `2` implies `π₂` bound via `G₂`).** If `E` is a real
   seminormed space with a finite family `v : ι → E` satisfying `‖g‖² ≤ ∑ i, g (v i)²` for every
   `g : StrongDual ℝ E`, and `Y` has Gaussian cotype `2` with constant `C`, then every
   `U : E →L[ℝ] Y` satisfies `π₂(U) ≤ C * G₂(U ∘ v)`. Specializing to an orthonormal basis gives
   `π₂(U) ≤ C * G₂(U ∘ b)` over `ℝ`, and restricting scalars to `ℝ` with the real Parseval family
   `(bᵢ, I • bᵢ)` gives `π₂(U) ≤ 2 * C * G₂(U ∘ b)` over any `RCLike` field `𝕜`.
2. **Lemma 3.8 (Truncation, absorption, and equivalence of Gaussian and Rademacher cotype `2`).**
   Splitting each coordinate of a standard Gaussian vector `g` at threshold `t ≥ 0` into its
   bounded part `|gᵢ| ≤ t` and tail part `|gᵢ| > t`, Rademacher contraction bounds the bounded sum
   by `t * R₂(y)`, while applying Proposition 3.7, Pietsch domination, and Fubini's theorem bounds
   the tail sum by `C * √(∫_{|x|>t} x² dγ₁) * G₂(y)`. Absorption yields
   `G₂(y) ≤ 2 * t * R₂(y)` whenever `C * √(∫_{|x|>t} x² dγ₁) ≤ 1 / 2`. Using the fourth-moment
   Chebyshev bound `∫_{|x|>t} x² dγ₁ ≤ 3 / t²` with `t = 2 * √3 * C` (and `Subsingleton Y` when
   `C = 0`) yields the explicit comparison `G₂(y) ≤ 4 * √3 * C * R₂(y)` and the Maurey–Pisier
   equivalence `HasGaussianCotype Y 2 C → HasCotype Y 2 (4 * √3 * C²)`.
3. **Theorem 3.9 (`2`-summing bound via Rademacher second moments).** Combining Proposition 3.7
   with Lemma 3.8 gives both the threshold-parametric bounds `2 * C * t * R₂(U ∘ b)` over `ℝ`
   and `4 * C * t * R₂(U ∘ b)` over `RCLike 𝕜`, and the explicit closed-form bounds
   `4 * √3 * C² * R₂(U ∘ b)` over `ℝ` and `8 * √3 * C² * R₂(U ∘ b)` over `RCLike 𝕜`, valid for
   all `C : ℝ≥0` (including `C = 0`), empty index types, and arbitrary (possibly incomplete)
   target spaces `Y`.

## Main results

* `ContinuousLinearMap.summingENorm_two_le_of_sum_sq_ge`: `π₂(U) ≤ C * G₂(U ∘ v)` for any finite
  real lower frame `v` and Gaussian cotype `2` target.
* `ContinuousLinearMap.summingENorm_two_le_gaussianSecondMoment_real` and
  `ContinuousLinearMap.summingENorm_two_le_gaussianSecondMoment`: Proposition 3.7 for real and
  `RCLike` orthonormal bases (`C * G₂` and `2 * C * G₂`), with `EuclideanSpace` specializations.
* `TauCeti.HasGaussianCotype.gaussianSecondMoment_le_add_mul_sqrt_tail`,
  `TauCeti.HasGaussianCotype.gaussianSecondMoment_le_two_mul_rademacherSecondMoment`,
  `TauCeti.HasGaussianCotype.gaussianSecondMoment_le_rademacherSecondMoment`, and
  `TauCeti.HasCotype.gaussianSecondMoment_le_rademacherSecondMoment`: Lemma 3.8 truncation,
  absorption, and explicit `4 * √3 * C * R₂(y)` comparison.
* `TauCeti.HasGaussianCotype.hasCotype_two`: Maurey–Pisier equivalence at cotype `2`.
* `ContinuousLinearMap.summingENorm_two_le_rademacherSecondMoment_of_tail_real` and
  `ContinuousLinearMap.summingENorm_two_le_rademacherSecondMoment_of_tail`: threshold-parametric
  Theorem 3.9 (`2 * C * t * R₂` and `4 * C * t * R₂`).
* `ContinuousLinearMap.summingENorm_two_le_rademacherSecondMoment_real` and
  `ContinuousLinearMap.summingENorm_two_le_rademacherSecondMoment`: explicit closed-form
  Theorem 3.9 for Rademacher cotype `2` (`4 * √3 * C² * R₂` and `8 * √3 * C² * R₂`), together with
  their Gaussian-cotype and `EuclideanSpace` variants.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Proposition 3.7, Lemma 3.8, and Theorem 3.9, pp. 33–37.
-/

public section

noncomputable section

open Filter Finset MeasureTheory Metric ProbabilityTheory TauCeti
open scoped BigOperators ENNReal NNReal

/-! ### Proposition 3.7: Gaussian cotype `2` implies `π₂` bound via `G₂` -/

namespace ContinuousLinearMap

section Prop37

variable {ι Y : Type*} [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}

/-- **Pisier Proposition 3.7 (lower-frame form).** If `v : ι → E` satisfies
`‖g‖ ^ 2 ≤ ∑ i, g (v i) ^ 2` for every real continuous functional `g`, and `Y` has Gaussian
cotype `2` with constant `C`, then every `U : E →L[ℝ] Y` satisfies
`π₂(U) ≤ C * G₂(U ∘ v)`. -/
theorem summingENorm_two_le_of_sum_sq_ge {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ι → E} (hv : ∀ g : StrongDual ℝ E, ‖g‖ ^ 2 ≤ ∑ i, g (v i) ^ 2)
    (hY : HasGaussianCotype Y 2 C) (U : E →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment (U ∘ v)) := by
  refine (summingENorm_le_ofReal_iff (T := U) (p := 2)
    (mul_nonneg C.2 (gaussianSecondMoment_nonneg (U ∘ v)))).2 fun n x ↦ ?_
  set W := weakLpNorm (𝕜 := ℝ) 2 x
  have hW : 0 ≤ W := apply_nonneg _ _
  have hweak : ∀ f : StrongDual ℝ Y,
      ∑ j : Fin n, |f (U (x j))| ^ 2 ≤ ∑ i : ι, |f (W • U (v i))| ^ 2 := fun f ↦ by
    have hcomp := norm_eval_le_weakLpNorm (𝕜 := ℝ) 2 x (f.comp U)
    have hsq := (sq_le_sq₀ (PiLp.norm_nonneg' _)
      (mul_nonneg hW (norm_nonneg (f.comp U)))).2 hcomp
    rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), mul_pow] at hsq
    calc ∑ j : Fin n, |f (U (x j))| ^ 2
        = ∑ j : Fin n, ‖(f.comp U) (x j)‖ ^ 2 := by simp [Real.norm_eq_abs]
      _ ≤ W ^ 2 * ‖f.comp U‖ ^ 2 := hsq
      _ ≤ W ^ 2 * ∑ i : ι, (f.comp U) (v i) ^ 2 :=
          mul_le_mul_of_nonneg_left (hv (f.comp U)) (sq_nonneg W)
      _ = ∑ i : ι, |f (W • U (v i))| ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, smul_eq_mul, abs_mul, mul_pow, sq_abs, sq_abs]
          rfl
  have hG : gaussianSecondMoment (fun j : Fin n ↦ U (x j)) ≤
      W * gaussianSecondMoment (U ∘ v) := by
    have hle := gaussianSecondMoment_le_of_weakTwo_le (fun j ↦ U (x j))
      (fun i ↦ W • U (v i)) hweak
    simpa [gaussianSecondMoment_smul, Real.norm_eq_abs, abs_of_nonneg hW, Function.comp_def]
      using hle
  calc ‖WithLp.toLp 2 (fun j : Fin n ↦ U (x j))‖
      ≤ C * gaussianSecondMoment (fun j : Fin n ↦ U (x j)) := hY.norm_toLp_le _
    _ ≤ C * (W * gaussianSecondMoment (U ∘ v)) := mul_le_mul_of_nonneg_left hG C.2
    _ = C * gaussianSecondMoment (U ∘ v) * W := by ring

/-- **Pisier Proposition 3.7 (real orthonormal basis).** For an operator `U : H →L[ℝ] Y` from a
real finite-dimensional inner product space into a space of Gaussian cotype `2` with constant `C`,
`π₂(U) ≤ C * G₂(U ∘ b)` for any orthonormal basis `b`. -/
theorem summingENorm_two_le_gaussianSecondMoment_real {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (b : OrthonormalBasis ι ℝ H) (hY : HasGaussianCotype Y 2 C)
    (U : H →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment (U ∘ b)) :=
  summingENorm_two_le_of_sum_sq_ge (v := b) (fun g ↦ by
    have h := b.sum_sq_norm_apply_eq_norm_sq g
    simpa [Real.norm_eq_abs, sq_abs] using h.ge) hY U

/-- **Pisier Proposition 3.7 (`EuclideanSpace ℝ ι`).** -/
theorem summingENorm_two_le_gaussianSecondMoment_euclideanSpace_real [DecidableEq ι]
    (hY : HasGaussianCotype Y 2 C) (U : EuclideanSpace ℝ ι →L[ℝ] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (C * gaussianSecondMoment (fun i ↦ U (EuclideanSpace.single i 1))) := by
  have h := summingENorm_two_le_gaussianSecondMoment_real (EuclideanSpace.basisFun ι ℝ) hY U
  have heq : U ∘ EuclideanSpace.basisFun ι ℝ = fun i ↦ U (EuclideanSpace.single i 1) :=
    funext fun i ↦ congrArg U (EuclideanSpace.basisFun_apply ι ℝ i)
  rwa [heq] at h

/-- **Pisier Proposition 3.7 (`RCLike` orthonormal basis).** Restricting scalars to `ℝ` and using
the real Parseval family `(bᵢ, I • bᵢ)` gives `π₂(U) ≤ 2 * C * G₂(U ∘ b)` over `ℝ` or `ℂ`. -/
theorem summingENorm_two_le_gaussianSecondMoment {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    [NormedSpace 𝕜 Y] [IsScalarTower ℝ 𝕜 Y]
    (b : OrthonormalBasis ι 𝕜 H) (hY : HasGaussianCotype Y 2 C) (U : H →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * gaussianSecondMoment (U ∘ b)) := by
  have : SMulCommClass ℝ 𝕜 Y :=
    ⟨fun r c y ↦ by rw [← algebraMap_smul 𝕜 r, smul_comm, algebraMap_smul]⟩
  let v : ι ⊕ ι → H := Sum.elim (fun i ↦ b i) (fun i ↦ (RCLike.I : 𝕜) • b i)
  have hv (g : StrongDual ℝ H) : ‖g‖ ^ 2 ≤ ∑ k : ι ⊕ ι, g (v k) ^ 2 := by
    rw [Fintype.sum_sum_type]
    exact (b.sum_sq_apply_add_sum_sq_apply_I_smul g).ge
  have hcomp : (U.restrictScalars ℝ) ∘ v =
      Sum.elim (U ∘ b) (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i) := by
    ext k
    cases k <;> simp [v, map_smul]
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_I]
    split_ifs <;> norm_num
  have hG : gaussianSecondMoment ((U.restrictScalars ℝ) ∘ v) ≤
      2 * gaussianSecondMoment (U ∘ b) := by
    rw [hcomp]
    calc gaussianSecondMoment (Sum.elim (U ∘ b) (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i))
        ≤ gaussianSecondMoment (U ∘ b) +
            gaussianSecondMoment (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i) :=
          gaussianSecondMoment_sumElim_le _ _
      _ = gaussianSecondMoment (U ∘ b) +
            ‖(RCLike.I : 𝕜)‖ * gaussianSecondMoment (U ∘ b) := by
          rw [gaussianSecondMoment_smul (U ∘ b) (RCLike.I : 𝕜)]
      _ ≤ gaussianSecondMoment (U ∘ b) + 1 * gaussianSecondMoment (U ∘ b) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hI (gaussianSecondMoment_nonneg _)) _
      _ = 2 * gaussianSecondMoment (U ∘ b) := by ring
  calc U.summingENorm 2
      ≤ (U.restrictScalars ℝ).summingENorm 2 := U.summingENorm_le_restrictScalars
    _ ≤ ENNReal.ofReal (C * gaussianSecondMoment ((U.restrictScalars ℝ) ∘ v)) :=
        summingENorm_two_le_of_sum_sq_ge hv hY (U.restrictScalars ℝ)
    _ ≤ ENNReal.ofReal (2 * C * gaussianSecondMoment (U ∘ b)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (C : ℝ) * gaussianSecondMoment ((U.restrictScalars ℝ) ∘ v)
            ≤ C * (2 * gaussianSecondMoment (U ∘ b)) := mul_le_mul_of_nonneg_left hG C.2
          _ = 2 * C * gaussianSecondMoment (U ∘ b) := by ring

/-- **Pisier Proposition 3.7 (`EuclideanSpace 𝕜 ι`, `RCLike 𝕜`).** -/
theorem summingENorm_two_le_gaussianSecondMoment_euclideanSpace {𝕜 : Type*} [RCLike 𝕜]
    [DecidableEq ι] [NormedSpace 𝕜 Y] [IsScalarTower ℝ 𝕜 Y]
    (hY : HasGaussianCotype Y 2 C) (U : EuclideanSpace 𝕜 ι →L[𝕜] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (2 * C * gaussianSecondMoment (fun i ↦ U (EuclideanSpace.single i 1))) := by
  have h := summingENorm_two_le_gaussianSecondMoment (EuclideanSpace.basisFun ι 𝕜) hY U
  have heq : U ∘ EuclideanSpace.basisFun ι 𝕜 = fun i ↦ U (EuclideanSpace.single i 1) :=
    funext fun i ↦ congrArg U (EuclideanSpace.basisFun_apply ι 𝕜 i)
  rwa [heq] at h

end Prop37

end ContinuousLinearMap

/-! ### Lemma 3.8: Truncation, absorption, and equivalence of Gaussian and Rademacher cotype `2` -/

namespace TauCeti

section Lemma38Helpers

variable {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Coordinatewise bounded truncation of a vector in `EuclideanSpace ℝ ι` at threshold `t`. -/
private def truncLe (t : ℝ) (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if |g i| ≤ t then g i else 0

/-- Coordinatewise tail truncation of a vector in `EuclideanSpace ℝ ι` above threshold `t`. -/
private def truncGt (t : ℝ) (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if t < |g i| then g i else 0

private theorem truncLe_add_truncGt (t : ℝ) (g : EuclideanSpace ℝ ι) :
    truncLe t g + truncGt t g = g := by
  ext i
  by_cases h : |g i| ≤ t
  · simp [truncLe, truncGt, h, not_lt.2 h]
  · simp [truncLe, truncGt, h, lt_of_not_ge h]

private theorem norm_truncLe_le [Fintype ι] (t : ℝ) (g : EuclideanSpace ℝ ι) :
    ‖truncLe t g‖ ≤ ‖g‖ :=
  PiLp.norm_mono fun i ↦ by
    dsimp [truncLe]
    split_ifs <;> simp

private theorem norm_truncGt_le [Fintype ι] (t : ℝ) (g : EuclideanSpace ℝ ι) :
    ‖truncGt t g‖ ≤ ‖g‖ :=
  PiLp.norm_mono fun i ↦ by
    dsimp [truncGt]
    split_ifs <;> simp

private theorem measurable_truncLe [Finite ι] (t : ℝ) : Measurable (truncLe (ι := ι) t) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  refine (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun i ↦ ?_)
  exact Measurable.ite
    (measurableSet_le (continuous_abs.measurable.comp (EuclideanSpace.proj i).continuous.measurable)
      measurable_const)
    (EuclideanSpace.proj i).continuous.measurable measurable_const

private theorem measurable_truncGt [Finite ι] (t : ℝ) : Measurable (truncGt (ι := ι) t) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  refine (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun i ↦ ?_)
  exact Measurable.ite
    (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (EuclideanSpace.proj i).continuous.measurable))
    (EuclideanSpace.proj i).continuous.measurable measurable_const

private theorem memLp_comp_of_norm_le [Fintype ι] (U : EuclideanSpace ℝ ι →L[ℝ] Y)
    {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv_meas : Measurable v)
    (hv_norm : ∀ g, ‖v g‖ ≤ ‖g‖) :
    MemLp (fun g ↦ U (v g)) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hid := IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) 2 (by simp)
  have hnorm : MemLp (fun g : EuclideanSpace ℝ ι ↦ ‖U‖ * ‖g‖) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := hid.norm.const_mul ‖U‖
  refine hnorm.mono' (U.continuous.comp_aestronglyMeasurable hv_meas.aestronglyMeasurable)
    (ae_of_all _ fun g ↦ ?_)
  exact (U.le_opNorm (v g)).trans (mul_le_mul_of_nonneg_left (hv_norm g) (norm_nonneg U))

private theorem truncLe_signFlipEquiv_sum [Fintype ι] (y : ι → Y) (t : ℝ)
    (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) :
    ∑ i, truncLe t (Probability.signFlipEquiv ε g) i • y i =
      ∑ i, ε i • (truncLe t g i • y i) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Int.units_eq_one_or (ε i) with he | he <;> simp [truncLe, he]

private theorem integrable_norm_sq_truncLe_signFlip [Fintype ι] (y : ι → Y)
    (t : ℝ) (ε : ι → ℤˣ) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, ε i • (truncLe t g i • y i)‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := ∑ i, (EuclideanSpace.proj i).smulRight (y i)
  have hU (z : EuclideanSpace ℝ ι) : U z = ∑ i, z i • y i := by simp [U]
  have hint : Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, truncLe t g i • y i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [← hU] using
      (memLp_comp_of_norm_le U (measurable_truncLe t) (norm_truncLe_le t)).integrable_norm_pow
        (by norm_num)
  have hmp : MeasurePreserving (Probability.signFlipEquiv ε)
      (stdGaussian (EuclideanSpace ℝ ι)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨(Probability.signFlipEquiv ε).continuous.measurable,
      Probability.stdGaussian_map_signFlipEquiv ε⟩
  simpa only [Function.comp_def, truncLe_signFlipEquiv_sum] using
    hmp.integrable_comp_of_integrable hint

/-- The bounded-truncation part of a Gaussian sum has `L²` norm at most `t * R₂(y)`. -/
private theorem integral_norm_sq_truncLe_le [Fintype ι] [DecidableEq ι] (y : ι → Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ g : EuclideanSpace ℝ ι,
        ‖∑ i, (truncLe t g i) • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      (t * rademacherSecondMoment y) ^ 2 := by
  have hcard : (Fintype.card (ι → ℤˣ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hint_ε (ε : ι → ℤˣ) := integrable_norm_sq_truncLe_signFlip y t ε
  calc ∫ g : EuclideanSpace ℝ ι, ‖∑ i, truncLe t g i • y i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)
      = (∑ ε : ι → ℤˣ, ∫ g : EuclideanSpace ℝ ι, ‖∑ i, ε i • (truncLe t g i • y i)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) / Fintype.card (ι → ℤˣ) := by
        have hε (ε : ι → ℤˣ) :
            ∫ g : EuclideanSpace ℝ ι, ‖∑ i, ε i • (truncLe t g i • y i)‖ ^ 2
                ∂stdGaussian (EuclideanSpace ℝ ι) =
              ∫ g : EuclideanSpace ℝ ι, ‖∑ i, truncLe t g i • y i‖ ^ 2
                ∂stdGaussian (EuclideanSpace ℝ ι) := by
          simp_rw [← truncLe_signFlipEquiv_sum y t ε]
          exact Probability.integral_comp_signFlipEquiv_stdGaussian ε
            (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, truncLe t g i • y i‖ ^ 2)
        simp_rw [hε, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [hcard]
    _ = ∫ g : EuclideanSpace ℝ ι, 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (truncLe t g i • y i)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι) := by
        simp_rw [Finset.expect_eq_sum_div_card]
        rw [integral_div, integral_finsetSum _ fun ε _ ↦ hint_ε ε]
        rfl
    _ ≤ ∫ _ : EuclideanSpace ℝ ι, (t * rademacherSecondMoment y) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι) := by
        refine integral_mono ?_ (integrable_const _) fun g ↦ ?_
        · simp_rw [Finset.expect_eq_sum_div_card]
          exact (integrable_finsetSum _ fun ε _ ↦ hint_ε ε).div_const _
        · have hbd (i : ι) : |truncLe t g i| ≤ t := by
            dsimp [truncLe]
            split_ifs with h
            · exact h
            · simpa using ht
          have hcon := rademacherSecondMoment_smul_le hbd y
          have hsq := (sq_le_sq₀ (rademacherSecondMoment_nonneg _)
            (mul_nonneg ht (rademacherSecondMoment_nonneg _))).2 hcon
          rwa [rademacherSecondMoment_sq] at hsq
    _ = (t * rademacherSecondMoment y) ^ 2 := by simp

private theorem measurable_eval_truncGt_sq [Finite ι]
    [MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    [BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    (s : Set (WeakDual ℝ (EuclideanSpace ℝ ι))) (t : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ι × s ↦
      ((p.2 : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t p.1)) ^ 2) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfun : (fun p : EuclideanSpace ℝ ι × s ↦
      (p.2 : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t p.1)) =
      fun p ↦ ∑ i, truncGt t p.1 i *
        (p.2 : WeakDual ℝ (EuclideanSpace ℝ ι)) (EuclideanSpace.basisFun ι ℝ i) := by
    ext ⟨g, φ⟩
    have hvec : truncGt t g = ∑ i, truncGt t g i • EuclideanSpace.basisFun ι ℝ i :=
      ((EuclideanSpace.basisFun ι ℝ).sum_repr (truncGt t g)).symm
    conv_lhs => rw [hvec]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hlin : Measurable (fun p : EuclideanSpace ℝ ι × s ↦
      ∑ i, truncGt t p.1 i *
        (p.2 : WeakDual ℝ (EuclideanSpace ℝ ι)) (EuclideanSpace.basisFun ι ℝ i)) :=
    Finset.measurable_sum Finset.univ fun i _ ↦
      (((EuclideanSpace.proj i).continuous.measurable.comp (measurable_truncGt t)).comp
        measurable_fst).mul
      (((WeakDual.eval_continuous (EuclideanSpace.basisFun ι ℝ i)).measurable.comp
        measurable_subtype_coe).comp measurable_snd)
  have hbase : Measurable (fun p : EuclideanSpace ℝ ι × s ↦
      (p.2 : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t p.1)) := by
    rw [hfun]
    exact hlin
  exact hbase.pow_const 2

/-- Joint integrability of `(g, φ) ↦ (φ (truncGt t g))²` on `stdGaussian × ν` for any probability
measure `ν` on the weak-star dual unit ball, with no second-countability hypothesis. -/
private theorem integrable_eval_truncGt_sq [Fintype ι]
    [MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    [BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (EuclideanSpace ℝ ι)) 1))
    [IsProbabilityMeasure ν] (t : ℝ) :
    Integrable
      (fun p : EuclideanSpace ℝ ι ×
          (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (EuclideanSpace ℝ ι)) 1) ↦
        ((p.2 : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t p.1)) ^ 2)
      ((stdGaussian (EuclideanSpace ℝ ι)).prod ν) := by
  have hdom_g : Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖g‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) 2 (by simp)).integrable_norm_pow
      (by norm_num)
  refine (hdom_g.comp_fst ν).mono'
    (measurable_eval_truncGt_sq _ t).aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
  let φ : StrongDual ℝ (EuclideanSpace ℝ ι) :=
    WeakDual.toStrongDual (p.2 : WeakDual ℝ (EuclideanSpace ℝ ι))
  have hφ : ‖φ‖ ≤ 1 := mem_closedBall_zero_iff.1 p.2.2
  have hval : ‖φ (truncGt t p.1)‖ ≤ ‖p.1‖ := by
    calc ‖φ (truncGt t p.1)‖
        ≤ 1 * ‖truncGt t p.1‖ := φ.le_of_opNorm_le hφ (truncGt t p.1)
      _ = ‖truncGt t p.1‖ := one_mul _
      _ ≤ ‖p.1‖ := norm_truncGt_le t p.1
  change ‖(φ (truncGt t p.1)) ^ 2‖ ≤ ‖p.1‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, ← Real.norm_eq_abs]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hval

omit [NormedSpace ℝ Y] in
/-- Squaring a `p = 2` Pietsch domination inequality pointwise. -/
private theorem sq_le_of_pietsch_two {α : Type*} [MeasurableSpace α]
    {K : ℝ} (hK : 0 ≤ K) (ν : Measure α) {u : Y} {f : α → ℝ}
    (hd : ‖u‖ ≤ K * (∫ φ, ‖f φ‖ ^ (2 : ℝ≥0∞).toReal ∂ν) ^ (1 / (2 : ℝ≥0∞).toReal)) :
    ‖u‖ ^ 2 ≤ K ^ 2 * ∫ φ, (f φ) ^ 2 ∂ν := by
  have hnn : 0 ≤ ∫ φ, (f φ) ^ 2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  have hrew : ∫ φ, ‖f φ‖ ^ (2 : ℝ≥0∞).toReal ∂ν = ∫ φ, (f φ) ^ 2 ∂ν := by
    simp [Real.norm_eq_abs, sq_abs]
  rw [hrew, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow] at hd
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))).2 hd
  rwa [mul_pow, Real.sq_sqrt hnn] at hsq

private theorem integral_eval_truncGt_sq_le [Fintype ι]
    [MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    [BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι))]
    (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (EuclideanSpace ℝ ι)) 1))
    [IsProbabilityMeasure ν] (t : ℝ) :
    ∫ φ, ∫ g, ((φ : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t g)) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ∂ν ≤
      ∫ _, ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1 ∂ν := by
  set tail := ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1
  have htail_nn : 0 ≤ tail :=
    setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
      fun _ _ ↦ sq_nonneg _
  refine integral_mono (integrable_eval_truncGt_sq (ι := ι) ν t).integral_prod_right
    (integrable_const _) fun φ ↦ ?_
  have hφ : ‖WeakDual.toStrongDual (φ : WeakDual ℝ (EuclideanSpace ℝ ι))‖ ≤ 1 :=
    mem_closedBall_zero_iff.1 φ.2
  have hval := Probability.integral_strongDual_tail_sq_stdGaussian
    (WeakDual.toStrongDual (φ : WeakDual ℝ (EuclideanSpace ℝ ι))) t
  calc ∫ g, ((φ : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t g)) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)
      = ‖WeakDual.toStrongDual (φ : WeakDual ℝ (EuclideanSpace ℝ ι))‖ ^ 2 * tail := hval
    _ ≤ 1 ^ 2 * tail := mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hφ) htail_nn
    _ = tail := by simp

/-- The tail-truncation part of a Gaussian sum is controlled by Proposition 3.7, Pietsch
domination, and Fubini's theorem. -/
private theorem integral_norm_sq_truncGt_le [Fintype ι] {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (y : ι → Y) (t : ℝ) :
    ∫ g : EuclideanSpace ℝ ι,
        ‖∑ i, (truncGt t g i) • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      (C * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) * gaussianSecondMoment y) ^ 2 := by
  classical
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := ∑ i, (EuclideanSpace.proj i).smulRight (y i)
  have hU_apply (z : EuclideanSpace ℝ ι) : U z = ∑ i, z i • y i := by simp [U]
  have hUb : U ∘ EuclideanSpace.basisFun ι ℝ = y := funext fun i ↦ by
    simp [hU_apply, EuclideanSpace.basisFun_apply]
  have hpi : U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment y) := by
    have h := U.summingENorm_two_le_gaussianSecondMoment_real (EuclideanSpace.basisFun ι ℝ) hY
    rwa [hUb] at h
  let : MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι)) := borel _
  have : BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι)) := ⟨rfl⟩
  obtain ⟨ν, hν, _, hdom⟩ := U.exists_isProbabilityMeasure_of_summingENorm_le_ofReal (p := 2)
    ENNReal.ofNat_ne_top (mul_nonneg C.2 (gaussianSecondMoment_nonneg y)) hpi
  have := hν
  have hint_l : Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, truncGt t g i • y i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [← hU_apply] using
      (memLp_comp_of_norm_le U (measurable_truncGt t) (norm_truncGt_le t)).integrable_norm_pow
        (by norm_num)
  have hF_int := integrable_eval_truncGt_sq (ι := ι) ν t
  have hpt (g : EuclideanSpace ℝ ι) :
      ‖∑ i, truncGt t g i • y i‖ ^ 2 ≤ (C * gaussianSecondMoment y) ^ 2 *
        ∫ φ, ((φ : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t g)) ^ 2 ∂ν := by
    rw [← hU_apply]
    exact sq_le_of_pietsch_two (mul_nonneg C.2 (gaussianSecondMoment_nonneg y)) ν
      (hdom (truncGt t g))
  set tail := ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1
  have htail_nn : 0 ≤ tail :=
    setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
      fun _ _ ↦ sq_nonneg _
  calc ∫ g : EuclideanSpace ℝ ι, ‖∑ i, truncGt t g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)
      ≤ ∫ g, (C * gaussianSecondMoment y) ^ 2 *
          ∫ φ, ((φ : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t g)) ^ 2 ∂ν
          ∂stdGaussian (EuclideanSpace ℝ ι) :=
        integral_mono hint_l (hF_int.integral_prod_left.const_mul _) hpt
    _ = (C * gaussianSecondMoment y) ^ 2 *
          ∫ φ, ∫ g, ((φ : WeakDual ℝ (EuclideanSpace ℝ ι)) (truncGt t g)) ^ 2
            ∂stdGaussian (EuclideanSpace ℝ ι) ∂ν := by
        rw [integral_const_mul, integral_integral_swap hF_int]
    _ ≤ (C * gaussianSecondMoment y) ^ 2 * ∫ _, tail ∂ν :=
        mul_le_mul_of_nonneg_left (integral_eval_truncGt_sq_le ν t) (sq_nonneg _)
    _ = (C * √tail * gaussianSecondMoment y) ^ 2 := by
        simp only [integral_const, probReal_univ, one_smul]
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt htail_nn]
        ring

end Lemma38Helpers

section Lemma38

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {C : ℝ≥0}

/-- **Pisier Lemma 3.8 (truncation inequality).** Under Gaussian cotype `2` with constant `C`,
splitting each standard Gaussian coordinate at threshold `t ≥ 0` bounds
`G₂(y) ≤ t * R₂(y) + C * √(∫_{|x|>t} x² dγ₁) * G₂(y)`. -/
theorem HasGaussianCotype.gaussianSecondMoment_le_add_mul_sqrt_tail
    (hY : HasGaussianCotype Y 2 C) (y : ι → Y) {t : ℝ} (ht : 0 ≤ t) :
    gaussianSecondMoment y ≤
      t * rademacherSecondMoment y +
        C * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) * gaussianSecondMoment y := by
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := ∑ i, (EuclideanSpace.proj i).smulRight (y i)
  have hU (z : EuclideanSpace ℝ ι) : U z = ∑ i, z i • y i := by simp [U]
  have hm := memLp_gaussianSum y 2 (by simp)
  have hm_le : MemLp (fun g : EuclideanSpace ℝ ι ↦ ∑ i, truncLe t g i • y i) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [← hU] using memLp_comp_of_norm_le U (measurable_truncLe t) (norm_truncLe_le t)
  have hm_gt : MemLp (fun g : EuclideanSpace ℝ ι ↦ ∑ i, truncGt t g i • y i) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [← hU] using memLp_comp_of_norm_le U (measurable_truncGt t) (norm_truncGt_le t)
  have hsplit : (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • y i) =
      (fun g ↦ ∑ i, truncLe t g i • y i) + (fun g ↦ ∑ i, truncGt t g i • y i) := by
    ext g
    simp only [Pi.add_apply, ← hU, ← map_add, truncLe_add_truncGt]
  have htri : eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • y i) 2
        (stdGaussian (EuclideanSpace ℝ ι)) ≤
      eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, truncLe t g i • y i) 2
        (stdGaussian (EuclideanSpace ℝ ι)) +
      eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, truncGt t g i • y i) 2
        (stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [hsplit]
    exact eLpNorm_add_le one_le_two
  rw [hm.eLpNorm_two_eq_ofReal_sqrt_integral, hm_le.eLpNorm_two_eq_ofReal_sqrt_integral,
    hm_gt.eLpNorm_two_eq_ofReal_sqrt_integral,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at htri
  have h1 : √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, truncLe t g i • y i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ t * rademacherSecondMoment y :=
    Real.sqrt_le_iff.2 ⟨mul_nonneg ht (rademacherSecondMoment_nonneg y),
      integral_norm_sq_truncLe_le y ht⟩
  have h2 : √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, truncGt t g i • y i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      C * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) * gaussianSecondMoment y :=
    Real.sqrt_le_iff.2
      ⟨mul_nonneg (mul_nonneg C.2 (Real.sqrt_nonneg _)) (gaussianSecondMoment_nonneg y),
        integral_norm_sq_truncGt_le hY y t⟩
  rw [← gaussianSecondMoment_def] at htri
  exact htri.trans (add_le_add h1 h2)

/-- **Pisier Lemma 3.8 (absorption).** If `t ≥ 0` satisfies
`C * √(∫_{|x|>t} x² dγ₁) ≤ 1 / 2`, then Gaussian cotype `2` with constant `C` gives
`G₂(y) ≤ 2 * t * R₂(y)`. -/
theorem HasGaussianCotype.gaussianSecondMoment_le_two_mul_rademacherSecondMoment
    (hY : HasGaussianCotype Y 2 C) (y : ι → Y) {t : ℝ} (ht : 0 ≤ t)
    (htC : (C : ℝ) * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2) :
    gaussianSecondMoment y ≤ 2 * t * rademacherSecondMoment y := by
  have h := hY.gaussianSecondMoment_le_add_mul_sqrt_tail y ht
  have habs : (C : ℝ) * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) *
      gaussianSecondMoment y ≤ (1 / 2) * gaussianSecondMoment y :=
    mul_le_mul_of_nonneg_right htC (gaussianSecondMoment_nonneg y)
  linarith

/-- **Explicit Gaussian-vs-Rademacher comparison (Pisier Lemma 3.8).** In any real normed space of
Gaussian cotype `2` with constant `C` (including `C = 0`), every finite family satisfies
`G₂(y) ≤ 4 * √3 * C * R₂(y)`. -/
theorem HasGaussianCotype.gaussianSecondMoment_le_rademacherSecondMoment
    (hY : HasGaussianCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 4 * √3 * C * rademacherSecondMoment y := by
  rcases eq_or_ne C 0 with rfl | hC
  · have : Subsingleton Y := hY.subsingleton_of_zero
    have hy : y = 0 := funext fun i ↦ Subsingleton.elim _ _
    simp [hy]
  · have hCpos : 0 < (C : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hC)
    set t : ℝ := 2 * √3 * (C : ℝ)
    have ht : 0 < t := by positivity
    have htail : ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1 ≤
        1 / (2 * (C : ℝ)) ^ 2 := by
      calc ∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1
          ≤ 3 * ((1 : ℝ≥0) : ℝ) ^ 2 / t ^ 2 :=
            Probability.setIntegral_sq_abs_gt_gaussianReal_le 1 ht
        _ = 1 / (2 * (C : ℝ)) ^ 2 := by
            simp only [t, NNReal.coe_one, one_pow, mul_one, mul_pow,
              Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
            field_simp [hCpos.ne']
    have htC : (C : ℝ) * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2 := by
      calc (C : ℝ) * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1)
          ≤ (C : ℝ) * √(1 / (2 * (C : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htail) hCpos.le
        _ = (C : ℝ) * (1 / (2 * (C : ℝ))) := by
            rw [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_sq (by positivity)]
        _ = 1 / 2 := by field_simp [hCpos.ne']
    calc gaussianSecondMoment y
        ≤ 2 * t * rademacherSecondMoment y :=
          hY.gaussianSecondMoment_le_two_mul_rademacherSecondMoment y ht.le htC
      _ = 4 * √3 * C * rademacherSecondMoment y := by simp only [t]; ring

/-- In any real normed space of Rademacher cotype `2` with constant `C`, every finite family
satisfies `G₂(y) ≤ 4 * √3 * C * R₂(y)`. -/
theorem HasCotype.gaussianSecondMoment_le_rademacherSecondMoment
    (hY : HasCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 4 * √3 * C * rademacherSecondMoment y :=
  hY.hasGaussianCotype_two.gaussianSecondMoment_le_rademacherSecondMoment y

/-- **Maurey–Pisier equivalence at cotype `2`.** Gaussian cotype `2` with constant `C` implies
Rademacher cotype `2` with constant `4 * √3 * C²`. -/
theorem HasGaussianCotype.hasCotype_two (hY : HasGaussianCotype Y 2 C) :
    HasCotype Y 2 (4 * NNReal.sqrt 3 * C ^ 2) := by
  rw [hasCotype_iff]
  intro n y
  calc ‖WithLp.toLp 2 y‖
      ≤ C * gaussianSecondMoment y := hY.norm_toLp_le y
    _ ≤ C * (4 * √3 * C * rademacherSecondMoment y) :=
        mul_le_mul_of_nonneg_left (hY.gaussianSecondMoment_le_rademacherSecondMoment y) C.2
    _ = ((4 * NNReal.sqrt 3 * C ^ 2 : ℝ≥0) : ℝ) * rademacherSecondMoment y := by
        simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, Real.coe_sqrt]
        ring

end Lemma38

end TauCeti

/-! ### Theorem 3.9: `2`-summing bounds via Rademacher second moments -/

namespace ContinuousLinearMap

section Thm39

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}

/-- **Pisier Theorem 3.9 (parametric threshold form, real).** If `Y` has Gaussian cotype `2` with
constant `C` and `t ≥ 0` satisfies `C * √(∫_{|x|>t} x² dγ₁) ≤ 1 / 2`, then every `U : H →L[ℝ] Y`
from a finite-dimensional real inner product space with orthonormal basis `b` satisfies
`π₂(U) ≤ 2 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_rademacherSecondMoment_of_tail_real {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (b : OrthonormalBasis ι ℝ H)
    (hY : HasGaussianCotype Y 2 C) {t : ℝ} (ht : 0 ≤ t)
    (htC : (C : ℝ) * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (U : H →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * t * rademacherSecondMoment (U ∘ b)) := by
  refine (U.summingENorm_two_le_gaussianSecondMoment_real b hY).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc (C : ℝ) * gaussianSecondMoment (U ∘ b)
      ≤ C * (2 * t * rademacherSecondMoment (U ∘ b)) :=
        mul_le_mul_of_nonneg_left
          (hY.gaussianSecondMoment_le_two_mul_rademacherSecondMoment (U ∘ b) ht htC) C.2
    _ = 2 * C * t * rademacherSecondMoment (U ∘ b) := by ring

/-- **Pisier Theorem 3.9 (parametric threshold form, `RCLike`).** If `Y` has Gaussian cotype `2`
with constant `C` and `t ≥ 0` satisfies `C * √(∫_{|x|>t} x² dγ₁) ≤ 1 / 2`, then every
`U : H →L[𝕜] Y` from a finite-dimensional `RCLike` inner product space with orthonormal basis `b`
satisfies `π₂(U) ≤ 4 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_rademacherSecondMoment_of_tail {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    [NormedSpace 𝕜 Y] [IsScalarTower ℝ 𝕜 Y] (b : OrthonormalBasis ι 𝕜 H)
    (hY : HasGaussianCotype Y 2 C) {t : ℝ} (ht : 0 ≤ t)
    (htC : (C : ℝ) * √(∫ x in {x : ℝ | t < |x|}, x ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (U : H →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (4 * C * t * rademacherSecondMoment (U ∘ b)) := by
  refine (U.summingENorm_two_le_gaussianSecondMoment b hY).trans (ENNReal.ofReal_le_ofReal ?_)
  calc 2 * (C : ℝ) * gaussianSecondMoment (U ∘ b)
      ≤ 2 * C * (2 * t * rademacherSecondMoment (U ∘ b)) :=
        mul_le_mul_of_nonneg_left
          (hY.gaussianSecondMoment_le_two_mul_rademacherSecondMoment (U ∘ b) ht htC)
          (by positivity)
    _ = 4 * C * t * rademacherSecondMoment (U ∘ b) := by ring

/-- **Pisier Theorem 3.9 (Gaussian cotype `2`, real).** For an orthonormal basis `b` of a real
inner product space and any `Y` of Gaussian cotype `2` with constant `C`,
`π₂(U) ≤ 4 * √3 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_rademacherSecondMoment_of_hasGaussianCotype_real {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (b : OrthonormalBasis ι ℝ H)
    (hY : HasGaussianCotype Y 2 C) (U : H →L[ℝ] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (4 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) := by
  refine (U.summingENorm_two_le_gaussianSecondMoment_real b hY).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc (C : ℝ) * gaussianSecondMoment (U ∘ b)
      ≤ C * (4 * √3 * C * rademacherSecondMoment (U ∘ b)) :=
        mul_le_mul_of_nonneg_left (hY.gaussianSecondMoment_le_rademacherSecondMoment (U ∘ b)) C.2
    _ = 4 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b) := by ring

/-- **Pisier Theorem 3.9 (Rademacher cotype `2`, real).** For an orthonormal basis `b` of a real
inner product space and any `Y` of Rademacher cotype `2` with constant `C` (including `C = 0`),
`π₂(U) ≤ 4 * √3 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_rademacherSecondMoment_real {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (b : OrthonormalBasis ι ℝ H)
    (hY : HasCotype Y 2 C) (U : H →L[ℝ] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (4 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) :=
  U.summingENorm_two_le_rademacherSecondMoment_of_hasGaussianCotype_real b hY.hasGaussianCotype_two

/-- **Pisier Theorem 3.9 (`EuclideanSpace ℝ ι`).** -/
theorem summingENorm_two_le_rademacherSecondMoment_euclideanSpace_real
    (hY : HasCotype Y 2 C) (U : EuclideanSpace ℝ ι →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal
      (4 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (fun i ↦ U (EuclideanSpace.single i 1))) := by
  have h := U.summingENorm_two_le_rademacherSecondMoment_real (EuclideanSpace.basisFun ι ℝ) hY
  have heq : U ∘ EuclideanSpace.basisFun ι ℝ = fun i ↦ U (EuclideanSpace.single i 1) :=
    funext fun i ↦ congrArg U (EuclideanSpace.basisFun_apply ι ℝ i)
  rwa [heq] at h

/-- **Pisier Theorem 3.9 (Gaussian cotype `2`, `RCLike`).** For an orthonormal basis `b` of an
`RCLike` inner product space and any `Y` of Gaussian cotype `2` with constant `C`,
`π₂(U) ≤ 8 * √3 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_rademacherSecondMoment_of_hasGaussianCotype {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    [NormedSpace 𝕜 Y] [IsScalarTower ℝ 𝕜 Y] (b : OrthonormalBasis ι 𝕜 H)
    (hY : HasGaussianCotype Y 2 C) (U : H →L[𝕜] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (8 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) := by
  refine (U.summingENorm_two_le_gaussianSecondMoment b hY).trans (ENNReal.ofReal_le_ofReal ?_)
  calc 2 * (C : ℝ) * gaussianSecondMoment (U ∘ b)
      ≤ 2 * C * (4 * √3 * C * rademacherSecondMoment (U ∘ b)) :=
        mul_le_mul_of_nonneg_left (hY.gaussianSecondMoment_le_rademacherSecondMoment (U ∘ b))
          (by positivity)
    _ = 8 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b) := by ring

/-- **Pisier Theorem 3.9 (Rademacher cotype `2`, `RCLike`).** For an orthonormal basis `b` of an
`RCLike` inner product space and any `Y` of Rademacher cotype `2` with constant `C`
(including `C = 0`), `π₂(U) ≤ 8 * √3 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_rademacherSecondMoment {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    [NormedSpace 𝕜 Y] [IsScalarTower ℝ 𝕜 Y] (b : OrthonormalBasis ι 𝕜 H)
    (hY : HasCotype Y 2 C) (U : H →L[𝕜] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (8 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) :=
  U.summingENorm_two_le_rademacherSecondMoment_of_hasGaussianCotype b hY.hasGaussianCotype_two

/-- **Pisier Theorem 3.9 (`EuclideanSpace 𝕜 ι`, `RCLike 𝕜`).** -/
theorem summingENorm_two_le_rademacherSecondMoment_euclideanSpace {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 Y] [IsScalarTower ℝ 𝕜 Y] (hY : HasCotype Y 2 C)
    (U : EuclideanSpace 𝕜 ι →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal
      (8 * √3 * (C : ℝ) ^ 2 * rademacherSecondMoment (fun i ↦ U (EuclideanSpace.single i 1))) := by
  have h := U.summingENorm_two_le_rademacherSecondMoment (EuclideanSpace.basisFun ι 𝕜) hY
  have heq : U ∘ EuclideanSpace.basisFun ι 𝕜 = fun i ↦ U (EuclideanSpace.single i 1) :=
    funext fun i ↦ congrArg U (EuclideanSpace.basisFun_apply ι 𝕜 i)
  rwa [heq] at h

end Thm39

end ContinuousLinearMap
