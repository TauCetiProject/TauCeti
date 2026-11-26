/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.MeasureTheory.Integral.Lebesgue.SublevelGrowth

/-!
# Norm balls in groups of matrices: polynomial volume growth and integrable inverse powers

Let `ν` be a left-invariant measure on a group `S` and `j : S →* Eˣ` a homomorphism to the units
of a finite-dimensional real normed algebra `E` of dimension `d`. For `y ∈ Eˣ`, the points `s`
where `‖y * j s‖ ≤ R` and `‖(y * j s)⁻¹‖ ≤ R'` have measure at most `(1 + 2 R R' / ε) ^ d` times
the measure of the ball `B = {s | ‖j s - 1‖ ≤ ε}`, for every `ε > 0`. Indeed, the matrices
`y * j s` of these points lie in the ball of radius `R` of `E`, so a volume count gives an
`ε / R'`-net of them with at most `(1 + 2 R R' / ε) ^ d` points `y * j k`; if `y * j s` lies within
`ε / R'` of `y * j k`, then

`j (k⁻¹ s) - 1 = (y * j k)⁻¹ * (y * j s - y * j k)`

has norm at most `ε`, so the left translates `k B` cover the set.

For the unitary group `unitaryGroupOf J` of a unitary Gram matrix `J`, with the operator norm,
`‖g⁻¹‖ = ‖g‖` and `‖g‖ ≥ 1` (`Matrix.norm_val_inv_of_mem_unitaryGroupOf`,
`Matrix.one_le_norm_val_of_mem_unitaryGroupOf`). Hence the sets `{s | ‖y * j s‖ ≤ R}` have
measure at most `(3 R²) ^ d ν B` for `R ≥ 1` and `ε = 1`, where `d = dim_ℝ M_n(𝕜)`, which is
`2 n²` over `ℂ` and `n²` over `ℝ`. By the layer-cake bound of
`TauCeti.lintegral_ofReal_rpow_neg_le_of_measure_le_rpow`, the function `s ↦ ‖y * j s‖ ^ (-A)` is
integrable for every `A > 2 d` as soon as `B` has finite measure, with a bound uniform in `y`. In
particular, for a Haar measure on `unitaryGroupOf J` itself, such as `U(p, q)` with
`J = diag(1, …, 1, -1, …, -1)`, every inverse power `‖g‖ ^ (-A)` with `A > 2 d` of the operator
norm is integrable. The threshold `2 d` comes from the crude covering argument and is not sharp.

## Main results

* `MeasureTheory.measure_setOf_norm_le_and_norm_inv_le_le`: the covering bound for a homomorphism
  to the units of a finite-dimensional normed algebra.
* `Matrix.unitaryGroupOf.measure_setOf_norm_mul_le_le`: for a unitary Gram matrix `J`,
  `ν {s | ‖y * j s‖ ≤ R} ≤ (1 + 2 R² / ε) ^ d * ν {s | ‖j s - 1‖ ≤ ε}`.
* `Matrix.unitaryGroupOf.lintegral_norm_mul_rpow_neg_le`: for continuous `j` and `A > 2 d`,
  `∫⁻ ‖y * j s‖ ^ (-A) ∂ν ≤ 3 ^ d A / (A - 2 d) * ν {s | ‖j s - 1‖ ≤ 1}`.
* `Matrix.unitaryGroupOf.integrable_norm_mul_rpow_neg`: the corresponding integrability when the
  ball `{s | ‖j s - 1‖ ≤ 1}` has finite measure.
* `Matrix.unitaryGroupOf.integrable_norm_rpow_neg`: for a left-invariant measure on
  `unitaryGroupOf J` that is finite on compact sets, `g ↦ ‖g‖ ^ (-A)` is integrable for `A > 2 d`.

## Provenance

`MeasureTheory.measure_setOf_norm_le_and_norm_inv_le_le`,
`Matrix.unitaryGroupOf.measure_setOf_norm_mul_le_le`,
`Matrix.unitaryGroupOf.lintegral_norm_mul_rpow_neg_le`,
`Matrix.unitaryGroupOf.integrable_norm_mul_rpow_neg` and
`Matrix.unitaryGroupOf.integrable_norm_rpow_neg` are adapted from
`New.DiscreteSeries.measure_ball_le_covering`, `New.DiscreteSeries.integral_decay_le`,
`New.DiscreteSeries.lintegral_decay_le` and `New.DiscreteSeries.measure_ball_ne_top_of_isProperMap`
(file `src/Lib/DiscreteSeries/Haar/TotalMass.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The source
treats right-invariant measures, Hermitian involutions `J` and natural exponents `c > 8 n²`, and
counts a maximal separated family; here the measure is left-invariant as Mathlib's Haar measures
are, `J` is any unitary matrix, the covering bound is stated for units of any finite-dimensional
normed algebra, the net comes from the volumetric covering bound
`TauCeti.exists_finset_isCover_of_subset_closedBall`, and the exponent is any real `A > 2 d`
(`A > 4 n²` over `ℂ`).

## References

* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), §4.2 (the
  volumetric bound on nets).
-/

public section

open MeasureTheory Module
open scoped Matrix.Norms.L2Operator

namespace MeasureTheory

variable {S E : Type*} [Group S] [MeasurableSpace S] [MeasurableMul S]
  [NormedRing E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Polynomial covering bound for norm balls.** Let `ν` be a left-invariant measure on a group
`S`, `j : S →* Eˣ` a homomorphism to the units of a finite-dimensional real normed algebra and
`y ∈ Eˣ`. For `ε > 0`, the set where `‖y * j s‖ ≤ R` and `‖(y * j s)⁻¹‖ ≤ R'` has measure at most
`(1 + 2 R R' / ε) ^ dim E` times the measure of the ball where `‖j s - 1‖ ≤ ε`. -/
theorem measure_setOf_norm_le_and_norm_inv_le_le (ν : Measure S) [ν.IsMulLeftInvariant]
    (j : S →* Eˣ) (y : Eˣ) {ε R R' : ℝ} (hε : 0 < ε) :
    ν {s | ‖((y * j s : Eˣ) : E)‖ ≤ R ∧ ‖(((y * j s)⁻¹ : Eˣ) : E)‖ ≤ R'} ≤
      ENNReal.ofReal ((1 + 2 * R * R' / ε) ^ finrank ℝ E) * ν {s | ‖(j s : E) - 1‖ ≤ ε} := by
  set T := {s | ‖((y * j s : Eˣ) : E)‖ ≤ R ∧ ‖(((y * j s)⁻¹ : Eˣ) : E)‖ ≤ R'}
  set B := {s | ‖(j s : E) - 1‖ ≤ ε}
  rcases T.eq_empty_or_nonempty with hT | ⟨s₀, hs₀⟩
  · simp [hT]
  have hR : 0 ≤ R := (norm_nonneg _).trans hs₀.1
  rcases ((norm_nonneg _).trans hs₀.2).eq_or_lt with rfl | hR'
  · -- `R' = 0` forces `E` to be the zero ring, where every point lies in `B`.
    have : Subsingleton E := subsingleton_of_zero_eq_one <| by
      rw [← Units.mul_inv (y * j s₀), norm_le_zero_iff.1 hs₀.2, mul_zero]
    have hTB : T ⊆ B := fun s _ ↦ by simp [B, Subsingleton.elim ((j s : E) - 1) 0, hε.le]
    simpa [finrank_zero_of_subsingleton] using measure_mono hTB
  -- An `ε / R'`-net of the image of `T`, by points `y * j (k c)` with `k c ∈ T`.
  have hδ : ((ε / R').toNNReal : ℝ) = ε / R' := Real.coe_toNNReal _ (by positivity)
  have hA : (fun s ↦ ((y * j s : Eˣ) : E)) '' T ⊆ Metric.closedBall 0 R.toNNReal := by
    rintro _ ⟨s, hs, rfl⟩
    simpa [Real.coe_toNNReal _ hR] using hs.1
  obtain ⟨N, hNA, hcover, hcard⟩ := TauCeti.exists_finset_isCover_of_subset_closedBall
    (ε := (ε / R').toNNReal) (by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity) hA
  choose! k hkT hkf using fun c (hc : c ∈ N) ↦ hNA hc
  -- The left translates `k c • B` cover `T`.
  have hcov : T ⊆ ⋃ c ∈ N, (fun s ↦ (k c)⁻¹ * s) ⁻¹' B := by
    intro g hg
    obtain ⟨c, hc, hgc⟩ := Set.mem_iUnion₂.1 <| Metric.isCover_iff_subset_iUnion_closedBall.1
      hcover (Set.mem_image_of_mem _ hg)
    refine Set.mem_iUnion₂.2 ⟨c, hc, ?_⟩
    have hdist : ‖((y * j g : Eˣ) : E) - ((y * j (k c) : Eˣ) : E)‖ ≤ ε / R' := by
      simpa [hkf c hc, dist_eq_norm, hδ] using hgc
    have key : (j ((k c)⁻¹ * g) : E) - 1 = (((y * j (k c))⁻¹ : Eˣ) : E) *
        (((y * j g : Eˣ) : E) - ((y * j (k c) : Eˣ) : E)) := by
      rw [mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, _root_.mul_inv_rev,
        mul_assoc, inv_mul_cancel_left, ← map_inv, ← map_mul, Units.val_one]
    simp only [Set.mem_preimage, B, Set.mem_ofPred_eq, key]
    calc _ ≤ ‖(((y * j (k c))⁻¹ : Eˣ) : E)‖ *
          ‖((y * j g : Eˣ) : E) - ((y * j (k c) : Eˣ) : E)‖ := norm_mul_le _ _
      _ ≤ R' * (ε / R') := by gcongr; exact (hkT c hc).2
      _ = ε := by field_simp
  calc ν T ≤ ∑ c ∈ N, ν ((fun s ↦ (k c)⁻¹ * s) ⁻¹' B) :=
        (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    _ = N.card * ν B := by simp [measure_preimage_mul]
    _ ≤ ENNReal.ofReal ((1 + 2 * R * R' / ε) ^ finrank ℝ E) * ν B := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        refine ENNReal.ofReal_le_ofReal (hcard.trans_eq ?_)
        rw [hδ, Real.coe_toNNReal _ hR]
        field_simp

end MeasureTheory

namespace Matrix.unitaryGroupOf

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {J : Matrix n n 𝕜}

section Covering

variable {S : Type*} [Group S] [MeasurableSpace S] [MeasurableMul S]

/-- **Polynomial covering bound in `unitaryGroupOf J`.** Let `J` be a unitary matrix, `ν` a
left-invariant measure on a group `S`, `j : S →* unitaryGroupOf J` and `y ∈ unitaryGroupOf J`.
For `ε > 0`, the set where `‖y * j s‖ ≤ R` in the operator norm has measure at most
`(1 + 2 R² / ε) ^ d` times the measure of the ball where `‖j s - 1‖ ≤ ε`, where `d` is the real
dimension of the matrices. -/
theorem measure_setOf_norm_mul_le_le (ν : Measure S) [ν.IsMulLeftInvariant]
    (hJ : J ∈ unitary (Matrix n n 𝕜)) (j : S →* unitaryGroupOf J) (y : unitaryGroupOf J)
    {ε R : ℝ} (hε : 0 < ε) :
    ν {s | ‖(((y * j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)‖ ≤ R} ≤
      ENNReal.ofReal ((1 + 2 * R ^ 2 / ε) ^ finrank ℝ (Matrix n n 𝕜)) *
        ν {s | ‖(((j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) - 1‖ ≤ ε} := by
  -- The real normed space structure of the matrices, with the module structure already present.
  let : NormedSpace ℝ (Matrix n n 𝕜) :=
    { norm_smul_le := fun r A ↦ by
        rw [← algebraMap_smul 𝕜 r A]
        exact (norm_smul_le _ _).trans_eq (by rw [norm_algebraMap']) }
  -- In `unitaryGroupOf J` the inverse has the norm of the element.
  have hset : {s | ‖(((y * j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)‖ ≤ R} =
      {s | ‖(((y : GL n 𝕜) * (unitaryGroupOf J).subtype.comp j s : GL n 𝕜) : Matrix n n 𝕜)‖ ≤ R ∧
        ‖((((y : GL n 𝕜) * (unitaryGroupOf J).subtype.comp j s)⁻¹ : GL n 𝕜) :
          Matrix n n 𝕜)‖ ≤ R} := by
    ext s
    simp only [Set.mem_ofPred_eq, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      ← Subgroup.coe_mul, norm_val_inv_of_mem_unitaryGroupOf hJ (y * j s).property, and_self]
  rw [hset, sq, ← mul_assoc]
  exact measure_setOf_norm_le_and_norm_inv_le_le ν ((unitaryGroupOf J).subtype.comp j)
    (y : GL n 𝕜) hε

/-- The norm balls `{s | ‖y * j s‖ ≤ R}` of radius `R ≥ 1` have measure at most
`R ^ (2 d) * 3 ^ d * ν {s | ‖j s - 1‖ ≤ 1}`. -/
private theorem measure_setOf_norm_mul_le_le_rpow (ν : Measure S) [ν.IsMulLeftInvariant]
    (hJ : J ∈ unitary (Matrix n n 𝕜)) (j : S →* unitaryGroupOf J) (y : unitaryGroupOf J)
    {R : ℝ} (hR : 1 ≤ R) :
    ν {s | ‖(((y * j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)‖ ≤ R} ≤
      ENNReal.ofReal (R ^ (2 * finrank ℝ (Matrix n n 𝕜) : ℝ)) *
        (ENNReal.ofReal (3 ^ finrank ℝ (Matrix n n 𝕜)) *
          ν {s | ‖(((j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) - 1‖ ≤ 1}) := by
  refine (measure_setOf_norm_mul_le_le ν hJ j y one_pos).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Nat.cast_ofNat, ← Nat.cast_mul,
    Real.rpow_natCast, pow_mul, ← mul_pow, div_one]
  gcongr
  push_cast
  nlinarith [one_le_pow₀ (n := 2) hR]

variable [TopologicalSpace S]

omit [MeasurableSpace S] [MeasurableMul S] in
/-- For continuous `j`, the norm `s ↦ ‖y * j s‖` is continuous. -/
private theorem continuous_norm_val_mul {j : S →* unitaryGroupOf J} (hj : Continuous j)
    (y : unitaryGroupOf J) :
    Continuous fun s ↦ ‖(((y * j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)‖ :=
  (Units.continuous_val.comp (continuous_subtypeVal.comp (continuous_const.mul hj))).norm

variable [OpensMeasurableSpace S]

/-- **Inverse powers of the norm on `unitaryGroupOf J`.** Let `J` be a unitary matrix, `ν` a
left-invariant measure on a topological group `S`, `j : S →* unitaryGroupOf J` continuous and
`y ∈ unitaryGroupOf J`. For a real `A > 2 d`, where `d` is the real dimension of the matrices,

`∫⁻ ‖y * j s‖ ^ (-A) ∂ν ≤ 3 ^ d A / (A - 2 d) * ν {s | ‖j s - 1‖ ≤ 1}`

in the operator norm. The bound does not depend on `y`. -/
theorem lintegral_norm_mul_rpow_neg_le (ν : Measure S) [ν.IsMulLeftInvariant]
    (hJ : J ∈ unitary (Matrix n n 𝕜)) {j : S →* unitaryGroupOf J} (hj : Continuous j)
    (y : unitaryGroupOf J) {A : ℝ} (hA : 2 * finrank ℝ (Matrix n n 𝕜) < A) :
    ∫⁻ s, ENNReal.ofReal (‖(((y * j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)‖ ^ (-A)) ∂ν ≤
      ENNReal.ofReal (3 ^ finrank ℝ (Matrix n n 𝕜) * A / (A - 2 * finrank ℝ (Matrix n n 𝕜))) *
        ν {s | ‖(((j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) - 1‖ ≤ 1} := by
  have hA₀ : 0 < A := lt_of_le_of_lt (by positivity) hA
  cases isEmpty_or_nonempty n
  · simp [Subsingleton.elim (_ : Matrix n n 𝕜) 0, Real.zero_rpow (neg_ne_zero.2 hA₀.ne')]
  refine (TauCeti.lintegral_ofReal_rpow_neg_le_of_measure_le_rpow
    (continuous_norm_val_mul hj y).aemeasurable
    (.of_forall fun s ↦ one_le_norm_val_of_mem_unitaryGroupOf hJ (y * j s).property) hA₀ hA
    fun R hR ↦ measure_setOf_norm_mul_le_le_rpow ν hJ j y hR).trans_eq ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm (A / _), mul_div_assoc]

/-- **Integrability of inverse powers of the norm on `unitaryGroupOf J`.** Let `J` be a unitary
matrix, `ν` a left-invariant measure on a topological group `S` and `j : S →* unitaryGroupOf J`
continuous, such that the ball `{s | ‖j s - 1‖ ≤ 1}` has finite measure. Then for every
`y ∈ unitaryGroupOf J` and every real `A > 2 d`, where `d` is the real dimension of the
matrices, `s ↦ ‖y * j s‖ ^ (-A)` is integrable, in the operator norm. -/
theorem integrable_norm_mul_rpow_neg (ν : Measure S) [ν.IsMulLeftInvariant]
    (hJ : J ∈ unitary (Matrix n n 𝕜)) {j : S →* unitaryGroupOf J} (hj : Continuous j)
    (hν : ν {s | ‖(((j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) - 1‖ ≤ 1} ≠ ⊤)
    (y : unitaryGroupOf J) {A : ℝ} (hA : 2 * finrank ℝ (Matrix n n 𝕜) < A) :
    Integrable (fun s ↦ ‖(((y * j s : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)‖ ^ (-A)) ν := by
  refine ⟨((continuous_norm_val_mul hj y).aemeasurable.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun s ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  exact (lintegral_norm_mul_rpow_neg_le ν hJ hj y hA).trans_lt (by finiteness)

end Covering

variable [MeasurableSpace (unitaryGroupOf J)] [BorelSpace (unitaryGroupOf J)]

/-- **Inverse powers of the norm are integrable for a Haar measure on `unitaryGroupOf J`.** For a
unitary matrix `J`, such as `diag(1, …, 1, -1, …, -1)` for `U(p, q)`, and a left-invariant measure
`μ` on `unitaryGroupOf J` that is finite on compact sets, `g ↦ ‖g‖ ^ (-A)` is integrable in the
operator norm for every real `A > 2 d`, where `d` is the real dimension of the matrices. -/
theorem integrable_norm_rpow_neg (μ : Measure (unitaryGroupOf J)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hJ : J ∈ unitary (Matrix n n 𝕜)) {A : ℝ}
    (hA : 2 * finrank ℝ (Matrix n n 𝕜) < A) :
    Integrable (fun g : unitaryGroupOf J ↦ ‖((g : GL n 𝕜) : Matrix n n 𝕜)‖ ^ (-A)) μ := by
  have : ProperSpace (Matrix n n 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  -- The unit ball around `1` is compact, as `unitaryGroupOf J` is closed in the matrices.
  have hcpt : IsCompact {g : unitaryGroupOf J | ‖((g : GL n 𝕜) : Matrix n n 𝕜) - 1‖ ≤ 1} := by
    simpa [Set.preimage, ← dist_eq_norm] using
      (isClosedEmbedding_val (Unitary.isUnit_coe (U := ⟨J, hJ⟩))).isCompact_preimage
        (isCompact_closedBall (1 : Matrix n n 𝕜) 1)
  simpa using integrable_norm_mul_rpow_neg μ hJ (j := .id _) continuous_id
    hcpt.measure_ne_top 1 hA

end Matrix.unitaryGroupOf
