/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer

/-!
# A compatible norm without multiplicative small units

On an ultrametric normed ring, `maxSquareRingNorm` is the norm
`x ↦ max ‖x‖ (‖x‖ ^ 2)`. It agrees with the original norm on the closed unit ball,
so induces the same uniformity. `maxSquareNormedRing` installs it while retaining
the original uniformity and topology, hence also completeness.

On a normed ring, no unit of positive new norm less than one scales this norm
multiplicatively: testing against its inverse gives a contradiction.
Consequently the new norm is not Tate, even when the original topology is Tate.
This distinguishes existence of a topologically nilpotent unit from exact norm scaling.

The construction uses Mathlib's `RingNorm.toNormedRing` and
`MetricSpace.replaceUniformity`; no alternate carrier or global norm instance is introduced.
-/

public section

open scoped Uniformity

namespace TauCeti

section Ring

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

private theorem maxSquare_add_le_max (x y : R) :
    max ‖x + y‖ (‖x + y‖ ^ 2) ≤ max (max ‖x‖ (‖x‖ ^ 2)) (max ‖y‖ (‖y‖ ^ 2)) := by
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · have h := (IsUltrametricDist.norm_add_le_max x y).trans_eq (max_eq_right hxy)
    exact (max_le_max h (pow_le_pow_left₀ (norm_nonneg _) h 2)).trans (le_max_right _ _)
  · have h := (IsUltrametricDist.norm_add_le_max x y).trans_eq (max_eq_left hyx)
    exact (max_le_max h (pow_le_pow_left₀ (norm_nonneg _) h 2)).trans (le_max_left _ _)

/-- The maximum of the norm and its square, as a ring norm. -/
noncomputable def maxSquareRingNorm (R : Type*) [NormedRing R] [IsUltrametricDist R] :
    RingNorm R where
  toFun x := max ‖x‖ (‖x‖ ^ 2)
  map_zero' := by simp
  neg' x := by simp
  add_le' x y := (maxSquare_add_le_max x y).trans
    (max_le_add_of_nonneg (by positivity) (by positivity))
  mul_le' x y := by
    apply max_le
    · exact (norm_mul_le x y).trans
        (mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) (by positivity))
    · calc
        ‖x * y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le x y) 2
        _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := mul_pow _ _ _
        _ ≤ max ‖x‖ (‖x‖ ^ 2) * max ‖y‖ (‖y‖ ^ 2) :=
          mul_le_mul (le_max_right _ _) (le_max_right _ _) (sq_nonneg _) (by positivity)
  eq_zero_of_map_eq_zero' x hx := norm_eq_zero.mp <|
    le_antisymm ((le_max_left _ _).trans_eq hx) (norm_nonneg _)

/-- The defining formula for the maximum-square norm. -/
@[simp]
theorem maxSquareRingNorm_apply (x : R) :
    maxSquareRingNorm R x = max ‖x‖ (‖x‖ ^ 2) := (rfl)

/-- The maximum-square norm is normalized at one whenever the original norm is. -/
theorem maxSquareRingNorm_one [NormOneClass R] : maxSquareRingNorm R 1 = 1 := by
  simp

/-- On the closed unit ball the maximum-square norm is unchanged. -/
theorem maxSquareRingNorm_of_norm_le_one {x : R} (hx : ‖x‖ ≤ 1) :
    maxSquareRingNorm R x = ‖x‖ := by
  rw [maxSquareRingNorm_apply, max_eq_left]
  nlinarith [norm_nonneg x]

/-- Outside the open unit ball the maximum-square norm is the square of the norm. -/
theorem maxSquareRingNorm_of_one_le_norm {x : R} (hx : 1 ≤ ‖x‖) :
    maxSquareRingNorm R x = ‖x‖ ^ 2 := by
  rw [maxSquareRingNorm_apply, max_eq_right]
  nlinarith [norm_nonneg x]

/-- The maximum-square norm is ultrametric. -/
theorem isNonarchimedean_maxSquareRingNorm : IsNonarchimedean (maxSquareRingNorm R) :=
  maxSquare_add_le_max

/-- Below radius one, strict bounds for the two norms agree. -/
theorem maxSquareRingNorm_lt_iff {x : R} {ε : ℝ} (hε : ε ≤ 1) :
    maxSquareRingNorm R x < ε ↔ ‖x‖ < ε := by
  constructor
  · exact fun h ↦ (le_max_left _ _).trans_lt h
  · intro h
    rw [maxSquareRingNorm_of_norm_le_one (h.le.trans hε)]
    exact h

/-- The maximum-square norm induces the original uniformity, although it need not be
bounded-equivalent to the original norm. -/
theorem uniformity_maxSquareRingNorm :
    𝓤 R = @uniformity R (maxSquareRingNorm R).toNormedRing.toUniformSpace := by
  let g := ‹NormedRing R›
  let N := maxSquareRingNorm R
  let n := N.toNormedRing
  -- Keep the original metric implicit, and write the ring-norm metric explicitly.
  let := g
  -- The metric constructed by `RingNorm.toNormedRing` is the norm of the difference.
  have hd (x y : R) : @dist R n.toDist x y = maxSquareRingNorm R (-x + y) := rfl
  have hb := @Metric.uniformity_basis_dist_lt R n.toPseudoMetricSpace 1 zero_lt_one
  have heq (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
      {p : R × R | @dist R n.toDist p.1 p.2 < ε} =
        {p : R × R | dist p.1 p.2 < ε} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    rw [hd, maxSquareRingNorm_lt_iff hε.2.le, dist_eq_norm_neg_add]
  exact (Metric.uniformity_basis_dist_lt zero_lt_one).eq_of_same_basis
    (hb.congr (fun _ ↦ Iff.rfl) heq)

/-- Install the maximum-square norm with the original uniformity and topology retained.
This is explicit data, not a global instance. -/
@[instance_reducible]
noncomputable def maxSquareNormedRing (R : Type*) [NormedRing R] [IsUltrametricDist R] :
    NormedRing R :=
  { (maxSquareRingNorm R).toNormedRing with
    toMetricSpace := (maxSquareRingNorm R).toNormedRing.toMetricSpace.replaceUniformity
      (uniformity_maxSquareRingNorm (R := R)) }

/-- The compatible normed ring has the specified maximum-square norm. -/
@[simp]
theorem norm_maxSquareNormedRing (x : R) :
    @norm R (maxSquareNormedRing R).toNorm x = maxSquareRingNorm R x := (rfl)

/-- The compatible maximum-square norm retains the original ring structure. -/
@[simp]
theorem ring_maxSquareNormedRing :
    (maxSquareNormedRing R).toRing = (inferInstance : Ring R) := (rfl)

/-- The compatible maximum-square norm retains the original uniform space. -/
@[simp]
theorem uniformSpace_maxSquareNormedRing :
    (maxSquareNormedRing R).toUniformSpace = (inferInstance : UniformSpace R) := (rfl)

/-- Distance for the compatible maximum-square norm is the norm of the difference. -/
theorem dist_maxSquareNormedRing (x y : R) :
    @dist R (maxSquareNormedRing R).toDist x y = maxSquareRingNorm R (x - y) := by
  let := maxSquareNormedRing R
  exact dist_eq_norm x y

/-- Completeness is preserved by the compatible maximum-square norm. -/
theorem completeSpace_maxSquareNormedRing [CompleteSpace R] :
    @CompleteSpace R (maxSquareNormedRing R).toUniformSpace := by
  rw [uniformSpace_maxSquareNormedRing]
  infer_instance

/-- The compatible maximum-square norm is ultrametric. -/
theorem isUltrametricDist_maxSquareNormedRing :
    letI := maxSquareNormedRing R
    IsUltrametricDist R := by
  have h := isNonarchimedean_maxSquareRingNorm (R := R)
  let := maxSquareNormedRing R
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm h

/-- The maximum-square norm is normalized at one whenever the original norm is. -/
theorem normOneClass_maxSquareNormedRing [NormOneClass R] :
    @NormOneClass R (maxSquareNormedRing R).toNorm (inferInstance : One R) := by
  refine @NormOneClass.mk R (maxSquareNormedRing R).toNorm _ ?_
  rw [norm_maxSquareNormedRing, maxSquareRingNorm_one]

/-- The compatible maximum-square norm on a ring admits no multiplicative
pseudo-uniformiser. This does not assert that its topology fails to be Tate. -/
theorem not_isTate_maxSquareNormedRing :
    letI := maxSquareNormedRing R
    ¬ NormedRing.IsTate R := by
  let g := ‹NormedRing R›
  let := maxSquareNormedRing R
  intro h
  obtain ⟨ϖ⟩ := h.nonempty_pseudoUniformizer
  let u : Rˣ := ϖ.unit
  have hpos : 0 < ‖(u : R)‖ := ϖ.norm_pos
  have hlt : ‖(u : R)‖ < 1 := ϖ.norm_lt_one
  have hinv : ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := ϖ.norm_inv
  have : Nontrivial R := ϖ.nontrivial
  let := g
  simp only [norm_maxSquareNormedRing] at hpos hlt hinv
  have hx := (maxSquareRingNorm_lt_iff le_rfl).mp hlt
  rw [maxSquareRingNorm_of_norm_le_one hx.le] at hpos hinv
  have hmul : 1 ≤ ‖(u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ :=
    (one_le_norm_one R).trans (by
      simpa only [Units.mul_inv] using norm_mul_le (u : R) ((u⁻¹ : Rˣ) : R))
  have hprod : ‖(u : R)‖ * maxSquareRingNorm R ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [hinv, mul_inv_cancel₀ hpos.ne']
  have hbound : maxSquareRingNorm R ((u⁻¹ : Rˣ) : R) ≤ ‖((u⁻¹ : Rˣ) : R)‖ :=
    (mul_le_mul_iff_right₀ hpos).mp (hprod.trans_le hmul)
  have hinv_gt : 1 < ‖((u⁻¹ : Rˣ) : R)‖ := by
    nlinarith
  have hsq := (le_max_right ‖((u⁻¹ : Rˣ) : R)‖ (‖((u⁻¹ : Rˣ) : R)‖ ^ 2)).trans hbound
  nlinarith

end Ring

section DivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]

/-- For a nonzero element of norm less than one, the product of its maximum-square norm
and that of its inverse is the reciprocal of its original norm, not one. -/
theorem maxSquareRingNorm_mul_inv_of_norm_lt_one {x : K} (hx₀ : x ≠ 0) (hx : ‖x‖ < 1) :
    maxSquareRingNorm K x * maxSquareRingNorm K x⁻¹ = ‖x‖⁻¹ := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx₀
  have hinv : 1 < ‖x⁻¹‖ := by rw [norm_inv]; exact (one_lt_inv₀ hpos).mpr hx
  have hscale : ‖x‖ * (‖x‖⁻¹) ^ 2 = ‖x‖⁻¹ := by field_simp
  simpa only [maxSquareRingNorm_of_norm_le_one hx.le,
    maxSquareRingNorm_of_one_le_norm hinv.le, norm_inv] using hscale

/-- A nonzero element of norm less than one and its inverse have maximum-square norm
product strictly greater than one, obstructing multiplicative scaling. -/
theorem one_lt_maxSquareRingNorm_mul_inv {x : K} (hx₀ : x ≠ 0) (hx : ‖x‖ < 1) :
    1 < maxSquareRingNorm K x * maxSquareRingNorm K x⁻¹ := by
  rw [maxSquareRingNorm_mul_inv_of_norm_lt_one hx₀ hx]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hx₀)).mpr hx

end DivisionRing

/-- An ultrametric norm-one commutative ring with Tate topology has a compatible
ultrametric, norm-one ring norm which is not Tate. Equality of uniformities also preserves
completeness whenever the original ring is complete. -/
theorem exists_normedRing_isTateRing_not_isTate (R : Type*) [NormedCommRing R]
    [IsUltrametricDist R] [NormOneClass R] [Huber.IsTateRing R] :
    ∃ n : NormedRing R, n.toRing = (inferInstance : Ring R) ∧
      n.toMetricSpace.toUniformSpace = (inferInstance : UniformSpace R) ∧
      @IsUltrametricDist R n.toDist ∧ @NormOneClass R n.toNorm (inferInstance : One R) ∧
      Huber.IsTateRing R ∧ ¬ @NormedRing.IsTate R n.toSeminormedRing := by
  exact ⟨maxSquareNormedRing R, ring_maxSquareNormedRing,
    uniformSpace_maxSquareNormedRing, isUltrametricDist_maxSquareNormedRing,
    normOneClass_maxSquareNormedRing, inferInstance, not_isTate_maxSquareNormedRing⟩

end TauCeti
