/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import TauCeti.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Vague

/-!
# Approximate tangent spaces of measures

Let `μ` be a locally finite measure on a finite-dimensional real inner product space `E`, let
`x ∈ E` and `k : ℕ`. The `k`-dimensional **blow-up** of `μ` at `x` at scale `r > 0` is the measure

`μ_{x,r}(A) = r ^ (-k) μ (x + r • A)`,

the push-forward of `μ` by the dilation `y ↦ r⁻¹ • (y - x)`, multiplied by `r ^ (-k)`
(`MeasureTheory.Measure.blowUp`). A `k`-dimensional subspace `T` is the **approximate tangent
space** of `μ` at `x` with multiplicity `θ ∈ (0, ∞)` when the blow-ups `μ_{x,r}` converge to
`θ μHE[k]⌞T` against every compactly supported continuous function as `r → 0⁺`
(`MeasureTheory.Measure.HasApproxTangentSpace`). Approximate tangent spaces of measures are the
notion of tangent plane used for rectifiable and integral varifolds: by the rectifiability
criterion (Simon, Theorem 11.8, not proved here), a locally finite measure with a `k`-dimensional
approximate tangent space of positive multiplicity at `μ`-almost every point is `θ μHE[k]⌞Γ` for a
countably `k`-rectifiable set `Γ`, that is, the weight of a rectifiable `k`-varifold.

## Main results

* `MeasureTheory.Measure.blowUp_apply_vadd_smul`: `μ_{x,r}(A) = r ^ (-k) μ (x + r • A)` for
  `r > 0`.
* `MeasureTheory.Measure.blowUp_euclideanHausdorffMeasure`: the blow-ups of `μHE[k]` are `μHE[k]`.
* `AffineSubspace.blowUp_euclideanHausdorffMeasure_restrict`: at a point `x` of an affine subspace
  `A`, the blow-ups of `μHE[k]⌞A` are `μHE[k]⌞A.direction`.
* `AffineSubspace.hasApproxTangentSpace_smul_euclideanHausdorffMeasure_restrict`: hence
  `θ μHE[k]⌞A`, with `k` the dimension of `A`, has approximate tangent space `A.direction` with
  multiplicity `θ` at every point of `A`.
* `MeasureTheory.Measure.HasApproxTangentSpace.tendsto_blowUp_apply`: the blow-up masses of a
  bounded measurable set whose frontier the limit measure does not charge converge to its mass
  under the limit measure.
* `MeasureTheory.Measure.HasApproxTangentSpace.tendsto_measure_closedBall_div` and
  `MeasureTheory.Measure.HasApproxTangentSpace.tendsto_measure_ball_div`: the multiplicity is the
  density, `μ (B_r(x)) / (ω_k r ^ k) → θ`, for closed and for open balls.
* `MeasureTheory.Measure.HasApproxTangentSpace.unique`: the approximate tangent space and its
  multiplicity are unique.
* `MeasureTheory.Measure.hasApproxTangentSpace_congr_restrict`: locality, approximate tangent
  spaces at `x` depend only on the restriction of the measure to a neighbourhood of `x`.

## Implementation notes

The blow-up is defined for every real `r`, but only positive scales are meaningful; the lemmas
computing it from `μ` assume `r ≠ 0` or `r > 0`. The dimension of the approximate tangent space
is that of the subspace `T`, so it is not a separate parameter of `HasApproxTangentSpace`. The
convergence of the blow-ups is tested with Bochner integrals of compactly supported continuous
functions, and is meant for locally finite measures `μ`; the results about it assume that `μ` is
locally finite.
Since the limit measure gives the unit sphere measure zero, the vague convergence implies the
convergence of the masses of the unit ball
(`MeasureTheory.Measure.tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported`),
which is the density statement. Uniqueness compares these masses in two dimensions, and then the
limit measures, which determine their subspace.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent spaces of measures
  and the rectifiability criterion 11.8).
-/

public section

open Filter Metric MeasureTheory Set Module
open scoped ENNReal NNReal Topology CompactlySupported Pointwise

namespace MeasureTheory.Measure

section BlowUp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {k : ℕ} {x : E} {r : ℝ}

/-- The `k`-dimensional blow-up `μ_{x,r}` of a measure `μ` at `x` at scale `r`: the push-forward of
`μ` by the dilation `y ↦ r⁻¹ • (y - x)`, multiplied by `(ENNReal.ofReal r)⁻¹ ^ k`, which is
`r ^ (-k)` for `r > 0`. For `r > 0` it gives a set `A` the mass `r ^ (-k) μ (x + r • A)`. Only
positive scales are meaningful. -/
noncomputable def blowUp (μ : Measure E) (k : ℕ) (x : E) (r : ℝ) : Measure E :=
  (ENNReal.ofReal r)⁻¹ ^ k • μ.map fun y ↦ r⁻¹ • (y - x)

omit [BorelSpace E] in
/-- A blow-up is the push-forward of `μ` by the dilation `y ↦ r⁻¹ • (y - x)`, multiplied by
`(ENNReal.ofReal r)⁻¹ ^ k`. -/
theorem blowUp_def : μ.blowUp k x r = (ENNReal.ofReal r)⁻¹ ^ k • μ.map fun y ↦ r⁻¹ • (y - x) :=
  (rfl)

/-- The mass of a measurable set `s` under a blow-up is `(ENNReal.ofReal r)⁻¹ ^ k` times the mass
of its preimage under the dilation; for `r > 0` the factor is `r ^ (-k)`. -/
theorem blowUp_apply {s : Set E} (hs : MeasurableSet s) :
    μ.blowUp k x r s = (ENNReal.ofReal r)⁻¹ ^ k * μ ((fun y ↦ r⁻¹ • (y - x)) ⁻¹' s) := by
  rw [blowUp_def, smul_apply, map_apply (by fun_prop) hs, smul_eq_mul]

/-- A blow-up gives the closed ball of radius `ρ` about `0` the mass
`r ^ (-k) μ (closedBall x (r ρ))`. -/
theorem blowUp_apply_closedBall (hr : 0 < r) (ρ : ℝ) :
    μ.blowUp k x r (closedBall 0 ρ) = (ENNReal.ofReal r)⁻¹ ^ k * μ (closedBall x (r * ρ)) := by
  rw [blowUp_apply measurableSet_closedBall]
  congr 2
  ext y
  simp [norm_smul, abs_of_pos hr, dist_eq_norm, inv_mul_le_iff₀ hr]

/-- A blow-up gives the open ball of radius `ρ` about `0` the mass `r ^ (-k) μ (ball x (r ρ))`. -/
theorem blowUp_apply_ball (hr : 0 < r) (ρ : ℝ) :
    μ.blowUp k x r (ball 0 ρ) = (ENNReal.ofReal r)⁻¹ ^ k * μ (ball x (r * ρ)) := by
  rw [blowUp_apply measurableSet_ball]
  congr 2
  ext y
  simp [norm_smul, abs_of_pos hr, dist_eq_norm, inv_mul_lt_iff₀ hr]

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `r ≠ 0`, the dilation `y ↦ r⁻¹ • (y - x)` along which `μ.blowUp k x r` pushes `μ` forward,
as a homeomorphism of `E`; its inverse is `z ↦ r • z + x`. -/
noncomputable def blowUpDilation (x : E) {r : ℝ} (hr : r ≠ 0) : E ≃ₜ E :=
  (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_blowUpDilation (hr : r ≠ 0) : ⇑(blowUpDilation x hr) = fun y ↦ r⁻¹ • (y - x) :=
  (rfl)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_blowUpDilation_symm (hr : r ≠ 0) :
    ⇑(blowUpDilation x hr).symm = fun z ↦ r • z + x := by
  ext z
  simp [blowUpDilation]

/-- **The defining identity of blow-ups.** For `r ≠ 0`, a blow-up gives a measurable set `s` the
mass `(ENNReal.ofReal r)⁻¹ ^ k * μ (x + r • s)`, that is `r ^ (-k) μ (x + r • s)` for `r > 0`. -/
theorem blowUp_apply_vadd_smul (hr : r ≠ 0) {s : Set E} (hs : MeasurableSet s) :
    μ.blowUp k x r s = (ENNReal.ofReal r)⁻¹ ^ k * μ (x +ᵥ r • s) := by
  rw [blowUp_apply hs]
  rw [show (fun y ↦ r⁻¹ • (y - x)) = (r⁻¹ • ·) ∘ (· - x) from rfl, preimage_comp,
    preimage_smul_inv₀ hr]
  congr 2
  ext y
  simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

/-- Integrals against a blow-up are `r ^ (-k)` times integrals of the dilated function. -/
theorem integral_blowUp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (hr : 0 < r)
    (f : E → G) :
    ∫ y, f y ∂μ.blowUp k x r = (r ^ k)⁻¹ • ∫ y, f (r⁻¹ • (y - x)) ∂μ := by
  have he := (blowUpDilation x hr.ne').isOpenEmbedding.measurableEmbedding
  rw [coe_blowUpDilation] at he
  rw [blowUp_def, integral_smul_measure, he.integral_map]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le]

omit [BorelSpace E] in
@[simp]
theorem blowUp_zero : (0 : Measure E).blowUp k x r = 0 := by
  simp [blowUp_def]

@[simp]
theorem blowUp_add (μ ν : Measure E) :
    (μ + ν).blowUp k x r = μ.blowUp k x r + ν.blowUp k x r := by
  rw [blowUp_def, blowUp_def, blowUp_def, Measure.map_add _ _ (by fun_prop), smul_add]

@[simp]
theorem blowUp_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [SMulCommClass ℝ≥0∞ R ℝ≥0∞] (c : R) (μ : Measure E) :
    (c • μ).blowUp k x r = c • μ.blowUp k x r := by
  rw [blowUp_def, blowUp_def, Measure.map_smul _ (by fun_prop), smul_comm]

/-- The blow-up of a restriction is the restriction of the blow-up to the blown-up set. -/
theorem blowUp_restrict (hr : r ≠ 0) (s : Set E) :
    (μ.restrict s).blowUp k x r = (μ.blowUp k x r).restrict ((fun z ↦ r • z + x) ⁻¹' s) := by
  have he := (blowUpDilation x hr).isOpenEmbedding.measurableEmbedding
  rw [coe_blowUpDilation] at he
  rw [blowUp_def, blowUp_def, restrict_smul, he.restrict_map]
  congr 3
  ext y
  simp [smul_smul, mul_inv_cancel₀ hr]

/-- At positive scales, the blow-ups of a locally finite measure are locally finite. -/
theorem isLocallyFiniteMeasure_blowUp [IsLocallyFiniteMeasure μ] (hr : 0 < r) :
    IsLocallyFiniteMeasure (μ.blowUp k x r) := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨U, hyU, hU, hμU⟩ := μ.exists_isOpen_measure_lt_top (r • y + x)
  have hV : IsOpen ((fun z ↦ r • z + x) ⁻¹' U) := hU.preimage (by fun_prop)
  refine ⟨_, hV.mem_nhds hyU, ?_⟩
  rw [blowUp_apply hV.measurableSet, ← coe_blowUpDilation hr.ne', ← coe_blowUpDilation_symm hr.ne',
    ← preimage_comp, Homeomorph.symm_comp_self, preimage_id]
  exact ENNReal.mul_lt_top (by simp [hr]) hμU

end BlowUp

section Hausdorff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {k : ℕ} {x : E} {r : ℝ}

/-- The `k`-dimensional Euclidean Hausdorff measure is invariant under its own `k`-dimensional
blow-ups. -/
theorem blowUp_euclideanHausdorffMeasure (hr : 0 < r) :
    (μHE[k] : Measure E).blowUp k x r = μHE[k] := by
  ext s hs
  rw [blowUp_apply_vadd_smul hr.ne' hs, measure_vadd, euclideanHausdorffMeasure_smul₀ k hr.ne']
  simp [ENNReal.smul_def, ← mul_assoc, ← mul_pow, ← Real.eNorm_of_nonneg hr.le, eNorm_eq_nnNorm,
    ENNReal.inv_mul_cancel, hr.ne']

end Hausdorff

end MeasureTheory.Measure

namespace AffineSubspace

open MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {k : ℕ} {x : E} {r : ℝ} {A : AffineSubspace ℝ E}

/-- At a point `x` of an affine subspace `A`, the `k`-dimensional blow-ups of `μHE[k]⌞A` are
`μHE[k]⌞A.direction`. -/
theorem blowUp_euclideanHausdorffMeasure_restrict (hx : x ∈ A) (hr : 0 < r) :
    (μHE[k].restrict (A : Set E)).blowUp k x r = μHE[k].restrict (A.direction : Set E) := by
  rw [blowUp_restrict hr.ne', blowUp_euclideanHausdorffMeasure hr]
  congr 1
  ext z
  rw [mem_preimage, SetLike.mem_coe, SetLike.mem_coe, ← vsub_right_mem_direction_iff_mem hx,
    vsub_eq_sub, add_sub_cancel_right, Submodule.smul_mem_iff _ hr.ne']

end AffineSubspace

namespace MeasureTheory.Measure

section ApproxTangentSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {x : E} {T T₁ T₂ : Submodule ℝ E}
  {θ θ₁ θ₂ : ℝ≥0}

/-- A subspace `T` of dimension `k` is the **approximate tangent space** of the measure `μ` at `x`
with multiplicity `θ ∈ (0, ∞)` when the `k`-dimensional blow-ups `μ.blowUp k x r` converge to
`θ μHE[k]⌞T` against every compactly supported continuous function as `r → 0⁺`.

This is meant for locally finite measures `μ`. -/
@[mk_iff]
structure HasApproxTangentSpace (μ : Measure E) (x : E) (T : Submodule ℝ E) (θ : ℝ≥0) : Prop where
  /-- The multiplicity is positive. -/
  ne_zero : θ ≠ 0
  /-- The blow-ups converge to `θ μHE[k]⌞T` against compactly supported continuous functions. -/
  tendsto_integral (f : C_c(E, ℝ)) :
    Tendsto (fun r ↦ ∫ y, f y ∂μ.blowUp (finrank ℝ T) x r) (𝓝[>] 0)
      (𝓝 (θ * ∫ y, f y ∂μHE[finrank ℝ T].restrict (T : Set E)))

/-- The unit ball of a Euclidean space has positive volume. -/
private theorem volume_unitBall_ne_zero (k : ℕ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ 0 :=
  (measure_ball_pos volume _ one_pos).ne'

namespace HasApproxTangentSpace

variable [IsLocallyFiniteMeasure μ]

/-- If `μ` has approximate tangent space `T` with multiplicity `θ` at `x`, then the blow-up masses
of a bounded measurable set `s` whose frontier is not charged by `μHE[k]⌞T` converge to
`θ μHE[k]⌞T (s)`. -/
theorem tendsto_blowUp_apply (h : μ.HasApproxTangentSpace x T θ) {s : Set E}
    (hs : MeasurableSet s) (hsb : Bornology.IsBounded s)
    (hfr : μHE[finrank ℝ T].restrict (T : Set E) (frontier s) = 0) :
    Tendsto (fun r ↦ μ.blowUp (finrank ℝ T) x r s) (𝓝[>] 0)
      (𝓝 (θ * μHE[finrank ℝ T].restrict (T : Set E) s)) := by
  set ν := μHE[finrank ℝ T].restrict (T : Set E)
  let μs : Ioi (0 : ℝ) → Measure E := fun r ↦ μ.blowUp (finrank ℝ T) x r
  have : ∀ r, IsLocallyFiniteMeasure (μs r) := fun r ↦ isLocallyFiniteMeasure_blowUp r.property
  have hconv (f : C_c(E, ℝ)) : Tendsto (fun r ↦ ∫ y, f y ∂μs r)
      (Filter.comap Subtype.val (𝓝[>] 0)) (𝓝 (∫ y, f y ∂(θ • ν))) := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    exact (h.tendsto_integral f).comp tendsto_comap
  have hfr0 : (θ • ν) (frontier s) = 0 := by simp [ν, hfr]
  have hlim := tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported hconv hs
    hsb.isCompact_closure hfr0
  rw [smul_apply, ENNReal.smul_def, smul_eq_mul] at hlim
  exact (tendsto_comap'_iff (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)).1 hlim

private theorem tendsto_blowUp_closedBall (h : μ.HasApproxTangentSpace x T θ) :
    Tendsto (fun r ↦ μ.blowUp (finrank ℝ T) x r (closedBall 0 1)) (𝓝[>] 0)
      (𝓝 (θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ T))) 1))) := by
  simpa [Submodule.euclideanHausdorffMeasure_restrict_apply_closedBall T.zero_mem] using
    h.tendsto_blowUp_apply measurableSet_closedBall isBounded_closedBall
      (measure_mono_null frontier_closedBall_subset_sphere
        (Submodule.euclideanHausdorffMeasure_restrict_apply_sphere T.zero_mem one_ne_zero))

private theorem tendsto_blowUp_ball (h : μ.HasApproxTangentSpace x T θ) :
    Tendsto (fun r ↦ μ.blowUp (finrank ℝ T) x r (ball 0 1)) (𝓝[>] 0)
      (𝓝 (θ * volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ T))) 1))) := by
  simpa [Submodule.euclideanHausdorffMeasure_restrict_apply_ball T.zero_mem] using
    h.tendsto_blowUp_apply measurableSet_ball isBounded_ball
      (measure_mono_null frontier_ball_subset_sphere
        (Submodule.euclideanHausdorffMeasure_restrict_apply_sphere T.zero_mem one_ne_zero))

/-- `r ^ (-k) m / ω = m / (r ^ k ω)`, the conversion between the mass of a blow-up and a density
ratio. -/
private theorem inv_pow_mul_div_eq {r : ℝ} (hr : 0 < r) (k : ℕ) (m ω : ℝ≥0∞) :
    (ENNReal.ofReal r)⁻¹ ^ k * m / ω = m / (ENNReal.ofReal (r ^ k) * ω) := by
  rw [ENNReal.ofReal_pow hr.le, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ (by simp [hr]))) (Or.inl (by simp)), ENNReal.inv_pow]
  ring

/-- If the blow-up masses `r ^ (-k) m r` tend to `θ ω`, then the density ratios `m r / V r` tend to
`θ`, where `V r = r ^ k ω`. -/
private theorem tendsto_div_of_tendsto_inv_pow_mul {k : ℕ} {m V : ℝ → ℝ≥0∞} {ω : ℝ≥0∞}
    (hω : ω ≠ 0) (hω' : ω ≠ ∞)
    (hlim : Tendsto (fun r ↦ (ENNReal.ofReal r)⁻¹ ^ k * m r) (𝓝[>] 0) (𝓝 (θ * ω)))
    (hV : ∀ r, 0 < r → V r = ENNReal.ofReal (r ^ k) * ω) :
    Tendsto (fun r ↦ m r / V r) (𝓝[>] 0) (𝓝 θ) := by
  have hlim := ENNReal.Tendsto.div_const hlim (Or.inr hω)
  rw [ENNReal.mul_div_cancel_right hω hω'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [hV r hr, inv_pow_mul_div_eq hr]

/-- **The multiplicity is the density.** If `μ` has approximate tangent space `T` of dimension `k`
with multiplicity `θ` at `x`, then `μ (closedBall x r) / (ω_k r ^ k) → θ` as `r → 0⁺`, where
`ω_k r ^ k` is the volume of a ball of radius `r` in `k`-dimensional Euclidean space. -/
theorem tendsto_measure_closedBall_div (h : μ.HasApproxTangentSpace x T θ) :
    Tendsto (fun r ↦ μ (closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ T))) r)) (𝓝[>] 0) (𝓝 θ) := by
  refine tendsto_div_of_tendsto_inv_pow_mul (measure_closedBall_pos volume _ one_pos).ne'
    measure_closedBall_lt_top.ne (h.tendsto_blowUp_closedBall.congr' ?_) fun r hr ↦ by
      rw [addHaar_closedBall' volume 0 hr.le, finrank_euclideanSpace_fin]
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [blowUp_apply_closedBall hr, mul_one]

/-- **The multiplicity is the density**, for open balls: if `μ` has approximate tangent space `T`
of dimension `k` with multiplicity `θ` at `x`, then `μ (ball x r) / (ω_k r ^ k) → θ` as
`r → 0⁺`. -/
theorem tendsto_measure_ball_div (h : μ.HasApproxTangentSpace x T θ) :
    Tendsto (fun r ↦ μ (ball x r) /
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ T))) r)) (𝓝[>] 0) (𝓝 θ) := by
  refine tendsto_div_of_tendsto_inv_pow_mul (volume_unitBall_ne_zero _) measure_ball_lt_top.ne
    (h.tendsto_blowUp_ball.congr' ?_) fun r hr ↦ by
      rw [addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin]
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [blowUp_apply_ball hr, mul_one]

/-- An approximate tangent space at `x` has at most the dimension of any other one: blowing up in
a higher dimension would multiply the masses of the unit ball by a factor tending to infinity. -/
private theorem finrank_le (h₁ : μ.HasApproxTangentSpace x T₁ θ₁)
    (h₂ : μ.HasApproxTangentSpace x T₂ θ₂) : finrank ℝ T₁ ≤ finrank ℝ T₂ := by
  by_contra! hlt
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
  have hθω :=
    mul_ne_zero (ENNReal.coe_ne_zero.2 h₂.ne_zero) (volume_unitBall_ne_zero (finrank ℝ T₂))
  -- The scale factor `r ^ (-(m + 1))` tends to infinity.
  have hinf : Tendsto (fun r : ℝ ↦ (ENNReal.ofReal r)⁻¹ ^ (m + 1)) (𝓝[>] 0) (𝓝 ∞) := by
    have h0 : Tendsto ENNReal.ofReal (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def] using (ENNReal.continuous_pow (m + 1)).continuousAt.tendsto.comp
      (tendsto_inv_iff.2 h0)
  have hprod := ENNReal.Tendsto.mul hinf (Or.inl ENNReal.top_ne_zero) h₂.tendsto_blowUp_ball
    (Or.inl hθω)
  rw [ENNReal.top_mul hθω] at hprod
  have heq : (fun r ↦ μ.blowUp (finrank ℝ T₁) x r (ball 0 1)) =ᶠ[𝓝[>] 0]
      fun r ↦ (ENNReal.ofReal r)⁻¹ ^ (m + 1) * μ.blowUp (finrank ℝ T₂) x r (ball 0 1) := by
    filter_upwards with r
    rw [blowUp_apply measurableSet_ball, blowUp_apply measurableSet_ball, hm]
    ring
  have := tendsto_nhds_unique (h₁.tendsto_blowUp_ball.congr' heq) hprod
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top measure_ball_lt_top.ne this

/-- **Uniqueness of approximate tangent spaces.** A locally finite measure has at most one
approximate tangent space at a point, with at most one multiplicity. -/
theorem unique (h₁ : μ.HasApproxTangentSpace x T₁ θ₁) (h₂ : μ.HasApproxTangentSpace x T₂ θ₂) :
    T₁ = T₂ ∧ θ₁ = θ₂ := by
  have hk : finrank ℝ T₁ = finrank ℝ T₂ := (h₁.finrank_le h₂).antisymm (h₂.finrank_le h₁)
  set k := finrank ℝ T₂
  -- The multiplicities are the limits of the same masses of the unit ball.
  have hθ : θ₁ = θ₂ := by
    have l₁ := h₁.tendsto_blowUp_ball
    rw [hk] at l₁
    exact_mod_cast (ENNReal.mul_left_inj (volume_unitBall_ne_zero k) measure_ball_lt_top.ne).1
      (tendsto_nhds_unique l₁ h₂.tendsto_blowUp_ball)
  subst hθ
  -- The limit measures `μHE[k]⌞Tᵢ` have the same integrals, hence are equal.
  have hint (f : C_c(E, ℝ)) : ∫ y, f y ∂μHE[k].restrict (T₁ : Set E) =
      ∫ y, f y ∂μHE[k].restrict (T₂ : Set E) := by
    have l₁ := h₁.tendsto_integral f
    rw [hk] at l₁
    exact mul_left_cancel₀ (by exact_mod_cast h₁.ne_zero)
      (tendsto_nhds_unique l₁ (h₂.tendsto_integral f))
  have : IsLocallyFiniteMeasure (μHE[k].restrict (T₁ : Set E)) := by
    rw [← hk]
    infer_instance
  have hν := Measure.ext_of_integral_eq_on_compactlySupported hint
  exact ⟨Submodule.eq_of_euclideanHausdorffMeasure_restrict_eq hν hk rfl, rfl⟩

omit [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] in
/-- **Locality.** Approximate tangent spaces depend only on the restriction of the measure to a
neighbourhood of the point: if `μ` and `ν` agree on a neighbourhood `U` of `x`, then every
approximate tangent space of `μ` at `x` is one of `ν`, with the same multiplicity. At small
scales the blow-ups only see `U`. -/
theorem congr_restrict {ν : Measure E} {U : Set E} (hU : U ∈ 𝓝 x)
    (hμν : μ.restrict U = ν.restrict U) (h : μ.HasApproxTangentSpace x T θ) :
    ν.HasApproxTangentSpace x T θ := by
  refine ⟨h.ne_zero, fun f ↦ (h.tendsto_integral f).congr' ?_⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  have hR' : ∀ y, f y ≠ 0 → ‖y‖ ≤ max R 1 := fun y hy ↦
    (mem_closedBall_zero_iff.mp (hR (subset_tsupport _ hy))).trans (le_max_left _ _)
  have hpos : 0 < δ / max R 1 := div_pos hδ (lt_max_of_lt_right one_pos)
  filter_upwards [Ioo_mem_nhdsGT hpos] with r ⟨hr, hrδ⟩
  -- the dilated integrand vanishes outside `ball x δ ⊆ U`
  have hsupp : ∀ y ∉ U, f (r⁻¹ • (y - x)) = 0 := by
    intro y hyU
    by_contra hy
    refine hyU (hδU (mem_ball_iff_norm.mpr ?_))
    have h1 := hR' _ hy
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_le_iff₀ hr] at h1
    calc ‖y - x‖ ≤ r * max R 1 := h1
      _ < δ / max R 1 * max R 1 := by gcongr
      _ = δ := div_mul_cancel₀ _ (lt_max_of_lt_right one_pos).ne'
  rw [integral_blowUp hr, integral_blowUp hr,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hsupp,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) hsupp, hμν]

end HasApproxTangentSpace

omit [FiniteDimensional ℝ E] in
/-- **Locality.** Measures that agree on a neighbourhood of `x` have the same approximate tangent
spaces at `x`, with the same multiplicities. -/
theorem hasApproxTangentSpace_congr_restrict {ν : Measure E} {U : Set E} (hU : U ∈ 𝓝 x)
    (hμν : μ.restrict U = ν.restrict U) :
    μ.HasApproxTangentSpace x T θ ↔ ν.HasApproxTangentSpace x T θ :=
  ⟨HasApproxTangentSpace.congr_restrict hU hμν, HasApproxTangentSpace.congr_restrict hU hμν.symm⟩

end ApproxTangentSpace

end MeasureTheory.Measure

namespace AffineSubspace

open MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {x : E} {A : AffineSubspace ℝ E} {θ : ℝ≥0}

/-- For an affine subspace `A` of dimension `k` and `θ ≠ 0`, the measure `θ μHE[k]⌞A` has
approximate tangent space `A.direction` with multiplicity `θ` at every point of `A`. -/
theorem hasApproxTangentSpace_smul_euclideanHausdorffMeasure_restrict (hx : x ∈ A) (hθ : θ ≠ 0) :
    (θ • μHE[finrank ℝ A.direction].restrict (A : Set E)).HasApproxTangentSpace x A.direction
      θ := by
  refine ⟨hθ, fun f ↦ tendsto_const_nhds.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [blowUp_smul, blowUp_euclideanHausdorffMeasure_restrict hx hr, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul]

end AffineSubspace
