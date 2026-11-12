/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Moments
public import TauCeti.Probability.Distributions.Semicircle.Moments
import TauCeti.Algebra.GroupWithZero.Units.Basic
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# The free Poisson law

For a rate `r ≥ 0` and a jump size `c ∈ ℝ`, the free Poisson law `freePoissonReal r c` is the
compactly supported probability measure on `ℝ` whose free cumulants are `κ_n = r c ^ n`, that is,
whose moments are

`∫ x ^ n d(freePoissonReal r c) = c ^ n ∑_{π ∈ NC(n)} r ^ |π|`.

For jump size `1` and `r > 0` it is the dilation by `r` of the Marchenko–Pastur law of ratio
`1 / r`, and we take this as the definition, followed by the dilation by `c`:
`freePoissonReal r c` is the pushforward of `marchenkoPastur r⁻¹` along `x ↦ c r x`. Under
Lean's convention `0⁻¹ = 0` the same formula gives the Dirac mass at `0` for `r = 0`, because
`marchenkoPastur 0` is the Dirac mass at `1`; the jump size `c = 0` also gives the Dirac mass at
`0`, and a negative jump size reflects the law.

For `c = 1` and `r > 0`, with `a = (1 - √r)²` and `b = (1 + √r)²`, the law has an atom of mass
`max (1 - r) 0` at `0` and the density `√((b - t)(t - a)) / (2π t)` on `(a, b)`
(`freePoissonReal_one_eq_withDensity`). The real square root makes this density vanish outside
`[a, b]`, and its value at `t = 0` is `0` by Lean's convention for division by zero. At `r = 1`
the lower edge is `a = 0`, where the density blows up like `t^(-1/2)`; the identity of measures
includes this endpoint, since the law has total mass one.

The moment formula follows from the noncrossing-partition moments of the Marchenko–Pastur law,
with each part `B` of `π` contributing `r c ^ |B|`. Since free Poisson laws are compactly
supported, they are determined by these moments; in particular the pushforward of the centred
semicircle law of variance `v` along `x ↦ x²` is the free Poisson law of rate `1` and jump size
`v` (`map_sq_semicircleReal`).

## Main definitions

* `TauCeti.Probability.freePoissonReal r c` — the free Poisson law of rate `r` and jump size `c`.

## Main results

* `TauCeti.Probability.freePoissonReal_zero_left`, `TauCeti.Probability.freePoissonReal_zero_right`
  — the degenerate laws are the Dirac mass at `0`.
* `TauCeti.Probability.map_mul_freePoissonReal` — dilating by `d` multiplies the jump size by `d`.
* `TauCeti.Probability.freePoissonReal_one_eq_withDensity` — the atom and density for jump size
  `1` and positive rate.
* `TauCeti.Probability.ae_eq_zero_or_mem_Icc_freePoissonReal_one`,
  `TauCeti.Probability.support_freePoissonReal_one` — the carrier
  `{0} ∪ [(1 - √r)², (1 + √r)²]` and the exact topological support for jump size `1`.
* `TauCeti.Probability.ae_abs_le_freePoissonReal` — every free Poisson law is carried by
  `[-|c| (1 + √r)², |c| (1 + √r)²]`.
* `TauCeti.Probability.integral_pow_freePoissonReal` — the moments
  `c ^ n ∑_{π ∈ NC(n)} r ^ |π|`.
* `TauCeti.Probability.eq_freePoissonReal_of_integral_pow` — moment determinacy.
* `TauCeti.Probability.map_sq_semicircleReal` — the square of a centred semicircle variable of
  variance `v` is free Poisson of rate `1` and jump size `v`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12
  (free Poisson laws and their free cumulants).
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, §3.1 (the Marchenko–Pastur law).
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal Finset

namespace TauCeti.Probability

/-- The free Poisson law of rate `r` and jump size `c`: the pushforward of the Marchenko–Pastur law
of ratio `r⁻¹` along `x ↦ c r x`. For `r = 0` (where `r⁻¹ = 0` and `marchenkoPastur 0 = δ₁`) or
`c = 0` this is the Dirac mass at `0`. -/
def freePoissonReal (r : ℝ≥0) (c : ℝ) : Measure ℝ :=
  (marchenkoPastur r⁻¹).map fun x ↦ c * r * x

/-- The free Poisson law is the dilation of a Marchenko–Pastur law. -/
theorem freePoissonReal_def (r : ℝ≥0) (c : ℝ) :
    freePoissonReal r c = (marchenkoPastur r⁻¹).map fun x ↦ c * r * x :=
  (rfl)

/-- Every free Poisson law is a probability measure. -/
instance isProbabilityMeasure_freePoissonReal (r : ℝ≥0) (c : ℝ) :
    IsProbabilityMeasure (freePoissonReal r c) := by
  rw [freePoissonReal_def]
  infer_instance

/-- The free Poisson law of rate `0` is the Dirac mass at `0`. -/
@[simp]
theorem freePoissonReal_zero_left (c : ℝ) : freePoissonReal 0 c = Measure.dirac 0 := by
  simp [freePoissonReal_def, Measure.map_dirac' (by fun_prop : Measurable fun x : ℝ ↦ (0 : ℝ))]

/-- The free Poisson law of jump size `0` is the Dirac mass at `0`. -/
@[simp]
theorem freePoissonReal_zero_right (r : ℝ≥0) : freePoissonReal r 0 = Measure.dirac 0 := by
  simp [freePoissonReal_def, Measure.map_const]

/-- Dilating the free Poisson law of jump size `c` by `d` gives the free Poisson law of jump size
`d * c`. -/
theorem map_mul_freePoissonReal (r : ℝ≥0) (c d : ℝ) :
    (freePoissonReal r c).map (d * ·) = freePoissonReal r (d * c) := by
  rw [freePoissonReal_def, Measure.map_map (by fun_prop) (by fun_prop), freePoissonReal_def]
  congr 1
  ext x
  simp only [Function.comp_apply]
  ring

/-- The free Poisson law of rate `1` and jump size `1` is the Marchenko–Pastur law of ratio `1`. -/
@[simp]
theorem freePoissonReal_one_one : freePoissonReal 1 1 = marchenkoPastur 1 := by
  simp [freePoissonReal_def]

/-- The density of the free Poisson law of jump size `1` at positive rate is the rescaled density
of the corresponding Marchenko–Pastur law. -/
private theorem inv_mul_density_marchenkoPastur_inv {r : ℝ≥0} (hr : 0 < r) (t : ℝ) :
    |(r : ℝ)|⁻¹ * (√(((1 + √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2 - t / r) *
        (t / r - (1 - √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2)) / (2 * π * ((r⁻¹ : ℝ≥0) : ℝ) * (t / r))) =
      √(((1 + √(r : ℝ)) ^ 2 - t) * (t - (1 - √(r : ℝ)) ^ 2)) / (2 * π * t) := by
  have hr' : (0 : ℝ) < r := hr
  have hs : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr'
  have hss : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr'.le
  have hinv : √((r⁻¹ : ℝ≥0) : ℝ) = (√(r : ℝ))⁻¹ := by
    rw [NNReal.coe_inv, Real.sqrt_inv]
  have hprod : ((1 + √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2 - t / r) * (t / r - (1 - √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2) =
      (((1 + √(r : ℝ)) ^ 2 - t) * (t - (1 - √(r : ℝ)) ^ 2)) / (r : ℝ) ^ 2 := by
    rw [hinv]
    generalize √(r : ℝ) = s at hs hss ⊢
    rw [← hss]
    field_simp
    ring
  rw [hprod, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr'.le, abs_of_pos hr',
    NNReal.coe_inv]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · field_simp

/-- **The density of the free Poisson law.** For a rate `r > 0`, with `a = (1 - √r)²` and
`b = (1 + √r)²`, the free Poisson law of jump size `1` has an atom of mass `max (1 - r) 0` at `0`
and the density `√((b - t)(t - a)) / (2π t)` with respect to Lebesgue measure. The real square
root makes the density zero outside `(a, b)`, and its value at `t = 0` is `0`. -/
theorem freePoissonReal_one_eq_withDensity {r : ℝ≥0} (hr : 0 < r) :
    freePoissonReal r 1 = ENNReal.ofReal (1 - r) • Measure.dirac 0 +
      volume.withDensity fun t ↦ ENNReal.ofReal
        (√(((1 + √(r : ℝ)) ^ 2 - t) * (t - (1 - √(r : ℝ)) ^ 2)) / (2 * π * t)) := by
  have hr' : (r : ℝ) ≠ 0 := (NNReal.coe_pos.2 hr).ne'
  have hmap : (fun x : ℝ ↦ 1 * r * x) = fun x ↦ 0 + (r : ℝ) * x := by
    ext x
    ring
  have hmeas : Measurable fun x : ℝ ↦ 0 + (r : ℝ) * x := by fun_prop
  rw [freePoissonReal_def, hmap, marchenkoPastur_eq_withDensity (inv_pos.2 hr),
    Measure.map_add _ _ hmeas, Measure.map_smul _ hmeas.aemeasurable, Measure.map_dirac' hmeas,
    map_affine_withDensity_volume _ hr']
  congr 2
  · simp only [NNReal.coe_inv]
    field_simp
  · simp
  · ext t
    rw [affineDensity_apply, ← ENNReal.ofReal_mul (by positivity), sub_zero]
    congr 1
    exact inv_mul_density_marchenkoPastur_inv hr t

/-- The edges of the Marchenko–Pastur law of ratio `r⁻¹`, dilated by `r`, are the edges
`(1 ∓ √r)²` of the free Poisson law of rate `r`. -/
private theorem coe_mul_edges {r : ℝ≥0} (hr : 0 < r) :
    (r : ℝ) * (1 - √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2 = (1 - √(r : ℝ)) ^ 2 ∧
      (r : ℝ) * (1 + √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2 = (1 + √(r : ℝ)) ^ 2 := by
  have key (s : ℝ) (hs : 0 < s) :
      s ^ 2 * (1 - s⁻¹) ^ 2 = (1 - s) ^ 2 ∧ s ^ 2 * (1 + s⁻¹) ^ 2 = (1 + s) ^ 2 :=
    ⟨by field_simp; ring, by field_simp; ring⟩
  have k := key _ (Real.sqrt_pos.2 (NNReal.coe_pos.2 hr))
  rwa [Real.sq_sqrt (NNReal.coe_nonneg r), ← Real.sqrt_inv, ← NNReal.coe_inv] at k

/-- The free Poisson law of jump size `1` is carried by `{0} ∪ [(1 - √r)², (1 + √r)²]`. -/
theorem ae_eq_zero_or_mem_Icc_freePoissonReal_one (r : ℝ≥0) :
    ∀ᵐ x ∂freePoissonReal r 1, x = 0 ∨ x ∈ Icc ((1 - √(r : ℝ)) ^ 2) ((1 + √(r : ℝ)) ^ 2) := by
  rcases eq_zero_or_pos r with rfl | hr
  · simp
  have hm : MeasurableSet {x : ℝ | x = 0 ∨ x ∈ Icc ((1 - √(r : ℝ)) ^ 2) ((1 + √(r : ℝ)) ^ 2)} :=
    (measurableSet_singleton 0).union measurableSet_Icc
  rw [freePoissonReal_def, ae_map_iff (by fun_prop) hm]
  filter_upwards [ae_eq_zero_or_mem_Icc_marchenkoPastur r⁻¹] with x hx
  rcases hx with rfl | ⟨h1, h2⟩
  · simp
  right
  have hr' : (0 : ℝ) ≤ r := NNReal.coe_nonneg r
  rw [one_mul, ← (coe_mul_edges hr).1, ← (coe_mul_edges hr).2]
  exact ⟨mul_le_mul_of_nonneg_left h1 hr', mul_le_mul_of_nonneg_left h2 hr'⟩

/-- **The support of the free Poisson law.** For a rate `r > 0`, the topological support of the
free Poisson law of jump size `1` is the interval `[(1 - √r)², (1 + √r)²]`, together with the atom
`0` when `r < 1`. -/
theorem support_freePoissonReal_one {r : ℝ≥0} (hr : 0 < r) :
    (freePoissonReal r 1).support =
      if 1 ≤ r then Icc ((1 - √(r : ℝ)) ^ 2) ((1 + √(r : ℝ)) ^ 2)
      else insert 0 (Icc ((1 - √(r : ℝ)) ^ 2) ((1 + √(r : ℝ)) ^ 2)) := by
  have hr' : (0 : ℝ) < r := hr
  have hmap : (fun x : ℝ ↦ 1 * r * x) = fun x ↦ 0 + (r : ℝ) * x := by
    ext x
    ring
  have himage : (fun x : ℝ ↦ 0 + (r : ℝ) * x) '' Icc ((1 - √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2)
      ((1 + √((r⁻¹ : ℝ≥0) : ℝ)) ^ 2) = Icc ((1 - √(r : ℝ)) ^ 2) ((1 + √(r : ℝ)) ^ 2) := by
    simp only [zero_add]
    rw [image_mul_left_Icc' hr', (coe_mul_edges hr).1, (coe_mul_edges hr).2]
  have hle : r⁻¹ ≤ 1 ↔ 1 ≤ r := inv_le_one₀ hr
  rw [freePoissonReal_def, hmap, support_map_affine (NNReal.coe_pos.2 hr).ne',
    support_marchenkoPastur]
  by_cases h : 1 ≤ r
  · simp only [hle.2 h, h, ↓reduceIte, himage]
  · simp only [hle.not.2 h, h, ↓reduceIte, image_insert_eq, himage]
    simp

/-- Every free Poisson law of rate `r` and jump size `c` is carried by
`[-|c| (1 + √r)², |c| (1 + √r)²]`. -/
theorem ae_abs_le_freePoissonReal (r : ℝ≥0) (c : ℝ) :
    ∀ᵐ x ∂freePoissonReal r c, |x| ≤ |c| * (1 + √(r : ℝ)) ^ 2 := by
  have h1 := ae_eq_zero_or_mem_Icc_freePoissonReal_one r
  rw [freePoissonReal_def] at h1 ⊢
  have hm : MeasurableSet {x : ℝ | |x| ≤ |c| * (1 + √(r : ℝ)) ^ 2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hm1 : MeasurableSet {x : ℝ | x = 0 ∨ x ∈ Icc ((1 - √(r : ℝ)) ^ 2) ((1 + √(r : ℝ)) ^ 2)} :=
    (measurableSet_singleton 0).union measurableSet_Icc
  rw [ae_map_iff (by fun_prop) hm1] at h1
  rw [ae_map_iff (by fun_prop) hm]
  filter_upwards [h1] with x hx
  have hb : 0 ≤ (1 + √(r : ℝ)) ^ 2 := sq_nonneg _
  have key : |1 * r * x| ≤ (1 + √(r : ℝ)) ^ 2 := by
    rcases hx with hx | ⟨hx1, hx2⟩
    · rw [hx, abs_zero]
      exact hb
    · rw [abs_of_nonneg ((sq_nonneg _).trans hx1)]
      exact hx2
  calc |c * r * x| = |c| * |1 * r * x| := by rw [one_mul, mul_assoc, abs_mul]
    _ ≤ |c| * (1 + √(r : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left key (abs_nonneg c)

/-- Every free Poisson law gives no mass outside a compact interval. -/
theorem freePoissonReal_compl_Icc (r : ℝ≥0) (c : ℝ) :
    freePoissonReal r c (Icc (-(|c| * (1 + √(r : ℝ)) ^ 2)) (|c| * (1 + √(r : ℝ)) ^ 2))ᶜ = 0 := by
  rw [← mem_ae_iff]
  filter_upwards [ae_abs_le_freePoissonReal r c] with x hx
  exact abs_le.1 hx

/-- Every natural power is integrable against a free Poisson law. -/
theorem integrable_pow_freePoissonReal (r : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun x ↦ x ^ n) (freePoissonReal r c) := by
  rw [freePoissonReal_def, integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def, mul_pow] using (integrable_pow_marchenkoPastur r⁻¹ n).const_mul
    ((c * r) ^ n)

/-- **The moments of the free Poisson law.** The `n`-th moment of the free Poisson law of rate `r`
and jump size `c` is `c ^ n ∑_{π ∈ NC(n)} r ^ |π|`: each part of `π` contributes the free cumulant
`r c ^ |B|`. -/
theorem integral_pow_freePoissonReal (r : ℝ≥0) (c : ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂freePoissonReal r c =
      c ^ n * ∑ P : NoncrossingPartition (Finset.univ : Finset (Fin n)), (r : ℝ) ^ #P.1.parts := by
  have h := integral_pow_card_marchenkoPastur_eq_sum_prod r⁻¹ (Finset.univ : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hc := NoncrossingPartition.sum_prod_mul_pow_card (Finset.univ : Finset (Fin n)) (r : ℝ) c
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [freePoissonReal_def, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow (c * r)]
  rw [integral_const_mul, h, ← hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  -- Split `(c r) ^ n` along the parts of `P`, whose sizes add up to `n`.
  have hsplit : (c * r) ^ n = ∏ B ∈ P.1.parts, (c * r) ^ #B := by
    rw [Finset.prod_pow_eq_pow_sum, P.1.sum_card_parts, Finset.card_univ, Fintype.card_fin]
  rw [hsplit, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun B hB ↦ by
    -- A part of size `k ≥ 1` contributes `r c ^ k`.
    rw [NNReal.coe_inv,
      mul_pow_mul_inv_pow_sub_one₀ c (r : ℝ) (P.1.nonempty_of_mem_parts hB).card_pos.ne']

/-- **Moment determinacy of the free Poisson law.** A finite measure on `ℝ` concentrated on a
compact set is the free Poisson law of rate `r` and jump size `c` as soon as its moments are
`c ^ n ∑_{π ∈ NC(n)} r ^ |π|`. -/
theorem eq_freePoissonReal_of_integral_pow {μ : Measure ℝ} [IsFiniteMeasure μ] {K : Set ℝ}
    (hK : IsCompact K) (hμ : μ Kᶜ = 0) (r : ℝ≥0) (c : ℝ)
    (h : ∀ n : ℕ, ∫ x, x ^ n ∂μ =
      c ^ n * ∑ P : NoncrossingPartition (Finset.univ : Finset (Fin n)), (r : ℝ) ^ #P.1.parts) :
    μ = freePoissonReal r c := by
  set R := |c| * (1 + √(r : ℝ)) ^ 2
  refine TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (hK.union isCompact_Icc)
    (measure_mono_null (compl_subset_compl.2 subset_union_left) hμ)
    (measure_mono_null (compl_subset_compl.2 (subset_union_right (s := K) (t := Icc (-R) R)))
      (freePoissonReal_compl_Icc r c)) fun n ↦ ?_
  rw [h, integral_pow_freePoissonReal]

/-- **The square of a semicircle variable is free Poisson.** The pushforward of the centred
semicircle law of variance `v` along `x ↦ x²` is the free Poisson law of rate `1` and jump size
`v`; both have the moments `v ^ n * catalan n`. -/
theorem map_sq_semicircleReal (v : ℝ≥0) :
    (semicircleReal 0 v).map (· ^ 2) = freePoissonReal 1 v := by
  have hK : ∀ᵐ x ∂(semicircleReal 0 v).map (· ^ 2), x ∈ Icc 0 (4 * (v : ℝ)) := by
    rw [ae_map_iff (p := (· ∈ Icc (0 : ℝ) (4 * (v : ℝ)))) (by fun_prop) measurableSet_Icc]
    filter_upwards [ae_mem_Icc_semicircleReal 0 v] with x hx
    have hs := Real.sq_sqrt v.coe_nonneg
    refine ⟨sq_nonneg x, ?_⟩
    rw [zero_sub, zero_add] at hx
    nlinarith [hx.1, hx.2, Real.sqrt_nonneg (v : ℝ)]
  refine eq_freePoissonReal_of_integral_pow isCompact_Icc (mem_ae_iff.1 hK) 1 v fun n ↦ ?_
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [← pow_mul, NoncrossingPartition.card_fin_eq_catalan]

end TauCeti.Probability
