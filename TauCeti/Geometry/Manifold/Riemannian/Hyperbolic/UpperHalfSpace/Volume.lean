/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The volume of the upper half-space model

The Riemannian volume of the upper half-space model `UpperHalfSpace E` of hyperbolic space, of
dimension `n = dim E + 1`, has density `t⁻ⁿ` against Lebesgue measure of `E × ℝ`:

`dV = t⁻ⁿ dx dt`.

The hyperbolic metric is the Euclidean metric divided by `t²`, so in the inclusion chart its Gram
matrix is `t⁻²` times the Euclidean Gram matrix, and the square root of its determinant is `t⁻ⁿ`
times the Euclidean one.

## Main results

* `TauCeti.UpperHalfSpace.map_coe_riemannianVolume`: the image of the Riemannian volume in
  `E × ℝ` is Lebesgue measure on the open half-space `{0 < t}` with density `t⁻ⁿ`.
* `TauCeti.UpperHalfSpace.riemannianVolume_eq_withDensity`: the Riemannian volume is the pullback
  of Lebesgue measure with density `t⁻ⁿ`.
* `TauCeti.UpperHalfSpace.riemannianVolume_setOf_fst_mem_and_height_mem`: the product form
  `vol {(x, t) | x ∈ A, t ∈ T} = vol A · ∫_{T ∩ (0, ∞)} t⁻ⁿ dt`.
* `TauCeti.UpperHalfSpace.riemannianVolume_setOf_fst_mem_and_le_height`: a cusp region
  `{(x, t) | x ∈ A, c ≤ t}` has volume `vol A · c^{-(n - 1)} / (n - 1)` when `n ≥ 2`; for
  hyperbolic three-space and a horizontal region of area `a` above height `1`, this is `a / 2`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the Riemannian volume form in coordinates) and Chapter 3 (the upper half-space model).
* J. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019), §4.6
  (the hyperbolic volume element of the upper half-space model).
-/

public section

open Bundle MeasureTheory Riemannian.Tensor Set
open scoped Manifold

noncomputable section

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "P" => WithLp 2 (E × ℝ)
local notation "J" => 𝓘(ℝ, WithLp 2 (E × ℝ))

/-- In every chart, the Gram matrix of the hyperbolic metric at `x` is `height x⁻²` times the
Euclidean Gram matrix of the model basis. -/
private theorem chartGramMatrix_eq (α x : UpperHalfSpace E) :
    chartGramMatrix (I := J) α x = (height x ^ 2)⁻¹ • Matrix.gram ℝ (Module.finBasis ℝ P) := by
  ext i j
  rw [chartGramMatrix_apply, chartLocalFrame_eq_symmL, chartLocalFrame_eq_symmL, inner_def]
  simp [Matrix.gram_apply, div_eq_inv_mul]

/-- In every chart, the Riemannian volume density at `x` is `height x⁻ⁿ` times the Euclidean
volume density of the model basis. -/
private theorem chartVolumeDensity_eq (α x : UpperHalfSpace E) :
    chartVolumeDensity (I := J) α x =
      (height x ^ (Module.finrank ℝ E + 1))⁻¹ * √(Matrix.gram ℝ (Module.finBasis ℝ P)).det := by
  have h : ((height x ^ 2)⁻¹) ^ Module.finrank ℝ P =
      ((height x ^ (Module.finrank ℝ E + 1))⁻¹) ^ 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq, Module.finrank_prod, Module.finrank_self,
      ← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  have := (height_pos x).le
  rw [chartVolumeDensity_def, chartGramMatrix_eq, Matrix.det_smul, Fintype.card_fin, h,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

variable [MeasurableSpace (UpperHalfSpace E)] [BorelSpace (UpperHalfSpace E)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The inclusion of the upper half-space into `E × ℝ` is a measurable embedding. -/
theorem measurableEmbedding_coe [MeasurableSpace P] [BorelSpace P] :
    MeasurableEmbedding (coe : UpperHalfSpace E → P) :=
  isOpenEmbedding_coe.measurableEmbedding

/-- `map_coe_riemannianVolume` for a measurable structure on `E × ℝ` equal to the Borel one. The
chart volumes are built on the Borel structure of the model space, while the volume of `E × ℝ`
lives on the product structure of `WithLp`; taking the structure as a variable lets the two be
identified. -/
private theorem map_coe_riemannianVolume_of_eq_borel [m : MeasurableSpace P] [BorelSpace P]
    (hm : m = borel P) :
    (riemannianVolume J (UpperHalfSpace E)).map coe =
      (volume.restrict {p : P | 0 < p.snd}).withDensity
        fun p ↦ ENNReal.ofReal (p.snd ^ (Module.finrank ℝ E + 1))⁻¹ := by
  subst hm
  let : MeasurableSpace P := borel P
  have hemb : MeasurableEmbedding (coe : UpperHalfSpace E → P) := measurableEmbedding_coe
  have hpos : MeasurableSet {p : P | 0 < p.snd} :=
    (isOpen_lt continuous_const (WithLp.continuous_snd 2 E ℝ)).measurableSet
  -- Every chart of the upper half-space is defined everywhere; use the one at `(0, 1)`.
  let α : UpperHalfSpace E := mk (WithLp.toLp 2 (0, 1)) (by simp)
  ext t ht
  rw [hemb.map_apply, withDensity_apply _ ht, Measure.restrict_restrict ht,
    riemannianVolume_apply_of_subset (α := α) (by simp), chartRiemannianVolume_apply _
      (hemb.measurable ht), (Module.finBasis ℝ P).volume_eq_smul_addHaar,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsrc : (extChartAt J α).source = univ := by simp
  have hcoe : ⇑(extChartAt J α) = coe := by ext1 x; simp
  rw [hsrc, inter_univ, hcoe, image_preimage_eq_inter_range, range_coe]
  refine setLIntegral_congr_fun (ht.inter hpos) fun p hp ↦ ?_
  obtain ⟨x, rfl⟩ : p ∈ range coe := by simpa using hp.2
  have hx : (extChartAt J α).symm x = x := by
    simpa [hcoe] using (extChartAt J α).left_inv (x := x) (by simp)
  rw [hx, chartVolumeDensity_eq, snd_coe, mul_comm, ENNReal.ofReal_mul (by positivity)]

variable [MeasurableSpace E] [BorelSpace E]

/-- **The volume form of the upper half-space**: the image in `E × ℝ` of the Riemannian volume of
the upper half-space model of hyperbolic `n`-space is Lebesgue measure on the half-space
`{0 < t}` with density `t⁻ⁿ`, `n = dim E + 1`. -/
theorem map_coe_riemannianVolume :
    (riemannianVolume J (UpperHalfSpace E)).map coe =
      (volume.restrict {p : P | 0 < p.snd}).withDensity
        fun p ↦ ENNReal.ofReal (p.snd ^ (Module.finrank ℝ E + 1))⁻¹ :=
  map_coe_riemannianVolume_of_eq_borel BorelSpace.measurable_eq

/-- **The volume form of the upper half-space**: the Riemannian volume of the upper half-space
model of hyperbolic `n`-space, `n = dim E + 1`, is the pullback of Lebesgue measure of `E × ℝ`
with density `t⁻ⁿ`. -/
theorem riemannianVolume_eq_withDensity :
    riemannianVolume J (UpperHalfSpace E) =
      (volume.comap coe).withDensity
        fun x ↦ ENNReal.ofReal (height x ^ (Module.finrank ℝ E + 1))⁻¹ := by
  have hemb : MeasurableEmbedding (coe : UpperHalfSpace E → P) := measurableEmbedding_coe
  rw [← hemb.comap_map (riemannianVolume J _), map_coe_riemannianVolume, ← range_coe,
    ← hemb.map_comap, ← hemb.map_withDensity_comp, hemb.comap_map]
  -- The density `t⁻ⁿ` composed with `coe` is `height⁻ⁿ`.
  simp [Function.comp_def]

/-- **The volume of a product region of the upper half-space**: the points `(x, t)` with `x ∈ A`
and `t ∈ T` have volume `vol A · ∫_{T ∩ (0, ∞)} t⁻ⁿ dt`, `n = dim E + 1`. -/
theorem riemannianVolume_setOf_fst_mem_and_height_mem {A : Set E} (hA : MeasurableSet A)
    {T : Set ℝ} (hT : MeasurableSet T) :
    riemannianVolume J (UpperHalfSpace E) {x | (x : P).fst ∈ A ∧ height x ∈ T} =
      volume A * ∫⁻ t in T ∩ Ioi 0, ENNReal.ofReal (t ^ (Module.finrank ℝ E + 1))⁻¹ := by
  have hemb : MeasurableEmbedding (coe : UpperHalfSpace E → P) := measurableEmbedding_coe
  have hS : MeasurableSet (WithLp.ofLp ⁻¹' (A ×ˢ T) : Set P) :=
    (hA.prod hT).preimage (by fun_prop)
  have hT' : MeasurableSet (T ∩ Ioi 0) := hT.inter measurableSet_Ioi
  have hset : {x : UpperHalfSpace E | (x : P).fst ∈ A ∧ height x ∈ T} =
      coe ⁻¹' (WithLp.ofLp ⁻¹' (A ×ˢ T)) := by
    ext x
    simp
  have hset' : (WithLp.ofLp ⁻¹' (A ×ˢ T) : Set P) ∩ {p | 0 < p.snd} =
      WithLp.ofLp ⁻¹' (A ×ˢ (T ∩ Ioi 0)) := by
    ext p
    simp [and_assoc]
  rw [hset, ← hemb.map_apply, map_coe_riemannianVolume, withDensity_apply _ hS,
    Measure.restrict_restrict hS, hset']
  simp only [← WithLp.ofLp_snd]
  rw [(WithLp.volume_preserving_ofLp E ℝ).setLIntegral_comp_preimage (hA.prod hT')
      (f := fun q : E × ℝ ↦ ENNReal.ofReal (q.2 ^ (Module.finrank ℝ E + 1))⁻¹) (by fun_prop),
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa using lintegral_prod_mul (μ := volume.restrict A) (ν := volume.restrict (T ∩ Ioi 0))
    (f := fun _ ↦ 1) (g := fun t ↦ ENNReal.ofReal (t ^ (Module.finrank ℝ E + 1))⁻¹)
    aemeasurable_const (by fun_prop)

/-- **The volume of a cusp region**: for `0 < c` and `dim E ≠ 0`, the points `(x, t)` with
`x ∈ A` and `c ≤ t` have volume `vol A · c^{-(n - 1)} / (n - 1)`, `n = dim E + 1`. -/
theorem riemannianVolume_setOf_fst_mem_and_le_height (hE : Module.finrank ℝ E ≠ 0)
    {A : Set E} (hA : MeasurableSet A) {c : ℝ} (hc : 0 < c) :
    riemannianVolume J (UpperHalfSpace E) {x | (x : P).fst ∈ A ∧ c ≤ height x} =
      volume A * ENNReal.ofReal ((c ^ Module.finrank ℝ E)⁻¹ / Module.finrank ℝ E) := by
  set m := Module.finrank ℝ E
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hE
  have ha : -((m : ℝ) + 1) < -1 := by linarith
  -- On `(c, ∞)` the density `t⁻ⁿ` is the real power `t ^ (-(m + 1))`.
  have hrpow : EqOn (fun t : ℝ ↦ (t ^ (m + 1))⁻¹) (fun t ↦ t ^ (-((m : ℝ) + 1))) (Ioi c) :=
    fun t ht ↦ by
      dsimp only
      rw [Real.rpow_neg (hc.trans ht).le, ← Nat.cast_add_one, Real.rpow_natCast]
  have hint : IntegrableOn (fun t : ℝ ↦ (t ^ (m + 1))⁻¹) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun hrpow.symm measurableSet_Ioi
  have h := riemannianVolume_setOf_fst_mem_and_height_mem hA (measurableSet_Ici (a := c))
  simp only [mem_Ici] at h
  rw [h, inter_eq_left.2 (Ici_subset_Ioi.2 hc), Measure.restrict_congr_set Ioi_ae_eq_Ici.symm,
    ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun t ht ↦
        (inv_pos.2 (pow_pos (hc.trans ht) _)).le)),
    setIntegral_congr_fun measurableSet_Ioi hrpow, integral_Ioi_rpow_of_lt ha hc]
  have hexp : -((m : ℝ) + 1) + 1 = -m := by ring
  congr 2
  rw [hexp, Real.rpow_neg hc.le, Real.rpow_natCast, neg_div_neg_eq]

end TauCeti.UpperHalfSpace
