/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
public import TauCeti.MeasureTheory.Measure.PiWithDensity
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Coordinates

/-!
# The Haar measures of the archimedean parameters and of the norm-one hypersurface

Hecke's integral representation of a partial zeta function integrates a theta series against the
multiplicative Haar measure `dy / y` of the positive archimedean parameters `y = (y_w)_w` of a
number field `K`, and then splits off the norm `t = N(y)` as a radial coordinate, along
`y = x t^(1/n)` with `x` on the norm-one hypersurface `S` and `n = [K : ℚ]`. This file constructs
the measures of that decomposition:

* `archHaar K` is `dy / y = ∏_w dy_w / y_w`, the product over the infinite places of the measure
  `TauCeti.multHaar = dt / t` of `(0, ∞)`; it is Lebesgue measure on the positive orthant with
  density `∏_w y_w⁻¹` (`archHaar_eq_withDensity`), and it is invariant under the dilations
  `y ↦ c y`, `c > 0` (`map_archHaar_smul`), as well as independent positive dilations
  (`map_archHaar_mul_left`) and coordinatewise inversion (`map_archHaar_inv`).
* `surfaceHaar K` is the measure `d*x` on `S` induced by the product-over-places normalization of
  `dy / y`: the mass of `A ⊆ S` is the `dy / y`-mass of the parameters with surface part in `A`
  and norm in `[1, e]` (`surfaceHaar_apply`). It is σ-finite, and bounded subsets of `S` have
  finite mass (`surfaceHaar_lt_top_of_isBounded`). Neukirch's canonical surface measure is `2 ^ r₂`
  times `surfaceHaar K`.
* `archHaar_eq_map`: `dy / y` is the image of the product measure `d*x × dt / t` under
  `(x, t) ↦ x t^(1/n)`. The corresponding rectangle-mass formula is
  `archHaar_surfacePart_preimage_inter`, allowing any measurable radial shell.

The proof of the decomposition fixes a measurable `A ⊆ S` and pushes `dy / y`, restricted to the
parameters with surface part in `A`, forward along the norm. The dilations of `y` move the norm by
any factor `c > 0` and fix the surface part, so this image measure is invariant under the
dilations of `(0, ∞)`. It is therefore its mass on `[1, e]`, which is the `d*x`-mass of `A`,
times `dt / t` (`TauCeti.eq_smul_multHaar`), as soon as that mass is finite, and σ-finiteness of
`d*x` removes the finiteness assumption.

⚠ The measure is the product over places: Neukirch's canonical `dy / y` carries the factor
`e_𝔭 = 2` at each complex place and is `2 ^ r₂` times `archHaar K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open MeasureTheory Measure Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The multiplicative Haar measure of the parameters -/

variable (K) in
/-- The multiplicative Haar measure `dy / y = ∏_w dy_w / y_w` of the positive archimedean
parameters: the product over the infinite places of `dt / t`. ⚠ It is the product over places;
Neukirch's canonical `dy / y` carries the factor `e_𝔭 = 2` at each complex place and is `2 ^ r₂`
times this one. -/
def archHaar : Measure (realSpace K) :=
  Measure.pi fun _ ↦ multHaar

instance : SigmaFinite (archHaar K) := by
  unfold archHaar
  infer_instance

/-- `dy / y` is Lebesgue measure on the positive orthant with density `∏_w y_w⁻¹`. -/
theorem archHaar_eq_withDensity :
    archHaar K = (volume.restrict {y : realSpace K | ∀ w, 0 < y w}).withDensity
      fun y ↦ ENNReal.ofReal (∏ w, (y w)⁻¹) := by
  have hP : {y : realSpace K | ∀ w, 0 < y w} = univ.pi fun _ ↦ Ioi 0 := by
    ext y
    simp
  have hPmeas : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} :=
    hP ▸ MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioi
  rw [archHaar, multHaar_def, pi_withDensity _ fun _ ↦ measurable_inv.ennreal_ofReal,
    ← restrict_pi_pi, ← volume_pi, ← hP]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hPmeas] with y hy
  exact (ENNReal.ofReal_prod_of_nonneg fun w _ ↦ (inv_pos.mpr (hy w)).le).symm

/-- `dy / y` is concentrated on the positive orthant. -/
theorem ae_archHaar_pos : ∀ᵐ y ∂archHaar K, ∀ w, 0 < y w := by
  refine ae_all_iff.mpr fun w ↦ ae_iff.mpr ?_
  simp only [not_lt]
  exact pi_eval_preimage_null (μ := fun _ : InfinitePlace K ↦ multHaar) (i := w)
    multHaar_Iic_zero

/-- The product measure `dy / y` is invariant under independent positive dilations at the
infinite places, not just a common scalar dilation. -/
theorem map_archHaar_mul_left {c : realSpace K} (hc : ∀ w, 0 < c w) :
    (archHaar K).map (c * ·) = archHaar K := by
  have : ∀ w, SigmaFinite (multHaar.map (c w * ·)) := fun w ↦ by
    rw [map_multHaar_mul_left (hc w)]
    infer_instance
  have hmul : (c * · : realSpace K → realSpace K) = fun y w ↦ c w * y w := by
    ext y w
    exact Pi.mul_apply c y w
  rw [hmul, archHaar, pi_map_pi fun w ↦ (measurable_const_mul (c w)).aemeasurable]
  simp_rw [map_multHaar_mul_left (hc _)]

/-- `dy / y` is invariant under the dilations `y ↦ c y`, `c > 0`. -/
theorem map_archHaar_smul {c : ℝ} (hc : 0 < c) : (archHaar K).map (c • ·) = archHaar K := by
  have hsmul : (c • · : realSpace K → realSpace K) = ((fun _ ↦ c) * ·) := by
    ext
    simp
  rw [hsmul]
  exact map_archHaar_mul_left fun _ ↦ hc

/-- Coordinatewise inversion preserves the product measure `dy / y`. -/
theorem map_archHaar_inv : (archHaar K).map Inv.inv = archHaar K := by
  have : SigmaFinite (multHaar.map Inv.inv) := by
    rw [map_multHaar_inv]
    infer_instance
  have hinv : (Inv.inv : realSpace K → realSpace K) = fun y w ↦ (y w)⁻¹ := by
    ext y w
    exact Pi.inv_apply y w
  rw [hinv, archHaar, pi_map_pi fun _ ↦ measurable_inv.aemeasurable]
  simp_rw [map_multHaar_inv]

/-! ### The Haar measure of the norm-one hypersurface -/

variable (K) in
/-- The measure `d*x` on the norm-one hypersurface `S` induced by the product-over-places
normalization `archHaar K` of `dy / y`: the Haar measure for which `dy / y` is the product
`d*x × dt / t` along `(x, t) ↦ x t^(1/n)` (`archHaar_eq_map`). Since `dt / t` gives `[1, e]` mass
one, the mass of `A ⊆ S` is the `dy / y`-mass of the parameters with surface part in `A` and norm
in `[1, e]` (`surfaceHaar_apply`). Neukirch's canonical surface measure is `2 ^ r₂` times this
measure, as his `dy / y` is `2 ^ r₂` times `archHaar K`. -/
def surfaceHaar : Measure (normOneSurface K) :=
  comap Subtype.val
    (map surfacePart ((archHaar K).restrict (archNorm ⁻¹' Icc 1 (Real.exp 1))))

/-- The mass of a measurable `A ⊆ S` is the `dy / y`-mass of the parameters with surface part in
`A` and norm in `[1, e]`. -/
theorem surfaceHaar_apply {A : Set (normOneSurface K)} (hA : MeasurableSet A) :
    surfaceHaar K A =
      archHaar K (surfacePart ⁻¹' (Subtype.val '' A) ∩ archNorm ⁻¹' Icc 1 (Real.exp 1)) := by
  have hA' : MeasurableSet (Subtype.val '' A) :=
    (measurableSet_normOneSurface K).subtype_image hA
  rw [surfaceHaar, (MeasurableEmbedding.subtype_coe (measurableSet_normOneSurface K)).comap_apply,
    map_apply measurable_surfacePart hA',
    Measure.restrict_apply (measurable_surfacePart hA')]

/-- The points of `S` with all coordinates in `[(k + 1)⁻¹, k + 1]`. They have finite `d*x`-mass
and exhaust `S`. -/
private def surfaceBox (k : ℕ) : Set (normOneSurface K) :=
  Subtype.val ⁻¹' univ.pi fun _ ↦ Icc ((k + 1 : ℝ)⁻¹) (k + 1)

private theorem measurableSet_surfaceBox (k : ℕ) : MeasurableSet (surfaceBox (K := K) k) :=
  measurable_subtype_coe (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)

private theorem surfaceHaar_surfaceBox_lt_top (k : ℕ) : surfaceHaar K (surfaceBox k) < ∞ := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hn : (0 : ℝ) ≤ 1 / (Module.finrank ℚ K : ℝ) := by positivity
  have he : Real.exp 1 ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ Real.exp 1 :=
    (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp zero_le_one)
      (div_le_one_of_le₀ (Nat.one_le_cast.mpr Module.finrank_pos) (Nat.cast_nonneg _))).trans
      (Real.rpow_one _).le
  -- a parameter with surface part in the box and norm in `[1, e]` lies in a larger box
  have hsub : surfacePart ⁻¹' (Subtype.val '' surfaceBox (K := K) k) ∩
      archNorm ⁻¹' Icc 1 (Real.exp 1) ≤ᵐ[archHaar K]
      univ.pi fun _ ↦ Icc ((k + 1 : ℝ)⁻¹) ((k + 1) * Real.exp 1) := by
    filter_upwards [ae_archHaar_pos] with y hy ⟨⟨x, hx, hxy⟩, h1, he1⟩ w _
    have hN : 0 ≤ archNorm y := (archNorm_pos hy).le
    obtain ⟨hb1, hb2⟩ := hx w trivial
    rw [hxy, surfacePart_apply y hN] at hb1 hb2
    have hr1 : 1 ≤ archNorm y ^ (1 / (Module.finrank ℚ K : ℝ)) := Real.one_le_rpow h1 hn
    have hre : archNorm y ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ Real.exp 1 :=
      (Real.rpow_le_rpow hN he1 hn).trans he
    have hr0 : 0 < archNorm y ^ (1 / (Module.finrank ℚ K : ℝ)) := one_pos.trans_le hr1
    rw [le_div_iff₀ hr0] at hb1
    rw [div_le_iff₀ hr0] at hb2
    exact ⟨hb1.trans' (le_mul_of_one_le_right (by positivity) hr1),
      hb2.trans (mul_le_mul_of_nonneg_left hre hk.le)⟩
  rw [surfaceHaar_apply (measurableSet_surfaceBox k)]
  refine (measure_mono_ae hsub).trans_lt ?_
  rw [archHaar, pi_pi]
  exact ENNReal.prod_lt_top fun _ _ ↦ by
    rw [multHaar_Icc (by positivity) ((inv_le_one_of_one_le₀ (by simp)).trans
      (one_le_mul_of_one_le_of_one_le (by simp) (Real.one_le_exp zero_le_one)))]
    exact ENNReal.ofReal_lt_top

private theorem iUnion_surfaceBox : ⋃ k, surfaceBox (K := K) k = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  have hx := (mem_normOneSurface.mp x.2).1
  obtain ⟨k, hk⟩ := exists_nat_ge (∑ w, ((x : realSpace K) w + ((x : realSpace K) w)⁻¹))
  have hle (w : InfinitePlace K) :
      (x : realSpace K) w + ((x : realSpace K) w)⁻¹ ≤ k + 1 :=
    ((Finset.single_le_sum (fun v _ ↦ (add_pos (hx v) (inv_pos.mpr (hx v))).le)
      (Finset.mem_univ w)).trans hk).trans (le_add_of_nonneg_right zero_le_one)
  refine mem_iUnion.mpr ⟨k, fun w _ ↦ ⟨?_, ?_⟩⟩
  · rw [inv_le_comm₀ (by positivity) (hx w)]
    exact (le_add_of_nonneg_left (hx w).le).trans (hle w)
  · exact (le_add_of_nonneg_right (inv_pos.mpr (hx w)).le).trans (hle w)

instance : SigmaFinite (surfaceHaar K) :=
  FiniteSpanningSetsIn.sigmaFinite
    { set := surfaceBox
      set_mem := fun _ ↦ mem_univ _
      finite := surfaceHaar_surfaceBox_lt_top
      spanning := iUnion_surfaceBox }

/-- A bounded subset of `S` has finite `d*x`-mass: its coordinates are bounded above, hence also
bounded below on `S`, so it lies in a box of finite mass. -/
theorem surfaceHaar_lt_top_of_isBounded {A : Set (normOneSurface K)}
    (hA : Bornology.IsBounded (Subtype.val '' A)) : surfaceHaar K A < ∞ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hA
  set C' := max C 1
  obtain ⟨k, hk⟩ := exists_nat_ge (C' ^ Module.finrank ℚ K)
  have hk' : C' ^ Module.finrank ℚ K ≤ k + 1 := hk.trans (le_add_of_nonneg_right zero_le_one)
  refine (measure_mono (fun x hx ↦ ?_ : A ⊆ surfaceBox k)).trans_lt
    (surfaceHaar_surfaceBox_lt_top k)
  intro w _
  obtain ⟨hlo, hhi⟩ := mem_Icc_of_mem_normOneSurface_of_norm_le x.2 (hC _ ⟨x, hx, rfl⟩) w
  refine ⟨?_, ?_⟩
  · rw [inv_le_comm₀ (by positivity) ((mem_normOneSurface.mp x.2).1 w)]
    exact (inv_le_of_inv_le₀ (by positivity) hlo).trans hk'
  · exact hhi.trans ((le_self_pow₀ (le_max_right _ _) Module.finrank_pos.ne').trans hk')

/-! ### The decomposition `dy / y = d*x × dt / t` -/

open scoped Classical in
/-- The surface part of a parameter as a point of `S`, extended by the point `1` off the positive
orthant, where `dy / y` vanishes. -/
private def toSurface (y : realSpace K) : normOneSurface K :=
  ⟨if ∀ w, 0 < y w then surfacePart y else 1, by
    split_ifs with hy
    · exact surfacePart_mem_normOneSurface hy
    · exact mem_normOneSurface.mpr ⟨fun _ ↦ one_pos, map_one _⟩⟩

private theorem toSurface_of_pos {y : realSpace K} (hy : ∀ w, 0 < y w) :
    (toSurface y : realSpace K) = surfacePart y := by
  simp [toSurface, hy]

private theorem toSurface_preimage_ae_eq (A : Set (normOneSurface K)) :
    toSurface ⁻¹' A =ᵐ[archHaar K] surfacePart ⁻¹' (Subtype.val '' A) := by
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [ae_archHaar_pos] with y hy
  refine ⟨fun h ↦ ⟨_, h, toSurface_of_pos hy⟩, ?_⟩
  rintro ⟨x, hx, hxy⟩
  have hEq : toSurface y = x := Subtype.ext ((toSurface_of_pos hy).trans hxy.symm)
  rwa [mem_preimage, hEq]

private theorem measurable_toSurface : Measurable (toSurface (K := K)) := by
  classical
  have hP : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w ↦ measurableSet_lt measurable_const (measurable_pi_apply w)
  exact (Measurable.ite hP measurable_surfacePart measurable_const).subtype_mk

/-- A positive dilation does not move the surface coordinate. -/
private theorem toSurface_smul {c : ℝ} (hc : 0 < c) (y : realSpace K) :
    toSurface (c • y) = toSurface y := by
  have hpos : (∀ w, 0 < (c • y) w) ↔ ∀ w, 0 < y w :=
    forall_congr' fun w ↦ (mul_pos_iff_of_pos_left hc)
  by_cases hy : ∀ w, 0 < y w
  · exact Subtype.ext <| by rw [toSurface_of_pos (hpos.mpr hy), toSurface_of_pos hy,
      surfacePart_smul hc (archNorm_pos hy).le]
  · have hcy : ¬∀ w, 0 < c * y w := hpos.not.mpr hy
    simp [toSurface, hy, hcy]

variable (K) in
/-- The image along the norm of `dy / y`, restricted to the parameters with surface part in `A`.
-/
private def normImage (A : Set (normOneSurface K)) : Measure ℝ :=
  ((archHaar K).restrict (toSurface ⁻¹' A)).map archNorm

private theorem normImage_apply (A : Set (normOneSurface K)) {B : Set ℝ} (hB : MeasurableSet B) :
    normImage K A B = archHaar K (toSurface ⁻¹' A ∩ archNorm ⁻¹' B) := by
  rw [normImage, map_apply continuous_archNorm.measurable hB,
    Measure.restrict_apply (continuous_archNorm.measurable hB), inter_comm]

private theorem normImage_Iic_zero (A : Set (normOneSurface K)) : normImage K A (Iic 0) = 0 := by
  rw [normImage_apply A measurableSet_Iic]
  refine measure_mono_null inter_subset_right (measure_eq_zero_iff_ae_notMem.mpr ?_)
  filter_upwards [ae_archHaar_pos] with y hy
  exact (archNorm_pos hy).not_ge

/-- The image along the norm is invariant under the dilations of `(0, ∞)`: the dilation of the
parameters by `c ^ (1 / n)` moves the norm by `c` and fixes the surface part. -/
private theorem map_normImage_mul_left {A : Set (normOneSurface K)} (hA : MeasurableSet A)
    {c : ℝ} (hc : 0 < c) : (normImage K A).map (c * ·) = normImage K A := by
  set d := c ^ (1 / (Module.finrank ℚ K : ℝ))
  have hd : 0 < d := Real.rpow_pos_of_pos hc _
  have hdn : d ^ Module.finrank ℚ K = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div_mul_cancel
      (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), Real.rpow_one]
  have hcomp : (c * ·) ∘ archNorm = archNorm ∘ (d • · : realSpace K → realSpace K) := by
    ext y
    simp [hdn]
  have hpre : (d • · : realSpace K → realSpace K) ⁻¹' (toSurface ⁻¹' A) = toSurface ⁻¹' A := by
    ext y
    simp [toSurface_smul hd]
  have hmap : ((archHaar K).restrict (toSurface ⁻¹' A)).map (d • ·) =
      (archHaar K).restrict (toSurface ⁻¹' A) := by
    conv_lhs => rw [← hpre]
    rw [← restrict_map (measurable_const_smul d) (measurable_toSurface hA), map_archHaar_smul hd]
  rw [normImage, map_map (measurable_const_mul c) continuous_archNorm.measurable, hcomp,
    ← map_map continuous_archNorm.measurable (measurable_const_smul d), hmap]

/-- The mass of the image along the norm on `[1, e]` is the `d*x`-mass of `A`. -/
private theorem normImage_Icc_one_exp_one {A : Set (normOneSurface K)} (hA : MeasurableSet A) :
    normImage K A (Icc 1 (Real.exp 1)) = surfaceHaar K A := by
  rw [normImage_apply A measurableSet_Icc, surfaceHaar_apply hA]
  exact measure_congr ((toSurface_preimage_ae_eq A).inter (Filter.EventuallyEq.refl _ _))

/-- For a measurable `A ⊆ S` of finite `d*x`-mass and a measurable set of norms `B`, the
`dy / y`-mass of the parameters with surface part in `A` and norm in `B` is
`d*x(A) · dt / t (B)`: the image along the norm is a dilation-invariant measure of `(0, ∞)`, hence
a multiple of `dt / t`. -/
private theorem archHaar_toSurface_preimage_inter_of_ne_top {A : Set (normOneSurface K)}
    (hA : MeasurableSet A) (hAfin : surfaceHaar K A ≠ ∞) {B : Set ℝ} (hB : MeasurableSet B) :
    archHaar K (toSurface ⁻¹' A ∩ archNorm ⁻¹' B) = surfaceHaar K A * multHaar B := by
  rw [← normImage_apply A hB, eq_smul_multHaar (normImage_Iic_zero A)
    (fun _ ↦ map_normImage_mul_left hA) ((normImage_Icc_one_exp_one hA).symm ▸ hAfin),
    normImage_Icc_one_exp_one hA, smul_apply, smul_eq_mul]

/-- For a measurable `A ⊆ S` and a measurable set of norms `B`, the `dy / y`-mass of the parameters
with surface part in `A` and norm in `B` is `d*x(A) · dt / t (B)`. The finite case applies on the
sets of finite `d*x`-mass that exhaust `S`. -/
private theorem archHaar_toSurface_preimage_inter {A : Set (normOneSurface K)}
    (hA : MeasurableSet A) {B : Set ℝ} (hB : MeasurableSet B) :
    archHaar K (toSurface ⁻¹' A ∩ archNorm ⁻¹' B) = surfaceHaar K A * multHaar B := by
  have hmeas : ((archHaar K).restrict (archNorm ⁻¹' B)).map toSurface =
      multHaar B • surfaceHaar K := by
    refine ext_of_iUnion_eq_univ (iUnion_spanningSets (surfaceHaar K)) fun i ↦ ext fun C hC ↦ ?_
    have hCi : MeasurableSet (C ∩ spanningSets (surfaceHaar K) i) :=
      hC.inter (measurableSet_spanningSets _ i)
    rw [Measure.restrict_apply hC, Measure.restrict_apply hC, map_apply measurable_toSurface hCi,
      Measure.restrict_apply (measurable_toSurface hCi), smul_apply, smul_eq_mul, mul_comm,
      archHaar_toSurface_preimage_inter_of_ne_top hCi ((measure_mono inter_subset_right).trans_lt
        (measure_spanningSets_lt_top _ i)).ne hB]
  rw [← Measure.restrict_apply (measurable_toSurface hA), ← map_apply measurable_toSurface hA,
    hmeas, smul_apply, smul_eq_mul, mul_comm]

/-- The mass of parameters with surface coordinate in `A` and norm in `B` is the product
of their surface and radial masses. In particular the defining shell `[1, e]` can be replaced
by any measurable radial set of `dt / t`-mass one. -/
theorem archHaar_surfacePart_preimage_inter {A : Set (normOneSurface K)}
    (hA : MeasurableSet A) {B : Set ℝ} (hB : MeasurableSet B) :
    archHaar K (surfacePart ⁻¹' (Subtype.val '' A) ∩ archNorm ⁻¹' B) =
      surfaceHaar K A * multHaar B := by
  rw [← archHaar_toSurface_preimage_inter hA hB]
  exact measure_congr ((toSurface_preimage_ae_eq A).symm.inter (Filter.EventuallyEq.refl _ _))

/-- **The decomposition `dy / y = d*x × dt / t`** (Neukirch VII §5): the multiplicative Haar measure
of the archimedean parameters is the image of the product of `surfaceHaar K` and `dt / t` under
`(x, t) ↦ x t^(1/n)`, `n = [K : ℚ]`. -/
theorem archHaar_eq_map :
    archHaar K = ((surfaceHaar K).prod multHaar).map
      fun p : normOneSurface K × ℝ ↦ surfaceScale (p.1 : realSpace K) p.2 := by
  have hΨ : Measurable fun y : realSpace K ↦ (toSurface y, archNorm y) :=
    measurable_toSurface.prodMk continuous_archNorm.measurable
  have hΦ : Measurable fun p : normOneSurface K × ℝ ↦ surfaceScale (p.1 : realSpace K) p.2 :=
    continuous_surfaceScale.measurable.comp (measurable_subtype_coe.prodMap measurable_id)
  have hprod : (surfaceHaar K).prod multHaar =
      (archHaar K).map fun y ↦ (toSurface y, archNorm y) :=
    prod_eq fun s t hs ht ↦ by
      rw [map_apply hΨ (hs.prod ht), mk_preimage_prod,
        archHaar_toSurface_preimage_inter hs ht]
  rw [hprod, map_map hΦ hΨ]
  conv_lhs => rw [← map_id (μ := archHaar K)]
  refine map_congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  simp [toSurface_of_pos hy, surfaceScale_surfacePart hy]

end TauCeti.LFunctions
