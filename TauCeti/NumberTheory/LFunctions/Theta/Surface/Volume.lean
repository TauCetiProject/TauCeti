/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Invariance

/-!
# The volume of a unit fundamental domain

Hecke's integral representation of a partial zeta function of a number field `K` integrates a
theta series over a fundamental domain `D` for the action of the units on the norm-one hypersurface
`S` of the archimedean parameters, and the constant term of the resulting Mellin kernel is the
volume of `D`. This file computes that volume, Neukirch's (5.6):

* `surfaceHaar_eq_of_isUnitFundamentalDomain`: any two unit fundamental domains have the same
  `surfaceHaar`-mass. A unit acts on `S` as a translation, which preserves `surfaceHaar`, and the
  two domains are cut into pieces indexed by the units modulo torsion that these translations
  match up.
* `surfaceHaar_unitFundamentalDomain`: Mathlib's domain `unitFundamentalDomain K` has mass
  `2 ^ (r - 1) R / 2 ^ r₂`, where `r` is the number of infinite places, `r₂` the number of complex
  places and `R` the regulator.
* `surfaceHaar_of_isUnitFundamentalDomain`: hence so does every unit fundamental domain.

The value is read off Mathlib's volume `2 ^ r₁ π ^ r₂ R` of `normLeOne K`
(`NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne`), which Mathlib writes in polar
coordinates as an integral over the absolute values `ρ` of its points with the weight
`∏_{w complex} ρ_w` (`NumberField.mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral`).
Against `dρ / ρ` that weight is the norm `N(ρ)`; the substitution `y = ρ²` (`map_archHaar_pow`)
turns `N(ρ) dρ / ρ` into `2 ^ (-r) N(y) ^ (1/2) dy / y`, and the decomposition
`dy / y = d*x × dt / t` (`archHaar_eq_map`) splits its integral over the cone of norm at most one
above `unitFundamentalDomain K` into the volume of the domain times `∫_0^1 t ^ (1/2) dt / t = 2`.

⚠ Neukirch's value is `vol(F) = 2 ^ (r - 1) R`: his surface measure carries the factor `e_𝔭 = 2` at
each complex place and is `2 ^ r₂` times `surfaceHaar K`. Over `ℚ` the mass is `1`, over `ℚ(i)` it
is `1/2`, and over a real quadratic field with fundamental unit `ε` it is `2 log ε`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open MeasureTheory Measure Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units
open scoped ENNReal

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Independence of the fundamental domain -/

/-- On the norm-one hypersurface, the action of a unit is the translation by a point of it. -/
private def surfaceUnitScale (u : (𝓞 K)ˣ) : normOneSurface K ≃ₜ normOneSurface K :=
  surfaceMul ⟨unitScale u 1, (unitScale_mem_normOneSurface u).mpr
    (mem_normOneSurface.mpr ⟨fun _ ↦ one_pos, map_one _⟩)⟩

private theorem coe_surfaceUnitScale (u : (𝓞 K)ˣ) (x : normOneSurface K) :
    (surfaceUnitScale u x : realSpace K) = unitScale u x := by
  rw [surfaceUnitScale, surfaceMul_apply, mul_comm, ← unitScale_mul, mul_one]

private theorem measurePreserving_surfaceUnitScale (u : (𝓞 K)ˣ) :
    MeasurePreserving (surfaceUnitScale u) (surfaceHaar K) (surfaceHaar K) :=
  measurePreserving_surfaceMul _

private theorem surfaceUnitScale_inv_apply (u : (𝓞 K)ˣ) (x : normOneSurface K) :
    surfaceUnitScale u⁻¹ (surfaceUnitScale u x) = x :=
  Subtype.ext <| by simp [coe_surfaceUnitScale, unitScale_unitScale]

/-- A unit fundamental domain `D` is the disjoint union, over the units modulo torsion, of its
parts that a chosen representative moves into a second fundamental domain `D'`. -/
private theorem surfaceHaar_eq_tsum {D D' : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (hD' : IsUnitFundamentalDomain K D') (s : (𝓞 K)ˣ ⧸ torsion K → (𝓞 K)ˣ)
    (hs : ∀ q, (s q : (𝓞 K)ˣ ⧸ torsion K) = q) :
    surfaceHaar K (Subtype.val ⁻¹' D) =
      ∑' q, surfaceHaar K
        (Subtype.val ⁻¹' D ∩ surfaceUnitScale (s q) ⁻¹' (Subtype.val ⁻¹' D')) := by
  have hmeas : MeasurableSet (Subtype.val ⁻¹' D' : Set (normOneSurface K)) :=
    measurable_subtype_coe hD'.measurableSet
  have hcover : Subtype.val ⁻¹' D =
      ⋃ q, Subtype.val ⁻¹' D ∩ surfaceUnitScale (s q) ⁻¹' (Subtype.val ⁻¹' D') := by
    refine subset_antisymm (fun y hy ↦ ?_) (iUnion_subset fun _ ↦ inter_subset_left)
    obtain ⟨v, hv⟩ := hD'.exists_unitScale_mem y y.2
    have hq : v⁻¹ * s v ∈ torsion K := QuotientGroup.eq.mp (hs _).symm
    refine mem_iUnion.mpr ⟨v, hy, ?_⟩
    rw [mem_preimage, mem_preimage, coe_surfaceUnitScale, ← mul_inv_cancel_left v (s v),
      ← unitScale_unitScale, unitScale_of_mem_torsion hq]
    exact hv
  have : Countable (𝓞 K) := Countable.of_moduleFinite (R := ℤ)
  have : Countable (𝓞 K)ˣ := Units.val_injective.countable
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := QuotientGroup.mk_surjective.countable
  conv_lhs => rw [hcover]
  rw [measure_iUnion]
  · intro q q' hqq'
    refine Set.disjoint_left.mpr fun y ⟨_, hy⟩ ⟨_, hy'⟩ ↦ hqq' ?_
    rw [mem_preimage, mem_preimage, coe_surfaceUnitScale] at hy hy'
    have h := (hD'.unitScale_mem_iff _ hy (s q' * (s q)⁻¹)).mp (by
      rwa [unitScale_unitScale, inv_mul_cancel_right])
    rw [← hs q, ← hs q', QuotientGroup.eq, mul_comm]
    exact h
  · exact fun q ↦ (measurable_subtype_coe hD.measurableSet).inter
      ((surfaceUnitScale (s q)).continuous.measurable hmeas)

/-- Moving the part of `D` that `u` carries into `D'` by `u` gives the part of `D'` that `u⁻¹`
carries into `D`, of the same mass. -/
private theorem surfaceHaar_inter_preimage_surfaceUnitScale {D D' : Set (realSpace K)}
    (hD : MeasurableSet D) (hD' : MeasurableSet D') (u : (𝓞 K)ˣ) :
    surfaceHaar K (Subtype.val ⁻¹' D ∩ surfaceUnitScale u ⁻¹' (Subtype.val ⁻¹' D')) =
      surfaceHaar K (Subtype.val ⁻¹' D' ∩ surfaceUnitScale u⁻¹ ⁻¹' (Subtype.val ⁻¹' D)) := by
  have hset : Subtype.val ⁻¹' D ∩ surfaceUnitScale u ⁻¹' (Subtype.val ⁻¹' D') =
      surfaceUnitScale u ⁻¹'
        (Subtype.val ⁻¹' D' ∩ surfaceUnitScale u⁻¹ ⁻¹' (Subtype.val ⁻¹' D)) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, surfaceUnitScale_inv_apply]
    exact and_comm
  rw [hset, (measurePreserving_surfaceUnitScale u).measure_preimage]
  exact ((measurable_subtype_coe hD').inter ((surfaceUnitScale u⁻¹).continuous.measurable
    (measurable_subtype_coe hD))).nullMeasurableSet

/-- **The volume of a unit fundamental domain does not depend on the domain**: any two unit
fundamental domains have the same `surfaceHaar`-mass. -/
theorem surfaceHaar_eq_of_isUnitFundamentalDomain {D D' : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (hD' : IsUnitFundamentalDomain K D') :
    surfaceHaar K (Subtype.val ⁻¹' D) = surfaceHaar K (Subtype.val ⁻¹' D') := by
  rw [surfaceHaar_eq_tsum hD hD' (fun q ↦ q.out) fun q ↦ QuotientGroup.out_eq' q,
    surfaceHaar_eq_tsum hD' hD (fun q ↦ (Quotient.out (q⁻¹ : (𝓞 K)ˣ ⧸ torsion K))⁻¹) fun q ↦ by
      rw [QuotientGroup.mk_inv, QuotientGroup.out_eq']
      exact inv_inv q,
    ← (Equiv.inv ((𝓞 K)ˣ ⧸ torsion K)).tsum_eq]
  exact tsum_congr fun q ↦
    surfaceHaar_inter_preimage_surfaceUnitScale hD.measurableSet hD'.measurableSet _

/-! ### The volume of Mathlib's fundamental domain -/

open scoped Classical in
/-- The norm of a parameter is the product of its coordinates times the product of its coordinates
at the complex places, which count twice. -/
private theorem archNorm_eq_prod_mul_prod (x : realSpace K) :
    archNorm x = (∏ w, x w) * ∏ w : {w // IsComplex w}, x w.1 := by
  rw [archNorm_apply, ← Fintype.prod_subtype_mul_prod_subtype IsComplex,
    ← Fintype.prod_subtype_mul_prod_subtype IsComplex (fun w ↦ x w)]
  have h : ∏ w : {w // ¬IsComplex w}, x w.1 ^ mult w.1 = ∏ w : {w // ¬IsComplex w}, x w.1 :=
    Finset.prod_congr rfl fun w _ ↦ by rw [(not_isComplex_iff_isReal.mp w.2).mult_eq_one, pow_one]
  simp only [mult_isComplex, h, sq]
  rw [Finset.prod_mul_distrib]
  ring

/-- The radial integral `∫_0^1 t^(1/2) dt / t = 2`. -/
private theorem setLIntegral_multHaar_sqrt :
    ∫⁻ t in Ioc 0 1, ENNReal.ofReal √t ∂multHaar = 2 := by
  have hpre : Real.exp ⁻¹' Ioc 0 1 = Iic 0 := by
    ext u
    simp [Real.exp_pos]
  rw [← map_volume_exp, setLIntegral_map measurableSet_Ioc
      (Real.continuous_sqrt.measurable.ennreal_ofReal) Real.measurable_exp, hpre]
  simp_rw [← Real.exp_half, div_eq_inv_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic (by norm_num) 0)
    (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le), integral_exp_mul_Iic (by norm_num)]
  norm_num

open scoped Classical in
/-- Mathlib's polar-coordinate computation of the volume of `normLeOne K`, read as an integral
over the absolute values of its points. -/
private theorem two_pow_mul_setLIntegral_normLeOne :
    2 ^ nrComplexPlaces K * ∫⁻ x in normAtAllPlaces '' fundamentalCone.normLeOne K,
      ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) = ENNReal.ofReal (regulator K) := by
  have h := volume_eq_two_pow_mul_two_pi_pow_mul_integral
    (fundamentalCone.normLeOne_eq_preimage_image K).symm (fundamentalCone.measurableSet_normLeOne K)
  rw [fundamentalCone.volume_normLeOne, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    mul_pow, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, mul_assoc, mul_assoc, mul_assoc,
    ENNReal.mul_right_inj (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    mul_left_comm, ENNReal.mul_right_inj (pow_ne_zero _ (ENNReal.ofReal_pos.mpr Real.pi_pos).ne')
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)] at h
  exact h.symm

variable (K) in
/-- The absolute values of the points of `normLeOne K`. -/
private def normLeOneAbs : Set (realSpace K) :=
  {x | (∀ w, 0 < x w) ∧ mixedSpaceOfRealSpace x ∈ fundamentalCone.normLeOne K}

private theorem mem_normLeOneAbs {x : realSpace K} :
    x ∈ normLeOneAbs K ↔ (∀ w, 0 < x w) ∧ mixedSpaceOfRealSpace x ∈ fundamentalCone.normLeOne K :=
  Iff.rfl

private theorem measurableSet_pos : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun w ↦ measurableSet_lt measurable_const (measurable_pi_apply w)

private theorem measurableSet_normLeOneAbs : MeasurableSet (normLeOneAbs K) :=
  measurableSet_pos.inter <| (fundamentalCone.measurableSet_normLeOne K).preimage
    mixedSpaceOfRealSpace.continuous.measurable

private theorem normAtAllPlaces_image_normLeOne :
    normAtAllPlaces '' fundamentalCone.normLeOne K = normLeOneAbs K := by
  ext x
  refine ⟨?_, fun h ↦ ⟨_, (mem_normLeOneAbs.mp h).2,
    normAtAllPlaces_mixedSpaceOfRealSpace fun w ↦ ((mem_normLeOneAbs.mp h).1 w).le⟩⟩
  rintro ⟨x, hx, rfl⟩
  refine mem_normLeOneAbs.mpr ⟨fun w ↦ fundamentalCone.normAtPlace_pos_of_mem hx.1 w, ?_⟩
  rw [fundamentalCone.normLeOne_eq_preimage_image]
  exact ⟨x, hx, (normAtAllPlaces_normAtAllPlaces x).symm⟩

open scoped Classical in
/-- On the positive orthant, Lebesgue measure is `∏_w y_w dy / y`, and the weight
`∏_{w complex} y_w` turns it into `N(y) dy / y`. -/
private theorem setLIntegral_normLeOneAbs :
    ∫⁻ x in normLeOneAbs K, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) =
      ∫⁻ x in normLeOneAbs K, ENNReal.ofReal (archNorm x) ∂archHaar K := by
  rw [archHaar_eq_withDensity, setLIntegral_withDensity_eq_setLIntegral_mul _
      (by fun_prop) continuous_archNorm.measurable.ennreal_ofReal measurableSet_normLeOneAbs,
    Measure.restrict_restrict measurableSet_normLeOneAbs,
    inter_eq_left.mpr fun _ hx ↦ (mem_normLeOneAbs.mp hx).1]
  refine setLIntegral_congr_fun measurableSet_normLeOneAbs fun x hx ↦ ?_
  replace hx := (mem_normLeOneAbs.mp hx).1
  have hprod : (∏ w, (x w)⁻¹) * archNorm x = ∏ w : {w // IsComplex w}, x w.1 := by
    rw [archNorm_eq_prod_mul_prod, ← mul_assoc, Finset.prod_inv_distrib,
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun w _ ↦ (hx w).ne'), one_mul]
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ ↦ (inv_pos.mpr (hx w)).le),
    hprod]
  exact (ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun w : {w // IsComplex w} ↦ x w.1)
    fun w _ ↦ (hx w.1).le).symm

variable (K) in
/-- The parameters whose coordinatewise square roots lie in `normLeOne K`: the cone of norm at
most one over the unit fundamental domain `unitFundamentalDomain K`. -/
private def normLeOneSq : Set (realSpace K) :=
  {y | (∀ w, 0 < y w) ∧ mixedSpaceOfRealSpace (fun w ↦ √(y w)) ∈ fundamentalCone.normLeOne K}

private theorem mem_normLeOneSq {y : realSpace K} :
    y ∈ normLeOneSq K ↔
      (∀ w, 0 < y w) ∧ mixedSpaceOfRealSpace (fun w ↦ √(y w)) ∈ fundamentalCone.normLeOne K :=
  Iff.rfl

private theorem measurableSet_normLeOneSq : MeasurableSet (normLeOneSq K) :=
  measurableSet_pos.inter <| (fundamentalCone.measurableSet_normLeOne K).preimage <|
    mixedSpaceOfRealSpace.continuous.measurable.comp <|
      Measurable.of_eval fun w ↦ (measurable_pi_apply w).sqrt

/-- The substitution `y = x²` turns `N(x) dx / x` into `2 ^ (-r) N(y)^(1/2) dy / y`. -/
private theorem setLIntegral_normLeOneAbs_eq :
    ∫⁻ x in normLeOneAbs K, ENNReal.ofReal (archNorm x) ∂archHaar K =
      ((2 : ℝ≥0∞) ^ Fintype.card (InfinitePlace K))⁻¹ *
        ∫⁻ y in normLeOneSq K, ENNReal.ofReal √(archNorm y) ∂archHaar K := by
  have hg : Measurable fun y : realSpace K ↦ ENNReal.ofReal √(archNorm y) :=
    (Real.continuous_sqrt.comp continuous_archNorm).measurable.ennreal_ofReal
  rw [← lintegral_indicator measurableSet_normLeOneAbs,
    ← lintegral_indicator measurableSet_normLeOneSq,
    ← smul_eq_mul, ← lintegral_smul_measure, ← Nat.cast_ofNat (R := ℝ≥0∞) (n := 2),
    ← map_archHaar_pow two_ne_zero,
    lintegral_map (hg.indicator measurableSet_normLeOneSq) (continuous_pow 2).measurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_archHaar_pos] with x hx
  have hsqrt : (fun w ↦ √(x w ^ 2)) = x := funext fun w ↦ Real.sqrt_sq (hx w).le
  have hmem : x ^ 2 ∈ normLeOneSq K ↔ x ∈ normLeOneAbs K := by
    simp only [mem_normLeOneSq, mem_normLeOneAbs, Pi.pow_apply, hsqrt]
    exact and_congr_left fun _ ↦ ⟨fun _ ↦ hx, fun _ w ↦ pow_pos (hx w) 2⟩
  by_cases h : x ∈ normLeOneAbs K
  · rw [indicator_of_mem h, indicator_of_mem (hmem.mpr h), map_pow,
      Real.sqrt_sq (archNorm_pos hx).le]
  · rw [indicator_of_notMem h, indicator_of_notMem (hmem.not.mpr h)]

/-- A positive multiple of a parameter lies in `normLeOneSq K` exactly when its surface part lies
in `unitFundamentalDomain K` and its norm is at most one. -/
private theorem surfaceScale_mem_normLeOneSq_iff {x : realSpace K} (hx : x ∈ normOneSurface K)
    {t : ℝ} (ht : 0 < t) :
    surfaceScale x t ∈ normLeOneSq K ↔ x ∈ unitFundamentalDomain K ∧ t ≤ 1 := by
  have hx' := (mem_normOneSurface.mp hx).1
  have hpos := surfaceScale_pos hx' ht
  set c := t ^ (1 / (Module.finrank ℚ K : ℝ))
  have hc : 0 < c := Real.rpow_pos_of_pos ht _
  have hsmul : mixedSpaceOfRealSpace (fun w ↦ √(surfaceScale x t w)) =
      √c • mixedSpaceOfRealSpace (fun w ↦ √(x w)) := by
    rw [← map_smul]
    congr 1
    ext w
    rw [surfaceScale_apply, Real.sqrt_mul (hx' w).le, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hnorm : mixedEmbedding.norm (mixedSpaceOfRealSpace fun w ↦ √(surfaceScale x t w)) = √t := by
    rw [norm_mixedSpaceOfRealSpace_sqrt fun w ↦ (hpos w).le,
      archNorm_surfaceScale_of_mem_normOneSurface hx ht.le]
  rw [mem_normLeOneSq, fundamentalCone.mem_normLeOne, hnorm, hsmul,
    fundamentalCone.smul_mem_iff_mem (Real.sqrt_pos.mpr hc).ne', mem_unitFundamentalDomain,
    Real.sqrt_le_left zero_le_one, one_pow]
  exact ⟨fun h ↦ ⟨⟨hx, h.2.1⟩, h.2.2⟩, fun h ↦ ⟨hpos, h.1.2, h.2⟩⟩

/-- Integrating `N(y)^(1/2) dy / y` over the cone `normLeOneSq K` splits into the volume of
`unitFundamentalDomain K` times `∫_0^1 t^(1/2) dt / t = 2`. -/
private theorem setLIntegral_normLeOneSq :
    ∫⁻ y in normLeOneSq K, ENNReal.ofReal √(archNorm y) ∂archHaar K =
      surfaceHaar K (Subtype.val ⁻¹' unitFundamentalDomain K) * 2 := by
  have hg : Measurable fun y : realSpace K ↦ ENNReal.ofReal √(archNorm y) :=
    (Real.continuous_sqrt.comp continuous_archNorm).measurable.ennreal_ofReal
  have hΦ : Measurable fun p : normOneSurface K × ℝ ↦ surfaceScale (p.1 : realSpace K) p.2 :=
    continuous_surfaceScale.measurable.comp (measurable_subtype_coe.prodMap measurable_id)
  have hF : MeasurableSet (Subtype.val ⁻¹' unitFundamentalDomain K : Set (normOneSurface K)) :=
    measurable_subtype_coe isUnitFundamentalDomain_unitFundamentalDomain.measurableSet
  have hae : ∀ᵐ t ∂multHaar, 0 < t := ae_iff.mpr (by simp only [not_lt]; exact multHaar_Iic_zero)
  rw [← lintegral_indicator measurableSet_normLeOneSq, archHaar_eq_map,
    lintegral_map (hg.indicator measurableSet_normLeOneSq) hΦ,
    ← setLIntegral_multHaar_sqrt, ← lintegral_indicator_one hF,
    ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_prod_mul (measurable_one.indicator hF).aemeasurable
      ((Real.continuous_sqrt.measurable.ennreal_ofReal).indicator measurableSet_Ioc).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [quasiMeasurePreserving_snd.ae hae] with p hp
  obtain ⟨x, t⟩ := p
  dsimp only at hp ⊢
  have hmem := surfaceScale_mem_normLeOneSq_iff x.2 hp
  by_cases h : (x : realSpace K) ∈ unitFundamentalDomain K ∧ t ≤ 1
  · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem (show x ∈ Subtype.val ⁻¹' _ from h.1),
      indicator_of_mem (show t ∈ Ioc 0 1 from ⟨hp, h.2⟩), Pi.one_apply, one_mul,
      archNorm_surfaceScale_of_mem_normOneSurface x.2 hp.le]
  · rw [indicator_of_notMem (hmem.not.mpr h)]
    rcases not_and_or.mp h with h | h
    · rw [indicator_of_notMem (show x ∉ Subtype.val ⁻¹' _ from h), zero_mul]
    · rw [indicator_of_notMem (show t ∉ Ioc 0 1 from fun ht ↦ h ht.2), mul_zero]

/-- **The volume of Mathlib's unit fundamental domain**: `unitFundamentalDomain K` has
`surfaceHaar`-mass `2 ^ (r - 1) R / 2 ^ r₂`, with `r` the number of infinite places, `r₂` the
number of complex places and `R` the regulator. -/
theorem surfaceHaar_unitFundamentalDomain :
    surfaceHaar K (Subtype.val ⁻¹' unitFundamentalDomain K) =
      ENNReal.ofReal (2 ^ rank K * regulator K / 2 ^ nrComplexPlaces K) := by
  classical
  have h := two_pow_mul_setLIntegral_normLeOne (K := K)
  rw [normAtAllPlaces_image_normLeOne, setLIntegral_normLeOneAbs, setLIntegral_normLeOneAbs_eq,
    setLIntegral_normLeOneSq] at h
  have hcard : Fintype.card (InfinitePlace K) = rank K + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have h0 : ∀ n : ℕ, (2 : ℝ≥0∞) ^ n ≠ 0 := fun n ↦ pow_ne_zero n two_ne_zero
  have ht : ∀ n : ℕ, (2 : ℝ≥0∞) ^ n ≠ ⊤ := fun n ↦ ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ← h,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, hcard,
    pow_succ, ENNReal.mul_inv (Or.inl (h0 _)) (Or.inl (ht _)), div_eq_mul_inv]
  calc surfaceHaar K (Subtype.val ⁻¹' unitFundamentalDomain K)
      = (2 ^ rank K * (2 ^ rank K)⁻¹) * (2 ^ nrComplexPlaces K * (2 ^ nrComplexPlaces K)⁻¹) *
          (2 * 2⁻¹) * surfaceHaar K (Subtype.val ⁻¹' unitFundamentalDomain K) := by
        rw [ENNReal.mul_inv_cancel (h0 _) (ht _), ENNReal.mul_inv_cancel (h0 _) (ht _),
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul, one_mul, one_mul]
    _ = _ := by ring

/-- **The volume of a unit fundamental domain** (Neukirch VII (5.6)): every unit fundamental
domain `D` has `surfaceHaar`-mass `2 ^ (r - 1) R / 2 ^ r₂`, with `r` the number of infinite places,
`r₂` the number of complex places and `R` the regulator. Neukirch's `vol(F) = 2 ^ (r - 1) R` is
`2 ^ r₂` times this, as his surface measure is `2 ^ r₂` times `surfaceHaar K`. -/
theorem surfaceHaar_of_isUnitFundamentalDomain {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    surfaceHaar K (Subtype.val ⁻¹' D) =
      ENNReal.ofReal (2 ^ rank K * regulator K / 2 ^ nrComplexPlaces K) := by
  rw [surfaceHaar_eq_of_isUnitFundamentalDomain hD isUnitFundamentalDomain_unitFundamentalDomain,
    surfaceHaar_unitFundamentalDomain]

end TauCeti.LFunctions
