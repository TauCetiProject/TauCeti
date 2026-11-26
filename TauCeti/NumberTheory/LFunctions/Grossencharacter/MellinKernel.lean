/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Theta
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding

/-!
# The Mellin kernel of a Grossencharacter

The twisted theta series of an ideal is averaged over the norm-one surface with the
archimedean weight. The radial coordinate is scaled by the square of the covolume times the
norm of the finite conductor. The resulting kernel is continuous at positive radii and,
after subtraction of its constant term, decays exponentially in the `[K : ℚ]`-th root of
the radius. These are the large-radius conditions for Mellin's principle.

The centered kernel has a convergent Mellin transform on the Dirichlet half-plane, where
it represents the weighted theta integral over the cone above the fundamental domain.

The normalization uses the Euclidean mixed embedding. The factor
`2 ^ (-∑_{w complex} P_w / 2)` compensates for the complex-place powers in the gamma integral.
The power of the radial scale compensates for the shift in the Mellin exponent.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (8.2)–(8.4).
-/

public section

noncomputable section

open Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Set
  TauCeti.NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors Topology

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

open scoped Classical in
/-- The radial scale of the twisted theta series is the squared lattice covolume times
the norm of the finite conductor. -/
def heckeScale (χ : Grossencharacter K 𝔪) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  ZLattice.covolume (idealLattice K J) ^ 2 * (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ)

open scoped Classical in
/-- The defining formula for the radial scale. -/
theorem heckeScale_def (χ : Grossencharacter K 𝔪) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    χ.heckeScale J = ZLattice.covolume (idealLattice K J) ^ 2 *
      (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ) := (rfl)

/-- The radial scale is positive for every fractional ideal. -/
theorem heckeScale_pos (χ : Grossencharacter K 𝔪) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < χ.heckeScale J := by
  classical
  have hV := ZLattice.covolume_pos (idealLattice K J)
  have hN : 0 < Ideal.absNorm χ.toHeckeCharacter.finiteConductor :=
    Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr χ.toHeckeCharacter.finiteConductor_ne_bot)
  rw [heckeScale_def]
  positivity

open scoped Classical in
private def mellinFactor (χ : Grossencharacter K 𝔪) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
      (χ.harmonicExponent w : ℝ)) / 2) : ℝ) *
    ((χ.heckeScale J) ^ (-(χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) : ℝ)

/-- Hecke's Mellin kernel for a fractional ideal, obtained by averaging its twisted theta series
over the surface parameter and retaining the radial parameter. -/
def heckeMellinKernel (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) : ℂ :=
  mellinFactor χ J * ∫ x in Subtype.val ⁻¹' D,
    (χ.archWeight (x : realSpace K) : ℂ) *
      χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J)) ∂surfaceHaar K

open scoped Classical in
/-- The weighted surface-average formula for Hecke's Mellin kernel. -/
theorem heckeMellinKernel_def (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) :
    χ.heckeMellinKernel D J u =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w : ℝ)) / 2) : ℝ) *
        ((χ.heckeScale J) ^ (-(χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) : ℝ) *
        ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
          χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J))
            ∂surfaceHaar K := (rfl)

/-- The Mellin kernel is determined by the Hecke character. -/
theorem heckeMellinKernel_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) : χ.heckeMellinKernel = ψ.heckeMellinKernel := by
  ext D J u
  simp only [heckeMellinKernel_def, heckeScale_def, h, harmonicExponent_congr h,
    harmonicDegree_congr h, archWeight_congr h, heckeTheta_congr h]

open scoped Classical in
/-- When the theta constant is one, the Mellin kernel specializes to the Dedekind kernel. -/
theorem heckeMellinKernel_eq_mellinKernel (χ : Grossencharacter K 𝔪)
    (hχ : χ.heckeEpsilon = 1) (D : Set (realSpace K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℝ} (hu : 0 < u) :
    χ.heckeMellinKernel D J u = mellinKernel D (idealLattice K J) u := by
  obtain ⟨hf, hdeg⟩ := χ.heckeEpsilon_eq_one_iff.mp hχ
  have hP := χ.harmonicExponent_eq_zero_of_harmonicDegree_eq_zero hdeg
  simp only [heckeMellinKernel_def, mellinKernel_def, heckeScale_def, hf, hdeg, Ideal.absNorm_top,
    Nat.cast_one, mul_one, hP, Nat.cast_zero, Finset.sum_const_zero, neg_zero, zero_div,
    Real.rpow_zero, Complex.ofReal_one]
  apply congrArg ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) * ·)
  have hV := ZLattice.covolume_pos (idealLattice K J)
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [χ.heckeTheta_eq_latticeTheta hχ J
    (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (by positivity))]
  have hweight : (χ.archWeight (x : realSpace K) : ℂ) = 1 := by
    simpa only [hχ, mul_one] using χ.archWeight_mul_heckeEpsilon (x : realSpace K)
  rw [hweight, one_mul]

-- The radial power can be moved from the centered theta integrand into the Mellin exponent.
private theorem archWeight_mul_heckeTheta_sub_surfaceScale (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : normOneSurface K) {t : ℝ} (ht : 0 ≤ t) :
    (χ.archWeight (surfaceScale (x : realSpace K) t) : ℂ) *
        (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon) =
      ((t ^ ((χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) : ℝ) : ℂ) *
        ((χ.archWeight (x : realSpace K) : ℂ) *
          (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon)) := by
  have hx w := ((mem_normOneSurface.mp x.property).1 w).le
  have hweight : χ.archWeight (surfaceScale (x : realSpace K) t) =
      χ.archWeight (x : realSpace K) *
        t ^ ((χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) := by
    simp only [archWeight_def, surfaceScale_apply, Real.mul_rpow (hx _) (Real.rpow_nonneg ht _),
      Finset.prod_mul_distrib, ← Real.rpow_mul ht]
    congr 1
    have hexponent (w : InfinitePlace K) :
        (1 / (Module.finrank ℚ K : ℝ)) * ((χ.harmonicExponent w : ℝ) / 2) =
          (χ.harmonicExponent w : ℝ) / (2 * (Module.finrank ℚ K : ℝ)) := by ring
    rw [← Real.rpow_sum_of_nonneg ht (fun _ _ ↦ by positivity), harmonicDegree_def, Nat.cast_sum,
      Finset.sum_congr rfl (fun w _ ↦ hexponent w), Finset.sum_div]
  rw [hweight, Complex.ofReal_mul, mul_left_comm]
  ring

private def surfaceIntegrand (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (x : normOneSurface K) : ℂ :=
  (χ.archWeight (x : realSpace K) : ℂ) * χ.heckeTheta J (surfaceScale (x : realSpace K) t)

private theorem continuous_surfaceIntegrand (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    Continuous (surfaceIntegrand χ J t) := by
  have hweight : Continuous fun x : normOneSurface K ↦ χ.archWeight (x : realSpace K) := by
    simp only [archWeight_def]
    exact continuous_finsetProd _ fun w _ ↦
      ((continuous_apply w).comp continuous_subtypeVal).rpow_const fun _ ↦ Or.inr (by positivity)
  have hradial : Continuous fun x : normOneSurface K ↦ surfaceScale (x : realSpace K) t :=
    continuous_surfaceScale.comp (continuous_subtypeVal.prodMk continuous_const)
  refine (Complex.continuous_ofReal.comp hweight).mul
    (continuous_iff_continuousAt.mpr fun x ↦ ?_)
  exact ContinuousAt.comp (g := χ.heckeTheta J)
    (χ.continuousAt_heckeTheta J (surfaceScale_pos (mem_normOneSurface.mp x.property).1 ht))
    hradial.continuousAt

private theorem exists_norm_surfaceIntegrand_le (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ t ≥ t₀, ∀ x : normOneSurface K, (x : realSpace K) ∈ D →
      ‖surfaceIntegrand χ J t x‖ ≤ B := by
  obtain ⟨C, hC, hbox⟩ := exists_forall_mem_Icc_of_isBounded hD
  let δ := C⁻¹ * t₀ ^ (1 / (Module.finrank ℚ K : ℝ))
  have hδ : 0 < δ := by positivity
  let g : ↥(J : Submodule (𝓞 K) K) → realSpace K → ℂ := fun a y ↦
    χ.primitive.finiteCharacterField a * χ.harmonicFactor (mixedEmbedding K a) *
      archGaussian y (mixedEmbedding K a)
  have hsum : Summable fun a ↦ ‖g a (fun _ ↦ δ)‖ :=
    (χ.summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian J (fun _ ↦ hδ)).norm
  refine ⟨(∏ w : InfinitePlace K, C ^ ((χ.harmonicExponent w : ℝ) / 2)) *
    (‖χ.heckeEpsilon‖ + ∑' a, ‖g a (fun _ ↦ δ)‖), fun t ht x hx ↦ ?_⟩
  have hxpos := (mem_normOneSurface.mp x.property).1
  have hlower (w : InfinitePlace K) : δ ≤ surfaceScale (x : realSpace K) t w := by
    rw [surfaceScale_apply]
    exact mul_le_mul (hbox x hx x.property w).1 (Real.rpow_le_rpow ht₀.le ht (by positivity))
      (by positivity) (hxpos w).le
  have hterm (a : ↥(J : Submodule (𝓞 K) K)) :
      ‖g a (surfaceScale (x : realSpace K) t)‖ ≤ ‖g a (fun _ ↦ δ)‖ := by
    simp only [g, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_archGaussian_le hlower (mixedEmbedding K a))
      (by positivity)
  have htheta : ‖χ.heckeTheta J (surfaceScale (x : realSpace K) t)‖ ≤
      ‖χ.heckeEpsilon‖ + ∑' a, ‖g a (fun _ ↦ δ)‖ := by
    rw [heckeTheta_def]
    exact (norm_add_le _ _).trans
      (add_le_add_right (tsum_of_norm_bounded hsum.hasSum hterm) _)
  rw [surfaceIntegrand, norm_mul,
    Complex.norm_of_nonneg (χ.archWeight_nonneg fun w ↦ (hxpos w).le)]
  exact mul_le_mul (χ.archWeight_le_of_le_const (fun w ↦ (hxpos w).le)
    (fun w ↦ (hbox x hx x.property w).2))
    htheta (norm_nonneg _) (by positivity)

private theorem integrableOn_surfaceIntegrand (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (surfaceIntegrand χ J t) (Subtype.val ⁻¹' D) (surfaceHaar K) := by
  obtain ⟨B, hB⟩ := exists_norm_surfaceIntegrand_le χ J hD ht
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  refine (integrable_const B).mono' (continuous_surfaceIntegrand χ J ht).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurable_subtypeVal hDm)] with x hx
  exact hB t le_rfl x hx

/-- The Mellin kernel of a fractional ideal is continuous at positive radii for any bounded
measurable set of surface parameters. -/
theorem continuousOn_heckeMellinKernel (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) : ContinuousOn (χ.heckeMellinKernel D J) (Ioi 0) := by
  intro u hu
  have hscale := χ.heckeScale_pos J
  have hu₀ : 0 < u := hu
  obtain ⟨B, hB⟩ := exists_norm_surfaceIntegrand_le χ J hD
    (div_pos (half_pos hu₀) hscale)
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  refine ContinuousAt.continuousWithinAt (continuousAt_const.mul
    (continuousAt_of_dominated (bound := fun _ ↦ B) ?_ ?_ (integrable_const B) ?_))
  · filter_upwards [Ioi_mem_nhds hu₀] with v (hv : 0 < v)
    exact (continuous_surfaceIntegrand χ J (div_pos hv hscale)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (half_lt_self hu₀)] with v (hv : u / 2 < v)
    filter_upwards [ae_restrict_mem (measurable_subtypeVal hDm)] with x hx
    exact hB _ (div_le_div_of_nonneg_right hv.le hscale.le) x hx
  · refine Eventually.of_forall fun x ↦ continuousAt_const.mul ?_
    have hradial : Continuous fun v : ℝ ↦ surfaceScale (x : realSpace K) (v / χ.heckeScale J) :=
      continuous_surfaceScale.comp (continuous_const.prodMk (continuous_id.div_const _))
    exact ContinuousAt.comp (g := χ.heckeTheta J) (χ.continuousAt_heckeTheta J
      (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (div_pos hu₀ hscale)))
      hradial.continuousAt

private theorem heckeMellinKernel_sub_eq_integral (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {u : ℝ} (hu : 0 < u) :
    χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K =
      mellinFactor χ J * ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
        (χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J)) - χ.heckeEpsilon)
        ∂surfaceHaar K := by
  rw [heckeMellinKernel]
  have hconst :
      mellinFactor χ J * ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) * χ.heckeEpsilon =
        χ.heckeEpsilon * mellinConstant K := by
    rcases χ.heckeEpsilon_eq_zero_or_eq_one with h | h
    · simp [h]
    have hdeg := (χ.heckeEpsilon_eq_one_iff.mp h).2
    simp only [mellinFactor, hdeg, χ.harmonicExponent_eq_zero_of_harmonicDegree_eq_zero hdeg,
      Nat.cast_zero, Finset.sum_const_zero, neg_zero, zero_div, Real.rpow_zero, Complex.ofReal_one,
      mul_one, h, one_mul]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Complex.ofReal_natCast] using
      congrArg Complex.ofReal (mellinConstant_eq_mul_surfaceHaar_real hD).symm
  have hfin := surfaceHaar_preimage_lt_top hD.isBounded
  have hInt := integrableOn_surfaceIntegrand χ J hD.measurableSet hD.isBounded
    (div_pos hu (χ.heckeScale_pos J))
  unfold surfaceIntegrand at hInt
  simp_rw [mul_sub, archWeight_mul_heckeEpsilon]
  rw [integral_sub hInt (integrableOn_const hfin.ne), setIntegral_const,
    Complex.real_smul, mul_sub, ← mul_assoc, hconst]

private theorem norm_surfaceWeight_mul_sub_le (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : normOneSurface K) {t : ℝ} (ht : 1 ≤ t) :
    ‖(χ.archWeight (x : realSpace K) : ℂ) *
      (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon)‖ ≤
    ‖(χ.archWeight (surfaceScale (x : realSpace K) t) : ℂ) *
      (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon)‖ := by
  have hpow : 1 ≤ t ^ ((χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) :=
    Real.one_le_rpow ht (by positivity)
  rw [archWeight_mul_heckeTheta_sub_surfaceScale χ J x (zero_le_one.trans ht)]
  simp only [norm_mul, Complex.norm_of_nonneg (zero_le_one.trans hpow)]
  exact le_mul_of_one_le_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpow

/-- After subtraction of its constant term, the Mellin kernel over a unit fundamental domain
has stretched-exponential decay as the radius tends to infinity. -/
theorem exists_isBigO_heckeMellinKernel_sub_exp (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) :
    ∃ c > 0, (fun u ↦ χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K) =O[atTop]
      (fun u ↦ Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹)) := by
  obtain ⟨A, hA, htwist⟩ := χ.exists_norm_archWeight_mul_heckeTheta_sub_le
  obtain ⟨c, hc, B, _, hθ⟩ := exists_norm_latticeTheta_surfaceScale_sub_one_le (idealLattice K J)
    (hD.isBounded.subset inter_subset_left) inter_subset_right
  let n : ℝ := (Module.finrank ℚ K : ℝ)⁻¹
  let v : ℝ := χ.heckeScale J * 2 ^ Module.finrank ℚ K
  have hscale := χ.heckeScale_pos J
  have hv : 0 < v := by positivity
  have hvTop : Tendsto (fun u : ℝ ↦ u / v) atTop atTop := tendsto_id.atTop_div_const hv
  have hfin := surfaceHaar_preimage_lt_top hD.isBounded
  refine ⟨c / v ^ n, by positivity, Asymptotics.IsBigO.of_bound
    (‖mellinFactor χ J‖ * (A * B * (surfaceHaar K).real (Subtype.val ⁻¹' D))) ?_⟩
  filter_upwards [hvTop.eventually hθ, eventually_ge_atTop (χ.heckeScale J)] with u htu hu
  have hu₀ : 0 < u := hscale.trans_le hu
  have ht : 1 ≤ u / χ.heckeScale J := (le_div_iff₀ hscale).mpr (by simpa using hu)
  rw [heckeMellinKernel_sub_eq_integral χ J hD hu₀, norm_mul, Real.norm_eq_abs, Real.abs_exp]
  have hnorm (x : normOneSurface K) (hx : x ∈ Subtype.val ⁻¹' D) :
      ‖(χ.archWeight (x : realSpace K) : ℂ) *
        (χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J)) - χ.heckeEpsilon)‖ ≤
          A * (B * Real.exp (-(c / v ^ n) * u ^ n)) := by
    refine (norm_surfaceWeight_mul_sub_le χ J x ht).trans
      ((htwist J _ (surfaceScale_pos (mem_normOneSurface.mp x.property).1
        (div_pos hu₀ hscale))).trans ?_)
    have hdilate : (1 / 2 : ℝ) • surfaceScale (x : realSpace K) (u / χ.heckeScale J) =
        surfaceScale (x : realSpace K) (u / v) := by
      ext w
      simp only [Pi.smul_apply, smul_eq_mul, surfaceScale_apply, one_div, v, ← div_div]
      rw [Real.div_rpow (div_nonneg hu₀.le hscale.le) (by positivity),
        Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) Module.finrank_pos.ne']
      ring
    rw [hdilate]
    apply mul_le_mul_of_nonneg_left _ hA
    have hexp : -c * (u / v) ^ n = -(c / v ^ n) * u ^ n := by
      rw [Real.div_rpow hu₀.le hv.le]
      ring
    dsimp only [n] at hexp
    simpa only [hexp] using htu (x : realSpace K) ⟨hx, x.property⟩
  refine (mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hfin hnorm)
    (norm_nonneg _)).trans_eq ?_
  ring

/-- The centered Mellin kernel decays faster than every real power. -/
theorem isBigO_heckeMellinKernel_sub_rpow (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (r : ℝ) :
    (fun u ↦ χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K) =O[atTop]
      (fun u ↦ u ^ r) := by
  obtain ⟨c, hc, h⟩ := χ.exists_isBigO_heckeMellinKernel_sub_exp J hD
  exact isBigO_rpow_of_isBigO_exp_neg hc (inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)) h r

/-- For `Re s > 1`, the centered twisted theta series times the archimedean and Mellin weights
is absolutely integrable over the cone above a unit fundamental domain. -/
theorem integrableOn_unitCone_archNorm_cpow_mul_archWeight_mul_heckeTheta_sub
    (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
        ((χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon)))
      (unitCone D) (archHaar K) := by
  obtain ⟨C, _, hbound⟩ := χ.exists_norm_archWeight_mul_heckeTheta_sub_le
  have hcone := measurableSet_unitCone hD.measurableSet
  have hint := integrableOn_unitCone_archNorm_cpow_mul_latticeTheta_smul_sub_one
    J hD hs (c := 1 / 2) (by norm_num)
  have hcont : ContinuousOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
      ((χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon))) (unitCone D) := by
    intro y hy
    have hypos := (mem_unitCone.mp hy).1
    have hW : ContinuousAt (fun z ↦ (χ.archWeight z : ℂ)) y := by
      simp only [archWeight_def]
      exact Complex.continuous_ofReal.continuousAt.comp
        (continuous_finsetProd _ fun w _ ↦ (continuous_apply w).rpow_const
          fun _ ↦ Or.inr (by positivity)).continuousAt
    exact ContinuousAt.continuousWithinAt <|
      ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (archNorm_pos hypos).ne')).comp
        continuous_archNorm.continuousAt).mul
        (hW.mul ((χ.continuousAt_heckeTheta J hypos).sub continuousAt_const))
  refine (hint.norm.const_mul C).mono' (hcont.aestronglyMeasurable hcone) ?_
  filter_upwards [ae_restrict_mem hcone] with y hy
  specialize hbound J y (mem_unitCone.mp hy).1
  simp only [norm_mul] at hbound ⊢
  rw [mul_left_comm C]
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

private def centeredSurfaceAverage (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
    (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon) ∂surfaceHaar K

private theorem hasMellin_centeredSurfaceAverage (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (centeredSurfaceAverage χ D J)
      (s / 2 + ((χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ)) : ℝ))
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
        ((χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon)) ∂archHaar K) := by
  let q : ℝ := (χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))
  let f : realSpace K → ℂ := fun y ↦
    (χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon)
  let M := ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * f y ∂archHaar K
  have havg : HasMellin (fun t ↦ ∫ x in Subtype.val ⁻¹' D,
      f (surfaceScale (x : realSpace K) t) ∂surfaceHaar K) (s / 2) M :=
    hasMellin_integral_surfaceScale hD.measurableSet (s / 2)
      (χ.integrableOn_unitCone_archNorm_cpow_mul_archWeight_mul_heckeTheta_sub J hD hs)
  have heq : EqOn (fun t ↦ ∫ x in Subtype.val ⁻¹' D,
      f (surfaceScale (x : realSpace K) t) ∂surfaceHaar K)
      (fun t ↦ (t : ℂ) ^ (q : ℂ) • centeredSurfaceAverage χ D J t) (Ioi 0) := by
    intro t ht
    dsimp only [centeredSurfaceAverage]
    rw [← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only [f]
    rw [smul_eq_mul, archWeight_mul_heckeTheta_sub_surfaceScale χ J x (le_of_lt ht),
      Complex.ofReal_cpow (le_of_lt ht)]
  have hm := (hasMellin_congr heq).mp havg
  exact ⟨MellinConvergent.cpow_smul.mp hm.1, (mellin_cpow_smul _ _ _).symm.trans hm.2⟩

open scoped Classical in
/-- The Mellin transform of the centered kernel converges for `Re s > 1` at the shifted
exponent `s / 2 + Tr(p) / (2 [K : ℚ])`. It is the weighted theta integral over the unit cone
with the radial scale raised to `s / 2`. -/
theorem hasMellin_heckeMellinKernel_sub (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K)
      (s / 2 + ((χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ)) : ℝ))
      ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w : ℝ)) / 2) : ℝ) * (χ.heckeScale J : ℂ) ^ (s / 2) *
        ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          ((χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon)) ∂archHaar K) := by
  let q : ℝ := (χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))
  let f : realSpace K → ℂ := fun y ↦
    (χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon)
  let M := ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * f y ∂archHaar K
  have hscale := χ.heckeScale_pos J
  have heq (u : ℝ) (hu : u ∈ Ioi 0) : mellinFactor χ J •
      centeredSurfaceAverage χ D J (u / χ.heckeScale J) =
      χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K := by
    rw [heckeMellinKernel_sub_eq_integral χ J hD hu]
    simp only [centeredSurfaceAverage, smul_eq_mul]
  have hkernel := (hasMellin_congr heq).mp
    ((hasMellin_centeredSurfaceAverage χ J hD hs).const_smul_comp_div (mellinFactor χ J) hscale)
  have hpow :
      (↑((χ.heckeScale J) ^ (-q) : ℝ) : ℂ) * (χ.heckeScale J : ℂ) ^ (s / 2 + (q : ℂ)) =
        (χ.heckeScale J : ℂ) ^ (s / 2) := by
    rw [Complex.ofReal_cpow hscale.le, Complex.ofReal_neg,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hscale.ne'),
      neg_add_cancel_comm_assoc]
  let A : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex}, (χ.harmonicExponent w : ℝ)) / 2) : ℝ)
  have hfactor : mellinFactor χ J = A * ((χ.heckeScale J ^ (-q) : ℝ) : ℂ) := by
    simp only [mellinFactor, A, q, neg_div]
  refine ⟨hkernel.1, hkernel.2.trans ?_⟩
  calc
    _ = A * (((χ.heckeScale J ^ (-q) : ℝ) : ℂ) *
        (χ.heckeScale J : ℂ) ^ (s / 2 + (q : ℂ))) * M := by rw [smul_eq_mul, hfactor]; ring
    _ = _ := by rw [hpow]

end TauCeti.LFunctions.Grossencharacter
