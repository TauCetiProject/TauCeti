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

/-- Two presentations of the same Hecke character have the same `heckeScale`. -/
theorem heckeScale_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    χ.heckeScale J = ψ.heckeScale J := by
  rw [heckeScale_def, heckeScale_def, h]

/-- Passing to `χ.primitive` does not change `heckeScale`. -/
@[simp]
theorem heckeScale_primitive (χ : Grossencharacter K 𝔪) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    χ.primitive.heckeScale J = χ.heckeScale J :=
  heckeScale_congr χ.toHeckeCharacter_primitive J

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

/-- Passing to `χ.primitive` does not change `heckeMellinKernel`. -/
@[simp]
theorem heckeMellinKernel_primitive (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) :
    χ.primitive.heckeMellinKernel D J u = χ.heckeMellinKernel D J u := by
  rw [heckeMellinKernel_congr χ.toHeckeCharacter_primitive]

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

open scoped Classical in
/-- For the trivial ray class character at `Modulus.one K`, `heckeMellinKernel` recovers
`mellinKernel` of the ideal lattice `idealLattice K J` for `0 < u`. -/
@[simp]
theorem heckeMellinKernel_ofRayClassCharacter_one (D : Set (realSpace K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℝ} (hu : 0 < u) :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeMellinKernel D J u =
      mellinKernel D (idealLattice K J) u :=
  heckeMellinKernel_eq_mellinKernel _ heckeEpsilon_ofRayClassCharacter_one D J hu

-- The radial power can be moved from the centered theta integrand into the Mellin exponent.
private theorem archWeight_mul_heckeTheta_sub_surfaceScale (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : normOneSurface K) {t : ℝ} (ht : 0 ≤ t) :
    (χ.archWeight (surfaceScale (x : realSpace K) t) : ℂ) *
        (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon) =
      ((t ^ ((χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) : ℝ) : ℂ) *
        ((χ.archWeight (x : realSpace K) : ℂ) *
          (χ.heckeTheta J (surfaceScale (x : realSpace K) t) - χ.heckeEpsilon)) := by
  rw [χ.archWeight_surfaceScale (x : realSpace K) ht, Complex.ofReal_mul, mul_left_comm]
  ring

private theorem exists_archWeight_le_on_surface (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ x : normOneSurface K, (x : realSpace K) ∈ D →
      ‖(χ.archWeight (x : realSpace K) : ℂ)‖ ≤ W := by
  obtain ⟨S, hS, hsub⟩ := exists_isCompact_superset_preimage hD
  obtain ⟨W, hW⟩ := hS.exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp
      (χ.continuous_archWeight.comp continuous_subtypeVal)).continuousOn
  exact ⟨max W 0, le_max_right _ _, fun x hx ↦ (hW x (hsub hx)).trans (le_max_left _ _)⟩

/-- For a bounded surface set `D` and `0 < t`, `(χ.archWeight x : ℂ) * χ.heckeTheta J
(surfaceScale x t)` is integrable over `Subtype.val ⁻¹' D` with respect to `surfaceHaar K`. -/
theorem integrableOn_archWeight_mul_heckeTheta_surfaceScale (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : normOneSurface K ↦
      (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta J (surfaceScale (x : realSpace K) t))
      (Subtype.val ⁻¹' D) (surfaceHaar K) :=
  integrableOn_mul_surfaceScale
    (Complex.continuous_ofReal.comp (χ.continuous_archWeight.comp continuous_subtypeVal))
    (χ.continuousAt_heckeTheta J) hD ht

/-- The Mellin kernel of a fractional ideal is continuous at positive radii for any bounded
set of surface parameters. -/
theorem continuousOn_heckeMellinKernel (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) : ContinuousOn (χ.heckeMellinKernel D J) (Ioi 0) := by
  have hm : χ.heckeMellinKernel D J = fun u ↦
      mellinFactor χ J * ∫ x in Subtype.val ⁻¹' D,
        (Complex.ofReal ∘ χ.archWeight ∘ Subtype.val) x *
          χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J))
            ∂surfaceHaar K := by
    ext u
    simp [heckeMellinKernel]
  rw [hm]
  exact continuousOn_const_mul_integral_surfaceScale
    (mellinFactor χ J)
    (Complex.continuous_ofReal.comp (χ.continuous_archWeight.comp continuous_subtypeVal))
    (χ.continuousAt_heckeTheta J) hD (χ.heckeScale_pos J)

open scoped Classical in
/-- Multiplying `χ.heckeMellinKernel D J u` by `u ^ (Tr(p) / (2n))` absorbs the `heckeScale`
factor into `χ.archWeight (surfaceScale x (u / χ.heckeScale J))`. -/
theorem heckeMellinKernel_eq_integral_archWeight_surfaceScale (χ : Grossencharacter K 𝔪)
    (D : Set (realSpace K)) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℝ} (hu : 0 ≤ u) :
    (u : ℂ) ^ ((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)) *
        χ.heckeMellinKernel D J u =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w : ℝ)) / 2) : ℝ) *
        ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (surfaceScale (x : realSpace K) (u / χ.heckeScale J)) : ℂ) *
            χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J))
              ∂surfaceHaar K := by
  set lam := χ.heckeScale J
  have hlam : 0 < lam := χ.heckeScale_pos J
  set e : ℝ := (χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)
  have he_cast : ((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)) = (e : ℂ) := by
    simp [e]
  have hpow : (u : ℂ) ^ (e : ℂ) * ((lam ^ (-e) : ℝ) : ℂ) =
      ((u / lam : ℝ) : ℂ) ^ (e : ℂ) := by
    rw [← Complex.ofReal_cpow hu, ← Complex.ofReal_cpow (div_nonneg hu hlam.le),
      ← Complex.ofReal_mul, Real.rpow_neg hlam.le, ← div_eq_mul_inv, Real.div_rpow hu hlam.le]
  have hscale (x : normOneSurface K) :
      (χ.archWeight (surfaceScale (x : realSpace K) (u / lam)) : ℂ) =
        (((u / lam : ℝ) : ℂ) ^ (e : ℂ)) * (χ.archWeight (x : realSpace K) : ℂ) := by
    rw [χ.archWeight_surfaceScale (x : realSpace K) (div_nonneg hu hlam.le), Complex.ofReal_mul,
      ← Complex.ofReal_cpow (div_nonneg hu hlam.le), mul_comm]
  have hRHS :
      ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (surfaceScale (x : realSpace K) (u / lam)) : ℂ) *
            χ.heckeTheta J (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K =
        ((u / lam : ℝ) : ℂ) ^ (e : ℂ) * ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta J (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K := by
    simp_rw [hscale, mul_assoc]
    exact integral_const_mul _ _
  rw [heckeMellinKernel_def, he_cast, hRHS]
  have hneg : -(χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ)) = -e := by
    simp [e, neg_div]
  rw [hneg]
  calc (u : ℂ) ^ (e : ℂ) *
        ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
            (χ.harmonicExponent w : ℝ)) / 2) : ℝ) *
          ((lam ^ (-e) : ℝ) : ℂ) *
          ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta J (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K)
      = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
            (χ.harmonicExponent w : ℝ)) / 2) : ℝ) *
          (((u : ℂ) ^ (e : ℂ) * ((lam ^ (-e) : ℝ) : ℂ)) *
            ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
              χ.heckeTheta J (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K) := by
        ring
    _ = _ := by rw [hpow]

open scoped Classical in
/-- Subtracting the constant term from `χ.heckeMellinKernel D J` shifts `χ.heckeTheta J`
by `χ.heckeEpsilon` inside the surface integral. -/
theorem heckeMellinKernel_sub_eq_integral (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) {u : ℝ} (hu : 0 < u) :
    χ.heckeMellinKernel D J u -
        χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ)) =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((2 : ℝ) ^ (-(∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w : ℝ)) / 2) : ℝ) *
        ((χ.heckeScale J) ^ (-(χ.harmonicDegree : ℝ) / (2 * (Module.finrank ℚ K : ℝ))) : ℝ) *
        ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
          (χ.heckeTheta J (surfaceScale (x : realSpace K) (u / χ.heckeScale J)) -
            χ.heckeEpsilon) ∂surfaceHaar K := by
  change χ.heckeMellinKernel D J u - _ = mellinFactor χ J * _
  rw [heckeMellinKernel]
  have hconst :
      mellinFactor χ J * (((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) * χ.heckeEpsilon) =
        χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ)) := by
    rcases χ.heckeEpsilon_eq_zero_or_eq_one with h | h
    · simp [h]
    have hdeg := (χ.heckeEpsilon_eq_one_iff.mp h).2
    simp only [mellinFactor, hdeg, χ.harmonicExponent_eq_zero_of_harmonicDegree_eq_zero hdeg,
      Nat.cast_zero, Finset.sum_const_zero, neg_zero, zero_div, Real.rpow_zero, Complex.ofReal_one,
      mul_one, h, one_mul]
  have hfin := surfaceHaar_preimage_lt_top hD
  have hInt := χ.integrableOn_archWeight_mul_heckeTheta_surfaceScale hD
    J (div_pos hu (χ.heckeScale_pos J))
  simp_rw [mul_sub, archWeight_mul_heckeEpsilon]
  rw [integral_sub hInt (integrableOn_const hfin.ne), setIntegral_const,
    Complex.real_smul, mul_sub, hconst]

open scoped Classical in
/-- Over a bounded surface set `D`, `χ.heckeMellinKernel D J` tends to
`χ.heckeEpsilon * (2^r₂ / w) * vol(D)` with stretched-exponential error `O(exp(-c u^(1/n)))`,
`n = [K : ℚ]`. -/
theorem exists_norm_heckeMellinKernel_sub_le (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop,
      ‖χ.heckeMellinKernel D J u -
          χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
            ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  set lam := χ.heckeScale J
  have hlam : 0 < lam := χ.heckeScale_pos J
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_mul_integral_surfaceScale_sub_le
    (w := fun x : normOneSurface K ↦ (χ.archWeight (x : realSpace K) : ℂ))
    (g := χ.heckeTheta J) (ε := χ.heckeEpsilon) hD
    (χ.exists_archWeight_le_on_surface hD)
    (χ.exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le J
      (hD.subset inter_subset_left) inter_subset_right)
    (mellinFactor χ J) hlam
  refine ⟨c, hc, C, hC, ?_⟩
  filter_upwards [h, eventually_gt_atTop 0] with u hu hu0
  change _ ≤ _ at hu
  rwa [χ.heckeMellinKernel_sub_eq_integral J hD hu0]

open scoped Classical in
/-- Over any bounded surface set `D`, `χ.heckeMellinKernel D J` minus its asymptotic
constant `χ.heckeEpsilon * (2^r₂ / w) * vol(D)` satisfies a stretched-exponential bound with
exponent `[K : ℚ]⁻¹` on every ray `[a, ∞)` with `a > 0`. -/
theorem exists_norm_heckeMellinKernel_sub_le_on_Ici (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ici a,
      ‖χ.heckeMellinKernel D J u -
          χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
            ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) :=
  exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_exists_eventually (.inl ha)
    (((χ.continuousOn_heckeMellinKernel J hD).mono (Ici_subset_Ioi.mpr ha)).sub
      continuousOn_const)
    (χ.exists_norm_heckeMellinKernel_sub_le hD J)

open scoped Classical in
/-- Over any bounded surface set `D`, `χ.heckeMellinKernel D J` minus its constant term
`χ.heckeEpsilon * (2^r₂ / w) * vol(D)` decays faster than every power as `u → ∞`. -/
theorem isBigO_heckeMellinKernel_sub_rpow_of_isBounded (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun u ↦ χ.heckeMellinKernel D J u -
        χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))) =O[atTop] (· ^ r) :=
  isBigO_rpow_of_eventually_norm_le_exp_neg
    (inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))))
    (χ.exists_norm_heckeMellinKernel_sub_le hD J) r

/-- After subtraction of its constant term, the Mellin kernel over a unit fundamental domain
has stretched-exponential decay as the radius tends to infinity. -/
theorem exists_isBigO_heckeMellinKernel_sub_exp (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) :
    ∃ c > 0, (fun u ↦ χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K) =O[atTop]
      (fun u ↦ Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹)) := by
  obtain ⟨c, hc, C, _, h⟩ := χ.exists_norm_heckeMellinKernel_sub_le hD.isBounded J
  refine ⟨c, hc, Asymptotics.IsBigO.of_bound C ?_⟩
  filter_upwards [h] with u hu
  simpa only [coe_mellinConstant_eq_mul_surfaceHaar_real hD, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using hu

/-- The centered Mellin kernel decays faster than every real power. -/
theorem isBigO_heckeMellinKernel_sub_rpow (χ : Grossencharacter K 𝔪)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (r : ℝ) :
    (fun u ↦ χ.heckeMellinKernel D J u - χ.heckeEpsilon * mellinConstant K) =O[atTop]
      (fun u ↦ u ^ r) := by
  simpa only [coe_mellinConstant_eq_mul_surfaceHaar_real hD] using
    χ.isBigO_heckeMellinKernel_sub_rpow_of_isBounded hD.isBounded J r

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
    have hW : ContinuousAt (fun z ↦ (χ.archWeight z : ℂ)) y :=
      (Complex.continuous_ofReal.comp χ.continuous_archWeight).continuousAt
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
    rw [coe_mellinConstant_eq_mul_surfaceHaar_real hD,
      heckeMellinKernel_sub_eq_integral χ J hD.isBounded hu]
    simp only [centeredSurfaceAverage, mellinFactor, smul_eq_mul]
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
