/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Theta
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Kernel

/-!
# The Mellin kernel of a Grossencharacter

For a presented algebraic Hecke character `χ : Grossencharacter K 𝔪`, a surface set
`D : Set (realSpace K)`, and a nonzero integral ideal `𝔞 : (Ideal (𝓞 K))⁰`, Hecke's Mellin kernel
(Neukirch VII (8.3)) averages `χ.archWeight x * χ.heckeTheta 𝔞 (surfaceScale x (u / λ_𝔞))` over
`D` with respect to `surfaceHaar K`, where `λ_𝔞 = V_𝔞² * N(𝔣₀)` is the scaling constant attached
to the ideal lattice of `𝔞` and the finite conductor `𝔣₀ = χ.toHeckeCharacter.finiteConductor`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.heckeKernelLevel`: the scaling constant `λ_𝔞 = V_𝔞² N(𝔣₀)`.
* `TauCeti.LFunctions.Grossencharacter.heckeMellinKernel`: Hecke's Mellin kernel `f_D(χ, 𝔞, u)`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.heckeKernelLevel_pos`: positivity of `λ_𝔞`.
* `TauCeti.LFunctions.Grossencharacter.integrableOn_archWeight_mul_heckeTheta_surfaceScale`:
  integrability over bounded measurable surface sets for positive `u`.
* `TauCeti.LFunctions.Grossencharacter.continuousOn_heckeMellinKernel`: continuity on `(0, ∞)`.
* `TauCeti.LFunctions.Grossencharacter.heckeMellinKernel_eq_integral_archWeight_surfaceScale`:
  rewriting `u ^ (Tr(p)/(2n)) * heckeMellinKernel` in terms of `archWeight` at `surfaceScale`.
* `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeMellinKernel_sub_le`,
  `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeMellinKernel_sub_le_on_Ici`, and
  `TauCeti.LFunctions.Grossencharacter.isBigO_heckeMellinKernel_sub_rpow`: stretched-exponential
  and faster-than-every-power decay around the constant term.
* `TauCeti.LFunctions.Grossencharacter.heckeMellinKernel_ofRayClassCharacter_one`:
  at `Modulus.one K`, the trivial ray class character recovers `mellinKernel`.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8, (8.3).
-/

public section

noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  Set TauCeti.NumberField.mixedEmbedding
open scoped Topology nonZeroDivisors

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

open scoped Classical in
/-- The kernel scaling constant `λ_𝔞 = V_𝔞² * N(𝔣₀)` attached to a presentation `χ` and a nonzero
integral ideal `𝔞`, where `V_𝔞` is the covolume of `idealLattice K (FractionalIdeal.mk0 K 𝔞)` and
`𝔣₀ = χ.toHeckeCharacter.finiteConductor` is the finite conductor of `χ`. -/
def heckeKernelLevel (χ : Grossencharacter K 𝔪) (𝔞 : (Ideal (𝓞 K))⁰) : ℝ :=
  ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K 𝔞)) ^ 2 *
    (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ)

open scoped Classical in
/-- The defining equation of `Grossencharacter.heckeKernelLevel`. -/
theorem heckeKernelLevel_def (χ : Grossencharacter K 𝔪) (𝔞 : (Ideal (𝓞 K))⁰) :
    χ.heckeKernelLevel 𝔞 =
      ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K 𝔞)) ^ 2 *
        (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ) :=
  (rfl)

open scoped Classical in
/-- `χ.heckeKernelLevel 𝔞` is strictly positive, since the lattice covolume is positive and the
finite conductor is nonzero. -/
theorem heckeKernelLevel_pos (χ : Grossencharacter K 𝔪) (𝔞 : (Ideal (𝓞 K))⁰) :
    0 < χ.heckeKernelLevel 𝔞 := by
  have hV : 0 < ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K 𝔞)) :=
    ZLattice.covolume_pos _ volume
  have hf : 0 < (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.toHeckeCharacter.finiteConductor_ne_bot)
  rw [heckeKernelLevel_def]
  positivity

open scoped Classical in
/-- **The Mellin kernel of a Grossencharacter** (Neukirch VII (8.3)) over a surface set `D` and
nonzero integral ideal `𝔞`:
`f_D(χ, 𝔞, u) = (2^r₂ / w) * 2^(-∑_{w complex} P_w / 2) * λ_𝔞^(-Tr(p)/(2n)) *
  ∫_{x ∈ D} χ.archWeight x * χ.heckeTheta 𝔞 (surfaceScale x (u / λ_𝔞)) d*x`,
where `λ_𝔞 = χ.heckeKernelLevel 𝔞`. -/
def heckeMellinKernel (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (𝔞 : (Ideal (𝓞 K))⁰) (u : ℝ) : ℂ :=
  (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
      (χ.harmonicExponent w.val : ℂ)) / 2)) *
    (χ.heckeKernelLevel 𝔞 : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K))) *
    ∫ x in Subtype.val ⁻¹' D,
      (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta (𝔞 : Ideal (𝓞 K))
          (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel 𝔞)) ∂surfaceHaar K

open scoped Classical in
/-- The defining equation of `Grossencharacter.heckeMellinKernel`. -/
theorem heckeMellinKernel_def (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (𝔞 : (Ideal (𝓞 K))⁰) (u : ℝ) :
    χ.heckeMellinKernel D 𝔞 u =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w.val : ℂ)) / 2)) *
        (χ.heckeKernelLevel 𝔞 : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K))) *
        ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta (𝔞 : Ideal (𝓞 K))
              (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel 𝔞)) ∂surfaceHaar K :=
  (rfl)

private theorem exists_archWeight_le_on_surface (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ x : normOneSurface K, (x : realSpace K) ∈ D →
      χ.archWeight (x : realSpace K) ≤ W := by
  obtain ⟨C, hC1, hC⟩ := exists_forall_mem_Icc_of_isBounded hD
  refine ⟨∏ w : InfinitePlace K, C ^ ((χ.harmonicExponent w : ℝ) / 2),
    Finset.prod_nonneg fun w _ ↦ by positivity, fun x hx ↦ ?_⟩
  rw [archWeight_def]
  gcongr
  · exact fun w _ ↦ Real.rpow_nonneg ((mem_normOneSurface.mp x.property).1 w).le _
  · exact ((mem_normOneSurface.mp x.property).1 _).le
  · exact (hC _ hx x.property _).2

private theorem exists_norm_heckeTheta_surfaceScale_le (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D) (𝔞 : Ideal (𝓞 K))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ t ≥ t₀, ∀ x : normOneSurface K, (x : realSpace K) ∈ D →
      ‖χ.heckeTheta 𝔞 (surfaceScale (x : realSpace K) t)‖ ≤ B := by
  obtain ⟨C, hC1, hC⟩ := exists_forall_mem_Icc_of_isBounded hD
  let δ := C⁻¹ * t₀ ^ (1 / (Module.finrank ℚ K : ℝ))
  have hδ : 0 < δ := by positivity
  refine ⟨‖χ.heckeEpsilon‖ + ∑' a : 𝔞, ‖χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian (fun _ ↦ δ) (mixedEmbedding K ((a : 𝓞 K) : K))‖, fun t ht x hx ↦ ?_⟩
  have hy : ∀ w, δ ≤ surfaceScale (x : realSpace K) t w := fun w ↦ by
    rw [surfaceScale_apply]
    exact mul_le_mul (hC x hx x.property w).1
      (Real.rpow_le_rpow ht₀.le ht (by positivity)) (by positivity)
      ((mem_normOneSurface.mp x.property).1 w).le
  have hy_pos : ∀ w, 0 < surfaceScale (x : realSpace K) t w := fun w ↦ hδ.trans_le (hy w)
  rw [heckeTheta_def]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_tsum_le_tsum_norm (χ.summable_norm_heckeTheta 𝔞 hy_pos)).trans ?_
  refine (χ.summable_norm_heckeTheta 𝔞 hy_pos).tsum_le_tsum (fun a ↦ ?_)
    (χ.summable_norm_heckeTheta 𝔞 fun _ ↦ hδ)
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_archGaussian_le hy _) (mul_nonneg (norm_nonneg _)
    (norm_nonneg _))

private theorem continuous_archWeight_mul_heckeTheta_surfaceScale (χ : Grossencharacter K 𝔪)
    (𝔞 : Ideal (𝓞 K)) {t : ℝ} (ht : 0 < t) :
    Continuous fun x : normOneSurface K ↦
      (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta 𝔞 (surfaceScale (x : realSpace K) t) := by
  have hw : Continuous fun x : normOneSurface K ↦ (χ.archWeight (x : realSpace K) : ℂ) :=
    continuous_ofReal.comp (χ.continuous_archWeight.comp continuous_subtypeVal)
  have hth : Continuous fun x : normOneSurface K ↦
      χ.heckeTheta 𝔞 (surfaceScale (x : realSpace K) t) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ContinuousAt.comp (g := χ.heckeTheta 𝔞) (χ.continuousAt_heckeTheta 𝔞
      (surfaceScale_pos (mem_normOneSurface.mp x.property).1 ht))
      (continuous_surfaceScale.comp (continuous_subtypeVal.prodMk continuous_const)).continuousAt
  exact hw.mul hth

/-- For a bounded measurable surface set `D` and `0 < t`, `(χ.archWeight x : ℂ) * χ.heckeTheta 𝔞
(surfaceScale x t)` is integrable over `Subtype.val ⁻¹' D` with respect to `surfaceHaar K`. -/
theorem integrableOn_archWeight_mul_heckeTheta_surfaceScale (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (𝔞 : Ideal (𝓞 K)) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : normOneSurface K ↦
      (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta 𝔞 (surfaceScale (x : realSpace K) t))
      (Subtype.val ⁻¹' D) (surfaceHaar K) := by
  obtain ⟨W, hW, hWx⟩ := χ.exists_archWeight_le_on_surface hD
  obtain ⟨B, hB⟩ := χ.exists_norm_heckeTheta_surfaceScale_le hD 𝔞 ht
  have hmeas : AEStronglyMeasurable
      (fun x : normOneSurface K ↦ (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta 𝔞 (surfaceScale (x : realSpace K) t))
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) :=
    (χ.continuous_archWeight_mul_heckeTheta_surfaceScale 𝔞 ht).aestronglyMeasurable
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  refine (integrable_const (W * B)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (measurable_subtypeVal hDm)] with x hx
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (χ.archWeight_nonneg ((mem_normOneSurface.mp x.property).1 · |>.le))]
  exact mul_le_mul (hWx x hx) (hB t le_rfl x hx) (norm_nonneg _) hW

open scoped Classical in
/-- **The Mellin kernel of a Grossencharacter is continuous on `(0, ∞)`** for any bounded
measurable surface set `D`. -/
theorem continuousOn_heckeMellinKernel (χ : Grossencharacter K 𝔪) {D : Set (realSpace K)}
    (hDm : MeasurableSet D) (hD : Bornology.IsBounded D) (𝔞 : (Ideal (𝓞 K))⁰) :
    ContinuousOn (χ.heckeMellinKernel D 𝔞) (Set.Ioi 0) := by
  intro u₀ hu₀
  replace hu₀ : 0 < u₀ := hu₀
  refine ContinuousAt.continuousWithinAt ?_
  set lam := χ.heckeKernelLevel 𝔞
  have hlam : 0 < lam := χ.heckeKernelLevel_pos 𝔞
  set F : ℝ → normOneSurface K → ℂ := fun u x ↦
    (χ.archWeight (x : realSpace K) : ℂ) *
      χ.heckeTheta (𝔞 : Ideal (𝓞 K)) (surfaceScale (x : realSpace K) (u / lam))
  have ht₀ : 0 < u₀ / 2 / lam := by positivity
  obtain ⟨W, hW, hWx⟩ := χ.exists_archWeight_le_on_surface hD
  obtain ⟨B, hB⟩ := χ.exists_norm_heckeTheta_surfaceScale_le hD (𝔞 : Ideal (𝓞 K)) ht₀
  have hmeas : ∀ᶠ u in nhds u₀, AEStronglyMeasurable (F u)
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    filter_upwards [Ioi_mem_nhds hu₀] with u (hu : 0 < u)
    exact (χ.integrableOn_archWeight_mul_heckeTheta_surfaceScale hDm hD (𝔞 : Ideal (𝓞 K))
      (by positivity)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ x ∂(surfaceHaar K).restrict (Subtype.val ⁻¹' D),
      ‖F u x‖ ≤ W * B := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hu₀)] with u (hu : u₀ / 2 < u)
    filter_upwards [ae_restrict_mem (measurable_subtypeVal hDm)] with x hx
    dsimp only [F]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (χ.archWeight_nonneg ((mem_normOneSurface.mp x.property).1 · |>.le))]
    exact mul_le_mul (hWx x hx) (hB (u / lam) (div_le_div_of_nonneg_right hu.le hlam.le) x hx)
      (norm_nonneg _) hW
  have hint : Integrable (fun _ ↦ W * B) ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
    exact integrable_const _
  have hcont : ∀ᵐ x ∂(surfaceHaar K).restrict (Subtype.val ⁻¹' D),
      ContinuousAt (fun u ↦ F u x) u₀ := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hu : Continuous fun u : ℝ ↦ surfaceScale (x : realSpace K) (u / lam) :=
      continuous_surfaceScale.comp (continuous_const.prodMk (continuous_id.div_const _))
    exact continuousAt_const.mul (ContinuousAt.comp (g := χ.heckeTheta (𝔞 : Ideal (𝓞 K)))
      (χ.continuousAt_heckeTheta (𝔞 : Ideal (𝓞 K))
        (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (by positivity))) hu.continuousAt)
  exact continuousAt_const.mul (continuousAt_of_dominated hmeas hbound hint hcont)

open scoped Classical in
/-- Multiplying `χ.heckeMellinKernel D 𝔞 u` by `u ^ (Tr(p) / (2n))` absorbs the `λ_𝔞` factor
into `χ.archWeight (surfaceScale x (u / λ_𝔞))`. -/
theorem heckeMellinKernel_eq_integral_archWeight_surfaceScale (χ : Grossencharacter K 𝔪)
    (D : Set (realSpace K)) (𝔞 : (Ideal (𝓞 K))⁰) {u : ℝ} (hu : 0 ≤ u) :
    (u : ℂ) ^ ((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)) *
        χ.heckeMellinKernel D 𝔞 u =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w.val : ℂ)) / 2)) *
        ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel 𝔞)) : ℂ) *
            χ.heckeTheta (𝔞 : Ideal (𝓞 K))
              (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel 𝔞)) ∂surfaceHaar K := by
  set lam := χ.heckeKernelLevel 𝔞
  have hlam : 0 < lam := χ.heckeKernelLevel_pos 𝔞
  set e : ℝ := (χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)
  have he_cast : ((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)) = (e : ℂ) := by
    simp [e]
  have hpow : (u : ℂ) ^ (e : ℂ) * (lam : ℂ) ^ (-(e : ℂ)) =
      ((u / lam : ℝ) : ℂ) ^ (e : ℂ) := by
    rw [← ofReal_cpow hu, ← ofReal_neg, ← ofReal_cpow hlam.le,
      ← ofReal_cpow (div_nonneg hu hlam.le), ← ofReal_mul, Real.rpow_neg hlam.le,
      ← div_eq_mul_inv, Real.div_rpow hu hlam.le]
  have hscale (x : normOneSurface K) :
      (χ.archWeight (surfaceScale (x : realSpace K) (u / lam)) : ℂ) =
        (((u / lam : ℝ) : ℂ) ^ (e : ℂ)) * (χ.archWeight (x : realSpace K) : ℂ) := by
    rw [χ.archWeight_surfaceScale (x : realSpace K) (div_nonneg hu hlam.le), ofReal_mul,
      ← ofReal_cpow (div_nonneg hu hlam.le), mul_comm]
  rw [heckeMellinKernel_def, he_cast]
  have hRHS :
      ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (surfaceScale (x : realSpace K) (u / lam)) : ℂ) *
            χ.heckeTheta (𝔞 : Ideal (𝓞 K))
              (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K =
        ((u / lam : ℝ) : ℂ) ^ (e : ℂ) * ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta (𝔞 : Ideal (𝓞 K))
              (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K := by
    simp_rw [hscale, mul_assoc]
    exact integral_const_mul _ _
  rw [hRHS]
  calc (u : ℂ) ^ (e : ℂ) *
        ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
            (χ.harmonicExponent w.val : ℂ)) / 2)) *
          (lam : ℂ) ^ (-(e : ℂ)) *
          ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta (𝔞 : Ideal (𝓞 K))
              (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K)
      = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
            (χ.harmonicExponent w.val : ℂ)) / 2)) *
          (((u : ℂ) ^ (e : ℂ) * (lam : ℂ) ^ (-(e : ℂ))) *
            ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
              χ.heckeTheta (𝔞 : Ideal (𝓞 K))
                (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K) := by ring
    _ = _ := by rw [hpow]

section

open Filter

open scoped Classical in
/-- **The Mellin kernel of a Grossencharacter at `∞`**: over a bounded measurable surface set `D`,
the kernel tends to `χ.heckeEpsilon * (2^r₂ / w) * vol(D)` with error `O(exp(-c u^(1/n)))`,
`n = [K : ℚ]`. -/
theorem exists_norm_heckeMellinKernel_sub_le (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (𝔞 : (Ideal (𝓞 K))⁰) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop,
      ‖χ.heckeMellinKernel D 𝔞 u -
          χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
            ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  set lam := χ.heckeKernelLevel 𝔞
  have hlam : 0 < lam := χ.heckeKernelLevel_pos 𝔞
  set n : ℝ := (Module.finrank ℚ K : ℝ)⁻¹
  set A : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
      (χ.harmonicExponent w.val : ℂ)) / 2)) *
    (lam : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)))
  set S : Set (normOneSurface K) := Subtype.val ⁻¹' D
  have hfin : surfaceHaar K S < ⊤ := surfaceHaar_preimage_lt_top hD
  obtain ⟨W, hW, hWx⟩ := χ.exists_archWeight_le_on_surface hD
  obtain ⟨c, hc, C, hC, h⟩ := χ.exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le
    (𝔞 : Ideal (𝓞 K)) (hD.subset inter_subset_left) inter_subset_right
  refine ⟨c / lam ^ n, by positivity, ‖A‖ * (W * C * (surfaceHaar K).real S),
    by positivity, ?_⟩
  have hu : Tendsto (fun u : ℝ ↦ u / lam) atTop atTop :=
    tendsto_id.atTop_div_const hlam
  filter_upwards [hu.eventually h, eventually_gt_atTop 0] with u hu hu0
  set e := Real.exp (-c * (u / lam) ^ n)
  set θ : normOneSurface K → ℂ := fun x ↦
    χ.heckeTheta (𝔞 : Ideal (𝓞 K)) (surfaceScale (x : realSpace K) (u / lam))
  have hθ (x : normOneSurface K) (hx : x ∈ S) : ‖θ x - χ.heckeEpsilon‖ ≤ C * e :=
    hu x ⟨hx, x.property⟩
  have hsub : χ.heckeMellinKernel D 𝔞 u -
      χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((surfaceHaar K).real S : ℂ)) =
      A * ∫ x in S, (χ.archWeight (x : realSpace K) : ℂ) * (θ x - χ.heckeEpsilon)
        ∂surfaceHaar K := by
    have hint := χ.integrableOn_archWeight_mul_heckeTheta_surfaceScale hDm hD
      (𝔞 : Ideal (𝓞 K)) (by positivity : 0 < u / lam)
    by_cases hdeg : χ.harmonicDegree = 0
    · have hw : ∀ w, χ.harmonicExponent w = 0 := by
        simpa [harmonicDegree_def] using hdeg
      have hA : A = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) := by
        simp [A, hw, hdeg]
      have hW1 : ∀ x : normOneSurface K, (χ.archWeight (x : realSpace K) : ℂ) = 1 := fun x ↦ by
        rw [χ.archWeight_of_harmonicDegree_eq_zero hdeg, ofReal_one]
      simp_rw [hW1, one_mul] at hint
      rw [heckeMellinKernel_def]
      simp_rw [hw, hdeg, Nat.cast_zero, Finset.sum_const_zero, zero_div, neg_zero, cpow_zero,
        mul_one, hW1, one_mul]
      rw [hA, integral_sub hint (integrableOn_const hfin.ne), setIntegral_const, Complex.real_smul]
      dsimp only [θ, S]
      ring
    · have heps : χ.heckeEpsilon = 0 := χ.heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero hdeg
      simp only [heps, zero_mul, sub_zero, heckeMellinKernel_def]
      rfl
  have hnorm (x : normOneSurface K) (hx : x ∈ S) :
      ‖(χ.archWeight (x : realSpace K) : ℂ) * (θ x - χ.heckeEpsilon)‖ ≤ W * C * e := by
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (χ.archWeight_nonneg ((mem_normOneSurface.mp x.property).1 · |>.le))]
    calc χ.archWeight (x : realSpace K) * ‖θ x - χ.heckeEpsilon‖
        ≤ W * (C * e) := mul_le_mul (hWx x hx) (hθ x hx) (norm_nonneg _) hW
      _ = W * C * e := by ring
  have he : e = Real.exp (-(c / lam ^ n) * u ^ n) := by
    simp only [e]
    rw [Real.div_rpow hu0.le hlam.le]
    ring_nf
  rw [hsub, norm_mul, ← he]
  calc ‖A‖ * ‖∫ x in S, (χ.archWeight (x : realSpace K) : ℂ) * (θ x - χ.heckeEpsilon)
        ∂surfaceHaar K‖
      ≤ ‖A‖ * (W * C * e * (surfaceHaar K).real S) :=
        mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hfin hnorm) (norm_nonneg _)
    _ = ‖A‖ * (W * C * (surfaceHaar K).real S) * e := by ring

open scoped Classical in
/-- Over any bounded measurable surface set `D`, `χ.heckeMellinKernel D 𝔞` minus its asymptotic
constant `χ.heckeEpsilon * (2^r₂ / w) * vol(D)` satisfies a stretched-exponential bound with
exponent `[K : ℚ]⁻¹` on every ray `[a, ∞)` with `a > 0`. -/
theorem exists_norm_heckeMellinKernel_sub_le_on_Ici (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (𝔞 : (Ideal (𝓞 K))⁰) {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ici a,
      ‖χ.heckeMellinKernel D 𝔞 u -
          χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
            ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨c, hc, C₀, _, hev⟩ := χ.exists_norm_heckeMellinKernel_sub_le hDm hD 𝔞
  have hcont : ContinuousOn
      (fun u ↦ χ.heckeMellinKernel D 𝔞 u -
        χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))) (Ici a) :=
    ((χ.continuousOn_heckeMellinKernel hDm hD 𝔞).mono (Ici_subset_Ioi.mpr ha)).sub
      continuousOn_const
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_eventually (.inl ha) hcont hev
  exact ⟨c, hc, C, hC, hbound⟩

open scoped Classical in
/-- Over a bounded measurable surface set `D`, `χ.heckeMellinKernel D 𝔞` minus its constant term
`χ.heckeEpsilon * (2^r₂ / w) * vol(D)` decays faster than every power as `u → ∞`. -/
theorem isBigO_heckeMellinKernel_sub_rpow (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (𝔞 : (Ideal (𝓞 K))⁰) (r : ℝ) :
    (fun u ↦ χ.heckeMellinKernel D 𝔞 u -
        χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))) =O[atTop] (· ^ r) := by
  obtain ⟨c, hc, C, -, h⟩ := χ.exists_norm_heckeMellinKernel_sub_le hDm hD 𝔞
  refine isBigO_rpow_of_isBigO_exp_neg hc
    (inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))))
    (Asymptotics.IsBigO.of_bound C ?_) r
  filter_upwards [h] with u hu
  rwa [Real.norm_of_nonneg (Real.exp_pos _).le]

end

open scoped Classical in
/-- For the trivial ray class character at `Modulus.one K`, `heckeMellinKernel` recovers
`mellinKernel` of the ideal lattice `idealLattice K (FractionalIdeal.mk0 K 𝔞)` for `0 < u`. -/
theorem heckeMellinKernel_ofRayClassCharacter_one (D : Set (realSpace K))
    (𝔞 : (Ideal (𝓞 K))⁰) {u : ℝ} (hu : 0 < u) :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeMellinKernel D 𝔞 u =
      mellinKernel D (idealLattice K (FractionalIdeal.mk0 K 𝔞)) u := by
  set χ := ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))
  have hV : 0 < ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K 𝔞)) volume :=
    ZLattice.covolume_pos _ volume
  have hlev : χ.heckeKernelLevel 𝔞 =
      ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K 𝔞)) ^ 2 := by
    rw [heckeKernelLevel_def, show χ.toHeckeCharacter = 1 from by
      simp [χ, toHeckeCharacter_ofRayClassCharacter],
      HeckeCharacter.finiteConductor_one, Ideal.absNorm_top, Nat.cast_one, mul_one]
  rw [heckeMellinKernel_def, mellinKernel_def]
  simp only [χ, harmonicExponent_ofRayClassCharacter_one, Nat.cast_zero, Finset.sum_const_zero,
    zero_div, neg_zero, cpow_zero, mul_one, harmonicDegree_ofRayClassCharacter_one,
    archWeight_ofRayClassCharacter_one, ofReal_one, one_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [hlev]
  exact heckeTheta_ofRayClassCharacter_one 𝔞
    (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (by positivity))

end TauCeti.LFunctions.Grossencharacter
