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
`D : Set (realSpace K)`, and an invertible fractional ideal `I : (FractionalIdeal (𝓞 K)⁰ K)ˣ`,
Hecke's Mellin kernel (Neukirch VII (8.3)) averages
`χ.archWeight x * χ.heckeTheta I (surfaceScale x (u / λ_I))` over `D` with respect to
`surfaceHaar K`, where `λ_I = V_I² * N(𝔣₀)` is the scaling constant attached to the ideal lattice
of `I` and the finite conductor `𝔣₀ = χ.toHeckeCharacter.finiteConductor`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.heckeKernelLevel`: the scaling constant `λ_I = V_I² N(𝔣₀)`.
* `TauCeti.LFunctions.Grossencharacter.heckeMellinKernel`: Hecke's Mellin kernel `f_D(χ, I, u)`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.heckeKernelLevel_pos`, `heckeKernelLevel_congr`, and
  `heckeKernelLevel_primitive`: positivity and modulus independence of `λ_I`.
* `TauCeti.LFunctions.Grossencharacter.heckeMellinKernel_congr` and
  `TauCeti.LFunctions.Grossencharacter.heckeMellinKernel_primitive`: modulus independence of
  `heckeMellinKernel`.
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
/-- The kernel scaling constant `λ_I = V_I² * N(𝔣₀)` attached to a presentation `χ` and an
invertible fractional ideal `I`, where `V_I` is the covolume of `idealLattice K I` and
`𝔣₀ = χ.toHeckeCharacter.finiteConductor` is the finite conductor of `χ`. -/
def heckeKernelLevel (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  ZLattice.covolume (idealLattice K I) ^ 2 *
    (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ)

open scoped Classical in
/-- The defining equation of `Grossencharacter.heckeKernelLevel`. -/
theorem heckeKernelLevel_def (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    χ.heckeKernelLevel I =
      ZLattice.covolume (idealLattice K I) ^ 2 *
        (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ) :=
  (rfl)

open scoped Classical in
/-- `χ.heckeKernelLevel I` is strictly positive, since the lattice covolume is positive and the
finite conductor is nonzero. -/
theorem heckeKernelLevel_pos (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < χ.heckeKernelLevel I := by
  have hV : 0 < ZLattice.covolume (idealLattice K I) := ZLattice.covolume_pos _ volume
  have hf : 0 < (Ideal.absNorm χ.toHeckeCharacter.finiteConductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.toHeckeCharacter.finiteConductor_ne_bot)
  rw [heckeKernelLevel_def]
  positivity

/-- Two presentations of the same Hecke character have the same `heckeKernelLevel`. -/
theorem heckeKernelLevel_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    χ.heckeKernelLevel I = ψ.heckeKernelLevel I := by
  rw [heckeKernelLevel_def, heckeKernelLevel_def, h]

/-- Passing to `χ.primitive` does not change `heckeKernelLevel`. -/
@[simp]
theorem heckeKernelLevel_primitive (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    χ.primitive.heckeKernelLevel I = χ.heckeKernelLevel I :=
  heckeKernelLevel_congr χ.toHeckeCharacter_primitive I

open scoped Classical in
/-- **The Mellin kernel of a Grossencharacter** (Neukirch VII (8.3)) over a surface set `D` and
an invertible fractional ideal `I`:
`f_D(χ, I, u) = (2^r₂ / w) * 2^(-∑_{w complex} P_w / 2) * λ_I^(-Tr(p)/(2n)) *
  ∫_{x ∈ D} χ.archWeight x * χ.heckeTheta I (surfaceScale x (u / λ_I)) d*x`,
where `λ_I = χ.heckeKernelLevel I`. -/
def heckeMellinKernel (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) : ℂ :=
  (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
      (χ.harmonicExponent w.val : ℂ)) / 2)) *
    (χ.heckeKernelLevel I : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K))) *
    ∫ x in Subtype.val ⁻¹' D,
      (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta I (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel I))
          ∂surfaceHaar K

open scoped Classical in
/-- The defining equation of `Grossencharacter.heckeMellinKernel`. -/
theorem heckeMellinKernel_def (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) :
    χ.heckeMellinKernel D I u =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w.val : ℂ)) / 2)) *
        (χ.heckeKernelLevel I : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K))) *
        ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta I (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel I))
              ∂surfaceHaar K :=
  (rfl)

open scoped Classical in
/-- Two presentations of the same Hecke character have the same `heckeMellinKernel`. -/
theorem heckeMellinKernel_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (D : Set (realSpace K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) :
    χ.heckeMellinKernel D I u = ψ.heckeMellinKernel D I u := by
  simp_rw [heckeMellinKernel_def, harmonicExponent_congr h, harmonicDegree_congr h,
    heckeKernelLevel_congr h, archWeight_congr h, heckeTheta_congr h]

/-- Passing to `χ.primitive` does not change `heckeMellinKernel`. -/
@[simp]
theorem heckeMellinKernel_primitive (χ : Grossencharacter K 𝔪) (D : Set (realSpace K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) :
    χ.primitive.heckeMellinKernel D I u = χ.heckeMellinKernel D I u :=
  heckeMellinKernel_congr χ.toHeckeCharacter_primitive D I u

private theorem exists_archWeight_le_on_surface (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ x : normOneSurface K, (x : realSpace K) ∈ D →
      ‖(χ.archWeight (x : realSpace K) : ℂ)‖ ≤ W := by
  obtain ⟨C, _, hC⟩ := exists_forall_mem_Icc_of_isBounded hD
  refine ⟨∏ w : InfinitePlace K, C ^ ((χ.harmonicExponent w : ℝ) / 2),
    Finset.prod_nonneg fun w _ ↦ by positivity, fun x hx ↦ ?_⟩
  rw [Complex.norm_real,
    Real.norm_of_nonneg (χ.archWeight_nonneg ((mem_normOneSurface.mp x.property).1 · |>.le)),
    archWeight_def]
  gcongr
  · exact fun w _ ↦ Real.rpow_nonneg ((mem_normOneSurface.mp x.property).1 w).le _
  · exact ((mem_normOneSurface.mp x.property).1 _).le
  · exact (hC _ hx x.property _).2

private theorem exists_norm_heckeTheta_bound (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ y : realSpace K, (∀ w, δ ≤ y w) → ‖χ.heckeTheta I y‖ ≤ B :=
  ⟨_, fun _ hy ↦ χ.norm_heckeTheta_le I (fun _ ↦ hδ) hy⟩

/-- For a bounded measurable surface set `D` and `0 < t`, `(χ.archWeight x : ℂ) * χ.heckeTheta I
(surfaceScale x t)` is integrable over `Subtype.val ⁻¹' D` with respect to `surfaceHaar K`. -/
theorem integrableOn_archWeight_mul_heckeTheta_surfaceScale (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : normOneSurface K ↦
      (χ.archWeight (x : realSpace K) : ℂ) *
        χ.heckeTheta I (surfaceScale (x : realSpace K) t))
      (Subtype.val ⁻¹' D) (surfaceHaar K) :=
  integrableOn_mul_surfaceScale
    (continuous_ofReal.comp (χ.continuous_archWeight.comp continuous_subtypeVal))
    (χ.continuousAt_heckeTheta I)
    (fun hδ ↦ χ.exists_norm_heckeTheta_bound I hδ)
    hDm hD (χ.exists_archWeight_le_on_surface hD) ht

open scoped Classical in
/-- **The Mellin kernel of a Grossencharacter is continuous on `(0, ∞)`** for any bounded
measurable surface set `D`. -/
theorem continuousOn_heckeMellinKernel (χ : Grossencharacter K 𝔪) {D : Set (realSpace K)}
    (hDm : MeasurableSet D) (hD : Bornology.IsBounded D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (χ.heckeMellinKernel D I) (Set.Ioi 0) := by
  have hm : χ.heckeMellinKernel D I = fun u ↦
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w.val : ℂ)) / 2)) *
        (χ.heckeKernelLevel I : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K))) *
        ∫ x in Subtype.val ⁻¹' D,
          (ofReal ∘ χ.archWeight ∘ Subtype.val) x *
            χ.heckeTheta I (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel I))
              ∂surfaceHaar K := by
    ext u
    simp [heckeMellinKernel_def]
  rw [hm]
  exact continuousOn_const_mul_integral_surfaceScale
    ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
      (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
        (χ.harmonicExponent w.val : ℂ)) / 2)) *
      (χ.heckeKernelLevel I : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K))))
    (continuous_ofReal.comp (χ.continuous_archWeight.comp continuous_subtypeVal))
    (χ.continuousAt_heckeTheta I)
    (fun hδ ↦ χ.exists_norm_heckeTheta_bound I hδ)
    hDm hD (χ.exists_archWeight_le_on_surface hD) (χ.heckeKernelLevel_pos I)

open scoped Classical in
/-- Multiplying `χ.heckeMellinKernel D I u` by `u ^ (Tr(p) / (2n))` absorbs the `λ_I` factor
into `χ.archWeight (surfaceScale x (u / λ_I))`. -/
theorem heckeMellinKernel_eq_integral_archWeight_surfaceScale (χ : Grossencharacter K 𝔪)
    (D : Set (realSpace K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℝ} (hu : 0 ≤ u) :
    (u : ℂ) ^ ((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)) *
        χ.heckeMellinKernel D I u =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
          (χ.harmonicExponent w.val : ℂ)) / 2)) *
        ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel I)) : ℂ) *
            χ.heckeTheta I (surfaceScale (x : realSpace K) (u / χ.heckeKernelLevel I))
              ∂surfaceHaar K := by
  set lam := χ.heckeKernelLevel I
  have hlam : 0 < lam := χ.heckeKernelLevel_pos I
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
            χ.heckeTheta I (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K =
        ((u / lam : ℝ) : ℂ) ^ (e : ℂ) * ∫ x in Subtype.val ⁻¹' D,
          (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta I (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K := by
    simp_rw [hscale, mul_assoc]
    exact integral_const_mul _ _
  rw [hRHS]
  calc (u : ℂ) ^ (e : ℂ) *
        ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
            (χ.harmonicExponent w.val : ℂ)) / 2)) *
          (lam : ℂ) ^ (-(e : ℂ)) *
          ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
            χ.heckeTheta I (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K)
      = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
            (χ.harmonicExponent w.val : ℂ)) / 2)) *
          (((u : ℂ) ^ (e : ℂ) * (lam : ℂ) ^ (-(e : ℂ))) *
            ∫ x in Subtype.val ⁻¹' D, (χ.archWeight (x : realSpace K) : ℂ) *
              χ.heckeTheta I (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K) := by
        ring
    _ = _ := by rw [hpow]

section

open Filter

open scoped Classical in
/-- **The Mellin kernel of a Grossencharacter at `∞`**: over a bounded measurable surface set `D`,
the kernel tends to `χ.heckeEpsilon * (2^r₂ / w) * vol(D)` with error `O(exp(-c u^(1/n)))`,
`n = [K : ℚ]`. -/
theorem exists_norm_heckeMellinKernel_sub_le (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop,
      ‖χ.heckeMellinKernel D I u -
          χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
            ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  set lam := χ.heckeKernelLevel I
  have hlam : 0 < lam := χ.heckeKernelLevel_pos I
  set A : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    (2 : ℂ) ^ (-((∑ w : {w : InfinitePlace K // w.IsComplex},
      (χ.harmonicExponent w.val : ℂ)) / 2)) *
    (lam : ℂ) ^ (-((χ.harmonicDegree : ℂ) / (2 * Module.finrank ℚ K)))
  set S : Set (normOneSurface K) := Subtype.val ⁻¹' D
  have hfin : surfaceHaar K S < ⊤ := surfaceHaar_preimage_lt_top hD
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_mul_integral_surfaceScale_sub_le
    (w := fun x : normOneSurface K ↦ (χ.archWeight (x : realSpace K) : ℂ))
    (g := χ.heckeTheta I) (ε := χ.heckeEpsilon) hD
    (χ.exists_archWeight_le_on_surface hD)
    (χ.exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le I
      (hD.subset inter_subset_left) inter_subset_right)
    A hlam
  refine ⟨c, hc, C, hC, ?_⟩
  filter_upwards [h, eventually_gt_atTop 0] with u hu hu0
  have hsub : χ.heckeMellinKernel D I u -
      χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((surfaceHaar K).real S : ℂ)) =
      A * ∫ x in S, (χ.archWeight (x : realSpace K) : ℂ) *
        (χ.heckeTheta I (surfaceScale (x : realSpace K) (u / lam)) -
          χ.heckeEpsilon) ∂surfaceHaar K := by
    by_cases hdeg : χ.harmonicDegree = 0
    · have hw : ∀ w, χ.harmonicExponent w = 0 := by
        simpa [harmonicDegree_def] using hdeg
      have hA : A = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) := by
        simp [A, hw, hdeg]
      have hW1 : ∀ x : normOneSurface K, (χ.archWeight (x : realSpace K) : ℂ) = 1 := fun x ↦ by
        rw [χ.archWeight_of_harmonicDegree_eq_zero hdeg, ofReal_one]
      have hint := χ.integrableOn_archWeight_mul_heckeTheta_surfaceScale hDm hD
        I (by positivity : 0 < u / lam)
      simp_rw [hW1, one_mul] at hint
      rw [heckeMellinKernel_def]
      simp_rw [hw, hdeg, Nat.cast_zero, Finset.sum_const_zero, zero_div, neg_zero, cpow_zero,
        mul_one, hW1, one_mul]
      rw [hA, integral_sub hint (integrableOn_const hfin.ne), setIntegral_const, Complex.real_smul]
      ring
    · have heps : χ.heckeEpsilon = 0 := χ.heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero hdeg
      simp only [heps, zero_mul, sub_zero, heckeMellinKernel_def]
      rfl
  rwa [hsub]

open scoped Classical in
/-- Over any bounded measurable surface set `D`, `χ.heckeMellinKernel D I` minus its asymptotic
constant `χ.heckeEpsilon * (2^r₂ / w) * vol(D)` satisfies a stretched-exponential bound with
exponent `[K : ℚ]⁻¹` on every ray `[a, ∞)` with `a > 0`. -/
theorem exists_norm_heckeMellinKernel_sub_le_on_Ici (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ici a,
      ‖χ.heckeMellinKernel D I u -
          χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
            ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) :=
  exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_exists_eventually (.inl ha)
    (((χ.continuousOn_heckeMellinKernel hDm hD I).mono (Ici_subset_Ioi.mpr ha)).sub
      continuousOn_const)
    (χ.exists_norm_heckeMellinKernel_sub_le hDm hD I)

open scoped Classical in
/-- Over a bounded measurable surface set `D`, `χ.heckeMellinKernel D I` minus its constant term
`χ.heckeEpsilon * (2^r₂ / w) * vol(D)` decays faster than every power as `u → ∞`. -/
theorem isBigO_heckeMellinKernel_sub_rpow (χ : Grossencharacter K 𝔪)
    {D : Set (realSpace K)} (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun u ↦ χ.heckeMellinKernel D I u -
        χ.heckeEpsilon * ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ))) =O[atTop] (· ^ r) :=
  isBigO_rpow_of_eventually_norm_le_exp_neg
    (inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))))
    (χ.exists_norm_heckeMellinKernel_sub_le hDm hD I) r

end

open scoped Classical in
/-- For the trivial ray class character at `Modulus.one K`, `heckeMellinKernel` recovers
`mellinKernel` of the ideal lattice `idealLattice K I` for `0 < u`. -/
@[simp]
theorem heckeMellinKernel_ofRayClassCharacter_one (D : Set (realSpace K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℝ} (hu : 0 < u) :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeMellinKernel D I u =
      mellinKernel D (idealLattice K I) u := by
  set χ := ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))
  have hV : 0 < ZLattice.covolume (idealLattice K I) volume :=
    ZLattice.covolume_pos _ volume
  have hlev : χ.heckeKernelLevel I = ZLattice.covolume (idealLattice K I) ^ 2 := by
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
  exact heckeTheta_ofRayClassCharacter_one I
    (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (by positivity))

end TauCeti.LFunctions.Grossencharacter
