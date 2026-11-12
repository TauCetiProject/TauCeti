/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
public import TauCeti.Analysis.MellinTransform
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Radial integration over a surface cone

The cone above a set `D` of norm-one archimedean parameters consists of the positive parameters
whose surface part lies in `D`. Restricting `archHaar` to this cone gives the image of
`(surfaceHaar.restrict D) × multHaar` under radial scaling. Consequently integration over the
cone splits into a surface integral and a radial Mellin transform.

Over a unit fundamental domain `D`, the translates of the cone by the action
`y ↦ (|u|_w² y_w)_w` of the units cover the positive orthant, every point exactly `w = #μ(K)`
times (`IsUnitFundamentalDomain.hasSum_indicator_unitScale_inv_mem_unitCone`). Hence the integrals
over the cone of `g ∘ (y ↦ |u|² y)`, summed over the units, are `w` times the integral of `g`
over all parameters (`IsUnitFundamentalDomain.hasSum_integral_unitCone_unitScale`); this is the
unfolding of the unit sum in Hecke's integral representation of a partial zeta function. Mathlib's
`MeasureTheory.IsFundamentalDomain.integral_eq_tsum` does not apply as it stands: the torsion
acts trivially on the parameters, so the translates of the cone by the units are not disjoint.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5).
-/

public section
noncomputable section

open MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The cone of positive parameters above `D`: their surface coordinate belongs to `D`.
For a unit fundamental domain this is the domain of Hecke's unfolding integral. -/
def unitCone (D : Set (realSpace K)) : Set (realSpace K) :=
  {y | (∀ w, 0 < y w) ∧ surfacePart y ∈ D}

/-- Cone membership requires positivity and membership of the normalized parameter in `D`. -/
@[simp]
theorem mem_unitCone {D : Set (realSpace K)} {y : realSpace K} :
    y ∈ unitCone D ↔ (∀ w, 0 < y w) ∧ surfacePart y ∈ D := Iff.rfl

/-- Membership in the cone in norm-one and radial coordinates. -/
theorem surfaceScale_mem_unitCone_iff (D : Set (realSpace K)) (x : normOneSurface K)
    {t : ℝ} (ht : 0 < t) : surfaceScale (x : realSpace K) t ∈ unitCone D ↔
      (x : realSpace K) ∈ D := by
  rw [mem_unitCone, surfacePart_surfaceScale x.2 ht]
  exact and_iff_right (surfaceScale_pos (mem_normOneSurface.mp x.2).1 ht)

/-- A measurable surface set has a measurable cone. -/
theorem measurableSet_unitCone {D : Set (realSpace K)} (hD : MeasurableSet D) :
    MeasurableSet (unitCone D) := by
  have hpos : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter fun w : InfinitePlace K ↦
      measurableSet_lt (measurable_const (a := (0 : ℝ))) (measurable_pi_apply w)
  exact hpos.inter (measurable_surfacePart hD)

/-- **The measure on the cone splits into surface and radial measures.** There is no extra
Jacobian: the radial coordinate is the archimedean norm and its measure is `dt / t`. -/
theorem archHaar_restrict_unitCone {D : Set (realSpace K)} (hD : MeasurableSet D) :
    (archHaar K).restrict (unitCone D) =
      (((surfaceHaar K).restrict (Subtype.val ⁻¹' D)).prod multHaar).map
        (fun p : normOneSurface K × ℝ ↦ surfaceScale (p.1 : realSpace K) p.2) := by
  rw [archHaar_eq_map, Measure.restrict_map measurable_surfaceScale_prod
    (measurableSet_unitCone hD)]
  congr 1
  conv_rhs => rw [← Measure.restrict_univ (μ := multHaar), Measure.prod_restrict]
  apply Measure.restrict_congr_set
  have hpos : ∀ᵐ p : normOneSurface K × ℝ ∂(surfaceHaar K).prod multHaar, 0 < p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ ↦ ae_pos_multHaar)
  filter_upwards [hpos] with p hp
  simpa only [mem_preimage, mem_prod, mem_univ, and_true] using
    surfaceScale_mem_unitCone_iff D p.1 hp

section Integral

variable {E : Type*} [NormedAddCommGroup E]

/-- Integrability on the cone is precisely integrability in the surface and radial coordinates.
The measurability hypothesis is only on the original cone. -/
theorem integrableOn_unitCone_iff {D : Set (realSpace K)} (hD : MeasurableSet D)
    {f : realSpace K → E} (hf : AEStronglyMeasurable f ((archHaar K).restrict (unitCone D))) :
    IntegrableOn f (unitCone D) (archHaar K) ↔
      Integrable (fun p : normOneSurface K × ℝ ↦ f (surfaceScale (p.1 : realSpace K) p.2))
        (((surfaceHaar K).restrict (Subtype.val ⁻¹' D)).prod multHaar) := by
  rw [archHaar_restrict_unitCone hD] at hf
  rw [IntegrableOn, archHaar_restrict_unitCone hD]
  exact integrable_map_measure hf measurable_surfaceScale_prod.aemeasurable

variable [NormedSpace ℝ E]

/-- Fubini on the cone, with the radial coordinate integrated last. -/
theorem integral_unitCone_eq_integral_surfaceScale {D : Set (realSpace K)}
    (hD : MeasurableSet D) {f : realSpace K → E}
    (hf : IntegrableOn f (unitCone D) (archHaar K)) :
    ∫ y in unitCone D, f y ∂archHaar K =
      ∫ t, ∫ x in Subtype.val ⁻¹' D, f (surfaceScale (x : realSpace K) t)
        ∂surfaceHaar K ∂multHaar := by
  have hprod := (integrableOn_unitCone_iff hD hf.aestronglyMeasurable).mp hf
  rw [IntegrableOn, archHaar_restrict_unitCone hD] at hf
  rw [archHaar_restrict_unitCone hD]
  rw [integral_map measurable_surfaceScale_prod.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod_symm _ hprod

end Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- A norm-weighted cone integral is the convergent Mellin transform of its surface average. -/
theorem hasMellin_integral_surfaceScale {D : Set (realSpace K)} (hD : MeasurableSet D)
    {f : realSpace K → E} (s : ℂ)
    (hf : IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ s • f y) (unitCone D) (archHaar K)) :
    HasMellin (fun t ↦ ∫ x in Subtype.val ⁻¹' D, f (surfaceScale (x : realSpace K) t)
        ∂surfaceHaar K) s
      (∫ y in unitCone D, (archNorm y : ℂ) ^ s • f y ∂archHaar K) := by
  have havg : (fun t ↦ ∫ x in Subtype.val ⁻¹' D,
      (archNorm (surfaceScale (x : realSpace K) t) : ℂ) ^ s •
        f (surfaceScale (x : realSpace K) t) ∂surfaceHaar K) =ᵐ[multHaar]
      (fun t ↦ (t : ℂ) ^ s • ∫ x in Subtype.val ⁻¹' D,
        f (surfaceScale (x : realSpace K) t) ∂surfaceHaar K) := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp_rw [archNorm_surfaceScale_of_mem_normOneSurface (Subtype.property _) ht.le,
      integral_smul]
  constructor
  · exact integrable_multHaar_cpow_smul_iff.mp
      (((integrableOn_unitCone_iff hD hf.aestronglyMeasurable).mp hf).integral_prod_right.congr
        havg)
  · rw [← integral_multHaar_cpow_smul, integral_unitCone_eq_integral_surfaceScale hD hf]
    exact (integral_congr_ae havg).symm

/-! ### The unit orbits of a cone -/

namespace IsUnitFundamentalDomain

variable {D : Set (realSpace K)}

/-- Over a unit fundamental domain `D`, the units carrying a positive parameter into the cone
above `D` form a coset of the torsion. -/
theorem exists_forall_unitScale_mem_unitCone_iff_mul_inv_mem_torsion
    (hD : IsUnitFundamentalDomain K D) {y : realSpace K} (hy : ∀ w, 0 < y w) :
    ∃ u₀ : (𝓞 K)ˣ, ∀ u, unitScale u y ∈ unitCone D ↔ u * u₀⁻¹ ∈ Units.torsion K := by
  obtain ⟨u₀, hu₀⟩ := hD.exists_unitScale_mem _ (surfacePart_mem_normOneSurface hy)
  refine ⟨u₀, fun u ↦ ?_⟩
  rw [mem_unitCone, and_iff_right fun w ↦ unitScale_pos (hy w) u, surfacePart_unitScale,
    ← hD.unitScale_mem_iff _ hu₀, unitScale_unitScale, inv_mul_cancel_right]

/-- Over a unit fundamental domain, a positive parameter `y` lies in exactly `w = #μ(K)` of the
translates `u (cone D)` of the cone by the units: summing a constant `c` over the units `u` with
`u⁻¹ y` in the cone gives `w • c`. -/
theorem hasSum_indicator_unitScale_inv_mem_unitCone (hD : IsUnitFundamentalDomain K D)
    {y : realSpace K} (hy : ∀ w, 0 < y w) {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (c : M) :
    HasSum ({u : (𝓞 K)ˣ | unitScale u⁻¹ y ∈ unitCone D}.indicator fun _ ↦ c)
      (Units.torsionOrder K • c) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hD.exists_forall_unitScale_mem_unitCone_iff_mul_inv_mem_torsion hy
  have hT : HasSum ((Units.torsion K : Set (𝓞 K)ˣ).indicator fun _ ↦ c)
      (Units.torsionOrder K • c) := by
    refine hasSum_subtype_iff_indicator.mp ?_
    have := Fintype.ofFinite (Units.torsion K)
    simpa [Units.torsionOrder, Nat.card_eq_fintype_card, Function.comp_def] using
      hasSum_fintype fun _ : Units.torsion K ↦ c
  refine ((Equiv.mulLeft u₀).hasSum_iff.mpr hT).congr_fun fun u ↦ ?_
  have h : u⁻¹ * u₀⁻¹ ∈ Units.torsion K ↔ u₀ * u ∈ Units.torsion K := by
    rw [← mul_inv_rev, inv_mem_iff]
  simp [Set.indicator_apply, hu₀, h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Unfolding over the unit orbit of a cone.** If `D` is a unit fundamental domain and `g` is
integrable for `dy / y`, then the integrals of `g ∘ (y ↦ |u|² y)` over the cone above `D`, summed
over all the units `u`, give `w = #μ(K)` times the integral of `g` over all parameters: the
translates of the cone by the units cover the positive orthant, every point exactly `w` times. -/
theorem hasSum_integral_unitCone_unitScale (hD : IsUnitFundamentalDomain K D)
    {g : realSpace K → E} (hg : Integrable g (archHaar K)) :
    HasSum (fun u : (𝓞 K)ˣ ↦ ∫ y in unitCone D, g (unitScale u y) ∂archHaar K)
      (Units.torsionOrder K • ∫ y, g y ∂archHaar K) := by
  have : Countable (𝓞 K) := Countable.of_moduleFinite (R := ℤ)
  have : Countable (𝓞 K)ˣ := Function.Injective.countable (Units.val_injective (α := 𝓞 K))
  have hmeas (u : (𝓞 K)ˣ) : Measurable (unitScale (K := K) u) :=
    Measurable.of_eval fun w ↦ by
      simpa only [unitScale_apply] using (measurable_pi_apply w).const_mul _
  have hcone := measurableSet_unitCone hD.measurableSet
  -- after the substitution `z = |u|² y`, the integrand is `g` on the translate `u (cone D)`
  set F : (𝓞 K)ˣ → realSpace K → E := fun u ↦ (unitScale u⁻¹ ⁻¹' unitCone D).indicator g
  have hF (u : (𝓞 K)ˣ) :
      ∫ y in unitCone D, g (unitScale u y) ∂archHaar K = ∫ z, F u z ∂archHaar K := by
    conv_rhs => rw [← map_archHaar_unitScale u]
    rw [integral_map (hmeas u).aemeasurable, ← integral_indicator hcone]
    · refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      classical
      simp only [F, Set.indicator_apply, Set.mem_preimage, unitScale_unitScale, inv_mul_cancel,
        unitScale_one]
    · rw [map_archHaar_unitScale]
      exact hg.1.indicator (hcone.preimage (hmeas u⁻¹))
  have hlim : ∀ᵐ z ∂archHaar K, HasSum (fun u ↦ F u z) (Units.torsionOrder K • g z) := by
    filter_upwards [ae_archHaar_pos] with z hz
    exact hD.hasSum_indicator_unitScale_inv_mem_unitCone hz (g z)
  have hbound : ∀ᵐ z ∂archHaar K, HasSum (fun u ↦ ‖F u z‖)
      (Units.torsionOrder K • ‖g z‖) := by
    filter_upwards [ae_archHaar_pos] with z hz
    exact (hD.hasSum_indicator_unitScale_inv_mem_unitCone hz ‖g z‖).congr_fun fun u ↦
      norm_indicator_eq_indicator_norm g z
  have hsum := hasSum_integral_of_dominated_convergence (fun u z ↦ ‖F u z‖)
    (fun u ↦ hg.1.indicator (hcone.preimage (hmeas u⁻¹)))
    (fun u ↦ ae_of_all _ fun z ↦ le_rfl) (hbound.mono fun z hz ↦ hz.summable)
    ((hg.norm.smul (Units.torsionOrder K : ℝ)).congr (hbound.mono fun z hz ↦ by
      simp [hz.tsum_eq, nsmul_eq_mul])) hlim
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ (Units.torsionOrder K)] at hsum ⊢
  rw [integral_smul] at hsum
  simpa only [hF] using hsum

end IsUnitFundamentalDomain

end TauCeti.LFunctions
