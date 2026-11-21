/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.Mass.Slice.Lipschitz
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Flat-norm continuity and slicing inequalities for Lipschitz slices

This file establishes normal flat-norm continuity and flat-mass slicing bounds for slices of
normal currents by Lipschitz functions, following Federer, *Geometric Measure Theory*,
§§4.3.1–4.3.2.

## Main declarations

* `Distribution.lintegral_normalFlatMass_slice_sub_slice_le`: normal flat continuity of slices
  (`∫⁻ t, F(⟨T, v, t⟩ - ⟨T, u, t⟩) ≤ ∫⁻ x, edist (v x) (u x) ∂(‖T‖ + ‖∂T‖)`).
* `Distribution.lintegral_normalFlatMass_slice_le`,
  `Distribution.lintegral_normalFlatMass_slice_le_of_innerProductSpace`: the flat-norm slicing
  inequality `∫⁻ t, F(⟨N, u, t⟩) ≤ K · F(N)` on inner product spaces (factor `k + 2` generally).

## References

* H. Federer, *Geometric Measure Theory*, §§4.3.1–4.3.2.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology ContDiff symmDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {k : ℕ} {K : ℝ≥0} {u v : E → ℝ}

/-- **Normal flat continuity of slices with respect to the slicing function.**
For a real normal `(k + 1)`-current `T` and Lipschitz functions `u, v` on `Ω`,
`∫⁻ t, F(⟨T, v, t⟩ - ⟨T, u, t⟩) ≤ ∫⁻ x, edist (v x) (u x) ∂(‖T‖ + ‖∂T‖)`. -/
theorem lintegral_normalFlatMass_slice_sub_slice_le {K₁ K₂ : ℝ≥0}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : LipschitzOnWith K₁ u Ω) (hv : LipschitzOnWith K₂ v Ω) :
    ∫⁻ t : ℝ, (slice T v t - slice T u t).normalFlatMass ≤
      ∫⁻ x : Ω, edist (v x) (u x) ∂(massMeasure T + massMeasure (T ∘L extDerivCLM)) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hu_meas : Measurable fun x : Ω => u x := hu.continuousOn.domRestrict.measurable
  have hv_meas : Measurable fun x : Ω => v x := hv.continuousOn.domRestrict.measurable
  let Au (t : ℝ) : Set Ω := {x : Ω | u x < t}
  let Av (t : ℝ) : Set Ω := {x : Ω | v x < t}
  have hAu (t : ℝ) : MeasurableSet (Au t) := measurableSet_lt hu_meas (measurable_const (a := t))
  have hAv (t : ℝ) : MeasurableSet (Av t) := measurableSet_lt hv_meas (measurable_const (a := t))
  -- Step 1: bound the mass of the difference of sublevel restrictions by the symmetric difference.
  have hmass_diff {m : ℕ} (Q : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) (t : ℝ) :
      mass (massRestrict Q (hAv t) - massRestrict Q (hAu t)) ≤
        massMeasure Q (Av t ∆ Au t) := by
    have hsplit : massRestrict Q (hAv t) - massRestrict Q (hAu t) =
        massRestrict Q ((hAv t).diff (hAu t)) - massRestrict Q ((hAu t).diff (hAv t)) := by
      rw [massRestrict_congr_set (T := Q) (hAv t) (((hAv t).inter (hAu t)).union
          ((hAv t).diff (hAu t))) (inter_union_sdiff _ _).symm,
        massRestrict_congr_set (T := Q) (hAu t) (((hAv t).inter (hAu t)).union
          ((hAu t).diff (hAv t))) (by rw [inter_comm]; exact (inter_union_sdiff _ _).symm),
        massRestrict_union ((hAv t).inter (hAu t)) ((hAv t).diff (hAu t)) disjoint_inf_sdiff,
        massRestrict_union ((hAv t).inter (hAu t)) ((hAu t).diff (hAv t))
          (disjoint_sdiff_self_right.mono_left inter_subset_left),
        add_sub_add_left_eq_sub]
    rw [hsplit, Set.symmDiff_def,
      measure_union disjoint_sdiff_sdiff ((hAu t).diff (hAv t))]
    exact mass_sub_le.trans <| add_le_add (mass_massRestrict_le _) (mass_massRestrict_le _)
  -- Step 2: decompose `⟨T, v, t⟩ - ⟨T, u, t⟩ = Rt + ∂St` to bound its normal flat mass a.e.
  let μ : Measure Ω := massMeasure T + massMeasure (T ∘L extDerivCLM)
  have hae_bound : ∀ᵐ t : ℝ, (slice T v t - slice T u t).normalFlatMass ≤ μ (Av t ∆ Au t) := by
    filter_upwards [ae_isNormal_massRestrict_lt_of_lipschitzOnWith hT hu,
      ae_isNormal_massRestrict_lt_of_lipschitzOnWith hT hv,
      ae_isNormal_slice_of_lipschitzOnWith hT hu,
      ae_isNormal_slice_of_lipschitzOnWith hT hv] with t hNu_r hNv_r hNu_s hNv_s
    let St := massRestrict T (hAv t) - massRestrict T (hAu t)
    let Rt := -(massRestrict (T ∘L extDerivCLM) (hAv t) -
      massRestrict (T ∘L extDerivCLM) (hAu t))
    have hdecomp : slice T v t - slice T u t = Rt + St ∘L extDerivCLM := by
      ext φ; simp [St, Rt, slice_apply _ hu_meas, slice_apply _ hv_meas]; ring
    have hRt_normal : IsNormal Rt := by
      have hRt_eq : Rt = (slice T v t - slice T u t) - St ∘L extDerivCLM := by
        rw [hdecomp]; abel
      rw [hRt_eq]
      exact (hNv_s.sub hNu_s).sub (hNv_r.sub hNu_r).comp_extDerivCLM
    refine ((slice T v t - slice T u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM
      hRt_normal (hNv_r.sub hNu_r) hdecomp).trans ?_
    rw [FunLike.coe_neg, mass_neg, _root_.add_apply, add_comm]
    exact add_le_add (hmass_diff T t) (hmass_diff (T ∘L extDerivCLM) t)
  -- Step 3: integrate the a.e. bound and apply the superlevel symmetric-difference identity via
  -- negation (`v x < t ↔ -t < -v x`).
  refine (lintegral_mono_ae hae_bound).trans_eq ?_
  calc ∫⁻ t : ℝ, μ (Av t ∆ Au t)
      = ∫⁻ t : ℝ, μ ({x : Ω | -t < -v x} ∆ {x : Ω | -t < -u x}) := by
        refine lintegral_congr fun t => ?_
        simp only [Av, Au, neg_lt_neg_iff]
    _ = ∫⁻ s : ℝ, μ ({x : Ω | s < -v x} ∆ {x : Ω | s < -u x}) :=
        lintegral_neg_eq_self (fun s => μ ({x : Ω | s < -v x} ∆ {x : Ω | s < -u x}))
    _ = ∫⁻ x : Ω, ‖-v x - -u x‖ₑ ∂μ :=
        (Measure.lintegral_enorm_sub_eq_lintegral_measure_symmDiff_setOf_lt μ
          hv_meas.neg.aemeasurable hu_meas.neg.aemeasurable).symm
    _ = ∫⁻ x : Ω, edist (v x) (u x) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [neg_sub_neg, ← eDist_eq_eNorm_sub, edist_comm]

private theorem lintegral_normalFlatMass_slice_le_aux
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hu : LipschitzOnWith K u Ω)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hR_maj : ∀ R : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ, IsLocallyNormal R →
      ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice R u t) ≤ m t) ∧ ∫⁻ t, m t ≤ c * mass R)
    (hS_maj : ∀ S : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] ℝ) →L[ℝ] ℝ, IsLocallyNormal S →
      ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ (∀ t, mass (slice S u t) ≤ m t) ∧ ∫⁻ t, m t ≤ c * mass S) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤ c * N.normalFlatMass := by
  rw [normalFlatMass_def]
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  let R := N - S ∘L extDerivCLM
  obtain ⟨mR, hmR_meas, hmR_le, hmR_int⟩ := hR_maj R hR.isLocallyNormal
  obtain ⟨mS, -, hmS_le, hmS_int⟩ := hS_maj S hS.isLocallyNormal
  have hae : ∀ᵐ t : ℝ, (slice N u t).normalFlatMass ≤ mR t + mS t := by
    filter_upwards [ae_isNormal_slice_of_lipschitzOnWith hR hu,
      ae_isNormal_slice_of_lipschitzOnWith hS hu] with t hNR hNS
    refine ((slice N u t).normalFlatMass_le_of_eq_add_comp_extDerivCLM hNR hNS.neg (by
      rw [neg_comp, slice_comp_extDerivCLM S u t, neg_neg,
        ← slice_add hR.isLocallyNormal hS.comp_extDerivCLM.isLocallyNormal]
      simp)).trans ?_
    rw [FunLike.coe_neg, mass_neg]
    exact add_le_add (hmR_le t) (hmS_le t)
  calc ∫⁻ t : ℝ, (slice N u t).normalFlatMass
      ≤ ∫⁻ t : ℝ, (mR t + mS t) := lintegral_mono_ae hae
    _ = (∫⁻ t : ℝ, mR t) + ∫⁻ t : ℝ, mS t := lintegral_add_left hmR_meas _
    _ ≤ c * mass R + c * mass S := add_le_add hmR_int hmS_int
    _ = c * (mass R + mass S) := (mul_add _ _ _).symm

/-- **Flat-mass slicing inequality** on a general normed space:
for a real normal `(k + 1)`-current `N` and `u` that is `K`-Lipschitz on `Ω`,
`∫⁻ t, F(⟨N, u, t⟩) ≤ (k + 2) * K * F(N)`. -/
theorem lintegral_normalFlatMass_slice_le
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hN : IsNormal N)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤
      (k + 2 : ℝ≥0∞) * (K : ℝ≥0∞) * N.normalFlatMass := by
  by_cases hK : K = 0
  · subst hK; simp [slice_eq_zero_of_lipschitzOnWith_zero hN.isLocallyNormal hu]
  refine lintegral_normalFlatMass_slice_le_aux hu (mul_ne_zero (by positivity) (by positivity))
    (by finiteness) (fun _ hR => ?_) fun _ hS => ?_
  · obtain ⟨m, hm1, hm2, hm3⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hR hu
    exact ⟨m, hm1, hm2, hm3.trans (by gcongr; norm_num)⟩
  · obtain ⟨m, hm1, hm2, hm3⟩ := exists_measurable_mass_slice_le_of_lipschitzOnWith hS hu
    exact ⟨m, hm1, hm2, by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hm3⟩

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}

/-- **Sharp flat-mass slicing inequality on an inner product space** (Federer 4.3.2(2)):
for a real normal `(k + 1)`-current `N` and `u` that is `K`-Lipschitz on `Ω`,
`∫⁻ t, F(⟨N, u, t⟩) ≤ K * F(N)`. -/
theorem lintegral_normalFlatMass_slice_le_of_innerProductSpace
    {N : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hN : IsNormal N)
    (hu : LipschitzOnWith K u Ω) :
    ∫⁻ t : ℝ, (slice N u t).normalFlatMass ≤ (K : ℝ≥0∞) * N.normalFlatMass := by
  by_cases hK : K = 0
  · subst hK; simp [slice_eq_zero_of_lipschitzOnWith_zero hN.isLocallyNormal hu]
  exact lintegral_normalFlatMass_slice_le_aux hu (by positivity) ENNReal.coe_ne_top
    (fun _ hR => exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hR hu)
    (fun _ hS => exists_measurable_mass_slice_le_of_lipschitzOnWith_of_innerProductSpace hS hu)

end InnerProductSpace

end Distribution
