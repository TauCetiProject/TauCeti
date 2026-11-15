/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Mass.Normal
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Slicing currents by a function

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `T` be a
`(k + 1)`-current on `Ω` (a continuous linear functional on the test `(k + 1)`-forms), and let
`u : E → ℝ` be measurable. The **slice** of `T` by `u` at `t` is the `k`-current

`⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}`,

where `⌞` is the Borel restriction of a current of locally finite mass
(`Distribution.massRestrict`) and `∂S = S ∘ d`. It measures the failure of restriction to the
sublevel set `{u < t}` to commute with the boundary. For a locally normal `T` and continuous `u`
the slice is supported in `spt T ∩ u⁻¹{t}`, and `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`.

For a smooth `u`, the slice is the weak limit of `-T ⌞ dfₘ` for smooth functions `fₘ` of `u`
increasing to the indicator of `{u < t}`; this follows from the Leibniz rule
`∂(fT) = f ∂T - T ⌞ df` and dominated convergence for the Borel restriction. Bounding the mass of
`T ⌞ dfₘ` against the mass measure `‖T‖` and integrating over `t` gives the **slicing
inequality**

`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) ∫ ‖du‖ d‖T‖`,

so for a normal current `T` and a smooth `u` with bounded derivative almost every slice is a
normal current. The mass here is taken with respect to the operator norm on alternating forms
(`Distribution.mass`); the factor `k + 1` comes from the unnormalized alternatization defining the
wedge `du ∧ φ`. Slices by merely Lipschitz functions are not treated here.

## Main declarations

* `Distribution.slice`: the slice `⟨T, u, t⟩`, zero by convention when `u` is not measurable.
* `Distribution.slice_comp_extDerivCLM`: the boundary law `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`.
* `Distribution.dsupport_slice_subset`: `spt ⟨T, u, t⟩ ⊆ spt T ∩ u⁻¹{t}`.
* `Distribution.lintegral_mass_slice_le`: the slicing inequality
  `∫ M(⟨T, u, t⟩) dt ≤ (k + 1) ∫ ‖du‖ d‖T‖` for smooth `u`.
* `Distribution.lintegral_mass_slice_le_mul_mass`: if `‖du‖ ≤ L` on `Ω`, then
  `∫ M(⟨T, u, t⟩) dt ≤ (k + 1) L M(T)`.
* `Distribution.ae_mass_slice_lt_top`, `Distribution.ae_isNormal_slice`: almost every slice has
  finite mass, and almost every slice of a normal current is normal.

## References

* H. Federer, *Geometric Measure Theory*, §4.2.1 (slicing normal currents by a Lipschitz
  function, and the slicing inequality).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5 (slicing).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction
open scoped ENNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {u : E → ℝ} {t : ℝ}

/-! ### Definition and the boundary law -/

open scoped Classical in
/-- The **slice** `⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}` of a `(k + 1)`-current `T` on `Ω`
by a measurable function `u : E → ℝ` at the level `t`, a `k`-current on `Ω`. Here `⌞` is the
Borel restriction `Distribution.massRestrict` to the sublevel set `{x ∈ Ω | u x < t}`, which is
meaningful when `T` and `∂T` have locally finite mass. If `u` is not measurable, the slice is
zero by convention. -/
def slice (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) (t : ℝ) :
    𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ :=
  if hu : Measurable u then
    let hA := measurableSet_lt (hu.comp measurable_subtype_coe) (measurable_const (a := t))
    massRestrict T hA ∘L extDerivCLM - massRestrict (T ∘L extDerivCLM) hA
  else 0

section Defs

variable (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ)

/-- For measurable `u`, the slice evaluates as `(T ⌞ {u < t}) (dφ) - ((∂T) ⌞ {u < t}) φ`. -/
theorem slice_apply (hu : Measurable u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    slice T u t φ =
      massRestrict T (measurableSet_lt (hu.comp measurable_subtype_coe) (measurable_const (a := t)))
          (extDerivCLM φ) -
        massRestrict (T ∘L extDerivCLM)
          (measurableSet_lt (hu.comp measurable_subtype_coe) (measurable_const (a := t))) φ := by
  simp [slice, hu]

/-- The slice by a non-measurable function is zero by convention. -/
@[simp]
theorem slice_of_not_measurable (hu : ¬Measurable u) : slice T u t = 0 := by
  simp [slice, hu]

/-- The slice of the zero current is zero. -/
@[simp]
theorem slice_zero : slice (0 : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) u t = 0 := by
  by_cases hu : Measurable u
  · ext φ
    simp [slice_apply _ hu]
  · simp [hu]

end Defs

/-- **The boundary of a slice.** `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`. -/
theorem slice_comp_extDerivCLM (T : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ)
    (t : ℝ) : slice T u t ∘L extDerivCLM = -slice (T ∘L extDerivCLM) u t := by
  by_cases hu : Measurable u
  · ext φ
    have hdd : (T ∘L extDerivCLM) ∘L extDerivCLM = 0 := by
      rw [ContinuousLinearMap.comp_assoc, extDerivCLM_comp_extDerivCLM,
        ContinuousLinearMap.comp_zero]
    simp [slice_apply _ hu, hdd]
  · simp [hu]

/-! ### Support -/

/-- **Support of a slice.** For a locally normal current `T` and a continuous function `u`, the
slice `⟨T, u, t⟩` is supported in `spt T ∩ u⁻¹{t}`. -/
theorem dsupport_slice_subset {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : Continuous u) (t : ℝ) :
    dsupport (slice T u t) ⊆ dsupport T ∩ u ⁻¹' {t} := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hum : Measurable u := hu.measurable
  have hA : MeasurableSet {x : Ω | u x < t} :=
    measurableSet_lt (hum.comp measurable_subtype_coe) measurable_const
  -- Off `spt T`, both Borel restrictions vanish.
  have hv₁ : IsVanishingOn (slice T u t) (dsupport T)ᶜ := fun φ hφ => by
    have h₁ : massRestrict T hA (extDerivCLM φ) = 0 :=
      isVanishingOn_compl_dsupport (massRestrict T hA) _ ((tsupport_extDerivCLM_subset φ).trans
        (hφ.trans (compl_subset_compl.2 (dsupport_massRestrict_subset hA))))
    have h₂ : massRestrict (T ∘L extDerivCLM) hA φ = 0 :=
      isVanishingOn_compl_dsupport (massRestrict (T ∘L extDerivCLM) hA) _
        (hφ.trans (compl_subset_compl.2 ((dsupport_massRestrict_subset hA).trans
          (dsupport_comp_extDerivCLM_subset T))))
    simp [slice_apply _ hum, h₁, h₂]
  -- On `{u < t}`, both restrictions are the unrestricted currents, so their difference vanishes.
  have hv₂ : IsVanishingOn (slice T u t) {x | u x < t} := fun φ hφ => by
    have h₁ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφ (tsupport_extDerivCLM_subset φ h))
    have h₂ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφ h)
    rw [slice_apply _ hum, massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ h₁),
      massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ h₂)]
    simp
  -- On `{u > t}`, both restrictions vanish.
  have hv₃ : IsVanishingOn (slice T u t) {x | t < u x} := fun φ hφ => by
    have h₁ : ∀ x : Ω, x ∈ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h =>
        lt_asymm (a := u x) (b := t) hx (hφ (tsupport_extDerivCLM_subset φ h))
    have h₂ : ∀ x : Ω, x ∈ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => lt_asymm (a := u x) (b := t) hx (hφ h)
    rw [slice_apply _ hum, massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ h₁),
      massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ h₂), sub_zero]
  intro x hx
  refine ⟨?_, ?_⟩
  · by_contra h
    exact (notMem_dsupport_iff x).2 ⟨_, hv₁, isClosed_dsupport.isOpen_compl, h⟩ hx
  rcases lt_trichotomy (u x) t with h | h | h
  · exact ((notMem_dsupport_iff x).2 ⟨_, hv₂, isOpen_lt hu continuous_const, h⟩ hx).elim
  · exact h
  · exact ((notMem_dsupport_iff x).2 ⟨_, hv₃, isOpen_lt continuous_const hu, h⟩ hx).elim

/-! ### The slicing inequality for smooth functions

The slice `⟨T, u, t⟩` is approximated by `-T ⌞ dfₘ` for the smooth multipliers
`fₘ x = ψ(cₘ (t - u x))`, where `ψ = Real.smoothTransition` and `cₘ = m + 1`. They increase to the
indicator of `{u < t}`, and `‖dfₘ‖ = cₘ ψ'(cₘ (t - u)) ‖du‖`, whose integral in `t` is `‖du‖`. -/

/-- **Mass of a slice as a limit.** The slice is the weak limit of `-T ⌞ dfₘ` for
`fₘ x = ψ((m + 1) (t - u x))`, so its mass is at most the `liminf` of the weighted integrals
`(k + 1) ∫ (m + 1) ψ'((m + 1) (t - u)) ‖du‖ d‖T‖`. -/
private theorem mass_slice_le_liminf {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    mass (slice T u t) ≤ liminf (fun m : ℕ => (k + 1 : ℝ≥0∞) *
      ∫⁻ x, ENNReal.ofReal (((m : ℝ) + 1) *
        deriv Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) * ‖fderiv ℝ u x‖ₑ
        ∂massMeasure T) atTop := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hum : Measurable u := hu.continuous.measurable
  have hA : MeasurableSet {x : Ω | u x < t} :=
    measurableSet_lt (hum.comp measurable_subtype_coe) measurable_const
  have hf (m : ℕ) : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  have hfC (m : ℕ) : ∀ x ∈ Ω, |Real.smoothTransition (((m : ℝ) + 1) * (t - u x))| ≤ 1 :=
    fun x _ => Real.smoothTransition.abs_le_one _
  have hlim (x : Ω) : Tendsto (fun m : ℕ => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
      atTop (𝓝 ({y : Ω | u y < t}.indicator 1 x)) := by
    refine tendsto_const_nhds.congr' ?_
    by_cases hxt : u x < t
    · have htop : Tendsto (fun m : ℕ => ((m : ℝ) + 1) * (t - u x)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
          (sub_pos.2 hxt)
      filter_upwards [htop.eventually_ge_atTop 1] with m hm
      simp [Real.smoothTransition.one_of_one_le hm, hxt]
    · refine .of_forall fun m => ?_
      have hle : ((m : ℝ) + 1) * (t - u x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 (not_lt.1 hxt))
      simp [Real.smoothTransition.zero_of_nonpos hle, hxt]
  -- By the Leibniz rule `∂(fT) = f ∂T - T ⌞ df`, the slice is the weak limit of `-T ⌞ dfₘ`.
  refine (mass_le_liminf (fs := fun m =>
      -(T ∘ oneFormWedgeCLM (k := k) (contDiff_infty_iff_fderiv.1 (hf m)).2)) fun φ => ?_).trans
    (liminf_le_liminf (.of_forall fun m => ?_))
  · have h := (tendsto_apply_smulLeftCLM_massRestrict hT₁ hA hf hfC hlim (extDerivCLM φ)).sub
      (tendsto_apply_smulLeftCLM_massRestrict hT₂ hA hf hfC hlim φ)
    rw [← slice_apply _ hum] at h
    refine h.congr fun m => ?_
    have hL := DFunLike.congr_fun (ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM T (hf m)) φ
    simp only [ContinuousLinearMap.comp_apply, sub_apply] at hL
    simp [hL]
  · rw [mass_neg]
    refine (mass_comp_oneFormWedgeCLM_le_lintegral hT₁ _).trans_eq ?_
    simp_rw [(hu.differentiable (by simp) _).enorm_fderiv_smoothTransition_mul_sub
      (c := (m : ℝ) + 1) (by positivity)]

/-- A measurable majorant of `t ↦ M(⟨T, u, t⟩)` whose integral is at most
`(k + 1) ∫ ‖du‖ d‖T‖`. -/
private theorem exists_measurable_mass_slice_le {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ t, mass (slice T u t) ≤ G t) ∧
      ∫⁻ t, G t ≤ (k + 1) * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure T := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hum : Measurable fun x : Ω => u x := hu.continuous.measurable.comp measurable_subtype_coe
  have hdu : Measurable fun x : Ω => ‖fderiv ℝ u x‖ₑ := (continuous_eNorm.comp
    ((hu.continuous_fderiv (by simp)).comp continuous_subtype_val)).measurable
  have hg' (m : ℕ) :=
    Real.smoothTransition.measurable_ofReal_mul_deriv_mul_sub_mul hum hdu ((m : ℝ) + 1)
  have hg (m : ℕ) : Measurable fun t => (k + 1 : ℝ≥0∞) *
      ∫⁻ x, ENNReal.ofReal (((m : ℝ) + 1) *
        deriv Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) * ‖fderiv ℝ u x‖ₑ
        ∂massMeasure T :=
    (hg' m).lintegral_prod_right'.const_mul _
  refine ⟨_, .liminf hg, mass_slice_le_liminf hT hu, (lintegral_liminf_le hg).trans_eq ?_⟩
  simp_rw [lintegral_const_mul _ (hg' _).lintegral_prod_right',
    Real.smoothTransition.lintegral_lintegral_ofReal_mul_deriv_mul_sub_mul _ hum hdu
      (Nat.cast_add_one_pos _)]
  exact liminf_const _

/-- **The slicing inequality.** For a locally normal `(k + 1)`-current `T` and a smooth
`u : E → ℝ`, `∫ M(⟨T, u, t⟩) dt ≤ (k + 1) ∫ ‖du‖ d‖T‖`. -/
theorem lintegral_mass_slice_le {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) :
    ∫⁻ t, mass (slice T u t) ≤ (k + 1) * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure T := by
  obtain ⟨G, -, hG, hGint⟩ := exists_measurable_mass_slice_le hT hu
  exact (lintegral_mono hG).trans hGint

/-- **The slicing inequality with a Lipschitz bound.** If `‖du‖ ≤ L` on `Ω`, then
`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) L M(T)`. -/
theorem lintegral_mass_slice_le_mul_mass {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) {L : ℝ≥0∞}
    (hdu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ₑ ≤ L) :
    ∫⁻ t, mass (slice T u t) ≤ (k + 1) * L * mass T := by
  rw [mul_assoc]
  exact (lintegral_mass_slice_le hT hu).trans
    (by gcongr; exact lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass fun x => hdu x x.2)

/-- If `∫ ‖du‖ d‖T‖` is finite, then almost every slice `⟨T, u, t⟩` has finite mass. -/
theorem ae_mass_slice_lt_top {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (hfin : ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure T ≠ ⊤) :
    ∀ᵐ t, mass (slice T u t) < ⊤ := by
  obtain ⟨G, hGm, hG, hGint⟩ := exists_measurable_mass_slice_le hT hu
  filter_upwards [ae_lt_top hGm (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) hfin) hGint)] with t ht
  exact (hG t).trans_lt ht

/-- **Slices of normal currents are normal.** If `T` is a normal `(k + 1)`-current and `u` is
smooth with `‖du‖ ≤ L < ⊤` on `Ω`, then almost every slice `⟨T, u, t⟩` is a normal current. -/
theorem ae_isNormal_slice {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : ContDiff ℝ ∞ u) {L : ℝ≥0∞} (hL : L ≠ ⊤) (hdu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ₑ ≤ L) :
    ∀ᵐ t, IsNormal (slice T u t) := by
  have hfin {j : ℕ} {S : 𝓓(Ω, E [⋀^Fin (j + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hS : IsNormal S) :
      ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure S ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hL hS.mass_ne_top)
      (lintegral_massMeasure_le_mul_mass hS.isLocallyNormal.hasLocallyFiniteMass fun x => hdu x x.2)
  cases k with
  | zero =>
    filter_upwards [ae_mass_slice_lt_top hT.isLocallyNormal hu (hfin hT)] with t ht
    exact isNormal_finZero_iff.2 ht.ne
  | succ j =>
    have hT' : IsNormal (T ∘L extDerivCLM) := hT.comp_extDerivCLM
    filter_upwards [ae_mass_slice_lt_top hT.isLocallyNormal hu (hfin hT),
      ae_mass_slice_lt_top hT'.isLocallyNormal hu (hfin hT')] with t ht ht'
    refine isNormal_succ_iff.2 ⟨ht.ne, ?_⟩
    simpa [slice_comp_extDerivCLM, mass_neg] using ht'.ne

end Distribution
