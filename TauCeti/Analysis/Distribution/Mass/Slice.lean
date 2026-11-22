/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Mass.Normal
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Slicing currents by a function

Let `Ω` be an open set of a real normed space `E`, let `T` be a
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
wedge `du ∧ φ`. If `E` is infinite-dimensional, every test form is zero, so every current and every
slice is zero.

The slice depends on `u` only through its sublevel sets, so when functions `vᵢ` converge pointwise
on `Ω` to `u`, the slices `⟨T, vᵢ, t⟩` converge to `⟨T, u, t⟩` at every level `t` that is charged
neither by `‖T‖` nor by `‖∂T‖`, which excludes only countably many levels. Approximating a function
`u` that is `L`-Lipschitz on `Ω` by smooth functions with `‖dvⱼ‖ ≤ L`, lower semicontinuity of mass
and Fatou's lemma carry the slicing inequality over to `u`, also localized to a strip:

`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) L M(T)`, `∫_a^b M(⟨T, u, t⟩) dt ≤ (k + 1) L ‖T‖{a < u < b}`.

For the strip, `u` is truncated to `[a', b']` with `a < a' < b' < b` before smoothing, so that the
smooth approximations have vanishing differential off the strip. In particular almost every slice
of a normal current by a Lipschitz function is normal.

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
* `Distribution.slice_congr`: the slice depends only on the sublevel set `{x ∈ Ω | u x < t}`.
* `Distribution.tendsto_slice_apply`: slices converge when the slicing functions converge pointwise
  on `Ω`, at levels charged neither by `‖T‖` nor by `‖∂T‖`.
* `Distribution.lintegral_mass_slice_le_mul_mass_of_lipschitzOnWith`: the slicing inequality
  `∫ M(⟨T, u, t⟩) dt ≤ (k + 1) L M(T)` for `u` that is `L`-Lipschitz on `Ω`.
* `Distribution.setLIntegral_mass_slice_le_of_lipschitzOnWith`: its localization
  `∫_a^b M(⟨T, u, t⟩) dt ≤ (k + 1) L ‖T‖{a < u < b}` to a strip.
* `Distribution.ae_mass_slice_lt_top_of_lipschitzOnWith`,
  `Distribution.ae_isNormal_slice_of_lipschitzOnWith`: almost every Lipschitz slice of a current of
  finite mass has finite mass, and almost every Lipschitz slice of a normal current is normal.

## References

* H. Federer, *Geometric Measure Theory*, §4.2.1 (slicing normal currents by a Lipschitz
  function, and the slicing inequality on strips `{a < u < b}`).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5 (slicing).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction
open scoped ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    let hA := measurableSet_lt (hu.comp measurable_subtypeVal) (measurable_const (a := t))
    massRestrict T hA ∘L extDerivCLM - massRestrict (T ∘L extDerivCLM) hA
  else 0

section Defs

variable (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ)

/-- For measurable `u`, the slice evaluates as `(T ⌞ {u < t}) (dφ) - ((∂T) ⌞ {u < t}) φ`. -/
theorem slice_apply (hu : Measurable u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    slice T u t φ =
      massRestrict T (measurableSet_lt (hu.comp measurable_subtypeVal) (measurable_const (a := t)))
          (extDerivCLM φ) -
        massRestrict (T ∘L extDerivCLM)
          (measurableSet_lt (hu.comp measurable_subtypeVal) (measurable_const (a := t))) φ := by
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
    measurableSet_lt (hum.comp measurable_subtypeVal) measurable_const
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
    measurableSet_lt (hum.comp measurable_subtypeVal) measurable_const
  have hf (m : ℕ) : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  have hfC (m : ℕ) : ∀ x ∈ Ω, |Real.smoothTransition (((m : ℝ) + 1) * (t - u x))| ≤ 1 :=
    fun x _ => Real.smoothTransition.abs_le_one _
  have hlim (x : Ω) : Tendsto (fun m : ℕ => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
      atTop (𝓝 ({y : Ω | u y < t}.indicator 1 x)) := by
    simpa [sub_pos] using Real.smoothTransition.tendsto_indicator (fun y : Ω => t - u y) 0 x
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
  by_cases hE : FiniteDimensional ℝ E
  swap
  · -- In infinite dimension every test form is zero, so every slice has mass zero.
    refine ⟨0, measurable_const, fun t => ?_, by simp⟩
    rw [Pi.zero_apply, nonpos_iff_eq_zero, mass_eq_zero_iff]
    exact funext fun φ => by simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hum : Measurable fun x : Ω => u x := hu.continuous.measurable.comp measurable_subtypeVal
  have hdu : Measurable fun x : Ω => ‖fderiv ℝ u x‖ₑ := (continuous_eNorm.comp
    ((hu.continuous_fderiv (by simp)).comp continuous_subtypeVal)).measurable
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
    (by gcongr
        exact lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass fun x => hdu x x.property)

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
      (lintegral_massMeasure_le_mul_mass hS.isLocallyNormal.hasLocallyFiniteMass fun x => hdu x
          x.property)
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

/-! ### Convergence of slices

The slice `⟨T, u, t⟩` depends on `u` only through the sublevel set `{x ∈ Ω | u x < t}`. If `vᵢ → u`
pointwise on `Ω`, these sublevel sets converge to that of `u` off the level set `u⁻¹{t}`, so the
slices converge at every level `t` charged neither by `‖T‖` nor by `‖∂T‖`. Since these measures are
σ-finite, Mathlib's `MeasureTheory.Measure.countable_meas_level_set_pos` shows that this excludes
only countably many levels. -/

/-- A slice depends on the slicing function only through its sublevel set in `Ω`. -/
theorem slice_congr (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) {v : E → ℝ}
    (hu : Measurable u) (hv : Measurable v) (h : {x : Ω | u x < t} = {x : Ω | v x < t}) :
    slice T u t = slice T v t := by
  ext φ
  have key {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A = B) :
      massRestrict T hA = massRestrict T hB ∧
        massRestrict (T ∘L extDerivCLM) hA = massRestrict (T ∘L extDerivCLM) hB := by
    subst hAB
    exact ⟨rfl, rfl⟩
  obtain ⟨h₁, h₂⟩ := key _ _ h
  rw [slice_apply _ hu, slice_apply _ hv, h₁, h₂]

/-- **Convergence of slices.** If measurable functions `vᵢ` converge pointwise on `Ω` to a
measurable `u`, and neither `‖T‖` nor `‖∂T‖` charges the level set `u⁻¹{t}`, then
`⟨T, vᵢ, t⟩ → ⟨T, u, t⟩` on every test form. -/
theorem tendsto_slice_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) {v : ι → E → ℝ} (hv : ∀ i, Measurable (v i))
    (hu : Measurable u) (hlim : ∀ x ∈ Ω, Tendsto (fun i => v i x) l (𝓝 (u x)))
    (hT : massMeasure T {x | u x = t} = 0)
    (hdT : massMeasure (T ∘L extDerivCLM) {x | u x = t} = 0) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun i => slice T (v i) t φ) l (𝓝 (slice T u t φ)) := by
  -- Off the level set, membership in the sublevel sets of `vᵢ` eventually matches that of `u`.
  have hev (x : Ω) (hx : x ∉ {x : Ω | u x = t}) : ∀ᶠ i in l, (v i x < t ↔ u x < t) := by
    rcases lt_or_gt_of_ne hx with h | h
    · filter_upwards [(hlim x x.property).eventually_lt_const h] with i hi
      simp [hi, h]
    · filter_upwards [(hlim x x.property).eventually_const_lt h] with i hi
      simp [hi.not_gt, h.not_gt]
  simp_rw [slice_apply _ (hv _), slice_apply _ hu]
  exact (tendsto_massRestrict_apply _ _ (measure_eq_zero_iff_ae_notMem.1 hT |>.mono hev) _).sub
    (tendsto_massRestrict_apply _ _ (measure_eq_zero_iff_ae_notMem.1 hdT |>.mono hev) _)

/-- If smooth functions `vⱼ` converge pointwise on `Ω` to a measurable `u`, and
`∫ ‖dvⱼ‖ d‖T‖ ≤ C` for all `j`, then `t ↦ M(⟨T, u, t⟩)` has, off a null set, a measurable majorant
of integral at most `(k + 1) C`: the `liminf` of the majorants from the smooth slicing
inequality, by convergence of slices, lower semicontinuity of mass and Fatou's lemma. -/
private theorem exists_measurable_ae_mass_slice_le_of_tendsto
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {v : ℕ → E → ℝ}
    (hv : ∀ j, ContDiff ℝ ∞ (v j)) (hu : Measurable u)
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => v j x) atTop (𝓝 (u x))) {C : ℝ≥0∞}
    (hC : ∀ j, ∫⁻ x, ‖fderiv ℝ (v j) x‖ₑ ∂massMeasure T ≤ C) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ᵐ t, mass (slice T u t) ≤ G t) ∧
      ∫⁻ t, G t ≤ (k + 1) * C := by
  choose G hGm hG hGint using fun j => exists_measurable_mass_slice_le hT (hv j)
  have hum : Measurable fun x : Ω => u x := hu.comp measurable_subtypeVal
  have hcount := (Measure.countable_meas_level_set_pos (μ := massMeasure T) hum).union
    (Measure.countable_meas_level_set_pos (μ := massMeasure (T ∘L extDerivCLM)) hum)
  refine ⟨fun t => liminf (fun j => G j t) atTop, .liminf hGm, ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hcount.measure_zero volume)] with t ht
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, nonpos_iff_eq_zero] at ht
    exact (mass_le_liminf (tendsto_slice_apply T (fun j => (hv j).continuous.measurable) hu hlim
      ht.1 ht.2)).trans (liminf_le_liminf (.of_forall fun j => hG j t))
  · refine (lintegral_liminf_le hGm).trans (liminf_le_of_frequently_le' (.of_forall fun j => ?_))
    exact (hGint j).trans (by gcongr; exact hC j)

/-! ### The slicing inequality for Lipschitz functions

A Lipschitz function `u` is the pointwise limit of smooth functions `vⱼ` with `‖dvⱼ‖ ≤ Lip(u)`, so
the slicing inequality passes to `u` through the convergence of slices. To localize it to a strip
`{a < u < b}`, `u` is first truncated to `max a' (min u b')` for `a < a' < b' < b`: mollifying the
truncation on a scale finer than `a' - a` and `b - b'` gives smooth functions whose differential
vanishes off the strip. -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth approximation of the truncation `max a (min w b)` of a Lipschitz function `w`, within
`2η`, whose differential is bounded by `Lip(w)` and vanishes off the strip `{a < w < b}`. -/
private theorem exists_contDiff_approx_truncation [FiniteDimensional ℝ E] {w : E → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) {a b η : ℝ} (hη : 0 < η) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, ‖fderiv ℝ g x‖ₑ ≤ L) ∧
      (∀ x, w x ∉ Ioo a b → fderiv ℝ g x = 0) ∧ ∀ x, dist (g x) (max a (min (w x) b)) ≤ 2 * η := by
  set c : E → ℝ := fun x => max (a + η) (min (w x) (b - η))
  set r := η / (L + 1)
  have hLr : (L : ℝ) * r < η := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [L.coe_nonneg]
  obtain ⟨g, hsmooth, hLip, herr, hconst⟩ :=
    ((hw.min_const _).const_max _).exists_contDiff_lipschitzWith_dist_lt_fderiv_eq_zero
      (f := c) (r := r) (by positivity) hη
  -- On the ball of radius `r`, `w` moves by less than `η`.
  have hnear (x z : E) (hz : z ∈ Metric.ball x r) : |w z - w x| < η := by
    refine (hw.dist_le_mul z x).trans_lt (lt_of_le_of_lt ?_ hLr)
    exact mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hz).le L.coe_nonneg
  refine ⟨g, hsmooth, fun x => ?_, fun x hx => ?_, fun x => ?_⟩
  · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ hLip)
  · -- Off the strip, the truncation `c` is constant on the ball of radius `r` about `x`.
    refine hconst x fun z hz => ?_
    have h := abs_lt.1 (hnear x z hz)
    rcases not_and_or.1 hx with hxa | hxb
    · replace hxa := not_lt.1 hxa
      have hz : min (w z) (b - η) ≤ a + η := (min_le_left _ _).trans (by linarith)
      have hx : min (w x) (b - η) ≤ a + η := (min_le_left _ _).trans (by linarith)
      simp only [c, max_eq_left hz, max_eq_left hx]
    · replace hxb := not_lt.1 hxb
      simp only [c, min_eq_right (by linarith : b - η ≤ w z),
        min_eq_right (by linarith : b - η ≤ w x)]
  · refine (dist_triangle _ (c x) _).trans ?_
    have h₁ : dist (c x) (max a (min (w x) b)) ≤ η := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp [abs_of_pos hη]) ?_)
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp [hη.le]) ?_)
      simp [abs_of_pos hη]
    linarith [(herr x).le]

/-- The Lipschitz slicing inequality with a measurable majorant, for a Lipschitz function on all
of `E`. -/
private theorem exists_measurable_ae_mass_slice_le_of_lipschitzWith [FiniteDimensional ℝ E]
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {L : ℝ≥0}
    (hu : LipschitzWith L u) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ᵐ t, mass (slice T u t) ≤ G t) ∧
      ∫⁻ t, G t ≤ (k + 1) * (L * mass T) := by
  obtain ⟨v, hv, -, hvL, -, hlim⟩ := hu.exists_seq_contDiff_lipschitzWith_tendsto
  refine exists_measurable_ae_mass_slice_le_of_tendsto hT hv hu.continuous.measurable
    (fun x _ => hlim x) fun j => lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass
      fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ (hvL j))

/-- The Lipschitz slicing inequality on a strip, with a measurable majorant, for the truncation
`max a (min u b)` of a Lipschitz function on all of `E`. -/
private theorem exists_measurable_ae_mass_slice_truncation_le [FiniteDimensional ℝ E]
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {L : ℝ≥0}
    (hu : LipschitzWith L u) {a b : ℝ} (hab : a < b) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ᵐ t, mass (slice T (fun x => max a (min (u x) b)) t) ≤ G t) ∧
      ∫⁻ t, G t ≤ (k + 1) * (L * massMeasure T {x | u x ∈ Ioo a b}) := by
  have hη (j : ℕ) : 0 < (b - a) * (1 / ((j : ℝ) + 1)) := by
    have := sub_pos.2 hab
    positivity
  choose v hv hvL hv0 hvd using fun j : ℕ => exists_contDiff_approx_truncation hu (hη j)
  refine exists_measurable_ae_mass_slice_le_of_tendsto hT hv
    (continuous_const.max (hu.continuous.min continuous_const)).measurable (fun x _ => ?_)
    fun j => ?_
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => hvd j x) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)).const_mul 2
  · refine (lintegral_mono fun x => ?_).trans (lintegral_indicator_const_le _ _)
    by_cases hx : (x : Ω) ∈ {x : Ω | u x ∈ Ioo a b}
    · rw [indicator_of_mem hx]
      exact hvL j x
    · rw [indicator_of_notMem hx, hv0 j x hx, ← ofReal_norm]
      simp

/-- A function that is Lipschitz on `Ω` agrees on `Ω` with a Lipschitz function `w` on `E`, by
McShane extension. Its slices are those of `w` if it is measurable, and zero otherwise. -/
private theorem exists_lipschitzWith_eqOn_slice {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    {L : ℝ≥0} (hu : LipschitzOnWith L u Ω) :
    ∃ w : E → ℝ, LipschitzWith L w ∧ EqOn u w Ω ∧ ∀ t,
      slice T u t = 0 ∨ slice T u t = slice T w t := by
  obtain ⟨w, hw, huw⟩ := hu.extend_real
  refine ⟨w, hw, huw, fun t => ?_⟩
  by_cases hum : Measurable u
  · exact .inr (slice_congr T hum hw.continuous.measurable (by ext x; simp [huw x.property]))
  · exact .inl (slice_of_not_measurable T hum)

/-- In infinite dimension every test form is zero, so every slice has mass zero. -/
private theorem mass_slice_eq_zero_of_not_finiteDimensional (hE : ¬FiniteDimensional ℝ E)
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) (t : ℝ) :
    mass (slice T u t) = 0 := by
  rw [mass_eq_zero_iff]
  exact funext fun φ => by simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]

/-- The Lipschitz slicing inequality with a measurable majorant. -/
private theorem exists_measurable_ae_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {L : ℝ≥0}
    (hu : LipschitzOnWith L u Ω) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ᵐ t, mass (slice T u t) ≤ G t) ∧
      ∫⁻ t, G t ≤ (k + 1) * L * mass T := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · exact ⟨0, measurable_const, .of_forall fun t => by
      simp [mass_slice_eq_zero_of_not_finiteDimensional hE], by simp⟩
  obtain ⟨w, hw, -, hslice⟩ := exists_lipschitzWith_eqOn_slice (T := T) hu
  obtain ⟨G, hGm, hG, hGint⟩ := exists_measurable_ae_mass_slice_le_of_lipschitzWith hT hw
  refine ⟨G, hGm, hG.mono fun t ht => ?_, hGint.trans_eq (mul_assoc _ _ _).symm⟩
  rcases hslice t with h | h <;> simp [h, ht]

/-- **The slicing inequality for Lipschitz functions.** For a locally normal `(k + 1)`-current `T`
and a function `u` that is `L`-Lipschitz on `Ω`, `∫ M(⟨T, u, t⟩) dt ≤ (k + 1) L M(T)`. -/
theorem lintegral_mass_slice_le_mul_mass_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {L : ℝ≥0}
    (hu : LipschitzOnWith L u Ω) :
    ∫⁻ t, mass (slice T u t) ≤ (k + 1) * L * mass T := by
  obtain ⟨G, -, hG, hGint⟩ := exists_measurable_ae_mass_slice_le_of_lipschitzOnWith hT hu
  exact (lintegral_mono_ae hG).trans hGint

/-- **The slicing inequality on a strip.** For a locally normal `(k + 1)`-current `T` and a function
`u` that is `L`-Lipschitz on `Ω`, the slices at levels in `(a, b)` satisfy
`∫_a^b M(⟨T, u, t⟩) dt ≤ (k + 1) L ‖T‖{a < u < b}`. -/
theorem setLIntegral_mass_slice_le_of_lipschitzOnWith
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {L : ℝ≥0}
    (hu : LipschitzOnWith L u Ω) (a b : ℝ) :
    ∫⁻ t in Ioo a b, mass (slice T u t) ≤ (k + 1) * L * massMeasure T {x | u x ∈ Ioo a b} := by
  by_cases hab : a < b
  swap
  · simp [Ioo_eq_empty hab]
  by_cases hE : FiniteDimensional ℝ E
  swap
  · simp [mass_slice_eq_zero_of_not_finiteDimensional hE]
  obtain ⟨w, hw, huw, hslice⟩ := exists_lipschitzWith_eqOn_slice (T := T) hu
  obtain ⟨G, hGm, hG, hGint⟩ := exists_measurable_ae_mass_slice_truncation_le hT hw hab
  have hset : {x : Ω | w x ∈ Ioo a b} = {x : Ω | u x ∈ Ioo a b} := by
    ext x
    simp [huw x.property]
  rw [hset, ← mul_assoc] at hGint
  refine (setLIntegral_mono_ae hGm.aemeasurable (hG.mono fun t ht hts => ?_)).trans
    ((setLIntegral_le_lintegral _ _).trans hGint)
  -- At levels in `(a, b)`, slicing by `w` or by its truncation to `[a, b]` is the same.
  have htrunc : slice T w t = slice T (fun x => max a (min (w x) b)) t := by
    refine slice_congr T hw.continuous.measurable
      (continuous_const.max (hw.continuous.min continuous_const)).measurable (ext fun x => ?_)
    simp only [mem_ofPred_eq, max_lt_iff, min_lt_iff, hts.1, true_and]
    exact ⟨Or.inl, fun h => h.resolve_right hts.2.not_gt⟩
  rcases hslice t with h | h <;> simp [h, htrunc, ht]

/-- If `T` is a locally normal `(k + 1)`-current of finite mass and `u` is Lipschitz on `Ω`, then
almost every slice `⟨T, u, t⟩` has finite mass. -/
theorem ae_mass_slice_lt_top_of_lipschitzOnWith {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hfin : mass T ≠ ⊤) {L : ℝ≥0} (hu : LipschitzOnWith L u Ω) :
    ∀ᵐ t, mass (slice T u t) < ⊤ := by
  obtain ⟨G, hGm, hG, hGint⟩ := exists_measurable_ae_mass_slice_le_of_lipschitzOnWith hT hu
  filter_upwards [hG, ae_lt_top hGm (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hfin) hGint)] with t ht ht'
  exact ht.trans_lt ht'

/-- **Lipschitz slices of normal currents are normal.** If `T` is a normal `(k + 1)`-current and `u`
is Lipschitz on `Ω`, then almost every slice `⟨T, u, t⟩` is a normal current. -/
theorem ae_isNormal_slice_of_lipschitzOnWith {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsNormal T) {L : ℝ≥0} (hu : LipschitzOnWith L u Ω) :
    ∀ᵐ t, IsNormal (slice T u t) := by
  cases k with
  | zero =>
    filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT.mass_ne_top hu]
      with t ht
    exact isNormal_finZero_iff.2 ht.ne
  | succ j =>
    have hT' : IsNormal (T ∘L extDerivCLM) := hT.comp_extDerivCLM
    filter_upwards [ae_mass_slice_lt_top_of_lipschitzOnWith hT.isLocallyNormal hT.mass_ne_top hu,
      ae_mass_slice_lt_top_of_lipschitzOnWith hT'.isLocallyNormal hT'.mass_ne_top hu]
      with t ht ht'
    refine isNormal_succ_iff.2 ⟨ht.ne, ?_⟩
    simpa [slice_comp_extDerivCLM, mass_neg] using ht'.ne

end Distribution
