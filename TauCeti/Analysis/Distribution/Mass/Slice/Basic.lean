/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Distribution.TestFunction.Separable
import TauCeti.Analysis.Normed.Module.Multilinear.SecondCountable

/-!
# Slicing currents by a function

Let `Ω` be an open set of a real normed space `E`, let `T` be a
`(k + 1)`-current on `Ω` (a continuous linear functional on the test `(k + 1)`-forms), and let
`u : E → ℝ` be Borel measurable on `Ω`. The **slice** of `T` by `u` at `t` is the `k`-current

`⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}`,

where `⌞` is the Borel restriction of a current of locally finite mass
(`Distribution.massRestrict`) and `∂S = S ∘ d`. It measures the failure of restriction to the
sublevel set `{u < t}` to commute with the boundary. It depends only on the values of `u` on `Ω`,
vanishes when `u` is constant, is linear in `T` on locally normal currents, commutes with open
restrictions and proper smooth pushforwards, satisfies `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`, and has
`spt ⟨T, u, t⟩ ∩ Ω ⊆ spt T ∩ u⁻¹{t}` when `u` is continuous on `Ω`. For each test form `φ`, the
level-set pairing `t ↦ ⟨T, u, t⟩ φ` is Borel measurable, bounded, and compactly supported when `u`
is continuous on `Ω`; when the codomain `F` is second countable, `t ↦ localMass ⟨T, u, t⟩ U` and
`t ↦ mass ⟨T, u, t⟩` are also Borel measurable.

For a smooth `u`, the slice is the weak limit of `-T ⌞ dfₘ` for smooth functions `fₘ` of `u`
increasing to the indicator of `{u < t}`; this follows from the Leibniz rule
`∂(fT) = f ∂T - T ⌞ df` and dominated convergence for the Borel restriction. Bounding the mass of
`T ⌞ dfₘ` against the mass measure `‖T‖` and integrating over `t` gives the **slicing
inequality**

`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) ∫ ‖du‖ d‖T‖`,

and on a real inner product space the sharp bound

`∫ M(⟨T, u, t⟩) dt ≤ ∫ ‖du‖ d‖T‖`,

free of the `(k + 1)` factor because `‖du ∧ φ‖ ≤ ‖du‖ * ‖φ‖` in the operator (comass) norm, so for
a normal current `T` and a smooth `u` with bounded derivative almost every slice is a normal
current. The mass here is taken with respect to the operator norm on alternating forms
(`Distribution.mass`); the factor `k + 1` comes from the unnormalized alternatization defining the
wedge `du ∧ φ`. Slices by Lipschitz functions are treated in
`TauCeti.Analysis.Distribution.Mass.Slice.Lipschitz`. If `E` is infinite-dimensional, every test
form is zero, so every current and every slice is zero.

## Main declarations

* `Distribution.slice`: the slice `⟨T, u, t⟩`, zero by convention when `u` is not measurable on
  `Ω`.
* `Distribution.slice_const`: the slice of a locally normal current by a constant is zero.
* `Distribution.slice_comp_extDerivCLM`: the boundary law `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`.
* `Distribution.dsupport_slice_subset`, `Distribution.dsupport_slice_inter_subset`: support
  localization of a slice.
* `Distribution.measurable_slice_apply`, `Distribution.measurable_localMass_slice`,
  `Distribution.measurable_mass_slice`, `Distribution.hasCompactSupport_slice_apply`,
  `Distribution.integrable_mul_slice_apply`: regularity of `t ↦ ⟨T, u, t⟩ φ` and measurability of
  `t ↦ localMass ⟨T, u, t⟩ U` and `t ↦ M(⟨T, u, t⟩)`.
* `Distribution.slice_comp_monoCLM`, `Distribution.slice_comp_pullbackCLM`: compatibility with
  open restriction and proper smooth pushforward.
* `Distribution.continuous_apply_smulLeftCLM_smoothTransition`,
  `Distribution.continuous_neg_oneFormWedgeCLM_smoothTransition`,
  `Distribution.tendsto_neg_oneFormWedgeCLM_slice_apply`: continuity and weak convergence of the
  smooth-transition slice approximants.
* `Distribution.lintegral_mass_slice_le`,
  `Distribution.lintegral_mass_slice_le_of_innerProductSpace`: the slicing inequality for smooth
  `u`, on general normed spaces and sharp on inner product spaces.

## References

* H. Federer, *Geometric Measure Theory*, §4.2.1, §4.3.1–4.3.2 (slicing normal currents and the
  coarea formula for slices).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5 (slicing).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {u v : E → ℝ} {t : ℝ}

/-! ### Definition, linearity, and the boundary law -/

open scoped Classical in
/-- The **slice** `⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}` of a `(k + 1)`-current `T` on `Ω`
by a function `u : E → ℝ` measurable on `Ω` at the level `t`, a `k`-current on `Ω`. Here `⌞` is
the Borel restriction `Distribution.massRestrict` to the sublevel set `{x ∈ Ω | u x < t}`, which
is meaningful when `T` and `∂T` have locally finite mass. If `u` is not measurable on `Ω`, the
slice is zero by convention. -/
def slice (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) (t : ℝ) :
    𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ :=
  if hu : Measurable fun x : Ω => u x then
    let hA := measurableSet_lt hu (measurable_const (a := t))
    massRestrict T hA ∘L extDerivCLM - massRestrict (T ∘L extDerivCLM) hA
  else 0

section Defs

variable (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ)

/-- For `u` measurable on `Ω`, the slice evaluates as
`(T ⌞ {u < t}) (dφ) - ((∂T) ⌞ {u < t}) φ`. -/
theorem slice_apply (hu : Measurable fun x : Ω => u x) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    slice T u t φ =
      massRestrict T (measurableSet_lt hu (measurable_const (a := t))) (extDerivCLM φ) -
        massRestrict (T ∘L extDerivCLM) (measurableSet_lt hu (measurable_const (a := t))) φ := by
  simp [slice, hu]

/-- The slice by a function not measurable on `Ω` is zero by convention. -/
@[simp]
theorem slice_of_not_measurable (hu : ¬Measurable fun x : Ω => u x) : slice T u t = 0 := by
  simp [slice, hu]

/-- The slice depends only on the restriction of `u` to `Ω`. -/
theorem slice_congr_of_eqOn (huv : EqOn u v Ω) : slice T u t = slice T v t := by
  have hfun : (fun x : Ω => u x) = fun x : Ω => v x := funext fun x => huv x.property
  by_cases hu : Measurable fun x : Ω => u x
  · have hv : Measurable fun x : Ω => v x := hfun ▸ hu
    have hset : {x : Ω | u x < t} = {x : Ω | v x < t} := by ext x; simp [huv x.property]
    ext φ
    rw [slice_apply T hu φ, slice_apply T hv φ,
      massRestrict_congr_set _ _ hset, massRestrict_congr_set _ _ hset]
  · rw [slice_of_not_measurable T hu, slice_of_not_measurable T (hfun ▸ hu)]

/-- The slice of the zero current is zero. -/
@[simp]
theorem slice_zero : slice (0 : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) u t = 0 := by
  by_cases hu : Measurable fun x : Ω => u x
  · ext φ
    simp [slice_apply _ hu]
  · simp [hu]

/-- Slicing commutes with scalar multiplication. -/
@[simp]
theorem slice_smul (a : ℝ) : slice (a • T) u t = a • slice T u t := by
  by_cases hu : Measurable fun x : Ω => u x
  · ext φ
    have hbdry : (a • T) ∘L extDerivCLM = a • (T ∘L extDerivCLM) := by ext ψ; simp
    simp [slice_apply _ hu, hbdry, mul_sub]
  · simp [hu]

/-- Slicing commutes with negation. -/
@[simp]
theorem slice_neg : slice (-T) u t = -slice T u t := by
  rw [← neg_one_smul ℝ T, slice_smul]
  exact neg_one_smul ℝ (slice T u t)

end Defs

/-- The slice of a locally normal current by a constant function is zero. -/
@[simp]
theorem slice_const {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (c t : ℝ) : slice T (fun _ => c) t = 0 := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hm : Measurable fun _ : Ω => c := measurable_const
  ext φ
  rw [slice_apply _ hm, zero_apply]
  by_cases hct : c < t
  · have h : {_x : Ω | c < t} = univ := eq_univ_of_forall fun _ => hct
    rw [massRestrict_congr_set (T := T) _ MeasurableSet.univ h,
      massRestrict_congr_set (T := T ∘L extDerivCLM) _ MeasurableSet.univ h,
      massRestrict_univ_apply hT₁, massRestrict_univ_apply hT₂, comp_apply, sub_self]
  · have h : {_x : Ω | c < t} = ∅ := eq_empty_of_forall_notMem fun _ hx => hct hx
    rw [massRestrict_congr_set (T := T) _ MeasurableSet.empty h,
      massRestrict_congr_set (T := T ∘L extDerivCLM) _ MeasurableSet.empty h,
      massRestrict_eq_zero MeasurableSet.empty (by simp),
      massRestrict_eq_zero MeasurableSet.empty (by simp)]
    simp

/-- Slicing is additive on locally normal currents. -/
theorem slice_add {T S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hS : IsLocallyNormal S) (u : E → ℝ) (t : ℝ) :
    slice (T + S) u t = slice T u t + slice S u t := by
  by_cases hu : Measurable fun x : Ω => u x
  · obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
    obtain ⟨hS₁, hS₂⟩ := isLocallyNormal_succ_iff.1 hS
    let hA := measurableSet_lt hu (measurable_const (a := t))
    ext φ
    simp only [slice_apply _ hu, add_apply, add_comp, massRestrict_add hT₁ hS₁ hA,
      massRestrict_add hT₂ hS₂ hA]
    ring
  · simp [hu]

/-- Slicing commutes with subtraction on locally normal currents. -/
theorem slice_sub {T S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hS : IsLocallyNormal S) (u : E → ℝ) (t : ℝ) :
    slice (T - S) u t = slice T u t - slice S u t := by
  rw [sub_eq_add_neg, slice_add hT hS.neg, slice_neg, sub_eq_add_neg]

/-- **The boundary of a slice.** `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`. -/
theorem slice_comp_extDerivCLM (T : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ)
    (t : ℝ) : slice T u t ∘L extDerivCLM = -slice (T ∘L extDerivCLM) u t := by
  by_cases hu : Measurable fun x : Ω => u x
  · ext φ
    have hdd : (T ∘L extDerivCLM) ∘L extDerivCLM = 0 := by
      rw [comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero]
    simp [slice_apply _ hu, hdd]
  · simp [hu]

/-! ### Support, uniform bound, and measurability in the level -/

private theorem dsupport_slice_subset_of_open {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hum : Measurable fun x : Ω => u x) (t : ℝ) {S U₁ U₂ : Set E}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (h1 : ∀ x ∈ S, u x < t → x ∈ U₁)
    (h2 : ∀ x ∈ S, t < u x → x ∈ U₂) (h1' : ∀ x ∈ U₁, u x < t) (h2' : ∀ x ∈ U₂, t < u x) :
    dsupport (slice T u t) ∩ S ⊆ dsupport T ∩ u ⁻¹' {t} := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hum measurable_const
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
  have hv₂ : IsVanishingOn (slice T u t) U₁ := fun φ hφ => by
    rw [slice_apply _ hum,
      massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h =>
          hx (h1' _ (hφ (tsupport_extDerivCLM_subset φ h)))),
      massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (h1' _ (hφ h)))]
    simp
  have hv₃ : IsVanishingOn (slice T u t) U₂ := fun φ hφ => by
    rw [slice_apply _ hum,
      massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h =>
          lt_asymm (a := u x) (b := t) hx (h2' _ (hφ (tsupport_extDerivCLM_subset φ h)))),
      massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => lt_asymm (a := u x) (b := t) hx (h2' _ (hφ h))),
      sub_zero]
  rintro x ⟨hx, hxS⟩
  refine ⟨by_contra fun h => (notMem_dsupport_iff x).2
    ⟨_, hv₁, isClosed_dsupport.isOpen_compl, h⟩ hx, ?_⟩
  rcases lt_trichotomy (u x) t with h | h | h
  · exact ((notMem_dsupport_iff x).2 ⟨_, hv₂, hU₁, h1 x hxS h⟩ hx).elim
  · exact h
  · exact ((notMem_dsupport_iff x).2 ⟨_, hv₃, hU₂, h2 x hxS h⟩ hx).elim

/-- **Support of a slice inside the domain.** For a locally normal current `T` and a function `u`
continuous on `Ω`, `spt ⟨T, u, t⟩ ∩ Ω ⊆ spt T ∩ u⁻¹{t}`. -/
theorem dsupport_slice_inter_subset {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) (t : ℝ) :
    dsupport (slice T u t) ∩ (Ω : Set E) ⊆ dsupport T ∩ u ⁻¹' {t} :=
  dsupport_slice_subset_of_open hT hu.domRestrict.measurable t
    (hu.isOpen_inter_preimage Ω.isOpen isOpen_Iio) (hu.isOpen_inter_preimage Ω.isOpen isOpen_Ioi)
    (fun _ hΩ h => ⟨hΩ, h⟩) (fun _ hΩ h => ⟨hΩ, h⟩) (fun _ h => h.2) (fun _ h => h.2)

/-- **Support of a slice.** For a locally normal current `T` and a globally continuous function
`u`, the slice `⟨T, u, t⟩` is supported in `spt T ∩ u⁻¹{t}`. -/
theorem dsupport_slice_subset {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : Continuous u) (t : ℝ) :
    dsupport (slice T u t) ⊆ dsupport T ∩ u ⁻¹' {t} := by
  simpa using dsupport_slice_subset_of_open hT (hu.comp continuous_subtypeVal).measurable t
    (isOpen_lt hu continuous_const) (isOpen_lt continuous_const hu) (S := univ)
    (fun _ _ h => h) (fun _ _ h => h) (fun _ h => h) (fun _ h => h)

/-- Uniform level-independent bound on `⟨T, u, t⟩ φ` against the mass measures of `T` and `∂T`. -/
theorem enorm_slice_apply_le (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) (t : ℝ)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ‖slice T u t φ‖ₑ ≤ ∫⁻ x, ‖extDerivCLM φ x‖ₑ ∂massMeasure T +
      ∫⁻ x, ‖φ x‖ₑ ∂massMeasure (T ∘L extDerivCLM) := by
  by_cases hu : Measurable fun x : Ω => u x
  · let hA := measurableSet_lt hu (measurable_const (a := t))
    rw [slice_apply T hu φ]
    exact eNorm_sub_le.trans (add_le_add
      ((enorm_massRestrict_apply_le hA _).trans (setLIntegral_le_lintegral _ _))
      ((enorm_massRestrict_apply_le hA _).trans (setLIntegral_le_lintegral _ _)))
  · simp [hu]

/-- If `|u x| < M` on `Ω ∩ tsupport φ` and `t ∉ (-M, M]`, then `⟨T, u, t⟩ φ = 0`. -/
theorem slice_apply_eq_zero_of_notMem_Ioc {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) {M : ℝ} {φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)}
    (hφ : ∀ x : Ω, (x : E) ∈ tsupport φ → |u x| < M) (ht : t ∉ Ioc (-M) M) :
    slice T u t φ = 0 := by
  by_cases hum : Measurable fun x : Ω => u x
  · obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
    let hA := measurableSet_lt hum (measurable_const (a := t))
    rcases le_or_gt t (-M) with ht1 | ht1
    · have hv {m : ℕ} {ψ : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)}
          (hψ : tsupport ψ ⊆ tsupport φ) : ∀ x : Ω, x ∈ {x : Ω | u x < t} → ψ x = 0 :=
        fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
          (not_lt.2 ht1) ((neg_lt_of_abs_lt (hφ x (hψ h))).trans hx)
      rw [slice_apply _ hum,
        massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ (hv (tsupport_extDerivCLM_subset φ))),
        massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ (hv Subset.rfl)), sub_zero]
    · have htM : M < t := not_le.1 fun hle => ht ⟨ht1, hle⟩
      have hv {m : ℕ} {ψ : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)}
          (hψ : tsupport ψ ⊆ tsupport φ) : ∀ x : Ω, x ∉ {x : Ω | u x < t} → ψ x = 0 :=
        fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
          hx ((le_abs_self (u x)).trans_lt ((hφ x (hψ h)).trans htM))
      rw [slice_apply _ hum,
        massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ (hv (tsupport_extDerivCLM_subset φ))),
        massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ (hv Subset.rfl))]
      simp
  · simp [hum]

/-- If `T` is locally normal and `u` is continuous on `Ω`, then `t ↦ ⟨T, u, t⟩ φ` vanishes outside
a bounded interval of levels `t`, hence has compact support. -/
theorem hasCompactSupport_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    HasCompactSupport fun t => slice T u t φ := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (c := (0 : ℝ)).1
    (φ.hasCompactSupport.image_of_continuousOn (hu.mono φ.tsupport_subset)).isBounded
  let M : ℝ := max R 0 + 1
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) M) fun t ht => ?_
  have ht' : M < |t| := by simpa [Metric.mem_closedBall, Real.dist_eq] using ht
  refine slice_apply_eq_zero_of_notMem_Ioc hT (M := M) (fun x hx => ?_) fun htI =>
    ht'.not_ge (abs_le.2 ⟨htI.1.le, htI.2⟩)
  exact ((by simpa [Metric.mem_closedBall, Real.dist_eq] using hR ⟨x, hx, rfl⟩ : |u x| ≤ R).trans
    (le_max_left _ _)).trans_lt (lt_add_one _)

/-- For every `(k + 1)`-current `T`, every `u : E → ℝ`, and every test form `φ`, the level-set
pairing `t ↦ ⟨T, u, t⟩ φ` is Borel measurable. -/
theorem measurable_slice_apply (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) : Measurable fun t : ℝ => slice T u t φ := by
  by_cases hu : Measurable fun x : Ω => u x
  · simp_rw [slice_apply T hu φ]
    exact (measurable_massRestrict_lt_apply T hu (extDerivCLM φ)).sub
      (measurable_massRestrict_lt_apply (T ∘L extDerivCLM) hu φ)
  · simp [hu]

/-- For a second countable codomain `F`, `t ↦ localMass ⟨T, u, t⟩ U` is Borel measurable for every
set `U : Set E`. -/
theorem measurable_localMass_slice [SecondCountableTopology F]
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) (U : Set E) :
    Measurable fun t : ℝ => localMass (slice T u t) U := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · have h0 (t : ℝ) : localMass (slice T u t) U = 0 :=
      le_antisymm (localMass_le_iff.2 fun φ _ _ => by
        simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]) bot_le
    simp_rw [h0]
    exact measurable_const
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let Kex := CompactExhaustion.choice Ω
  let C (n : ℕ) : Compacts E := ⟨(↑) '' Kex n, (Kex.isCompact n).image continuous_subtypeVal⟩
  have hC (n : ℕ) : (C n : Set E) ⊆ Ω := Subtype.coe_image_subset _ _
  have : SecondCountableTopology (E [⋀^Fin k]→L[ℝ] F) :=
    (ContinuousAlternatingMap.toContinuousMultilinearMapLI (𝕜 := ℝ) (E := E) (F := F)
      (ι := Fin k)).isometry.isEmbedding.secondCountableTopology
  let S (n : ℕ) : Set 𝓓_{C n}(E, E [⋀^Fin k]→L[ℝ] F) :=
    {ψ | tsupport (ψ : E → E [⋀^Fin k]→L[ℝ] F) ⊆ U ∧ ∀ x, ‖ψ x‖ ≤ 1}
  choose D hDc hDd using fun n : ℕ => TopologicalSpace.exists_countable_dense (S n)
  have heq (t : ℝ) : localMass (slice T u t) U =
      ⨆ (n : ℕ) (ψ : D n), ‖slice T u t (ofSupportedIn (hC n) ψ.val.val)‖ₑ := by
    refine le_antisymm (localMass_le_iff.2 fun φ hφU hφ => ?_)
      (iSup_le fun n => iSup_le fun ψ => enorm_le_localMass ψ.val.property.1 ψ.val.property.2)
    obtain ⟨n, hn⟩ := Kex.exists_superset_of_isCompact (TestFunction.isCompact_preimage_tsupport φ)
    have hφCn : tsupport φ ⊆ C n := fun x hx => ⟨⟨x, φ.tsupport_subset hx⟩, hn hx, rfl⟩
    let ψ₀ : 𝓓_{C n}(E, E [⋀^Fin k]→L[ℝ] F) :=
      ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφCn h)⟩
    have hψ₀ : ψ₀ ∈ S n := ⟨hφU, hφ⟩
    have hcont : Continuous fun ψ : S n => ‖slice T u t (ofSupportedIn (hC n) ψ.val)‖ₑ :=
      ((slice T u t).continuous.comp
        ((continuous_ofSupportedIn (hC n)).comp continuous_subtypeVal)).eNorm
    have hφ_eq : φ = ofSupportedIn (hC n) ψ₀ := TestFunction.ext fun _ => rfl
    rw [hφ_eq]
    have hsub : (D n : Set (S n)) ⊆ {ψ : S n |
        ‖slice T u t (ofSupportedIn (hC n) ψ.val)‖ₑ ≤
          ⨆ (m : ℕ) (ψ' : D m), ‖slice T u t (ofSupportedIn (hC m) ψ'.val.val)‖ₑ} :=
      fun ψ hψ => le_trans
        (le_iSup (fun ψ' : D n => ‖slice T u t (ofSupportedIn (hC n) ψ'.val.val)‖ₑ) ⟨ψ, hψ⟩)
        (le_iSup (fun m : ℕ =>
          ⨆ ψ' : D m, ‖slice T u t (ofSupportedIn (hC m) ψ'.val.val)‖ₑ) n)
    exact (isClosed_le hcont continuous_const).closure_subset_iff.2 hsub
      ((hDd n).closure_eq.symm ▸ mem_univ (⟨ψ₀, hψ₀⟩ : S n))
  simp_rw [heq]
  refine Measurable.iSup fun n => ?_
  have : Countable (D n) := (hDc n).to_subtype
  exact Measurable.iSup fun ψ => (measurable_slice_apply T u _).eNorm

/-- For a second countable codomain `F`, `t ↦ mass ⟨T, u, t⟩` is Borel measurable. -/
theorem measurable_mass_slice [SecondCountableTopology F]
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) :
    Measurable fun t : ℝ => mass (slice T u t) := by
  simpa only [localMass_univ] using measurable_localMass_slice T u univ

/-- For a locally normal current `T` and `u` continuous on `Ω`, `t ↦ ⟨T, u, t⟩ φ` is integrable on
`ℝ`. -/
theorem integrable_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Integrable fun t : ℝ => slice T u t φ := by
  have hcpt := hasCompactSupport_slice_apply hT hu φ
  let C : ℝ≥0∞ := ‖TestFunction.toLp 1 (massMeasure T) (extDerivCLM φ)‖ₑ +
    ‖TestFunction.toLp 1 (massMeasure (T ∘L extDerivCLM)) φ‖ₑ
  refine (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
    ⟨(measurable_slice_apply T u φ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  refine (setLIntegral_mono' (g := fun _ => C) hcpt.isClosed.measurableSet fun t _ => ?_).trans_lt
    (by rw [setLIntegral_const]; exact ENNReal.mul_lt_top (by finiteness) hcpt.measure_lt_top)
  simpa [C, TestFunction.enorm_toLp_one] using enorm_slice_apply_le T u t φ

/-- For a locally normal current `T`, `u` continuous on `Ω`, and `g : ℝ → ℝ` continuous,
`t ↦ g t * ⟨T, u, t⟩ φ` is integrable on `ℝ`. -/
theorem integrable_mul_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) {g : ℝ → ℝ} (hg : Continuous g)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Integrable fun t : ℝ => g t * slice T u t φ := by
  refine (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right g _).trans (subset_tsupport _))).1 ?_
  simpa only [smul_eq_mul] using (integrable_slice_apply hT hu φ).integrableOn.continuousOn_smul
    hg.continuousOn (hasCompactSupport_slice_apply hT hu φ)

/-! ### Compatibility with open restriction and proper smooth pushforward -/

/-- **Slicing commutes with open restriction.** For `Ω' ≤ Ω`, a locally normal current `T` on `Ω`,
and `u` measurable on `Ω`, restricting `⟨T, u, t⟩` to `Ω'` equals `⟨T|_{Ω'}, u, t⟩`. -/
theorem slice_comp_monoCLM {Ω' : Opens E} {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (h : Ω' ≤ Ω) (hu : Measurable fun x : Ω => u x) (t : ℝ) :
    slice T u t ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      slice (T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) u t := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hu' : Measurable fun x : Ω' => u x := hu.comp (continuous_inclusion h).measurable
  let hA := measurableSet_lt hu (measurable_const (a := t))
  have hset : Set.inclusion h ⁻¹' {x : Ω | u x < t} = {x : Ω' | u x < t} := rfl
  ext φ
  rw [comp_apply, slice_apply T hu, slice_apply _ hu', extDerivCLM_monoCLM,
    ← comp_apply (g := massRestrict T hA), ← comp_apply (g := massRestrict (T ∘L extDerivCLM) hA),
    massRestrict_comp_monoCLM hT₁ h hA, massRestrict_comp_monoCLM hT₂ h hA,
    comp_monoCLM_comp_extDerivCLM,
    massRestrict_congr_set _ (measurableSet_lt hu' measurable_const) hset,
    massRestrict_congr_set _ (measurableSet_lt hu' measurable_const) hset]

private theorem slice_comp_pullbackCLM_aux {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] {Ω' : Opens E'} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {u : E' → ℝ}
    (hu' : Measurable fun y : Ω' => u y) (huΦ : Measurable fun x : Ω => (u ∘ Φ) x) (t : ℝ) :
    slice (T ∘L pullbackCLM Φ hΦ hΦp) u t =
      slice T (u ∘ Φ) t ∘L pullbackCLM Φ hΦ hΦp := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  let B : Set Ω' := {y : Ω' | u y < t}
  have hB : MeasurableSet B := measurableSet_lt hu' (measurable_const (a := t))
  let A₀ : Set Ω := (fun x : Ω => Φ x) ⁻¹' ((↑) '' B : Set E')
  have hA₀ : MeasurableSet A₀ :=
    (Ω'.isOpen.measurableSet.subtype_image hB).preimage hΦ.continuousOn.domRestrict.measurable
  let A₁ : Set Ω := {x : Ω | (u ∘ Φ) x < t}
  have hA₁ : MeasurableSet A₁ := measurableSet_lt huΦ (measurable_const (a := t))
  have heq {m : ℕ} (S : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] ℝ) (η : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
      massRestrict S hA₀ (pullbackCLM Φ hΦ hΦp η) =
        massRestrict S hA₁ (pullbackCLM Φ hΦ hΦp η) := by
    simp only [massRestrict_apply, TestFunction.indicatorToLp_apply]
    refine congrArg (extendL1 S) (MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_))
    by_cases hxΩ' : Φ x ∈ Ω'
    · have hiff : x ∈ A₀ ↔ x ∈ A₁ := by simp [A₀, A₁, B, Subtype.coe_image, hxΩ']
      by_cases hx1 : x ∈ A₁ <;> simp [hiff, hx1]
    · have h0 : pullbackCLM Φ hΦ hΦp η x = 0 := by
        rw [pullbackCLM_apply_of_mem η x.property, image_eq_zero_of_notMem_tsupport fun h =>
          hxΩ' (η.tsupport_subset h)]
        ext _; simp
      refine Eq.trans (b := 0) ?_ (Eq.symm ?_) <;>
        (apply Set.indicator_apply_eq_zero.mpr; exact fun _ => h0)
  ext φ
  rw [slice_apply _ hu', comp_apply, slice_apply _ huΦ, massRestrict_comp_pullbackCLM hT₁ hB,
    comp_pullbackCLM_comp_extDerivCLM T, massRestrict_comp_pullbackCLM hT₂ hB, comp_apply,
    comp_apply, extDerivCLM_pullbackCLM]
  exact congrArg₂ (· - ·) (heq T (extDerivCLM φ)) (heq (T ∘L extDerivCLM) φ)

/-- **Slicing commutes with proper smooth pushforward** when `Φ` maps `Ω` into `Ω'`:
`⟨Φ_# T, u, t⟩ = Φ_# ⟨T, u ∘ Φ, t⟩` for any locally normal `T` and `u` measurable on `Ω'`. -/
theorem slice_comp_pullbackCLM {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] {Ω' : Opens E'} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    (hmaps : MapsTo Φ Ω Ω') {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) {u : E' → ℝ} (hu : Measurable fun y : Ω' => u y) (t : ℝ) :
    slice (T ∘L pullbackCLM Φ hΦ hΦp) u t =
      slice T (u ∘ Φ) t ∘L pullbackCLM Φ hΦ hΦp :=
  slice_comp_pullbackCLM_aux hT hu
    (hu.comp (hΦ.continuousOn.domRestrict.subtype_mk fun x => hmaps x.property).measurable) t

/-- **Slicing commutes with proper smooth pushforward** for any globally measurable `u : E' → ℝ`,
without assuming `MapsTo Φ Ω Ω'`. -/
theorem slice_comp_pullbackCLM_of_measurable {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    {Ω' : Opens E'} {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    {u : E' → ℝ} (hu : Measurable u) (t : ℝ) :
    slice (T ∘L pullbackCLM Φ hΦ hΦp) u t =
      slice T (u ∘ Φ) t ∘L pullbackCLM Φ hΦ hΦp :=
  slice_comp_pullbackCLM_aux hT (hu.comp measurable_subtypeVal)
    (hu.comp hΦ.continuousOn.domRestrict.measurable) t

/-! ### The slicing inequality for smooth functions

The slice `⟨T, u, t⟩` is approximated by `-T ⌞ dfₘ` for the smooth multipliers
`fₘ x = ψ(cₘ (t - u x))`, where `ψ = Real.smoothTransition` and `cₘ = m + 1`. They increase to the
indicator of `{u < t}`, and `‖dfₘ‖ = cₘ ψ'(cₘ (t - u)) ‖du‖`, whose integral in `t` is `‖du‖`. -/

/-- Continuity of `s ↦ S (ψ(c (s - u ·)) • η)` for a locally finite-mass functional `S`. -/
theorem continuous_apply_smulLeftCLM_smoothTransition {n : ℕ∞} {S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ}
    (hS : HasLocallyFiniteMass S) {u : E → ℝ} (hu : ContDiff ℝ n u)
    (η : 𝓓^{n}(Ω, F)) (c : ℝ) :
    Continuous fun s : ℝ =>
      S (TestFunction.smulLeftCLM (hu.smoothTransition_mul_sub c s) η) := by
  have hmem (s : ℝ) : MemLp (fun x : Ω =>
      Real.smoothTransition (c * (s - u x)) • η x) 1 (massMeasure S) := by
    simpa [TestFunction.smulLeftCLM_apply] using TestFunction.memLp_subtype (p := 1)
      (μ := massMeasure S) (TestFunction.smulLeftCLM (hu.smoothTransition_mul_sub c s) η)
  simp_rw [← extendL1_toLp hS]
  refine (extendL1 S).continuous.comp (continuous_iff_continuousAt.2 fun s₀ => ?_)
  have htoLp (s : ℝ) :
      TestFunction.toLp 1 (massMeasure S)
          (TestFunction.smulLeftCLM (hu.smoothTransition_mul_sub c s) η) = (hmem s).toLp _ := by
    rw [TestFunction.toLp_apply, MemLp.toLp_eq_toLp_iff]
    exact ae_of_all _ fun x => by simp [TestFunction.smulLeftCLM_apply]
  simp_rw [ContinuousAt, htoLp]
  refine TestFunction.tendsto_toLp_smul_of_dominated ENNReal.one_ne_top hmem (hmem s₀) 2
    (.of_forall fun s x _ => (abs_sub _ _).trans <| by
      linarith [Real.smoothTransition.abs_le_one (c * (s - u x)),
        Real.smoothTransition.abs_le_one (c * (s₀ - u x))])
    fun x _ => (Real.smoothTransition.continuous.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).tendsto s₀

/-- Continuity of the smooth-transition slice approximant `t ↦ -T (df(t) ∧ φ)` in `t`, where
`f(t) x = ψ(c (t - u x))`. -/
theorem continuous_neg_oneFormWedgeCLM_smoothTransition
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) (c : ℝ) :
    Continuous fun t : ℝ =>
      -T (oneFormWedgeCLM (k := k)
        (contDiff_infty_iff_fderiv.1 (hu.smoothTransition_mul_sub c t)).2 φ) := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  refine ((continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ) c).sub
    (continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ c)).congr fun t => ?_
  have hL := DFunLike.congr_fun
    (comp_smulLeftCLM_comp_extDerivCLM T (hu.smoothTransition_mul_sub c t)) φ
  simp only [comp_apply, sub_apply] at hL
  dsimp only [Pi.sub_apply]
  rw [comp_apply]
  linarith

/-- For smooth `u`, `-T ⌞ dfₘ` with `fₘ x = ψ((m + 1) (t - u x))` converges weakly to
`⟨T, u, t⟩`. -/
theorem tendsto_neg_oneFormWedgeCLM_slice_apply
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun m : ℕ =>
        -T (oneFormWedgeCLM (k := k)
          (contDiff_infty_iff_fderiv.1 (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t)).2 φ))
      atTop (𝓝 (slice T u t φ)) := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hum : Measurable fun x : Ω => u x := (hu.continuous.comp continuous_subtypeVal).measurable
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hum measurable_const
  have hf (m : ℕ) := hu.smoothTransition_mul_sub ((m : ℝ) + 1) t
  have hfC (m : ℕ) : ∀ x ∈ Ω, |Real.smoothTransition (((m : ℝ) + 1) * (t - u x))| ≤ 1 :=
    fun x _ => Real.smoothTransition.abs_le_one _
  have hlim (x : Ω) : Tendsto (fun m : ℕ => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
      atTop (𝓝 ({y : Ω | u y < t}.indicator 1 x)) := by
    simpa [sub_pos] using Real.smoothTransition.tendsto_indicator (fun y : Ω => t - u y) 0 x
  have h := (tendsto_apply_smulLeftCLM_massRestrict hT₁ hA hf hfC hlim (extDerivCLM φ)).sub
    (tendsto_apply_smulLeftCLM_massRestrict hT₂ hA hf hfC hlim φ)
  rw [← slice_apply _ hum] at h
  refine h.congr fun m => ?_
  have hL := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hf m)) φ
  simp only [comp_apply, sub_apply] at hL
  simp [hL]

private theorem exists_measurable_mass_slice_le_aux
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (c : ℝ≥0∞)
    (hwedge : ∀ {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α),
      mass (T ∘ oneFormWedgeCLM (k := k) hα) ≤ c * ∫⁻ x, ‖α x‖ₑ ∂massMeasure T) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ t, mass (slice T u t) ≤ G t) ∧
      ∫⁻ t, G t ≤ c * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure T := by
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
  have hf (t : ℝ) (m : ℕ) := hu.smoothTransition_mul_sub ((m : ℝ) + 1) t
  have hg' (m : ℕ) :=
    Real.smoothTransition.measurable_ofReal_mul_deriv_mul_sub_mul hum hdu ((m : ℝ) + 1)
  have hg (m : ℕ) : Measurable fun t => c *
      ∫⁻ x, ENNReal.ofReal (((m : ℝ) + 1) *
        deriv Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) * ‖fderiv ℝ u x‖ₑ
        ∂massMeasure T :=
    (hg' m).lintegral_prod_right'.const_mul c
  refine ⟨_, .liminf hg, fun t => ?_, (lintegral_liminf_le hg).trans_eq ?_⟩
  · refine (mass_le_liminf (fs := fun m =>
        -(T ∘ oneFormWedgeCLM (k := k) (contDiff_infty_iff_fderiv.1 (hf t m)).2))
        (tendsto_neg_oneFormWedgeCLM_slice_apply hT hu t)).trans
      (liminf_le_liminf (.of_forall fun m => ?_))
    rw [mass_neg]
    refine (hwedge _).trans_eq ?_
    simp_rw [(hu.differentiable (by simp) _).enorm_fderiv_smoothTransition_mul_sub
      (c := (m : ℝ) + 1) (by positivity)]
  · simp_rw [lintegral_const_mul _ (hg' _).lintegral_prod_right',
      Real.smoothTransition.lintegral_lintegral_ofReal_mul_deriv_mul_sub_mul _ hum hdu
        (Nat.cast_add_one_pos _)]
    exact liminf_const _

/-- A measurable majorant of `t ↦ M(⟨T, u, t⟩)` whose integral is at most
`(k + 1) ∫ ‖du‖ d‖T‖`. -/
theorem exists_measurable_mass_slice_le {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ t, mass (slice T u t) ≤ G t) ∧
      ∫⁻ t, G t ≤ (k + 1) * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure T :=
  exists_measurable_mass_slice_le_aux hT hu (k + 1) fun hα =>
    mass_comp_oneFormWedgeCLM_le_lintegral hT.hasLocallyFiniteMass hα

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

section InnerProductSpace

/-- On a real inner product space, a measurable majorant of `t ↦ M(⟨T, u, t⟩)` has integral at
most `∫ ‖du‖ d‖T‖`, without the `(k + 1)` factor. -/
theorem exists_measurable_mass_slice_le_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ t, mass (slice T w t) ≤ G t) ∧
      ∫⁻ t, G t ≤ ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂massMeasure T := by
  simpa only [one_mul] using exists_measurable_mass_slice_le_aux hT hw 1 fun hα => by
    simpa only [one_mul] using
      mass_comp_oneFormWedgeCLM_le_lintegral_of_innerProductSpace hT.hasLocallyFiniteMass hα

/-- **Sharp slicing inequality on an inner product space.** For a locally normal `(k + 1)`-current
`T` and smooth `w`, `∫ M(⟨T, w, t⟩) dt ≤ ∫ ‖dw‖ d‖T‖`. -/
theorem lintegral_mass_slice_le_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) :
    ∫⁻ t, mass (slice T w t) ≤ ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂massMeasure T := by
  obtain ⟨G, -, hG, hGint⟩ := exists_measurable_mass_slice_le_of_innerProductSpace hT hw
  exact (lintegral_mono hG).trans hGint

/-- **Sharp slicing inequality with a derivative bound on an inner product space.** If
`‖dw‖ ≤ L` on `U`, then `∫ M(⟨T, w, t⟩) dt ≤ L M(T)`. -/
theorem lintegral_mass_slice_le_mul_mass_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) {L : ℝ≥0∞}
    (hdw : ∀ x ∈ U, ‖fderiv ℝ w x‖ₑ ≤ L) :
    ∫⁻ t, mass (slice T w t) ≤ L * mass T :=
  (lintegral_mass_slice_le_of_innerProductSpace hT hw).trans
    (lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass fun x => hdw x x.property)

end InnerProductSpace

end Distribution
