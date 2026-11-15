/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.Distribution.TestFunction.Pullback
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Slicing currents by a function

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `T` be a
`(k + 1)`-current on `Ω` (a continuous linear functional on the test `(k + 1)`-forms), and let
`u : E → ℝ` be Borel measurable on `Ω`. The **slice** of `T` by `u` at `t` is the `k`-current

`⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}`,

where `⌞` is the Borel restriction of a current of locally finite mass
(`Distribution.massRestrict`) and `∂S = S ∘ d`. It measures the failure of restriction to the
sublevel set `{u < t}` to commute with the boundary. It depends only on the values of `u` on `Ω`,
is linear in `T` on locally normal currents, commutes with open restrictions and proper smooth
pushforwards, satisfies `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`, and has `spt ⟨T, u, t⟩ ∩ Ω ⊆ spt T ∩ u⁻¹{t}`
when `u` is continuous on `Ω`. For each test form `φ`, the level-set pairing `t ↦ ⟨T, u, t⟩ φ` is
Borel measurable, bounded, and compactly supported when `u` is continuous on `Ω`.

For a smooth `u`, the slice is the weak limit of `-T ⌞ dfₘ` for smooth functions `fₘ` of `u`
increasing to the indicator of `{u < t}`; this follows from the Leibniz rule
`∂(fT) = f ∂T - T ⌞ df` and dominated convergence for the Borel restriction. Bounding the mass of
`T ⌞ dfₘ` against the mass measure `‖T‖` and integrating over `t` gives the **slicing
inequality**

`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) ∫ ‖du‖ d‖T‖`,

and on a real inner product space the sharp bound

`∫ M(⟨T, u, t⟩) dt ≤ ∫ ‖du‖ d‖T‖`,

free of the `(k + 1)` factor because `‖du ∧ φ‖ ≤ ‖du‖ * ‖φ‖` in the operator (comass) norm.

## Main declarations

* `Distribution.slice`: the slice `⟨T, u, t⟩`, zero by convention when `u` is not measurable on
  `Ω`.
* `Distribution.slice_comp_extDerivCLM`: the boundary law `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`.
* `Distribution.dsupport_slice_subset`, `Distribution.dsupport_slice_inter_subset`: support
  localization of a slice.
* `Distribution.measurable_slice_apply`, `Distribution.hasCompactSupport_slice_apply`,
  `Distribution.integrable_mul_slice_apply`: regularity of `t ↦ ⟨T, u, t⟩ φ`.
* `Distribution.slice_comp_monoCLM`, `Distribution.massRestrict_comp_pullbackCLM`,
  `Distribution.slice_comp_pullbackCLM`: compatibility with open restriction and proper smooth
  pushforward.
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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

/-- Convenience form of `Distribution.slice_apply` when `u : E → ℝ` is globally measurable. -/
theorem slice_apply_of_measurable (hu : Measurable u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    slice T u t φ =
      massRestrict T (measurableSet_lt (hu.comp measurable_subtype_coe) (measurable_const (a := t)))
          (extDerivCLM φ) -
        massRestrict (T ∘L extDerivCLM)
          (measurableSet_lt (hu.comp measurable_subtype_coe) (measurable_const (a := t))) φ :=
  slice_apply T (hu.comp measurable_subtype_coe) φ

/-- The slice by a function not measurable on `Ω` is zero by convention. -/
@[simp]
theorem slice_of_not_measurable (hu : ¬Measurable fun x : Ω => u x) : slice T u t = 0 := by
  simp [slice, hu]

private theorem massRestrict_congr_set {n : ℕ∞} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {U : Opens E} (S : 𝓓^{n}(U, G) →L[ℝ] ℝ)
    {A₁ A₂ : Set U} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) (h : A₁ = A₂) :
    massRestrict S hA₁ = massRestrict S hA₂ := by
  subst h
  rfl

/-- The slice depends only on the restriction of `u` to `Ω`. -/
theorem slice_congr_of_eqOn (huv : EqOn u v Ω) : slice T u t = slice T v t := by
  have hfun : (fun x : Ω => u x) = fun x : Ω => v x := funext fun x => huv x.2
  by_cases hu : Measurable fun x : Ω => u x
  · have hv : Measurable fun x : Ω => v x := hfun ▸ hu
    have hset : {x : Ω | u x < t} = {x : Ω | v x < t} := by
      ext x
      simp [huv x.2]
    ext φ
    rw [slice_apply T hu φ, slice_apply T hv φ,
      massRestrict_congr_set T _ _ hset, massRestrict_congr_set (T ∘L extDerivCLM) _ _ hset]
  · have hv : ¬Measurable fun x : Ω => v x := hfun ▸ hu
    rw [slice_of_not_measurable T hu, slice_of_not_measurable T hv]

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
    have hbdry : (a • T) ∘L extDerivCLM = a • (T ∘L extDerivCLM) := by
      ext ψ
      simp
    simp [slice_apply _ hu, hbdry, mul_sub]
  · simp [hu]

/-- Slicing commutes with negation. -/
@[simp]
theorem slice_neg : slice (-T) u t = -slice T u t := by
  have h1 : (-1 : ℝ) • T = -T := by ext φ; simp
  have h2 : (-1 : ℝ) • slice T u t = -slice T u t := by ext φ; simp
  rw [← h1, slice_smul, h2]

end Defs

/-- Slicing is additive on locally normal currents. -/
theorem slice_add {T S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hS : IsLocallyNormal S) (u : E → ℝ) (t : ℝ) :
    slice (T + S) u t = slice T u t + slice S u t := by
  by_cases hu : Measurable fun x : Ω => u x
  · obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
    obtain ⟨hS₁, hS₂⟩ := isLocallyNormal_succ_iff.1 hS
    let hA := measurableSet_lt hu (measurable_const (a := t))
    ext φ
    have hbdry : (T + S) ∘L extDerivCLM = T ∘L extDerivCLM + S ∘L extDerivCLM := add_comp ..
    simp only [slice_apply _ hu, add_apply, hbdry, massRestrict_add hT₁ hS₁ hA,
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

/-- **Support of a slice inside the domain.** For a locally normal current `T` and a function `u`
continuous on `Ω`, `spt ⟨T, u, t⟩ ∩ Ω ⊆ spt T ∩ u⁻¹{t}`. -/
theorem dsupport_slice_inter_subset {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) (t : ℝ) :
    dsupport (slice T u t) ∩ (Ω : Set E) ⊆ dsupport T ∩ u ⁻¹' {t} := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hum : Measurable fun x : Ω => u x := hu.domRestrict.measurable
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hum measurable_const
  have hv₁ : IsVanishingOn (slice T u t) (dsupport T)ᶜ := fun φ hφ => by
    have h₁ : massRestrict T hA (extDerivCLM φ) = 0 :=
      isVanishingOn_compl_dsupport (massRestrict T hA) _ ((tsupport_extDerivCLM_subset φ).trans
        (hφ.trans (compl_subset_compl.2 (dsupport_massRestrict_subset hA))))
    have h₂ : massRestrict (T ∘L extDerivCLM) hA φ = 0 :=
      isVanishingOn_compl_dsupport (massRestrict (T ∘L extDerivCLM) hA) _
        (hφ.trans (compl_subset_compl.2 ((dsupport_massRestrict_subset hA).trans
          (dsupport_comp_extDerivCLM_subset T))))
    simp [slice_apply _ hum, h₁, h₂]
  have hv₂ : IsVanishingOn (slice T u t) ((Ω : Set E) ∩ u ⁻¹' Iio t) := fun φ hφ => by
    have h₁ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφ (tsupport_extDerivCLM_subset φ h)).2
    have h₂ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφ h).2
    rw [slice_apply _ hum, massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ h₁),
      massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ h₂)]
    simp
  have hv₃ : IsVanishingOn (slice T u t) ((Ω : Set E) ∩ u ⁻¹' Ioi t) := fun φ hφ => by
    have h₁ : ∀ x : Ω, x ∈ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h =>
        lt_asymm (a := u x) (b := t) hx (hφ (tsupport_extDerivCLM_subset φ h)).2
    have h₂ : ∀ x : Ω, x ∈ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => lt_asymm (a := u x) (b := t) hx (hφ h).2
    rw [slice_apply _ hum, massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ h₁),
      massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ h₂), sub_zero]
  rintro x ⟨hx, hxΩ⟩
  refine ⟨?_, ?_⟩
  · by_contra h
    exact (notMem_dsupport_iff x).2 ⟨_, hv₁, isClosed_dsupport.isOpen_compl, h⟩ hx
  rcases lt_trichotomy (u x) t with h | h | h
  · exact ((notMem_dsupport_iff x).2
      ⟨_, hv₂, hu.isOpen_inter_preimage Ω.isOpen isOpen_Iio, hxΩ, h⟩ hx).elim
  · exact h
  · exact ((notMem_dsupport_iff x).2
      ⟨_, hv₃, hu.isOpen_inter_preimage Ω.isOpen isOpen_Ioi, hxΩ, h⟩ hx).elim

/-- **Support of a slice.** For a locally normal current `T` and a globally continuous function
`u`, the slice `⟨T, u, t⟩` is supported in `spt T ∩ u⁻¹{t}`. -/
theorem dsupport_slice_subset {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : Continuous u) (t : ℝ) :
    dsupport (slice T u t) ⊆ dsupport T ∩ u ⁻¹' {t} := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hum : Measurable fun x : Ω => u x := (hu.comp continuous_subtype_val).measurable
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hum measurable_const
  have hv₁ : IsVanishingOn (slice T u t) (dsupport T)ᶜ := fun φ hφ => by
    have h₁ : massRestrict T hA (extDerivCLM φ) = 0 :=
      isVanishingOn_compl_dsupport (massRestrict T hA) _ ((tsupport_extDerivCLM_subset φ).trans
        (hφ.trans (compl_subset_compl.2 (dsupport_massRestrict_subset hA))))
    have h₂ : massRestrict (T ∘L extDerivCLM) hA φ = 0 :=
      isVanishingOn_compl_dsupport (massRestrict (T ∘L extDerivCLM) hA) _
        (hφ.trans (compl_subset_compl.2 ((dsupport_massRestrict_subset hA).trans
          (dsupport_comp_extDerivCLM_subset T))))
    simp [slice_apply _ hum, h₁, h₂]
  have hv₂ : IsVanishingOn (slice T u t) {x | u x < t} := fun φ hφ => by
    have h₁ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφ (tsupport_extDerivCLM_subset φ h))
    have h₂ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφ h)
    rw [slice_apply _ hum, massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ h₁),
      massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ h₂)]
    simp
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

/-- Uniform level-independent bound on `⟨T, u, t⟩ φ` against the mass measures of `T` and `∂T`. -/
theorem enorm_slice_apply_le (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ) (t : ℝ)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ‖slice T u t φ‖ₑ ≤ ∫⁻ x, ‖extDerivCLM φ x‖ₑ ∂massMeasure T +
      ∫⁻ x, ‖φ x‖ₑ ∂massMeasure (T ∘L extDerivCLM) := by
  by_cases hu : Measurable fun x : Ω => u x
  · let hA := measurableSet_lt hu (measurable_const (a := t))
    rw [slice_apply T hu φ]
    refine eNorm_sub_le.trans (add_le_add ?_ ?_)
    · exact (enorm_massRestrict_apply_le hA _).trans (setLIntegral_le_lintegral _ _)
    · exact (enorm_massRestrict_apply_le hA _).trans (setLIntegral_le_lintegral _ _)
  · simp [hu]

/-- If `|u x| < M` on `Ω ∩ tsupport φ` and `t ∉ (-M, M]`, then `⟨T, u, t⟩ φ = 0`. -/
theorem slice_apply_eq_zero_of_notMem_Ioc {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) {M : ℝ} {φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)}
    (hφ : ∀ x : Ω, (x : E) ∈ tsupport φ → |u x| < M) (ht : t ∉ Ioc (-M) M) :
    slice T u t φ = 0 := by
  by_cases hum : Measurable fun x : Ω => u x
  · obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
    have hdφ : ∀ x : Ω, (x : E) ∈ tsupport (extDerivCLM φ) → |u x| < M :=
      fun x hx => hφ x (tsupport_extDerivCLM_subset φ hx)
    let hA := measurableSet_lt hum (measurable_const (a := t))
    rcases le_or_gt t (-M) with ht1 | ht1
    · have h₁ : ∀ x : Ω, x ∈ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => by
          have hux : -M < u x := neg_lt_of_abs_lt (hdφ x h)
          change u x < t at hx
          linarith
      have h₂ : ∀ x : Ω, x ∈ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => by
          have hux : -M < u x := neg_lt_of_abs_lt (hφ x h)
          change u x < t at hx
          linarith
      rw [slice_apply _ hum, massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ h₁),
        massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ h₂), sub_zero]
    · have htM : M < t := not_le.1 fun hle => ht ⟨ht1, hle⟩
      have h₁ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → extDerivCLM φ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h =>
          hx ((le_abs_self (u x)).trans_lt ((hdφ x h).trans htM))
      have h₂ : ∀ x : Ω, x ∉ {x : Ω | u x < t} → φ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h =>
          hx ((le_abs_self (u x)).trans_lt ((hφ x h).trans htM))
      rw [slice_apply _ hum, massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ h₁),
        massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ h₂)]
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
  refine slice_apply_eq_zero_of_notMem_Ioc hT (M := M) (fun x hx => ?_) fun htI => ?_
  · have hxR : |u x| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hR ⟨x, hx, rfl⟩
    exact (hxR.trans (le_max_left _ _)).trans_lt (lt_add_one _)
  · exact ht'.not_ge (abs_le.2 ⟨htI.1.le, htI.2⟩)

/-- For any functional `S`, `t ↦ (S ⌞ {u < t}) φ` is left-continuous in `t`, hence Borel
measurable as a pointwise limit of dyadic step functions from below. -/
theorem measurable_massRestrict_lt_apply {n : ℕ∞} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (S : 𝓓^{n}(Ω, G) →L[ℝ] ℝ)
    (hu : Measurable fun x : Ω => u x) (φ : 𝓓^{n}(Ω, G)) :
    Measurable fun t : ℝ =>
      massRestrict S (measurableSet_lt hu (measurable_const (a := t))) φ := by
  let hA (s : ℝ) : MeasurableSet {x : Ω | u x < s} :=
    measurableSet_lt hu (measurable_const (a := s))
  let step (m : ℕ) (t : ℝ) : ℝ := ((⌊(2 : ℝ) ^ m * t⌋ : ℝ) - 1) / (2 : ℝ) ^ m
  have hstep_meas (m : ℕ) : Measurable fun t : ℝ => massRestrict S (hA (step m t)) φ := by
    change Measurable ((fun k : ℤ => massRestrict S (hA (((k : ℝ) - 1) / (2 : ℝ) ^ m)) φ) ∘
      fun t : ℝ => ⌊(2 : ℝ) ^ m * t⌋)
    exact (measurable_of_countable _).comp (measurable_const.mul measurable_id).floor
  refine measurable_of_tendsto_metrizable hstep_meas (tendsto_pi_nhds.2 fun t => ?_)
  have hstep_lt (m : ℕ) : step m t < t := by
    have hc : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [div_lt_iff₀ hc]
    have hfl : (⌊(2 : ℝ) ^ m * t⌋ : ℝ) ≤ (2 : ℝ) ^ m * t := Int.floor_le _
    linarith
  have hstep_tendsto : Tendsto (fun m => step m t) atTop (𝓝 t) := by
    have hpow : Tendsto (fun m : ℕ => t - 2 * (2⁻¹ : ℝ) ^ m) atTop (𝓝 (t - 2 * 0)) :=
      tendsto_const_nhds.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by positivity : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹ : ℝ) < 1)).const_mul 2)
    rw [mul_zero, sub_zero] at hpow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hpow tendsto_const_nhds (fun m => ?_)
      fun m => (hstep_lt m).le
    have hc : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hfl : (2 : ℝ) ^ m * t - 1 < (⌊(2 : ℝ) ^ m * t⌋ : ℝ) := Int.sub_one_lt_floor _
    have hcalc : t - 2 * (2⁻¹ : ℝ) ^ m = ((2 : ℝ) ^ m * t - 2) / (2 : ℝ) ^ m := by
      rw [inv_pow]
      field_simp
    rw [hcalc, div_le_div_iff_of_pos_right hc]
    linarith
  simp_rw [massRestrict_apply]
  refine ((extendL1 S).continuous.tendsto _).comp ?_
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  have hnorm (m : ℕ) :
      ‖TestFunction.indicatorToLp 1 (massMeasure S) (hA (step m t)) φ -
          TestFunction.indicatorToLp 1 (massMeasure S) (hA t) φ‖ₑ =
        ∫⁻ x : Ω, ‖({y : Ω | u y < step m t}.indicator (fun y : Ω => φ y) x -
          {y : Ω | u y < t}.indicator (fun y : Ω => φ y) x)‖ₑ ∂massMeasure S := by
    rw [TestFunction.indicatorToLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub,
      Lp.eNorm_toLp, eLpNorm_one_eq_lintegral_eNorm
        ((((TestFunction.memLp_subtype (p := 1) φ).indicator (hA (step m t)).nullMeasurableSet).sub
          ((TestFunction.memLp_subtype φ).indicator
            (hA t).nullMeasurableSet)).aestronglyMeasurable)]
    rfl
  simp_rw [hnorm]
  rw [← lintegral_zero (μ := massMeasure S)]
  refine tendsto_lintegral_of_dominated_convergence' (fun x => 2 * ‖φ x‖ₑ)
    (fun m => ?_) (fun m => ae_of_all _ fun x => ?_) ?_ (ae_of_all _ fun x => ?_)
  · exact (((φ.continuous.comp continuous_subtype_val).aestronglyMeasurable.indicator
      (hA (step m t))).sub
      ((φ.continuous.comp continuous_subtype_val).aestronglyMeasurable.indicator (hA t))).eNorm
  · refine eNorm_sub_le.trans ?_
    dsimp only
    rw [two_mul]
    refine add_le_add ?_ ?_
    · by_cases hx : u x < step m t <;> simp [hx]
    · by_cases hx : u x < t <;> simp [hx]
  · rw [lintegral_const_mul' _ _ (by simp), ← TestFunction.enorm_toLp_one]
    exact ENNReal.mul_ne_top (by simp) eNorm_ne_top
  · refine tendsto_const_nhds.congr' ?_
    by_cases hxt : u x < t
    · filter_upwards [(tendsto_order.1 hstep_tendsto).1 _ hxt] with m hm
      simp [hm, hxt]
    · refine .of_forall fun m => ?_
      have hm : ¬u x < step m t := fun h => hxt (h.trans (hstep_lt m))
      simp [hm, hxt]

/-- For every `(k + 1)`-current `T`, every `u : E → ℝ`, and every test form `φ`, the level-set
pairing `t ↦ ⟨T, u, t⟩ φ` is Borel measurable. -/
theorem measurable_slice_apply (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) (u : E → ℝ)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) : Measurable fun t : ℝ => slice T u t φ := by
  by_cases hu : Measurable fun x : Ω => u x
  · simp_rw [slice_apply T hu φ]
    exact (measurable_massRestrict_lt_apply T hu (extDerivCLM φ)).sub
      (measurable_massRestrict_lt_apply (T ∘L extDerivCLM) hu φ)
  · simp [hu]

/-- For a locally normal current `T` and `u` continuous on `Ω`, `t ↦ ⟨T, u, t⟩ φ` is integrable on
`ℝ`. -/
theorem integrable_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Integrable fun t : ℝ => slice T u t φ := by
  have hcpt := hasCompactSupport_slice_apply hT hu φ
  let C : ℝ≥0∞ := ‖TestFunction.toLp 1 (massMeasure T) (extDerivCLM φ)‖ₑ +
    ‖TestFunction.toLp 1 (massMeasure (T ∘L extDerivCLM)) φ‖ₑ
  have hC : C ≠ ⊤ := ENNReal.add_ne_top.2 ⟨eNorm_ne_top, eNorm_ne_top⟩
  refine (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1 ?_
  refine ⟨(measurable_slice_apply T u φ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  refine ((setLIntegral_mono' (g := fun _ => C) hcpt.isClosed.measurableSet fun t _ => ?_).trans_lt
    ?_)
  · simpa [C, TestFunction.enorm_toLp_one] using enorm_slice_apply_le T u t φ
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hC.lt_top hcpt.measure_lt_top

/-- For a locally normal current `T`, `u` continuous on `Ω`, and `g : ℝ → ℝ` continuous,
`t ↦ g t * ⟨T, u, t⟩ φ` is integrable on `ℝ`. -/
theorem integrable_mul_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) {g : ℝ → ℝ} (hg : Continuous g)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Integrable fun t : ℝ => g t * slice T u t φ := by
  have hcpt := hasCompactSupport_slice_apply hT hu φ
  refine (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right g _).trans (subset_tsupport _))).1 ?_
  simpa only [smul_eq_mul] using
    (integrable_slice_apply hT hu φ).integrableOn.continuousOn_smul hg.continuousOn hcpt

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
  have hset : Set.inclusion h ⁻¹' {x : Ω | u x < t} = {x : Ω' | u x < t} := by
    ext x
    rfl
  ext φ
  rw [comp_apply, slice_apply T hu, slice_apply _ hu', extDerivCLM_monoCLM,
    ← comp_apply (g := massRestrict T hA), ← comp_apply (g := massRestrict (T ∘L extDerivCLM) hA),
    massRestrict_comp_monoCLM hT₁ h hA, massRestrict_comp_monoCLM hT₂ h hA,
    comp_monoCLM_comp_extDerivCLM,
    massRestrict_congr_set _ _ (measurableSet_lt hu' measurable_const) hset,
    massRestrict_congr_set _ _ (measurableSet_lt hu' measurable_const) hset]

/-- **Borel restriction commutes with proper smooth pushforward.** For `T` of locally finite mass
on `Ω`, a smooth map `Φ` on `Ω` proper over `Ω'`, and a measurable set `B ⊆ Ω'`,
`(Φ_# T) ⌞ B = Φ_# (T ⌞ Φ⁻¹(B))`. -/
theorem massRestrict_comp_pullbackCLM {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] {Ω' : Opens E'} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (hT : HasLocallyFiniteMass T)
    {B : Set Ω'} (hB : MeasurableSet B) :
    massRestrict (T ∘L pullbackCLM Φ hΦ hΦp) hB =
      massRestrict T
        ((Ω'.isOpen.measurableSet.subtype_image hB).preimage
          hΦ.continuousOn.domRestrict.measurable) ∘L
        pullbackCLM Φ hΦ hΦp := by
  let P : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) := pullbackCLM Φ hΦ hΦp
  have hB' : MeasurableSet ((↑) '' B : Set E') := Ω'.isOpen.measurableSet.subtype_image hB
  have hΦc : Continuous fun x : Ω => Φ x := hΦ.continuousOn.domRestrict
  let A : Set Ω := {x : Ω | Φ x ∈ ((↑) '' B : Set E')}
  have hA : MeasurableSet A := hB'.preimage hΦc.measurable
  ext φ
  cases isEmpty_or_nonempty Ω' with
  | inl hE =>
    have hφ0 : φ = 0 := DFunLike.ext _ _ fun z => by
      by_cases hz : z ∈ Ω'
      · exact (hE.false ⟨z, hz⟩).elim
      · simpa using image_eq_zero_of_notMem_tsupport (f := φ) fun h => hz (φ.tsupport_subset h)
    simp [hφ0]
  | inr hne =>
  let y₀ : Ω' := hne.some
  classical
  have hU : IsOpen {x : Ω | Φ x ∈ (Ω' : Set E')} := Ω'.isOpen.preimage hΦc
  let g : Ω → Ω' := fun x => if hx : Φ x ∈ Ω' then ⟨Φ x, hx⟩ else y₀
  have hg : Measurable g :=
    Measurable.dite (s := {x : Ω | Φ x ∈ (Ω' : Set E')})
      ((hΦc.comp continuous_subtype_val).subtype_mk fun p => p.2).measurable
      measurable_const hU.measurableSet
  let CΩ : Set Ω := (↑) ⁻¹' ((Ω : Set E) ∩ Φ ⁻¹' tsupport φ)
  have hCΩ : IsCompact CΩ :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
      (hΦp _ φ.hasCompactSupport φ.tsupport_subset)
      (by rw [Subtype.range_coe]; exact inter_subset_left)
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have : IsFiniteMeasure ((massMeasure T).restrict CΩ) := ⟨by simp [hCΩ.measure_lt_top]⟩
  let ν : Measure Ω' := ((massMeasure T).restrict CΩ).map g
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ g
  have hTP : HasLocallyFiniteMass (T ∘L P) := hT.comp_pullbackCLM
  let μ' : Measure Ω' := massMeasure (T ∘L P) + ν
  have : IsFiniteMeasureOnCompacts μ' :=
    ⟨fun _ hK => ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, measure_lt_top ν _⟩⟩
  let K' : Set Ω' := (↑) ⁻¹' tsupport φ
  have hK' : IsCompact K' :=
    Ω'.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' φ.hasCompactSupport
      (by simpa using φ.tsupport_subset)
  obtain ⟨χ, hχ⟩ := exists_testFunction_tendsto_lintegral_indicator μ' hB hK'
  have hlimL := tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hB φ hχ hTP
    (fun s => by simp [μ'])
  refine tendsto_nhds_unique hlimL ?_
  change Tendsto (fun m => (T ∘L P) (smulLeftCLM (contDiff_of_testFunction (χ m)) φ)) atTop
    (𝓝 (massRestrict T hA (P φ)))
  have heval (m : ℕ) : (T ∘L P) (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) =
      extendL1 T (TestFunction.toLp 1 (massMeasure T)
        (P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ))) := by
    rw [extendL1_toLp hT]
    rfl
  rw [massRestrict_apply]
  refine (tendsto_congr heval).2 (((extendL1 T).continuous.tendsto _).comp ?_)
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  have hle (m : ℕ) :
      ‖TestFunction.toLp 1 (massMeasure T) (P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ)) -
          TestFunction.indicatorToLp 1 (massMeasure T) hA (P φ)‖ₑ ≤
        (∫⁻ y : Ω', ‖χ m y - (B ∩ K').indicator (1 : Ω' → ℝ) y‖ₑ ∂μ') *
          ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ := by
    rw [TestFunction.toLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub,
      Lp.eNorm_toLp, eLpNorm_one_eq_lintegral_eNorm
        (((TestFunction.memLp_subtype (p := 1) _).sub
          ((TestFunction.memLp_subtype (P φ)).indicator
            hA.nullMeasurableSet)).aestronglyMeasurable),
      ← lintegral_mul_const' _ _ eNorm_ne_top]
    have hvanish : ∫⁻ x : Ω,
        ‖P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x -
          A.indicator (fun z : Ω => P φ z) x‖ₑ ∂massMeasure T =
        ∫⁻ x in CΩ,
          ‖P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x -
            A.indicator (fun z : Ω => P φ z) x‖ₑ ∂massMeasure T := by
      symm
      refine setLIntegral_eq_of_support_subset fun x hx => ?_
      by_contra hxC
      have hxts : Φ x ∉ tsupport φ := fun h => hxC ⟨x.2, h⟩
      have hφx : φ (Φ x) = 0 := image_eq_zero_of_notMem_tsupport hxts
      have hP1 : P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x = 0 := by
        ext v
        simp [P, pullbackCLM_apply_of_mem _ x.2, hφx]
      have hP2 : P φ x = 0 := by
        ext v
        simp [P, pullbackCLM_apply_of_mem _ x.2, hφx]
      have hA0 : A.indicator (fun z : Ω => P φ z) x = 0 := by
        by_cases hxA : x ∈ A <;> simp [hxA, hP2]
      exact Function.mem_support.1 hx
        (by rw [hP1, hA0, sub_zero, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero])
    have hpoint : ∀ x ∈ CΩ,
        ‖P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x -
            A.indicator (fun z : Ω => P φ z) x‖ₑ ≤
          ‖χ m (g x) - (B ∩ K').indicator (1 : Ω' → ℝ) (g x)‖ₑ *
            ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ := by
      intro x hxC
      have hxts : Φ x ∈ tsupport φ := hxC.2
      have hxΩ' : Φ x ∈ Ω' := φ.tsupport_subset hxts
      have hgx : g x = ⟨Φ x, hxΩ'⟩ := by simp [g, hxΩ']
      have hgK : g x ∈ K' := by simpa [K', hgx] using hxts
      have hxAB : x ∈ A ↔ g x ∈ B := by
        change Φ x ∈ ((↑) '' B : Set E') ↔ g x ∈ B
        rw [Subtype.coe_image, hgx]
        exact ⟨fun ⟨_, h2⟩ => by convert h2, fun hB' => ⟨hxΩ', hB'⟩⟩
      have hP1 : P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x = χ m (g x) • P φ x := by
        rw [pullbackCLM_apply_of_mem _ x.2, pullbackCLM_apply_of_mem _ x.2, hgx]
        ext v
        simp
      have hsub : P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x -
          A.indicator (fun z : Ω => P φ z) x =
          (χ m (g x) - (B ∩ K').indicator (1 : Ω' → ℝ) (g x)) • P φ x := by
        rw [hP1]
        by_cases hgB : g x ∈ B
        · have hxA : x ∈ A := hxAB.2 hgB
          simp [hxA, hgB, hgK, sub_smul]
        · have hxA : x ∉ A := fun h => hgB (hxAB.1 h)
          simp [hxA, hgB]
      rw [hsub, eNorm_smul]
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        (BoundedContinuousFunction.norm_coe_le_norm (P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F) x)
    have hf_meas : AEMeasurable
        (fun y : Ω' => ‖χ m y - (B ∩ K').indicator (1 : Ω' → ℝ) y‖ₑ *
          ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ) ν := by
      exact (((χ m).continuous.comp continuous_subtype_val).aestronglyMeasurable.sub
        (aestronglyMeasurable_const.indicator
          (hB.inter hK'.isClosed.measurableSet))).eNorm.mul_const _
    simp_rw [Pi.sub_apply]
    rw [hvanish]
    calc ∫⁻ x in CΩ, ‖P (smulLeftCLM (contDiff_of_testFunction (χ m)) φ) x -
            A.indicator (fun z : Ω => P φ z) x‖ₑ ∂massMeasure T
        ≤ ∫⁻ x in CΩ, ‖χ m (g x) - (B ∩ K').indicator (1 : Ω' → ℝ) (g x)‖ₑ *
            ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ ∂massMeasure T :=
          setLIntegral_mono' hCΩ.isClosed.measurableSet hpoint
      _ = ∫⁻ y : Ω', ‖χ m y - (B ∩ K').indicator (1 : Ω' → ℝ) y‖ₑ *
            ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ ∂ν :=
          (lintegral_map' hf_meas hg.aemeasurable).symm
      _ ≤ ∫⁻ y : Ω', ‖χ m y - (B ∩ K').indicator (1 : Ω' → ℝ) y‖ₑ *
            ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ ∂μ' :=
          lintegral_mono' (fun s => by simp [μ']) le_rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hle
  simpa only [zero_mul] using ENNReal.Tendsto.mul_const hχ (Or.inr eNorm_ne_top)

/-- **Slicing commutes with proper smooth pushforward** when `Φ` maps `Ω` into `Ω'`:
`⟨Φ_# T, u, t⟩ = Φ_# ⟨T, u ∘ Φ, t⟩` for any locally normal `T` and `u` measurable on `Ω'`. -/
theorem slice_comp_pullbackCLM {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] {Ω' : Opens E'} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    (hmaps : MapsTo Φ Ω Ω') {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) {u : E' → ℝ} (hu : Measurable fun y : Ω' => u y) (t : ℝ) :
    slice (T ∘L pullbackCLM Φ hΦ hΦp) u t =
      slice T (u ∘ Φ) t ∘L pullbackCLM Φ hΦ hΦp := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hΦc : Continuous fun x : Ω => Φ x := hΦ.continuousOn.domRestrict
  have hΦm : Measurable fun x : Ω => (⟨Φ x, hmaps x.2⟩ : Ω') :=
    (hΦc.subtype_mk fun x => hmaps x.2).measurable
  have huΦ : Measurable fun x : Ω => (u ∘ Φ) x := hu.comp hΦm
  let B : Set Ω' := {y : Ω' | u y < t}
  have hB : MeasurableSet B := measurableSet_lt hu (measurable_const (a := t))
  have hAeq : (fun x : Ω => Φ x) ⁻¹' ((↑) '' B : Set E') = {x : Ω | (u ∘ Φ) x < t} := by
    ext x
    change Φ x ∈ ((↑) '' B : Set E') ↔ (u ∘ Φ) x < t
    rw [Subtype.coe_image]
    exact ⟨fun ⟨_, hlt⟩ => hlt, fun hlt => ⟨hmaps x.2, hlt⟩⟩
  have hR₁ := massRestrict_comp_pullbackCLM (hΦ := hΦ) (hΦp := hΦp) hT₁ hB
  have hR₂ := massRestrict_comp_pullbackCLM (hΦ := hΦ) (hΦp := hΦp) hT₂ hB
  ext φ
  rw [slice_apply _ hu, comp_apply, slice_apply _ huΦ, hR₁,
    comp_pullbackCLM_comp_extDerivCLM T, hR₂, comp_apply, comp_apply, extDerivCLM_pullbackCLM]
  exact congrArg₂ (· - ·)
    (DFunLike.congr_fun (massRestrict_congr_set T _ _ hAeq) _)
    (DFunLike.congr_fun (massRestrict_congr_set (T ∘L extDerivCLM) _ _ hAeq) _)

/-- **Slicing commutes with proper smooth pushforward** for any globally measurable `u : E' → ℝ`,
without assuming `MapsTo Φ Ω Ω'`. -/
theorem slice_comp_pullbackCLM_of_measurable {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    {Ω' : Opens E'} {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    {u : E' → ℝ} (hu : Measurable u) (t : ℝ) :
    slice (T ∘L pullbackCLM Φ hΦ hΦp) u t =
      slice T (u ∘ Φ) t ∘L pullbackCLM Φ hΦ hΦp := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hu' : Measurable fun y : Ω' => u y := hu.comp measurable_subtype_coe
  have hΦc : Continuous fun x : Ω => Φ x := hΦ.continuousOn.domRestrict
  have huΦ : Measurable fun x : Ω => (u ∘ Φ) x := hu.comp hΦc.measurable
  let B : Set Ω' := {y : Ω' | u y < t}
  have hB : MeasurableSet B := measurableSet_lt hu' (measurable_const (a := t))
  have hB' : MeasurableSet ((↑) '' B : Set E') := Ω'.isOpen.measurableSet.subtype_image hB
  let A₀ : Set Ω := (fun x : Ω => Φ x) ⁻¹' ((↑) '' B : Set E')
  have hA₀ : MeasurableSet A₀ := hB'.preimage hΦc.measurable
  let A₁ : Set Ω := {x : Ω | (u ∘ Φ) x < t}
  have hA₁ : MeasurableSet A₁ := measurableSet_lt huΦ (measurable_const (a := t))
  have heq_restrict {m : ℕ} (S : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] ℝ)
      (η : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
      massRestrict S hA₀ (pullbackCLM Φ hΦ hΦp η) =
        massRestrict S hA₁ (pullbackCLM Φ hΦ hΦp η) := by
    simp only [massRestrict_apply]
    congr 1
    rw [TestFunction.indicatorToLp_apply, TestFunction.indicatorToLp_apply]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
    by_cases hxΩ' : Φ x ∈ Ω'
    · have hiff : x ∈ A₀ ↔ x ∈ A₁ := by
        simp [A₀, A₁, B, Subtype.coe_image, hxΩ']
      by_cases hx1 : x ∈ A₁
      · simp [hiff.2 hx1, hx1]
      · simp [mt hiff.1 hx1, hx1]
    · have hP0 : pullbackCLM Φ hΦ hΦp η x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hxΩ' (η.tsupport_subset (tsupport_pullbackCLM_subset η h).2)
      exact (indicator_apply_eq_zero (f := fun z : Ω => pullbackCLM Φ hΦ hΦp η z).2
        fun _ => hP0).trans
        (indicator_apply_eq_zero (f := fun z : Ω => pullbackCLM Φ hΦ hΦp η z).2
          fun _ => hP0).symm
  ext φ
  rw [slice_apply _ hu', comp_apply, slice_apply _ huΦ,
    massRestrict_comp_pullbackCLM hT₁ hB, comp_pullbackCLM_comp_extDerivCLM T,
    massRestrict_comp_pullbackCLM hT₂ hB, comp_apply, comp_apply, extDerivCLM_pullbackCLM]
  exact congrArg₂ (· - ·) (heq_restrict T (extDerivCLM φ)) (heq_restrict (T ∘L extDerivCLM) φ)

/-! ### The slicing inequality for smooth functions

The slice `⟨T, u, t⟩` is approximated by `-T ⌞ dfₘ` for the smooth multipliers
`fₘ x = ψ(cₘ (t - u x))`, where `ψ = Real.smoothTransition` and `cₘ = m + 1`. They increase to the
indicator of `{u < t}`, and `‖dfₘ‖ = cₘ ψ'(cₘ (t - u)) ‖du‖`, whose integral in `t` is `‖du‖`. -/

/-- For smooth `u`, `-T ⌞ dfₘ` with `fₘ x = ψ((m + 1) (t - u x))` converges weakly to
`⟨T, u, t⟩`. -/
theorem tendsto_neg_oneFormWedgeCLM_slice_apply
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (t : ℝ) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun m : ℕ =>
        -T (oneFormWedgeCLM (k := k)
          (contDiff_infty_iff_fderiv.1 (Real.smoothTransition.contDiff.comp
            (contDiff_const.mul (contDiff_const.sub hu)) :
              ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))).2 φ))
      atTop (𝓝 (slice T u t φ)) := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hum : Measurable fun x : Ω => u x := (hu.continuous.comp continuous_subtype_val).measurable
  have hA : MeasurableSet {x : Ω | u x < t} := measurableSet_lt hum measurable_const
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
  have h := (tendsto_apply_smulLeftCLM_massRestrict hT₁ hA hf hfC hlim (extDerivCLM φ)).sub
    (tendsto_apply_smulLeftCLM_massRestrict hT₂ hA hf hfC hlim φ)
  rw [← slice_apply _ hum] at h
  refine h.congr fun m => ?_
  have hL := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hf m)) φ
  simp only [comp_apply, sub_apply] at hL
  simp [hL]

/-- **Mass of a slice as a limit.** The slice is the weak limit of `-T ⌞ dfₘ` for
`fₘ x = ψ((m + 1) (t - u x))`, so its mass is at most the `liminf` of the weighted integrals
`(k + 1) ∫ (m + 1) ψ'((m + 1) (t - u)) ‖du‖ d‖T‖`. -/
private theorem mass_slice_le_liminf {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    mass (slice T u t) ≤ liminf (fun m : ℕ => (k + 1 : ℝ≥0∞) *
      ∫⁻ x, ENNReal.ofReal (((m : ℝ) + 1) *
        deriv Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) * ‖fderiv ℝ u x‖ₑ
        ∂massMeasure T) atTop := by
  obtain ⟨hT₁, -⟩ := isLocallyNormal_succ_iff.1 hT
  have hf (m : ℕ) : ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hu))
  refine (mass_le_liminf (fs := fun m =>
      -(T ∘ oneFormWedgeCLM (k := k) (contDiff_infty_iff_fderiv.1 (hf m)).2))
      (tendsto_neg_oneFormWedgeCLM_slice_apply hT hu t)).trans
    (liminf_le_liminf (.of_forall fun m => ?_))
  rw [mass_neg]
  refine (mass_comp_oneFormWedgeCLM_le_lintegral hT₁ _).trans_eq ?_
  simp_rw [(hu.differentiable (by simp) _).enorm_fderiv_smoothTransition_mul_sub
    (c := (m : ℝ) + 1) (by positivity)]

/-- A measurable majorant of `t ↦ M(⟨T, u, t⟩)` whose integral is at most
`(k + 1) ∫ ‖du‖ d‖T‖`. -/
theorem exists_measurable_mass_slice_le {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
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

section InnerProductSpace

/-- On a real inner product space, a measurable majorant of `t ↦ M(⟨T, u, t⟩)` has integral at
most `∫ ‖du‖ d‖T‖`, without the `(k + 1)` factor. -/
theorem exists_measurable_mass_slice_le_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧ (∀ t, mass (slice T w t) ≤ G t) ∧
      ∫⁻ t, G t ≤ ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂massMeasure T := by
  obtain ⟨hT₁, -⟩ := isLocallyNormal_succ_iff.1 hT
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hwm : Measurable fun x : U => w x := hw.continuous.measurable.comp measurable_subtype_coe
  have hdw : Measurable fun x : U => ‖fderiv ℝ w x‖ₑ := (continuous_eNorm.comp
    ((hw.continuous_fderiv (by simp)).comp continuous_subtype_val)).measurable
  have hf (t : ℝ) (m : ℕ) :
      ContDiff ℝ ∞ fun x => Real.smoothTransition (((m : ℝ) + 1) * (t - w x)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub hw))
  have hg' (m : ℕ) :=
    Real.smoothTransition.measurable_ofReal_mul_deriv_mul_sub_mul hwm hdw ((m : ℝ) + 1)
  have hg (m : ℕ) : Measurable fun t =>
      ∫⁻ x, ENNReal.ofReal (((m : ℝ) + 1) *
        deriv Real.smoothTransition (((m : ℝ) + 1) * (t - w x))) * ‖fderiv ℝ w x‖ₑ
        ∂massMeasure T :=
    (hg' m).lintegral_prod_right'
  refine ⟨_, .liminf hg, fun t => ?_, (lintegral_liminf_le hg).trans_eq ?_⟩
  · refine (mass_le_liminf (fs := fun m =>
        -(T ∘ oneFormWedgeCLM (k := k) (contDiff_infty_iff_fderiv.1 (hf t m)).2))
        (tendsto_neg_oneFormWedgeCLM_slice_apply hT hw t)).trans
      (liminf_le_liminf (.of_forall fun m => ?_))
    rw [mass_neg]
    refine (mass_comp_oneFormWedgeCLM_le_lintegral_of_innerProductSpace hT₁ _).trans_eq ?_
    simp_rw [(hw.differentiable (by simp) _).enorm_fderiv_smoothTransition_mul_sub
      (c := (m : ℝ) + 1) (by positivity)]
  · simp_rw [Real.smoothTransition.lintegral_lintegral_ofReal_mul_deriv_mul_sub_mul _ hwm hdw
      (Nat.cast_add_one_pos _)]
    exact liminf_const _

/-- **Sharp slicing inequality on an inner product space.** For a locally normal `(k + 1)`-current
`T` and smooth `w`, `∫ M(⟨T, w, t⟩) dt ≤ ∫ ‖dw‖ d‖T‖`. -/
theorem lintegral_mass_slice_le_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) :
    ∫⁻ t, mass (slice T w t) ≤ ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂massMeasure T := by
  obtain ⟨G, -, hG, hGint⟩ := exists_measurable_mass_slice_le_of_innerProductSpace hT hw
  exact (lintegral_mono hG).trans hGint

/-- **Sharp slicing inequality with a derivative bound on an inner product space.** If
`‖dw‖ ≤ L` on `U`, then `∫ M(⟨T, w, t⟩) dt ≤ L M(T)`. -/
theorem lintegral_mass_slice_le_mul_mass_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) {L : ℝ≥0∞}
    (hdw : ∀ x ∈ U, ‖fderiv ℝ w x‖ₑ ≤ L) :
    ∫⁻ t, mass (slice T w t) ≤ L * mass T :=
  (lintegral_mass_slice_le_of_innerProductSpace hT hw).trans
    (lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass fun x => hdw x x.2)

end InnerProductSpace

end Distribution
