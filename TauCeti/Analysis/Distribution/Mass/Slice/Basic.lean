/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.Distribution.TestFunction.Pullback
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Distribution.Mass.Pullback
import TauCeti.Analysis.Normed.Module.Alternating.SecondCountable

/-!
# Slicing currents by a function

Let `Ω` be an open set of a real normed space `E`, let `T` be a
`(k + 1)`-current on `Ω` (a continuous linear functional on the test `(k + 1)`-forms), and let
`u : E → ℝ` be Borel measurable on `Ω`. The **slice** of `T` by `u` at `t` is the `k`-current

`⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}`,

where `⌞` is the Borel restriction of a current of locally finite mass
(`Distribution.massRestrict`) and `∂S = S ∘ d`. It measures the failure of restriction to the
sublevel set `{u < t}` to commute with the boundary. It depends only on the values of `u` on `Ω`
and satisfies `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`. For locally normal `T`, slicing vanishes when `u` is
constant, is linear in `T`, commutes with open restrictions and proper smooth pushforwards, and
has `spt ⟨T, u, t⟩ ∩ Ω ⊆ spt T ∩ u⁻¹{t}` when `u` is continuous on `Ω`. For each test form `φ`,
the level-set pairing `t ↦ ⟨T, u, t⟩ φ` is Borel measurable for every `T`, and for locally normal
`T` and `u` continuous on `Ω` it is bounded, compactly supported, and integrable; when the codomain
`F` is second countable, `t ↦ localMass ⟨T, u, t⟩ U` and `t ↦ mass ⟨T, u, t⟩` are also Borel
measurable.

For a locally normal current `T` and a smooth function `u : E → ℝ` on the ambient space, the slice
is the weak limit of `-T ⌞ dfₘ` for smooth functions `fₘ` of `u` increasing to the indicator of
`{u < t}`; this follows from the Leibniz rule `∂(fT) = f ∂T - T ⌞ df` and dominated convergence
for the Borel restriction. Bounding the mass of `T ⌞ dfₘ` against the mass measure `‖T‖` and
integrating over `t` gives the **slicing inequality**

`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) ∫ ‖du‖ d‖T‖`,

where the mass is taken with respect to the operator norm on alternating forms (`Distribution.mass`)
and the factor `k + 1` comes from the unnormalized alternatization defining the wedge `du ∧ φ`.
In particular, for a normal current `T` and a smooth `u` with bounded derivative on `Ω`, almost
every slice is a normal current. On a real inner product space, `‖du ∧ φ‖ ≤ ‖du‖ * ‖φ‖` in the
operator (comass) norm, yielding the sharp bound

`∫ M(⟨T, u, t⟩) dt ≤ ∫ ‖du‖ d‖T‖`

free of the `(k + 1)` factor. Slices by Lipschitz functions are treated in
`TauCeti.Analysis.Distribution.Mass.Slice.Lipschitz`. If `E` is infinite-dimensional, every test
form is zero, so every current and every slice is zero.

## Main declarations

* `Distribution.slice`, `Distribution.slice_def`, `Distribution.slice_apply`,
  `Distribution.massRestrict_lt_comp_extDerivCLM`, `Distribution.slice_congr`,
  `Distribution.slice_eq_zero_of_not_finiteDimensional`: the slice `⟨T, u, t⟩`, zero by convention
  when `u` is not measurable on `Ω` or `E` is infinite-dimensional, the sublevel boundary identity
  `∂(T ⌞ {u < t}) = ⟨T, u, t⟩ + (∂T) ⌞ {u < t}`, and determination by `{x ∈ Ω | u x < t}` when
  both slicing functions are measurable on `Ω`.
* `Distribution.slice_const`: the slice of a locally normal current by a constant is zero.
* `Distribution.slice_comp_extDerivCLM`: the boundary law `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`.
* `Distribution.tendsto_slice_apply_of_eventually_iff`, `Distribution.tendsto_slice_apply`: slices
  converge when sublevel membership eventually agrees almost everywhere for `‖T‖` and `‖∂T‖`, and
  in particular when measurable slicing functions converge pointwise on `Ω` at levels charged
  neither by `‖T‖` nor by `‖∂T‖`.
* `Distribution.dsupport_slice_subset`, `Distribution.dsupport_slice_inter_subset`: support
  localization of a slice.
* `Distribution.measurable_slice_apply`, `Distribution.measurable_localMass_slice`,
  `Distribution.measurable_mass_slice`, `Distribution.hasCompactSupport_slice_apply`,
  `Distribution.integrable_mul_slice_apply`: regularity of `t ↦ ⟨T, u, t⟩ φ` and measurability of
  `t ↦ localMass ⟨T, u, t⟩ U` and `t ↦ M(⟨T, u, t⟩)`.
* `Distribution.slice_comp_monoCLM`, `Distribution.slice_comp_pullbackCLM_of_measurable_comp`,
  `Distribution.slice_comp_pullbackCLM`, `Distribution.slice_comp_pullbackCLM_of_measurable`:
  compatibility with open restriction and proper smooth pushforward.
* `Distribution.tendsto_neg_oneFormWedgeCLM_slice_apply`: weak convergence of the smooth-transition
  slice approximants.
* `Distribution.measurable_slice_apply_of_contDiff`,
  `Distribution.measurable_uncurry_slice_apply_of_contDiff`: level and joint measurability for
  weakly measurable families of locally normal currents sliced by a smooth function.
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

/-- For `u` measurable on `Ω`, `⟨T, u, t⟩ = ∂(T ⌞ {u < t}) - (∂T) ⌞ {u < t}` as continuous linear
maps. -/
theorem slice_def (hu : Measurable fun x : Ω => u x) :
    slice T u t =
      massRestrict T (measurableSet_lt hu (measurable_const (a := t))) ∘L extDerivCLM -
        massRestrict (T ∘L extDerivCLM) (measurableSet_lt hu (measurable_const (a := t))) := by
  simp [slice, hu]

/-- For `u` measurable on `Ω`, the slice evaluates as
`(T ⌞ {u < t}) (dφ) - ((∂T) ⌞ {u < t}) φ`. -/
theorem slice_apply (hu : Measurable fun x : Ω => u x) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    slice T u t φ =
      massRestrict T (measurableSet_lt hu (measurable_const (a := t))) (extDerivCLM φ) -
        massRestrict (T ∘L extDerivCLM) (measurableSet_lt hu (measurable_const (a := t))) φ := by
  simp [slice_def T hu]

/-- **Sublevel boundary identity.** For `u` measurable on `Ω`,
`∂(T ⌞ {u < t}) = ⟨T, u, t⟩ + (∂T) ⌞ {u < t}`. -/
theorem massRestrict_lt_comp_extDerivCLM (hu : Measurable fun x : Ω => u x) (t : ℝ) :
    massRestrict T (measurableSet_lt hu (measurable_const (a := t))) ∘L extDerivCLM =
      slice T u t +
        massRestrict (T ∘L extDerivCLM) (measurableSet_lt hu (measurable_const (a := t))) := by
  rw [slice_def T hu, sub_add_cancel]

/-- The slice by a function not measurable on `Ω` is zero by convention. -/
@[simp]
theorem slice_of_not_measurable (hu : ¬Measurable fun x : Ω => u x) : slice T u t = 0 := by
  simp [slice, hu]

/-- Two slicing functions that are both measurable on `Ω` and share the same sublevel set in `Ω`
give the same slice. -/
theorem slice_congr {v : E → ℝ} (hu : Measurable fun x : Ω => u x)
    (hv : Measurable fun x : Ω => v x) (h : {x : Ω | u x < t} = {x : Ω | v x < t}) :
    slice T u t = slice T v t := by
  ext φ
  rw [slice_apply _ hu, slice_apply _ hv,
    massRestrict_congr_set (T := T) _ _ h,
    massRestrict_congr_set (T := T ∘L extDerivCLM) _ _ h]

/-- The slice depends only on the restriction of `u` to `Ω`. -/
theorem slice_congr_of_eqOn (huv : EqOn u v Ω) : slice T u t = slice T v t := by
  have hfun : (fun x : Ω => u x) = fun x : Ω => v x := funext fun x => huv x.property
  by_cases hu : Measurable fun x : Ω => u x
  · exact slice_congr T hu (hfun ▸ hu) (by ext x; simp [huv x.property])
  · rw [slice_of_not_measurable T hu, slice_of_not_measurable T (hfun ▸ hu)]

/-- The slice of the zero current is zero. -/
@[simp]
theorem slice_zero : slice (0 : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) u t = 0 := by
  by_cases hu : Measurable fun x : Ω => u x
  · ext φ; simp [slice_apply _ hu]
  · simp [hu]

/-- If `E` is infinite-dimensional, every test form is zero, so every slice is zero. -/
theorem slice_eq_zero_of_not_finiteDimensional (hE : ¬FiniteDimensional ℝ E) :
    slice T u t = 0 := by
  ext φ; simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]

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
  rw [← neg_one_smul ℝ T, slice_smul]; exact neg_one_smul ℝ (slice T u t)

end Defs

/-- The slice of a locally normal current by a constant function is zero. -/
@[simp]
theorem slice_const {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (c t : ℝ) : slice T (fun _ => c) t = 0 := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  ext φ
  rw [slice_apply _ measurable_const, zero_apply]
  by_cases hct : c < t
  · have h : {_x : Ω | c < t} = univ := eq_univ_of_forall fun _ => hct
    rw [massRestrict_congr_set (T := T) _ MeasurableSet.univ h,
      massRestrict_congr_set (T := T ∘L extDerivCLM) _ MeasurableSet.univ h,
      massRestrict_univ_apply hT₁, massRestrict_univ_apply hT₂, comp_apply, sub_self]
  · have h : {_x : Ω | c < t} = ∅ := eq_empty_of_forall_notMem fun _ hx => hct hx
    simp [massRestrict_congr_set (T := T) _ MeasurableSet.empty h,
      massRestrict_congr_set (T := T ∘L extDerivCLM) _ MeasurableSet.empty h,
      massRestrict_eq_zero MeasurableSet.empty (by simp)]

/-- Slicing is additive on locally normal currents. -/
@[simp]
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
@[simp]
theorem slice_sub {T S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T)
    (hS : IsLocallyNormal S) (u : E → ℝ) (t : ℝ) :
    slice (T - S) u t = slice T u t - slice S u t := by
  rw [sub_eq_add_neg, slice_add hT hS.neg, slice_neg, sub_eq_add_neg]

/-- **The boundary of a slice.** `∂⟨T, u, t⟩ = -⟨∂T, u, t⟩`. -/
@[simp]
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
    rw [slice_apply _ hum, massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h =>
          hx (h1' _ (hφ (tsupport_extDerivCLM_subset φ h)))),
      massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (h1' _ (hφ h))),
      comp_apply, sub_self]
  have hv₃ : IsVanishingOn (slice T u t) U₂ := fun φ hφ => by
    rw [slice_apply _ hum, massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ fun x hx =>
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
  swap; · simp [hum]
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  let hA := measurableSet_lt hum (measurable_const (a := t))
  rcases le_or_gt t (-M) with ht1 | ht1
  · have hv {m : ℕ} {ψ : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)} (hψ : tsupport ψ ⊆ tsupport φ) :
        ∀ x : Ω, x ∈ {x : Ω | u x < t} → ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
      fun h => (not_lt.2 ht1) ((neg_lt_of_abs_lt (hφ x (hψ h))).trans hx)
    rw [slice_apply _ hum,
      massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ (hv (tsupport_extDerivCLM_subset φ))),
      massRestrict_apply_eq_zero_of_ae hA (ae_of_all _ (hv Subset.rfl)), sub_zero]
  · have htM : M < t := not_le.1 fun hle => ht ⟨ht1, hle⟩
    have hv {m : ℕ} {ψ : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)} (hψ : tsupport ψ ⊆ tsupport φ) :
        ∀ x : Ω, x ∉ {x : Ω | u x < t} → ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
      fun h => hx ((le_abs_self (u x)).trans_lt ((hφ x (hψ h)).trans htM))
    rw [slice_apply _ hum,
      massRestrict_apply_eq_apply_of_ae hT₁ hA (ae_of_all _ (hv (tsupport_extDerivCLM_subset φ))),
      massRestrict_apply_eq_apply_of_ae hT₂ hA (ae_of_all _ (hv Subset.rfl)), comp_apply, sub_self]

/-- If `T` is locally normal and `u` is continuous on `Ω`, then `t ↦ ⟨T, u, t⟩ φ` vanishes outside
a bounded interval of levels `t`, hence has compact support. -/
theorem hasCompactSupport_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContinuousOn u Ω) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    HasCompactSupport fun t => slice T u t φ := by
  obtain ⟨M, _, hM⟩ := φ.exists_pos_norm_lt_of_continuousOn hu
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) M) fun t ht => ?_
  have ht' : M < |t| := by simpa [Metric.mem_closedBall, Real.dist_eq] using ht
  refine slice_apply_eq_zero_of_notMem_Ioc hT (M := M)
    (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx) fun htI =>
    ht'.not_ge (abs_le.2 ⟨htI.1.le, htI.2⟩)

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
  -- `SecondCountableTopology (E [⋀^Fin k]→L[ℝ] F)` requires `FiniteDimensional ℝ E`.
  by_cases hE : FiniteDimensional ℝ E
  · exact measurable_localMass (fun t => (slice T u t).continuous) (measurable_slice_apply T u) U
  · simp_rw [show ∀ t : ℝ, localMass (slice T u t) U = 0 from fun t => le_antisymm
      (localMass_le_iff.2 fun φ _ _ => by simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE])
      bot_le]
    exact measurable_const

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

/-- **Slicing commutes with proper smooth pushforward** under domain measurability hypotheses on
`u` and `u ∘ Φ`: `⟨Φ_# T, u, t⟩ = Φ_# ⟨T, u ∘ Φ, t⟩`. -/
theorem slice_comp_pullbackCLM_of_measurable_comp {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    {Ω' : Opens E'} {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsLocallyNormal T) {u : E' → ℝ}
    (hu' : Measurable fun y : Ω' => u y) (huΦ : Measurable fun x : Ω => (u ∘ Φ) x) (t : ℝ) :
    slice (T ∘L pullbackCLM Φ hΦ hΦp) u t =
      slice T (u ∘ Φ) t ∘L pullbackCLM Φ hΦ hΦp := by
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  have hB : MeasurableSet {y : Ω' | u y < t} := measurableSet_lt hu' (measurable_const (a := t))
  let A₀ : Set Ω := (fun x : Ω => Φ x) ⁻¹' ((↑) '' {y : Ω' | u y < t} : Set E')
  have hA₀ : MeasurableSet A₀ :=
    (Ω'.isOpen.measurableSet.subtype_image hB).preimage hΦ.continuousOn.domRestrict.measurable
  have hA₁ : MeasurableSet {x : Ω | (u ∘ Φ) x < t} := measurableSet_lt huΦ measurable_const
  have heq {m : ℕ} (S : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] ℝ) (η : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
      massRestrict S hA₀ (pullbackCLM Φ hΦ hΦp η) =
        massRestrict S hA₁ (pullbackCLM Φ hΦ hΦp η) := by
    simp only [massRestrict_apply, TestFunction.indicatorToLp_apply]
    refine congrArg (extendL1 S) (MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_))
    by_cases hxΩ' : Φ x ∈ Ω'
    · have hiff : x ∈ A₀ ↔ (u ∘ Φ) x < t := by simp [A₀, Subtype.coe_image, hxΩ']
      by_cases hx1 : (u ∘ Φ) x < t
      · rw [Set.indicator_of_mem (hiff.2 hx1), Set.indicator_of_mem hx1]
      · rw [Set.indicator_of_notMem (mt hiff.1 hx1), Set.indicator_of_notMem hx1]
    · have h0 : pullbackCLM Φ hΦ hΦp η x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hxΩ' (η.tsupport_subset (tsupport_pullbackCLM_subset η h).2)
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
  slice_comp_pullbackCLM_of_measurable_comp hT hu
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
  slice_comp_pullbackCLM_of_measurable_comp hT (hu.comp measurable_subtypeVal)
    (hu.comp hΦ.continuousOn.domRestrict.measurable) t

/-- **Convergence of slices from sublevel-set agreement.** If functions `vᵢ` measurable on `Ω`
eventually share sublevel membership `{vᵢ < t} ↔ {u < t}` almost everywhere for both `‖T‖` and
`‖∂T‖`, then `⟨T, vᵢ, t⟩ φ → ⟨T, u, t⟩ φ` for every test form `φ`. -/
theorem tendsto_slice_apply_of_eventually_iff {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) {v : ι → E → ℝ}
    (hv : ∀ i, Measurable fun x : Ω => v i x) (hu : Measurable fun x : Ω => u x)
    (hT : ∀ᵐ x : Ω ∂massMeasure T, ∀ᶠ i in l, (v i x < t ↔ u x < t))
    (hdT : ∀ᵐ x : Ω ∂massMeasure (T ∘L extDerivCLM), ∀ᶠ i in l, (v i x < t ↔ u x < t))
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun i => slice T (v i) t φ) l (𝓝 (slice T u t φ)) := by
  simp_rw [slice_apply _ (hv _), slice_apply _ hu]
  exact (tendsto_massRestrict_apply _ _ hT (extDerivCLM φ)).sub
    (tendsto_massRestrict_apply _ _ hdT φ)

/-- **Convergence of slices.** If functions `vᵢ` measurable on `Ω` converge pointwise on `Ω` to
a function `u` measurable on `Ω`, and neither `‖T‖` nor `‖∂T‖` charges the level set `u⁻¹{t}`,
then `⟨T, vᵢ, t⟩ → ⟨T, u, t⟩` on every test form. -/
theorem tendsto_slice_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) {v : ι → E → ℝ}
    (hv : ∀ i, Measurable fun x : Ω => v i x) (hu : Measurable fun x : Ω => u x)
    (hlim : ∀ x ∈ Ω, Tendsto (fun i => v i x) l (𝓝 (u x)))
    (hT : massMeasure T {x | u x = t} = 0)
    (hdT : massMeasure (T ∘L extDerivCLM) {x | u x = t} = 0) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun i => slice T (v i) t φ) l (𝓝 (slice T u t φ)) := by
  -- Off the level set, membership in the sublevel sets of `vᵢ` eventually matches that of `u`.
  have hev (x : Ω) (hx : x ∉ {x : Ω | u x = t}) : ∀ᶠ i in l, (v i x < t ↔ u x < t) := by
    rcases lt_or_gt_of_ne hx with h | h
    · filter_upwards [(hlim x x.property).eventually_lt_const h] with i hi; simp [hi, h]
    · filter_upwards [(hlim x x.property).eventually_const_lt h] with i hi
      simp [hi.not_gt, h.not_gt]
  exact tendsto_slice_apply_of_eventually_iff T hv hu
    (measure_eq_zero_iff_ae_notMem.1 hT |>.mono hev)
    (measure_eq_zero_iff_ae_notMem.1 hdT |>.mono hev) φ

/-! ### The slicing inequality for smooth functions

The slice `⟨T, u, t⟩` is approximated by `-T ⌞ dfₘ` for the smooth multipliers
`fₘ x = ψ(cₘ (t - u x))`, where `ψ = Real.smoothTransition` and `cₘ = m + 1`. They increase to the
indicator of `{u < t}`, and `‖dfₘ‖ = cₘ ψ'(cₘ (t - u)) ‖du‖`, whose integral in `t` is `‖du‖`. -/

/-- For a locally normal `(k + 1)`-current `T` and a smooth function `u : E → ℝ` on the ambient
space, `-T ⌞ dfₘ` with `fₘ x = ψ((m + 1) (t - u x))` converges weakly to `⟨T, u, t⟩`. -/
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
  exact h.congr fun m => apply_smulLeftCLM_extDerivCLM_sub T (hf m) φ

/-- For a weakly measurable family of locally normal `(k + 1)`-currents
`T : α → 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ` and a smooth function `u : E → ℝ` on the ambient
space, `a ↦ ⟨T a, u, t⟩ φ` is measurable for every level `t` and every test form `φ`. -/
theorem measurable_slice_apply_of_contDiff {α : Type*} [MeasurableSpace α]
    {T : α → 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hTm : ∀ ψ, Measurable fun a => T a ψ) (hTn : ∀ a, IsLocallyNormal (T a))
    (hu : ContDiff ℝ ∞ u) (t : ℝ) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Measurable fun a => slice (T a) u t φ :=
  measurable_of_tendsto_metrizable (fun _ => (hTm _).neg)
    (tendsto_pi_nhds.2 fun a => tendsto_neg_oneFormWedgeCLM_slice_apply (hTn a) hu t φ)

/-- For a weakly measurable family of locally normal `(k + 1)`-currents
`T : α → 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ` and a smooth function `u : E → ℝ` on the ambient
space, the joint pairing `(a, t) ↦ ⟨T a, u, t⟩ φ` is measurable on `α × ℝ`. -/
theorem measurable_uncurry_slice_apply_of_contDiff {α : Type*} [MeasurableSpace α]
    {T : α → 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hTm : ∀ ψ, Measurable fun a => T a ψ) (hTn : ∀ a, IsLocallyNormal (T a))
    (hu : ContDiff ℝ ∞ u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Measurable fun p : α × ℝ => slice (T p.1) u p.2 φ := by
  have hum : Measurable fun x : Ω => u x := (hu.continuous.comp continuous_subtypeVal).measurable
  let step (m : ℕ) (t : ℝ) : ℝ := ((⌊(2 : ℝ) ^ m * t⌋ : ℝ) - 1) / (2 : ℝ) ^ m
  have hstep_meas (m : ℕ) : Measurable fun p : α × ℝ => slice (T p.1) u (step m p.2) φ := by
    let f (j : ℤ) (a : α) : ℝ := slice (T a) u (((j : ℝ) - 1) / (2 : ℝ) ^ m) φ
    have hf (j : ℤ) : Measurable (f j) := measurable_slice_apply_of_contDiff hTm hTn hu _ φ
    let k' (t : ℝ) : ℤ := ⌊(2 : ℝ) ^ m * t⌋
    have hk' : Measurable k' := (measurable_const.mul measurable_id).floor
    intro s hs
    have hpre : (fun p : α × ℝ => slice (T p.1) u (step m p.2) φ) ⁻¹' s =
        ⋃ j : ℤ, (f j ⁻¹' s) ×ˢ (k' ⁻¹' {j}) := by
      ext ⟨a, t⟩
      simp only [mem_preimage, mem_iUnion, mem_prod, mem_singleton_iff, step, k', f]
      exact ⟨fun h => ⟨⌊(2 : ℝ) ^ m * t⌋, h, rfl⟩, fun ⟨_, hj1, hj2⟩ => hj2 ▸ hj1⟩
    rw [hpre]
    exact MeasurableSet.iUnion fun j => (hf j hs).prod (hk' (MeasurableSet.singleton j))
  refine measurable_of_tendsto_metrizable hstep_meas (tendsto_pi_nhds.2 fun ⟨a, t⟩ => ?_)
  have hstep_lt (m : ℕ) : step m t < t := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
    linarith [Int.floor_le ((2 : ℝ) ^ m * t)]
  have hstep_tendsto : Tendsto (fun m => step m t) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds (x := t)).sub ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by positivity : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).const_mul 2))
      tendsto_const_nhds (fun m => ?_) (fun m => (hstep_lt m).le)
    have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [show t - 2 * ((2 : ℝ) ^ m)⁻¹ = ((2 : ℝ) ^ m * t - 2) / (2 : ℝ) ^ m by field_simp,
      div_le_div_iff_of_pos_right hpow]
    linarith [Int.sub_one_lt_floor ((2 : ℝ) ^ m * t)]
  have hev (x : Ω) : ∀ᶠ m in atTop, (u x < step m t ↔ u x < t) := by
    by_cases hxt : u x < t
    · exact ((tendsto_order.1 hstep_tendsto).1 _ hxt).mono fun m hm => ⟨fun _ => hxt, fun _ => hm⟩
    · exact .of_forall fun m => ⟨fun h => (hxt (h.trans (hstep_lt m))).elim, fun h => (hxt h).elim⟩
  simp_rw [slice_apply _ hum]
  exact (tendsto_massRestrict_apply _ _ (ae_of_all _ hev) (extDerivCLM φ)).sub
    (tendsto_massRestrict_apply _ _ (ae_of_all _ hev) φ)

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
    exact ⟨0, measurable_const, fun t => by simp [slice_eq_zero_of_not_finiteDimensional _ hE],
      by simp⟩
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hum : Measurable fun x : Ω => u x := hu.continuous.measurable.comp measurable_subtypeVal
  have hdu : Measurable fun x : Ω => ‖fderiv ℝ u x‖ₑ := (continuous_eNorm.comp
    ((hu.continuous_fderiv (by simp)).comp continuous_subtypeVal)).measurable
  have hf (t : ℝ) (m : ℕ) := hu.smoothTransition_mul_sub ((m : ℝ) + 1) t
  have hg' (m : ℕ) :=
    Real.smoothTransition.measurable_ofReal_mul_deriv_mul_sub_mul hum hdu ((m : ℝ) + 1)
  have hg (m : ℕ) : Measurable fun t => c *
      ∫⁻ x, ENNReal.ofReal (((m : ℝ) + 1) *
        deriv Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) * ‖fderiv ℝ u x‖ₑ ∂massMeasure T :=
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

/-- For a locally normal `(k + 1)`-current `T` and a smooth function `u : E → ℝ` on the ambient
space, a measurable majorant of `t ↦ M(⟨T, u, t⟩)` whose integral is at most
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
  obtain ⟨_, -, hG, hGint⟩ := exists_measurable_mass_slice_le hT hu
  exact (lintegral_mono hG).trans hGint

/-- **The slicing inequality with a Lipschitz bound.** For a locally normal `(k + 1)`-current `T`
and a smooth function `u : E → ℝ` on the ambient space with `‖du‖ ≤ L` on `Ω`,
`∫ M(⟨T, u, t⟩) dt ≤ (k + 1) L M(T)`. -/
theorem lintegral_mass_slice_le_mul_mass {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) {L : ℝ≥0∞}
    (hdu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ₑ ≤ L) :
    ∫⁻ t, mass (slice T u t) ≤ (k + 1) * L * mass T := by
  rw [mul_assoc]
  exact (lintegral_mass_slice_le hT hu).trans <| mul_le_mul_right
    (lintegral_massMeasure_le_mul_mass hT.hasLocallyFiniteMass fun x => hdu x x.property) _

/-- For a locally normal `(k + 1)`-current `T` and a smooth function `u : E → ℝ` on the ambient
space with `∫ ‖du‖ d‖T‖ < ⊤`, almost every slice `⟨T, u, t⟩` has finite mass. -/
theorem ae_mass_slice_lt_top {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u)
    (hfin : ∫⁻ x, ‖fderiv ℝ u x‖ₑ ∂massMeasure T ≠ ⊤) :
    ∀ᵐ t, mass (slice T u t) < ⊤ := by
  obtain ⟨G, hGm, hG, hGint⟩ := exists_measurable_mass_slice_le hT hu
  filter_upwards [ae_lt_top hGm (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) hfin) hGint)] with t ht
  exact (hG t).trans_lt ht

/-- If almost every slice by `u` of every normal current has finite mass, then almost every slice
of a normal current `T` is normal: the boundary of a slice of `T` is minus a slice of `∂T`. -/
theorem ae_isNormal_slice_of_ae_mass_lt_top {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsNormal T)
    (h : ∀ {j : ℕ} (S : 𝓓(Ω, E [⋀^Fin (j + 1)]→L[ℝ] F) →L[ℝ] ℝ), IsNormal S →
      ∀ᵐ t, mass (slice S u t) < ⊤) :
    ∀ᵐ t, IsNormal (slice T u t) := by
  cases k with
  | zero => exact (h T hT).mono fun t ht => isNormal_finZero_iff.2 ht.ne
  | succ j =>
    filter_upwards [h T hT, h _ hT.comp_extDerivCLM] with t ht ht'
    exact isNormal_succ_iff.2 ⟨ht.ne, by simpa [slice_comp_extDerivCLM, mass_neg] using ht'.ne⟩

/-- **Slices of normal currents are normal.** If `T` is a normal `(k + 1)`-current and `u` is
smooth with `‖du‖ ≤ L < ⊤` on `Ω`, then almost every slice `⟨T, u, t⟩` is a normal current. -/
theorem ae_isNormal_slice {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hu : ContDiff ℝ ∞ u) {L : ℝ≥0∞} (hL : L ≠ ⊤) (hdu : ∀ x ∈ Ω, ‖fderiv ℝ u x‖ₑ ≤ L) :
    ∀ᵐ t, IsNormal (slice T u t) :=
  ae_isNormal_slice_of_ae_mass_lt_top hT fun _ hS =>
    ae_mass_slice_lt_top hS.isLocallyNormal hu
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top hL hS.mass_ne_top)
        (lintegral_massMeasure_le_mul_mass hS.isLocallyNormal.hasLocallyFiniteMass fun x =>
          hdu x x.property))

section InnerProductSpace

/-- On a real inner product space, for a locally normal `(k + 1)`-current `T` and a smooth function
`w : V → ℝ` on the ambient space, a measurable majorant of `t ↦ M(⟨T, w, t⟩)` has integral at most
`∫ ‖dw‖ d‖T‖`, without the `(k + 1)` factor. -/
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
`T` and a smooth function `w : V → ℝ` on the ambient space, `∫ M(⟨T, w, t⟩) dt ≤ ∫ ‖dw‖ d‖T‖`. -/
theorem lintegral_mass_slice_le_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {U : Opens V} {w : V → ℝ}
    {T : 𝓓(U, V [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hw : ContDiff ℝ ∞ w) :
    ∫⁻ t, mass (slice T w t) ≤ ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂massMeasure T := by
  obtain ⟨_, -, hG, hGint⟩ := exists_measurable_mass_slice_le_of_innerProductSpace hT hw
  exact (lintegral_mono hG).trans hGint

/-- **Sharp slicing inequality with a derivative bound on an inner product space.** For a locally
normal `(k + 1)`-current `T` and a smooth function `w : V → ℝ` on the ambient space with `‖dw‖ ≤ L`
on `U`, `∫ M(⟨T, w, t⟩) dt ≤ L M(T)`. -/
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
