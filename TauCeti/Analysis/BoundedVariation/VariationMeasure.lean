/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
public import TauCeti.MeasureTheory.Measure.ContentOfOpens
import TauCeti.Topology.Sets.Opens

/-!
# The variation measure of a function of locally finite variation

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and let `u : E → ℝ`
be locally integrable on `Ω`. The variational total variation `|Du|(U)` of `u` on open sets
`U ⊆ Ω` (`TauCeti.totalVariationOn`) is the restriction to open sets of a regular Borel measure
on `Ω`, the **variation measure** `|Du|` (`TauCeti.variationMeasure`), provided `u` has locally
finite variation on `Ω`: every compact `K ⊆ Ω` has an open neighbourhood `U` with
`|Du|(U) < ∞`. No global finiteness of the variation is needed, so this covers functions of
locally bounded variation on unbounded open sets, and perimeter measures of sets of locally
finite perimeter.

The construction is the De Giorgi–Letta criterion in the form of Mathlib's contents. As a
function of the open set, the total variation is countably subadditive
(`TauCeti.totalVariationOn_iSup_le_tsum`) and additive on disjoint open sets
(`TauCeti.totalVariationOn_sup_of_disjoint`). The set function
`K ↦ inf { |Du|(U) | K ⊆ U ⊆ Ω open }` on the compact subsets of `Ω` is therefore a content
(`TauCeti.contentOfOpens`), whose measure agrees with `|Du|` on open sets because a test vector
field is admissible on every open neighbourhood of its compact support. Uniqueness among outer
regular measures follows from `MeasureTheory.Measure.OuterRegular.ext_isOpen`.

## Main declarations

* `TauCeti.forall_isCompact_exists_totalVariationOn_ne_top_iff`: along an exhaustion of `Ω` by
  relatively compact open sets, the variation is locally finite on `Ω` exactly when it is finite
  on each of them.
* `TauCeti.variationMeasure μ Ω u`: the variation measure `|Du|` on `Ω`, a regular measure.
* `TauCeti.variationMeasure_preimage_coe`: `|Du|(U) = totalVariationOn μ U u` for every open
  `U ⊆ Ω`, and `TauCeti.variationMeasure_univ`: `|Du|(Ω) = totalVariationOn μ Ω u`.
* `TauCeti.enorm_integral_divergenceCLM_mul_le_variationMeasure`: a test vector field of norm at
  most one supported in an open `U ⊆ Ω` pairs with `u` to at most `|Du|(U)`.
* `TauCeti.eq_variationMeasure`: an outer regular measure with these values on open sets is
  the variation measure.
* `TauCeti.variationMeasure_eq_comap_inclusion` and `TauCeti.map_inclusion_variationMeasure`:
  for open `U ⊆ Ω`, the variation measure on `U` is that on `Ω` pulled back to `U`, and pushes
  forward to its restriction to `U`.
* `TauCeti.variationMeasure_congr_ae`: the variation measure only depends on `u` almost
  everywhere on `Ω`.
* `TauCeti.variationMeasure_const_sub`: against an additive Haar measure, `c - u` has the same
  variation measure as `u`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1 (the structure theorem for functions of locally bounded variation).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §1.5 (the De Giorgi–Letta criterion) and §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set TestFunction
open scoped ENNReal Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω U V : Opens E} {u v : E → ℝ}

/-! ### The variation content -/

section Content

variable [OpensMeasurableSpace E]

variable (hu : LocallyIntegrableOn u Ω μ)
  (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)

/-- The variation content on `Ω`: the outer approximation of the total variation on compact
subsets of `Ω`, which is finite by local finiteness of the variation. -/
private def variationContent : Content Ω :=
  contentOfOpens (m := fun V => totalVariationOn μ V u) (fun _ _ h => totalVariationOn_mono h)
    (fun _ _ hV₁ hV₂ => totalVariationOn_sup_le (hu.mono_set (sup_le hV₁ hV₂)))
    (fun _ _ hV₁ hV₂ h => (totalVariationOn_sup_of_disjoint (hu.mono_set (sup_le hV₁ hV₂)) h).ge)
    hfin

/-- The measure of the variation content on an open set `U ⊆ Ω` is the total variation on `U`. -/
private theorem variationContent_measure_preimage_coe [BorelSpace E] (hU : U ≤ Ω) :
    (variationContent hu hfin).measure ((↑) ⁻¹' (U : Set E)) = totalVariationOn μ U u := by
  refine contentOfOpens_measure_preimage_coe _ _ _ _ (totalVariationOn_le_iff.mpr fun φ hφ => ?_)
  -- The support of `φ` is a compact subset of `Ω`, on which the outer approximation is tested.
  have himage : ((↑) : Ω → E) '' ((↑) ⁻¹' tsupport φ) = tsupport φ :=
    image_preimage_eq_of_subset (by simpa using φ.tsupport_subset.trans hU)
  let K : Compacts Ω := ⟨(↑) ⁻¹' tsupport φ, by
    rw [Subtype.isCompact_iff, himage]
    exact φ.hasCompactSupport.isCompact⟩
  refine le_iSup₂_of_le K (preimage_mono φ.tsupport_subset) (le_opensInf fun V hV _ => ?_)
  exact ofReal_integral_le_totalVariationOn_of_tsupport_subset φ hφ (himage ▸ hV)

end Content

/-! ### Local finiteness of the variation -/

/-- Along an exhaustion `V` of `Ω` by open sets with compact closures in `Ω`, a function has locally
finite variation on `Ω` exactly when it has finite variation on every `V j`. -/
theorem forall_isCompact_exists_totalVariationOn_ne_top_iff {V : ℕ → Opens E}
    (hVc : ∀ j, IsCompact (closure (V j : Set E))) (hVΩ : ∀ j, closure (V j : Set E) ⊆ Ω)
    (hVmono : Monotone V) (hVU : ⋃ j, (V j : Set E) = Ω) {w : E → ℝ} :
    (∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U w ≠ ∞) ↔
      ∀ j, totalVariationOn μ (V j) w ≠ ∞ := by
  refine ⟨fun h j => ?_, fun h K hK hKΩ => ?_⟩
  · obtain ⟨U, hU, hfin⟩ := h _ (hVc j) (hVΩ j)
    exact ne_top_of_le_ne_top hfin (totalVariationOn_mono (subset_closure.trans hU))
  · obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j => (V j : Set E)) (fun j => (V j).isOpen)
      (hVU ▸ hKΩ) fun i j => ⟨max i j, hVmono (le_max_left i j), hVmono (le_max_right i j)⟩
    exact ⟨V j, hj, h j⟩

/-! ### The variation measure -/

section Measure

variable [BorelSpace E]

open scoped Classical in
/-- The **variation measure** `|Du|` of `u` on the open set `Ω`: if `u` is locally integrable on
`Ω` and has locally finite variation there, meaning that every compact `K ⊆ Ω` has an open
neighbourhood `U` with `totalVariationOn μ U u < ∞`, it is the regular measure on `Ω` whose value
on every open `U ⊆ Ω` is the total variation of `u` on `U`
(`TauCeti.variationMeasure_preimage_coe`). Otherwise it is `0` by convention. -/
def variationMeasure (μ : Measure E) (Ω : Opens E) (u : E → ℝ) : Measure Ω :=
  if h : LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞ then
    (variationContent h.1 h.2).measure
  else 0

/-- The variation measure is a regular measure. -/
instance : (variationMeasure μ Ω u).Regular := by
  have := Ω.isOpen.locallyCompactSpace
  unfold variationMeasure
  split_ifs <;> infer_instance

/-- **The total variation is a measure.** The variation measure of a function of locally finite
variation on `Ω` gives every open set `U ⊆ Ω` its total variation `|Du|(U)`. -/
theorem variationMeasure_preimage_coe (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hU : U ≤ Ω) :
    variationMeasure μ Ω u ((↑) ⁻¹' (U : Set E)) = totalVariationOn μ U u := by
  rw [variationMeasure, dite_eq_left ⟨hu, hfin⟩, variationContent_measure_preimage_coe hu hfin hU]

/-- A test vector field on `Ω` supported in an open set `U ⊆ Ω` with norm at most one pairs with
`u` to at most `|Du|(U)`. -/
theorem enorm_integral_divergenceCLM_mul_le_variationMeasure (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hU : U ≤ Ω) (φ : 𝓓(Ω, E)) (hφU : tsupport φ ⊆ U) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∫ x, divergenceCLM φ x * u x ∂μ‖ₑ ≤ variationMeasure μ Ω u ((↑) ⁻¹' (U : Set E)) := by
  let φU : 𝓓(U, E) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφU⟩
  have hdiv (x : E) : divergenceCLM φU x = divergenceCLM φ x := by simp [φU]
  rw [variationMeasure_preimage_coe hu hfin hU, Real.enorm_eq_ofReal_abs]
  simpa only [hdiv] using ofReal_abs_integral_le_totalVariationOn (μ := μ) (u := u) φU hφ

/-- The total mass of the variation measure of a function of locally finite variation on `Ω` is
its total variation `|Du|(Ω)`. -/
theorem variationMeasure_univ (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) :
    variationMeasure μ Ω u univ = totalVariationOn μ Ω u := by
  rw [← variationMeasure_preimage_coe hu hfin le_rfl]
  exact congrArg _ (eq_univ_of_forall fun x => x.2).symm

/-- The variation measure is `0` for a function which is not locally integrable on `Ω` or does
not have locally finite variation there. -/
theorem variationMeasure_eq_zero_of_not (h : ¬(LocallyIntegrableOn u Ω μ ∧
    ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)) :
    variationMeasure μ Ω u = 0 :=
  dite_eq_right h

/-- **Uniqueness of the variation measure.** An outer regular measure on `Ω` which gives every
open set `U ⊆ Ω` the total variation `|Du|(U)` is the variation measure. -/
theorem eq_variationMeasure (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {ν : Measure Ω} [ν.OuterRegular]
    (h : ∀ U : Opens E, U ≤ Ω → ν ((↑) ⁻¹' (U : Set E)) = totalVariationOn μ U u) :
    ν = variationMeasure μ Ω u := by
  refine Measure.OuterRegular.ext_isOpen fun W hW => ?_
  obtain ⟨U, hU, rfl⟩ := Ω.exists_le_preimage_coe_eq hW
  rw [h U hU, variationMeasure_preimage_coe hu hfin hU]

/-- **Restriction to an open subset.** For `U ⊆ Ω` open, the variation measure on `U` is the
pullback of the variation measure on `Ω` along the inclusion `U → Ω`. -/
theorem variationMeasure_eq_comap_inclusion (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hU : U ≤ Ω) :
    variationMeasure μ U u =
      (variationMeasure μ Ω u).comap (inclusion (SetLike.coe_subset_coe.2 hU)) := by
  have hemb := Opens.isOpenEmbedding_of_le hU
  have := Measure.OuterRegular.comap' (variationMeasure μ Ω u) hemb.continuous
    hemb.measurableEmbedding
  refine (eq_variationMeasure (hu.mono_set hU) (fun K hK hKU => hfin K hK (hKU.trans hU))
    fun V hV => ?_).symm
  rw [hemb.measurableEmbedding.comap_apply,
    ← variationMeasure_preimage_coe hu hfin (hV.trans hU)]
  -- The inclusion carries the trace of `V` on `U` onto its trace on `Ω`.
  congr 1
  ext x
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨⟨x, hV hx⟩, hx, rfl⟩⟩

/-- For `U ⊆ Ω` open, the pushforward of the variation measure on `U` along the inclusion
`U → Ω` is the restriction of the variation measure on `Ω` to the trace of `U`. -/
theorem map_inclusion_variationMeasure (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hU : U ≤ Ω) :
    (variationMeasure μ U u).map (inclusion (SetLike.coe_subset_coe.2 hU)) =
      (variationMeasure μ Ω u).restrict ((↑) ⁻¹' (U : Set E)) := by
  rw [variationMeasure_eq_comap_inclusion hu hfin hU,
    (Opens.isOpenEmbedding_of_le hU).measurableEmbedding.map_comap, range_inclusion]
  rfl

/-- The variation measure on `Ω` only depends on local integrability on `Ω` and on the total
variations on open subsets of `Ω`. -/
theorem variationMeasure_congr (hloc : LocallyIntegrableOn u Ω μ ↔ LocallyIntegrableOn v Ω μ)
    (htv : ∀ U : Opens E, U ≤ Ω → totalVariationOn μ U u = totalVariationOn μ U v) :
    variationMeasure μ Ω u = variationMeasure μ Ω v := by
  -- Local finiteness of the variation only needs neighbourhoods inside `Ω`.
  have hfin {w : E → ℝ} : (∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U w ≠ ∞) ↔
      ∀ K, IsCompact K → K ⊆ Ω →
        ∃ U : Opens E, K ⊆ (U : Set E) ∧ U ≤ Ω ∧ totalVariationOn μ U w ≠ ∞ := by
    refine forall₃_congr fun K _ hKΩ => ⟨fun ⟨U, hKU, hU⟩ => ⟨U ⊓ Ω, ?_, inf_le_right,
      ne_top_of_le_ne_top hU (totalVariationOn_mono inf_le_left)⟩,
      fun ⟨U, hKU, _, hU⟩ => ⟨U, hKU, hU⟩⟩
    simpa using ⟨hKU, hKΩ⟩
  have hiff : (LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) ↔
      (LocallyIntegrableOn v Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U v ≠ ∞) := by
    rw [hloc, hfin, hfin]
    refine and_congr_right fun _ => forall₃_congr fun K _ _ => exists_congr fun U => ?_
    exact and_congr_right fun _ => and_congr_right fun hU => by rw [htv U hU]
  by_cases hu : LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞
  · have hv := hiff.1 hu
    exact eq_variationMeasure hv.1 hv.2 fun U hU => by
      rw [variationMeasure_preimage_coe hu.1 hu.2 hU, htv U hU]
  · rw [variationMeasure_eq_zero_of_not hu, variationMeasure_eq_zero_of_not (hiff.not.1 hu)]

/-- **Locality.** The variation measure on `Ω` only depends on `u` almost everywhere on `Ω`. -/
theorem variationMeasure_congr_ae (h : u =ᵐ[μ.restrict Ω] v) :
    variationMeasure μ Ω u = variationMeasure μ Ω v :=
  variationMeasure_congr (locallyIntegrableOn_congr h) fun _ hU =>
    totalVariationOn_congr_ae (ae_restrict_of_ae_restrict_of_subset hU h)

/-- Against an additive Haar measure, `c - u` has the same variation measure as `u`. In
particular the indicators of a set and of its complement have the same variation measure. -/
@[simp]
theorem variationMeasure_const_sub [μ.IsAddHaarMeasure] (c : ℝ) :
    variationMeasure μ Ω (fun x => c - u x) = variationMeasure μ Ω u := by
  have hc : LocallyIntegrableOn (fun _ : E => c) Ω μ :=
    (locallyIntegrable_const c).locallyIntegrableOn _
  refine variationMeasure_congr ⟨fun h => ?_, fun h => hc.sub h⟩ fun U _ =>
    totalVariationOn_const_sub c
  exact (locallyIntegrableOn_congr (ae_of_all _ fun x => sub_sub_cancel c (u x))).1 (hc.sub h)

end Measure

end TauCeti
