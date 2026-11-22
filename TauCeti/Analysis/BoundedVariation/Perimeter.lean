/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The perimeter of a set in an open set

The **perimeter** of a set `s` in an open set `Ω` of a finite-dimensional real inner product space
is the total variation of its indicator on `Ω` (`TauCeti.perimeter`). For a measurable `s` this is
De Giorgi's extended perimeter

`P(s; Ω) = ⨆ { ∫_s div φ | φ ∈ 𝓓(Ω, E), ‖φ x‖ ≤ 1 for all x }`

(`TauCeti.perimeter_eq_iSup`), defined without any regularity of its topological boundary. It is
the measure-theoretic notion of boundary area: a measurable set has finite perimeter in `Ω`
exactly when `P(s; Ω) < ∞`, which does not require `s` to have finite volume. The perimeter is
meaningful when `s ∩ Ω` is null-measurable; otherwise the integrals in the supremum may be
Mathlib's junk value `0` for non-integrable functions, and the perimeter may then be a junk value
carrying no geometric meaning.

The perimeter only sees `s` up to null sets (`TauCeti.perimeter_congr_ae`), so topological
frontier and perimeter can differ, and it only sees `s ∩ Ω`
(`TauCeti.perimeter_congr_of_inter_eq`). Against an additive Haar measure, complements have the same
perimeter (`TauCeti.perimeter_compl`), since their indicators differ by a constant. The perimeter
is carried by the topological frontier: a set has no perimeter in an open set disjoint from its
frontier (`TauCeti.perimeter_eq_zero_of_disjoint_frontier`), so perimeters add up over sets with
disjoint closures (`TauCeti.perimeter_union_of_disjoint_closure`). Lower
semicontinuity under local convergence in measure (`TauCeti.perimeter_le_liminf`) supplies
the semicontinuity half of the direct method for perimeter problems.

## Main declarations

* `TauCeti.perimeter μ Ω s`: the perimeter of `s` in `Ω`.
* `TauCeti.perimeter_eq_iSup`: the perimeter of a null-measurable set as a supremum of `∫_s div φ`.
* `TauCeti.perimeter_congr_ae`, `TauCeti.perimeter_congr_of_inter_eq`, `TauCeti.perimeter_mono`
  and `TauCeti.perimeter_iSup`: invariance under null modification inside `Ω` and locality, and
  monotonicity and inner continuity in `Ω`.
* `TauCeti.perimeter_compl`, `TauCeti.perimeter_empty`, `TauCeti.perimeter_univ`,
  `TauCeti.perimeter_of_subsingleton`, `TauCeti.perimeter_smul_measure` and
  `TauCeti.perimeter_eq_addHaarScalarFactor_mul`.
* `TauCeti.perimeter_eq_zero_of_disjoint_frontier` and
  `TauCeti.perimeter_eq_of_frontier_inter_subset`: the perimeter is carried by the frontier.
* `TauCeti.perimeter_union_of_disjoint_closure`: additivity for sets with disjoint closures.
* `TauCeti.perimeter_le_liminf`: lower semicontinuity of the perimeter.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 and
  Proposition 12.15.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Filter TestFunction Set
open scoped ENNReal NNReal Distributions Topology symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω Ω' : Opens E} {s t : Set E}

/-- The **perimeter** of a set `s` in the open set `Ω`, relative to the measure `μ`: the total
variation of the indicator of `s` on `Ω`. For a null-measurable `s` it is the extended supremum
of `∫_s div φ ∂μ` over test vector fields `φ ∈ 𝓓(Ω, E)` with `‖φ x‖ ≤ 1` everywhere
(`TauCeti.perimeter_eq_iSup`). -/
def perimeter (μ : Measure E) (Ω : Opens E) (s : Set E) : ℝ≥0∞ :=
  totalVariationOn μ Ω (s.indicator 1)

/-- The perimeter is the total variation of the indicator. -/
theorem perimeter_def : perimeter μ Ω s = totalVariationOn μ Ω (s.indicator 1) :=
  (rfl)

/-- **The perimeter by duality.** For a null-measurable set `s`,
`P(s; Ω) = ⨆ { ∫_s div φ ∂μ | φ ∈ 𝓓(Ω, E), ‖φ‖ ≤ 1 }`. -/
theorem perimeter_eq_iSup (hs : NullMeasurableSet s μ) : perimeter μ Ω s =
    ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x in s, divergenceCLM φ x ∂μ) := by
  rw [perimeter_def, totalVariationOn_def]
  refine iSup_congr fun φ => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  rw [← integral_indicator₀ hs]
  congr 1 with x
  by_cases hx : x ∈ s <;> simp [hx]

/-- **Locality.** Modifying a set by a null set inside `Ω` does not change its perimeter in
`Ω`. -/
theorem perimeter_congr_ae (h : s =ᵐ[μ.restrict Ω] t) : perimeter μ Ω s = perimeter μ Ω t :=
  totalVariationOn_congr_ae (indicator_ae_eq_of_ae_eq_set h)

/-- **Locality of the perimeter.** Sets that agree on `Ω` have the same perimeter in `Ω`. -/
theorem perimeter_congr_of_inter_eq [OpensMeasurableSpace E] (h : s ∩ Ω = t ∩ Ω) :
    perimeter μ Ω s = perimeter μ Ω t :=
  perimeter_congr_ae <| eventuallyEqSet_iff.2 <| (ae_restrict_mem Ω.isOpen.measurableSet).mono
    fun y hy => by simpa [hy] using Set.ext_iff.1 h y

/-- The perimeter grows with the open set. -/
theorem perimeter_mono (h : Ω' ≤ Ω) : perimeter μ Ω' s ≤ perimeter μ Ω s :=
  totalVariationOn_mono h

/-- **Inner continuity in the open set.** The perimeter in the union of a directed family of open
sets is the supremum of the perimeters in its members. -/
theorem perimeter_iSup {ι : Type*} {Ω : ι → Opens E} (hΩ : Directed (· ≤ ·) Ω) :
    perimeter μ (⨆ i, Ω i) s = ⨆ i, perimeter μ (Ω i) s :=
  totalVariationOn_iSup hΩ

/-- The empty set has perimeter zero. -/
@[simp]
theorem perimeter_empty : perimeter μ Ω ∅ = 0 := by
  rw [perimeter_def, indicator_empty]
  exact totalVariationOn_zero

/-- In dimension zero every set has perimeter zero, for every measure. -/
@[simp]
theorem perimeter_of_subsingleton [Subsingleton E] : perimeter μ Ω s = 0 :=
  totalVariationOn_of_subsingleton

/-- The perimeter of a subset `t ⊆ s` with respect to `μ.restrict s` agrees with its perimeter with
respect to `μ`, because the indicator of `t` vanishes off `s`. -/
theorem perimeter_restrict_of_subset {t : Set E} (h : t ⊆ s) :
    perimeter (μ.restrict s) Ω t = perimeter μ Ω t := by
  rw [perimeter_def, perimeter_def, totalVariationOn_def, totalVariationOn_def]
  refine iSup_congr fun φ => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp [indicator_of_notMem (fun hxt => hx (h hxt))]

/-- Scaling the reference measure by `c : ℝ≥0` scales the perimeter by `c`. -/
@[simp]
theorem perimeter_smul_measure (c : ℝ≥0) :
    perimeter (c • μ) Ω s = (c : ℝ≥0∞) * perimeter μ Ω s :=
  totalVariationOn_smul_measure c

section Haar

variable [BorelSpace E] [μ.IsAddHaarMeasure]

/-- Any two additive Haar measures rescale perimeter by their Haar scalar factor. -/
theorem perimeter_eq_addHaarScalarFactor_mul (ν : Measure E) [ν.IsAddHaarMeasure] :
    perimeter μ Ω s = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) * perimeter ν Ω s := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  exact perimeter_smul_measure _

/-- **Complements have the same perimeter**, against an additive Haar measure. No measurability
of `s` is needed: the indicators of `s` and `sᶜ` differ by a constant up to sign. -/
@[simp]
theorem perimeter_compl : perimeter μ Ω sᶜ = perimeter μ Ω s := by
  have h : sᶜ.indicator (1 : E → ℝ) = fun x => (-s.indicator 1) x + 1 := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [perimeter_def, perimeter_def, h, totalVariationOn_add_const, totalVariationOn_neg]

/-- The whole space has perimeter zero, against an additive Haar measure. -/
@[simp]
theorem perimeter_univ : perimeter μ Ω univ = 0 := by
  rw [← compl_empty, perimeter_compl, perimeter_empty]

/-- **No perimeter off the frontier.** Against an additive Haar measure, a set has perimeter zero
in every open set disjoint from its topological frontier. No measurability of `s` is needed: on
such an open set `s` agrees with its interior, and the indicator is locally constant. -/
theorem perimeter_eq_zero_of_disjoint_frontier (h : Disjoint (frontier s) Ω) :
    perimeter μ Ω s = 0 := by
  -- On `Ω` the set `s` agrees with its interior, and `Ω` is covered by the interior of `s` and the
  -- complement of its closure, on each of which the indicator is constant.
  let U : Opens E := Ω ⊓ ⟨interior s, isOpen_interior⟩
  let V : Opens E := Ω ⊓ ⟨(closure s)ᶜ, isClosed_closure.isOpen_compl⟩
  have hx {x : E} (hx : x ∈ Ω) : x ∈ interior s ∨ x ∉ closure s := by
    by_contra! hx'
    exact h.ne_of_mem ⟨hx'.2, hx'.1⟩ hx rfl
  have hΩ : Ω = U ⊔ V := by
    refine le_antisymm (fun x hxΩ => ?_) (sup_le inf_le_left inf_le_left)
    rcases hx hxΩ with hxs | hxs
    · exact Or.inl ⟨hxΩ, hxs⟩
    · exact Or.inr ⟨hxΩ, hxs⟩
  have hs : s ∩ Ω = interior s ∩ Ω := by
    refine Subset.antisymm (fun x ⟨hxs, hxΩ⟩ => ⟨?_, hxΩ⟩)
      (inter_subset_inter_left _ interior_subset)
    exact (hx hxΩ).resolve_right (not_not.2 (subset_closure hxs))
  have hU : perimeter μ U (interior s) = 0 := by
    rw [perimeter_congr_of_inter_eq (t := univ) (by simp [U, inter_comm]), perimeter_univ]
  have hV : perimeter μ V (interior s) = 0 := by
    rw [perimeter_congr_of_inter_eq (t := ∅) ?_, perimeter_empty]
    rw [empty_inter]
    exact eq_empty_of_forall_notMem fun x ⟨hxs, hxV⟩ => hxV.2 (subset_closure (interior_subset hxs))
  rw [perimeter_congr_of_inter_eq hs, hΩ]
  refine le_antisymm ?_ zero_le
  have := totalVariationOn_sup_le (μ := μ) (Ω := U) (Ω' := V) (u := (interior s).indicator 1)
    (locallyIntegrableOn_indicator_const isOpen_interior.measurableSet.nullMeasurableSet 1)
  simp only [← perimeter_def] at this
  simpa [hU, hV] using this

/-- **The perimeter is carried by the frontier.** Against an additive Haar measure, if an open set
`Ω' ⊆ Ω` contains the part of the topological frontier of `s` inside `Ω`, then `s` has the same
perimeter in `Ω'` as in `Ω`. -/
theorem perimeter_eq_of_frontier_inter_subset (hs : NullMeasurableSet s (μ.restrict Ω))
    (hΩ' : Ω' ≤ Ω) (h : frontier s ∩ Ω ⊆ Ω') : perimeter μ Ω' s = perimeter μ Ω s := by
  -- Off its frontier the set has no perimeter, and `Ω` is covered by `Ω'` and the rest of `Ω`.
  let W : Opens E := Ω ⊓ ⟨(frontier s)ᶜ, isClosed_frontier.isOpen_compl⟩
  have hΩ : Ω = Ω' ⊔ W := by
    refine le_antisymm (fun x hx => ?_) (sup_le hΩ' inf_le_left)
    by_cases hx' : x ∈ frontier s
    · exact Or.inl (h ⟨hx', hx⟩)
    · exact Or.inr ⟨hx, hx'⟩
  have hW : perimeter μ W s = 0 :=
    perimeter_eq_zero_of_disjoint_frontier (disjoint_left.2 fun _ hx hxW => hxW.2 hx)
  refine le_antisymm (perimeter_mono hΩ') ?_
  have := totalVariationOn_sup_le (μ := μ) (Ω := Ω') (Ω' := W) (u := s.indicator 1)
    (by rw [← Opens.coe_sup, ← hΩ]; exact locallyIntegrableOn_indicator_const hs 1)
  simp only [← perimeter_def, ← hΩ, hW, add_zero] at this
  exact this

/-- **Additivity for sets with disjoint closures.** Against an additive Haar measure, sets `s` and
`t` that are null-measurable on `Ω` and have disjoint closures satisfy
`P(s ∪ t; Ω) = P(s; Ω) + P(t; Ω)`. Disjointness of `s` and `t` alone does not suffice: in `ℝ`, the
intervals `(0, 1)` and `(1, 2)` have perimeter `2` each, while their union agrees a.e. with
`(0, 2)`, of perimeter `2`. -/
theorem perimeter_union_of_disjoint_closure (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) (h : Disjoint (closure s) (closure t)) :
    perimeter μ Ω (s ∪ t) = perimeter μ Ω s + perimeter μ Ω t := by
  -- Separate the closures by disjoint open sets `U ⊇ closure s` and `V ⊇ closure t`. The
  -- perimeters of `s`, `t` and `s ∪ t` in `Ω` are carried by `Ω ∩ U`, `Ω ∩ V` and their union.
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := normal_separation isClosed_closure isClosed_closure h
  let ΩU : Opens E := Ω ⊓ ⟨U, hU⟩
  let ΩV : Opens E := Ω ⊓ ⟨V, hV⟩
  have hdisj : Disjoint ΩU ΩV := by
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    simpa [ΩU, ΩV, ← disjoint_iff_inter_eq_empty] using
      hUV.mono inter_subset_right inter_subset_right
  have hst : NullMeasurableSet (s ∪ t) (μ.restrict Ω) := hs.union ht
  have hsΩ : perimeter μ ΩU s = perimeter μ Ω s :=
    perimeter_eq_of_frontier_inter_subset hs inf_le_left fun x hx =>
      ⟨hx.2, hsU (frontier_subset_closure hx.1)⟩
  have htΩ : perimeter μ ΩV t = perimeter μ Ω t :=
    perimeter_eq_of_frontier_inter_subset ht inf_le_left fun x hx =>
      ⟨hx.2, htV (frontier_subset_closure hx.1)⟩
  have hstΩ : perimeter μ (ΩU ⊔ ΩV) (s ∪ t) = perimeter μ Ω (s ∪ t) := by
    refine perimeter_eq_of_frontier_inter_subset hst (sup_le inf_le_left inf_le_left) fun x hx => ?_
    have hx' : x ∈ closure (s ∪ t) := frontier_subset_closure hx.1
    rw [closure_union] at hx'
    rcases hx' with hxs | hxt
    · exact Or.inl ⟨hx.2, hsU hxs⟩
    · exact Or.inr ⟨hx.2, htV hxt⟩
  have hsU' : perimeter μ ΩU (s ∪ t) = perimeter μ ΩU s := by
    refine perimeter_congr_of_inter_eq ?_
    rw [union_inter_distrib_right, union_eq_left]
    rintro x ⟨hxt, -, hxU⟩
    exact (hUV.ne_of_mem hxU (htV (subset_closure hxt)) rfl).elim
  have htV' : perimeter μ ΩV (s ∪ t) = perimeter μ ΩV t := by
    refine perimeter_congr_of_inter_eq ?_
    rw [union_inter_distrib_right, union_eq_right]
    rintro x ⟨hxs, -, hxV⟩
    exact (hUV.ne_of_mem (hsU (subset_closure hxs)) hxV rfl).elim
  have hli : LocallyIntegrableOn ((s ∪ t).indicator (1 : E → ℝ)) (ΩU ⊔ ΩV : Opens E) μ :=
    locallyIntegrableOn_indicator_const
      (hst.mono (Measure.restrict_mono_set μ (sup_le inf_le_left inf_le_left))) 1
  have := totalVariationOn_sup_of_disjoint hli hdisj
  simp only [← perimeter_def, hstΩ, hsU', htV', hsΩ, htΩ] at this
  exact this

end Haar

/-! ### Lower semicontinuity -/

/-- **Lower semicontinuity of the perimeter.** If the sets `s i` converge to `s₀` locally in
measure in `Ω`, that is `μ ((s i ∆ s₀) ∩ K) → 0` for every compact `K ⊆ Ω`, then
`P(s₀; Ω) ≤ liminf P(s i; Ω)`. -/
theorem perimeter_le_liminf [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ] {ι : Type*}
    {l : Filter ι} {s : ι → Set E} {s₀ : Set E}
    (hs : ∀ᶠ i in l, NullMeasurableSet (s i) μ) (hs₀ : NullMeasurableSet s₀ μ)
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => μ ((s i ∆ s₀) ∩ K)) l (𝓝 0)) :
    perimeter μ Ω s₀ ≤ liminf (fun i => perimeter μ Ω (s i)) l := by
  -- The indicator of a null-measurable set is locally integrable.
  have hli {t : Set E} (ht : NullMeasurableSet t μ) :
      LocallyIntegrableOn (t.indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const (ht.mono Measure.restrict_le_self) 1
  refine totalVariationOn_le_liminf (hs.mono fun i hi => hli hi) (hli hs₀) fun K hK hKΩ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h K hK hKΩ)
    (fun _ => zero_le) fun i => ?_
  have hpt : ∀ x, ‖(s i).indicator (1 : E → ℝ) x - s₀.indicator 1 x‖ₑ =
      (s i ∆ s₀).indicator 1 x := fun x => by
    by_cases h₁ : x ∈ s i <;> by_cases h₂ : x ∈ s₀ <;> simp [mem_symmDiff, h₁, h₂]
  simp_rw [hpt]
  exact (lintegral_indicator_one_le _).trans
    (Measure.restrict_apply' hK.isClosed.measurableSet).le

end TauCeti
