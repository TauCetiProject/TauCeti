/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.MeasureTheory.LpComp
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# `L²` of a measure splits over a countable measurable partition

Extension by zero,

```text
F ↦ s.indicator F,
```

is a linear isometry `L²(μ|_s) →ₗᵢ[ℂ] L²(μ)` for every measurable `s`.  Over a countable
measurable partition of the space these isometries have pairwise orthogonal ranges spanning a
dense subspace, so

```text
L²(μ)  ≅  ⊕ₙ L²(μ|_{Bₙ})
```

as a Hilbert sum, and the isomorphism commutes with multiplication by any bounded measurable
symbol.

This is the one Hilbert-space step in the multiplicity construction.  Everything after it --
dominating a countable family of measures, passing to level sets, and rearranging the fibres --
is carried out on *measures*, where it is elementary, and transported back through this
decomposition together with the Radon--Nikodym unitary of
`ForTauCeti/MeasureTheory/RadonNikodymL2.lean` and the relabelling unitary of
`ForTauCeti/MeasureTheory/LpComp.lean`.

## Main results

* `TauCeti.extendLp`: the extension-by-zero isometry.
* `TauCeti.inner_extendLp_eq_zero_of_disjoint`: orthogonality of the ranges over disjoint sets.
* `TauCeti.isHilbertSum_extendLp`: **the decomposition**, as a `MeasureTheory.IsHilbertSum`.
* `TauCeti.extendLp_mulLp`: extension by zero intertwines the multiplication operators.

## Design notes

The analytic content is a single Mathlib lemma,
`MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`; everything else is bookkeeping about
almost-everywhere representatives.  Denseness is proved in the contrapositive -- the orthogonal
complement of the supremum of the ranges is trivial -- which avoids any summability argument:
a vector orthogonal to every range has zero restriction to every piece of the partition, hence
vanishes almost everywhere.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

section Indicator

/-- Extension by zero is well defined on almost-everywhere classes: functions that agree
`μ|_s`-almost everywhere have indicators that agree `μ`-almost everywhere. -/
theorem indicator_ae_eq_of_restrict (hs : MeasurableSet s) {f g : α → ℂ}
    (h : f =ᵐ[μ.restrict s] g) : s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at h
  filter_upwards [h] with x hx
  by_cases hxs : x ∈ s
  · simp [hxs, hx hxs]
  · simp [hxs]

/-- **Extension by zero**, on representatives.  The indicator of a square-integrable class for
the restricted measure is square-integrable for the ambient one. -/
noncomputable def extendLpFun (μ : Measure α) (hs : MeasurableSet s)
    (F : Lp ℂ 2 (μ.restrict s)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hs.nullMeasurableSet).mpr (Lp.memLp F)).toLp
    (s.indicator (F : α → ℂ))

/-- Extension by zero, on representatives: the class is represented by the indicator. -/
theorem coeFn_extendLpFun (μ : Measure α) (hs : MeasurableSet s) (F : Lp ℂ 2 (μ.restrict s)) :
    (extendLpFun μ hs F : α → ℂ) =ᵐ[μ] s.indicator (F : α → ℂ) :=
  MemLp.coeFn_toLp _

/-- Extension by zero is additive; the indicator of a sum is the sum of the indicators. -/
theorem extendLpFun_add (μ : Measure α) (hs : MeasurableSet s)
    (F G : Lp ℂ 2 (μ.restrict s)) :
    extendLpFun μ hs (F + G) = extendLpFun μ hs F + extendLpFun μ hs G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendLpFun μ hs (F + G),
    indicator_ae_eq_of_restrict (μ := μ) hs (Lp.coeFn_add F G),
    Lp.coeFn_add (extendLpFun μ hs F) (extendLpFun μ hs G),
    coeFn_extendLpFun μ hs F, coeFn_extendLpFun μ hs G] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3]
  simp only [Pi.add_apply]
  rw [h4, h5]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Extension by zero is homogeneous. -/
theorem extendLpFun_smul (μ : Measure α) (hs : MeasurableSet s) (c : ℂ)
    (F : Lp ℂ 2 (μ.restrict s)) :
    extendLpFun μ hs (c • F) = c • extendLpFun μ hs F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendLpFun μ hs (c • F),
    indicator_ae_eq_of_restrict (μ := μ) hs (Lp.coeFn_smul c F),
    Lp.coeFn_smul c (extendLpFun μ hs F), coeFn_extendLpFun μ hs F] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h4]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- **Extension by zero preserves the norm.**  This is the whole analytic content of the file,
and it is `eLpNorm_indicator_eq_eLpNorm_restrict` in `L²` clothing. -/
theorem norm_extendLpFun (μ : Measure α) (hs : MeasurableSet s)
    (F : Lp ℂ 2 (μ.restrict s)) : ‖extendLpFun μ hs F‖ = ‖F‖ := by
  rw [extendLpFun, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, ← Lp.norm_def]

/-- **Extension by zero**, as a linear isometry `L²(μ|_s) →ₗᵢ[ℂ] L²(μ)`. -/
noncomputable def extendLp (μ : Measure α) (hs : MeasurableSet s) :
    Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := extendLpFun μ hs
  map_add' := extendLpFun_add μ hs
  map_smul' c F := extendLpFun_smul μ hs c F
  norm_map' := norm_extendLpFun μ hs

/-- The bundled isometry, on representatives. -/
theorem coeFn_extendLp (μ : Measure α) (hs : MeasurableSet s) (F : Lp ℂ 2 (μ.restrict s)) :
    (extendLp μ hs F : α → ℂ) =ᵐ[μ] s.indicator (F : α → ℂ) :=
  coeFn_extendLpFun μ hs F

/-- **Restriction**, on representatives: an ambient `L²` class restricts to an `L²` class for the
restricted measure.

Only used to feed the density argument, so it is not packaged as a map. -/
noncomputable def restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    Lp ℂ 2 (μ.restrict s) :=
  ((Lp.memLp g).restrict s).toLp (g : α → ℂ)

/-- Restriction, on representatives: the restricted class is represented by the same function. -/
theorem coeFn_restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    (restrictLp μ s g : α → ℂ) =ᵐ[μ.restrict s] (g : α → ℂ) :=
  MemLp.coeFn_toLp _

/-- The extension of the restriction of `g` is the indicator of `g`. -/
theorem coeFn_extendLp_restrictLp (μ : Measure α) (hs : MeasurableSet s) (g : Lp ℂ 2 μ) :
    (extendLp μ hs (restrictLp μ s g) : α → ℂ) =ᵐ[μ] s.indicator (g : α → ℂ) :=
  (coeFn_extendLp μ hs _).trans (indicator_ae_eq_of_restrict hs (coeFn_restrictLp μ s g))

end Indicator

section Orthogonality

/-- **Extensions from disjoint sets are orthogonal.**  Their representatives have disjoint
supports, so the integrand of the inner product vanishes pointwise. -/
theorem inner_extendLp_eq_zero_of_disjoint (μ : Measure α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) (F : Lp ℂ 2 (μ.restrict s))
    (G : Lp ℂ 2 (μ.restrict t)) : ⟪extendLp μ hs F, extendLp μ ht G⟫_ℂ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [coeFn_extendLp μ hs F, coeFn_extendLp μ ht G] with x h1 h2
  rw [Pi.zero_apply, h1, h2]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.mp hst hxs
    simp [hxt]
  · simp [hxs]

/-- **The indicator is a self-adjoint idempotent**, in the only form needed here: the inner
product of `1_s g` with `g` equals its inner product with itself. -/
theorem inner_extendLp_restrictLp_self (μ : Measure α) (hs : MeasurableSet s) (g : Lp ℂ 2 μ) :
    ⟪extendLp μ hs (restrictLp μ s g), g⟫_ℂ
      = ⟪extendLp μ hs (restrictLp μ s g), extendLp μ hs (restrictLp μ s g)⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_extendLp_restrictLp μ hs g] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs]

/-- **A vector orthogonal to the range of an extension vanishes on that set.** -/
theorem indicator_ae_eq_zero_of_inner_eq_zero (μ : Measure α) (hs : MeasurableSet s)
    {g : Lp ℂ 2 μ} (h : ∀ F : Lp ℂ 2 (μ.restrict s), ⟪extendLp μ hs F, g⟫_ℂ = 0) :
    s.indicator (g : α → ℂ) =ᵐ[μ] 0 := by
  have hzero : extendLp μ hs (restrictLp μ s g) = 0 :=
    inner_self_eq_zero.mp ((inner_extendLp_restrictLp_self μ hs g).symm.trans
      (h (restrictLp μ s g)))
  refine (coeFn_extendLp_restrictLp μ hs g).symm.trans ?_
  rw [hzero]
  exact Lp.coeFn_zero ℂ 2 μ

end Orthogonality

section Partition

variable {ι : Type*} [Countable ι] {B : ι → Set α}

/-- **`L²` of a measure is the Hilbert sum of the `L²` spaces of its restrictions to the pieces
of a countable measurable partition.**

The partition hypotheses are the weakest possible: the pieces are measurable and pairwise
disjoint, and what they miss is null. -/
theorem isHilbertSum_extendLp (μ : Measure α) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) (hcover : μ (⋃ i, B i)ᶜ = 0) :
    IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ.restrict (B i))) (fun i => extendLp μ (hB i)) := by
  refine IsHilbertSum.mk (𝕜 := ℂ) (fun i j hij F G => ?_) ?_
  · exact inner_extendLp_eq_zero_of_disjoint μ (hB i) (hB j) (hdisj hij) F G
  · refine (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hgi : ∀ i, (B i).indicator (g : α → ℂ) =ᵐ[μ] 0 := by
      intro i
      refine indicator_ae_eq_zero_of_inner_eq_zero μ (hB i) fun F => ?_
      refine (Submodule.mem_orthogonal _ g).mp hg _ ?_
      exact le_iSup (fun i => LinearMap.range (extendLp μ (hB i)).toLinearMap) i
        ⟨F, rfl⟩
    have hnull : ∀ i, μ (B i ∩ {x | (g : α → ℂ) x ≠ 0}) = 0 := by
      intro i
      have := hgi i
      rw [Filter.EventuallyEq, ae_iff] at this
      refine measure_mono_null (fun x hx => ?_) this
      have hxB : x ∈ B i := hx.1
      have hxg : (g : α → ℂ) x ≠ 0 := hx.2
      have hne : ¬ (B i).indicator (g : α → ℂ) x = (0 : α → ℂ) x := by
        rw [Set.indicator_of_mem hxB]
        exact hxg
      exact hne
    refine Lp.ext ?_
    refine (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℂ 2 μ).symm)
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null
      (show {x | ¬ (g : α → ℂ) x = (0 : α → ℂ) x}
        ⊆ (⋃ i, B i)ᶜ ∪ ⋃ i, B i ∩ {x | (g : α → ℂ) x ≠ 0} from fun x hx => ?_) ?_
    · by_cases hxU : x ∈ ⋃ i, B i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi, by simpa using hx⟩)
      · exact Or.inl hxU
    · exact measure_union_null hcover (measure_iUnion_null hnull)

end Partition

section Multiplication

/-- **Extension by zero intertwines the multiplication operators.**  The symbol is the same
function on both sides; restricting it to `s` is what the restricted measure sees. -/
theorem extendLp_mulLp (μ : Measure α) (hs : MeasurableSet s) {g : α → ℂ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 (μ.restrict s)) :
    extendLp μ hs (mulLp (μ.restrict s) hg hgC F) = mulLp μ hg hgC (extendLp μ hs F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendLp μ hs (mulLp (μ.restrict s) hg hgC F),
    indicator_ae_eq_of_restrict (μ := μ) hs (coeFn_mulLp (μ.restrict s) hg hgC F),
    coeFn_mulLp μ hg hgC (extendLp μ hs F), coeFn_extendLp μ hs F] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  by_cases hxs : x ∈ s <;> simp [hxs]

end Multiplication

section Star

omit [MeasurableSpace α] in
/-- Pointwise conjugation passes through an indicator, because it fixes zero. -/
theorem star_indicator_apply (s : Set α) (u : α → ℂ) (x : α) :
    star (s.indicator u x) = s.indicator (star u) x := by
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, Pi.star_apply]
  · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, star_zero]

/-- **Extension by zero is `star`-equivariant.**  Conjugation fixes the zero that the extension
inserts, so it commutes with the indicator. -/
theorem star_extendLp (μ : Measure α) (hs : MeasurableSet s) (F : Lp ℂ 2 (μ.restrict s)) :
    star (extendLp μ hs F) = extendLp μ hs (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (extendLp μ hs F), coeFn_extendLp μ hs F,
    coeFn_extendLp μ hs (star F),
    indicator_ae_eq_of_restrict (μ := μ) hs (Lp.coeFn_star F)] with x h1 h2 h3 h4
  calc ((star (extendLp μ hs F) : Lp ℂ 2 μ) : α → ℂ) x
      = star (s.indicator (F : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = s.indicator (star (F : α → ℂ)) x := star_indicator_apply s _ x
    _ = s.indicator ((star F : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x := (h4 ▸ rfl)
    _ = ((extendLp μ hs (star F) : Lp ℂ 2 μ) : α → ℂ) x := h3.symm

/-- **Restriction is `star`-equivariant**: both sides are represented by the same function. -/
theorem star_restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    star (restrictLp μ s g) = restrictLp μ s (star g) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (restrictLp μ s g), coeFn_restrictLp μ s g,
    coeFn_restrictLp μ s (star g), ae_restrict_of_ae (Lp.coeFn_star g)] with x h1 h2 h3 h4
  calc ((star (restrictLp μ s g) : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x
      = star ((g : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = ((star g : Lp ℂ 2 μ) : α → ℂ) x := by rw [h4, Pi.star_apply]
    _ = ((restrictLp μ s (star g) : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x := h3.symm

end Star

end TauCeti
