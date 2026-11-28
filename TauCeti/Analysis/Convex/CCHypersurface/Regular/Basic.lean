/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import TauCeti.Analysis.Convex.CCHypersurface.Basic

/-!
# `c - c`-regular measures

A measure `μ` on a real inner product space `E` is **`c - c`-regular** (`TauCeti.IsCCRegular`,
avoiding Mathlib's topological `Measure.Regular`) if it vanishes on every `c - c` hypersurface
(`TauCeti.IsCCHypersurface`). In finite dimensions, `IsCCRegular μ` is equivalent to `μ`-a.e.
differentiability of every convex `E → ℝ` (see
`TauCeti.Analysis.Convex.CCHypersurface.Regular.Differentiability`) and is the sharp source
regularity hypothesis for Brenier's theorem
(`TauCeti/MeasureTheory/OptimalTransport/Brenier/Basic.lean`,
`TauCeti/MeasureTheory/OptimalTransport/Brenier/RegularSource.lean`). For Hausdorff-dimension and
Haar absolute-continuity criteria, see
`TauCeti.Analysis.Convex.CCHypersurface.Regular.SufficientConditions`.

## Main declarations

* `TauCeti.IsCCRegular` — vanishing on every `c - c` hypersurface.
* `TauCeti.isCCRegular_add_iff`, `TauCeti.isCCRegular_smul_iff`, `TauCeti.isCCRegular_sum_iff`,
  `TauCeti.isCCRegular_sum_iff_of_countable`,
  `TauCeti.isCCRegular_map_add_left_iff_of_aemeasurable`,
  `TauCeti.isCCRegular_map_add_right_iff_of_aemeasurable`,
  `TauCeti.isCCRegular_map_continuousLinearEquiv_iff_of_aemeasurable`,
  `TauCeti.isCCRegular_map_linearIsometryEquiv_iff_of_aemeasurable`,
  `TauCeti.isCCRegular_map_add_left_iff`, `TauCeti.isCCRegular_map_add_right_iff`,
  `TauCeti.isCCRegular_map_continuousLinearEquiv_iff`,
  `TauCeti.isCCRegular_map_linearIsometryEquiv_iff` — closure and invariance properties.
* `TauCeti.IsCCRegular.measure_singleton`, `TauCeti.IsCCRegular.nullSingletonClass`,
  `TauCeti.not_isCCRegular_dirac`, `TauCeti.isCCRegular_iff_nullSingletonClass` — null singletons.
* `TauCeti.isCCRegular_of_forall_isLipschitzHypersurface`,
  `TauCeti.isCCRegular_of_null_lipschitz_graphs` — Lipschitz-graph criteria for
  `c - c`-regularity.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113–161.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.25.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace TauCeti

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ ν : Measure E}

/-- A measure `μ` on a real inner product space `E` is **`c - c`-regular** if it assigns measure
zero to every `c - c` hypersurface (`TauCeti.IsCCHypersurface`). In finite dimensions, for
probability sources of finite second moment, this is the sharp condition under which quadratic
optimal transport out of `μ` is uniquely solved by convex gradients for all probability targets
with finite second moment (Ambrosio–Gigli, Def. 1.25 and Thm. 1.26). -/
def IsCCRegular (μ : Measure E) : Prop := ∀ ⦃s : Set E⦄, IsCCHypersurface s → μ s = 0

/-- Unfolding lemma for `TauCeti.IsCCRegular`. -/
theorem isCCRegular_def (μ : Measure E) :
    IsCCRegular μ ↔ ∀ ⦃s : Set E⦄, IsCCHypersurface s → μ s = 0 := Iff.rfl

/-- A `c - c`-regular measure vanishes on every `c - c` hypersurface. -/
@[grind →]
theorem IsCCRegular.measure_eq_zero (hμ : IsCCRegular μ) {s : Set E} (hs : IsCCHypersurface s) :
    μ s = 0 := hμ hs

/-- A `c - c`-regular measure vanishes on any countable union of `c - c` hypersurfaces. -/
theorem IsCCRegular.measure_sUnion_eq_zero (hμ : IsCCRegular μ) {C : Set (Set E)}
    (hC : C.Countable) (hs : ∀ s ∈ C, IsCCHypersurface s) : μ (⋃₀ C) = 0 :=
  (measure_sUnion_null_iff hC).2 fun s h => hμ (hs s h)

/-- A `c - c`-regular measure vanishes on any indexed countable union of `c - c` hypersurfaces. -/
theorem IsCCRegular.measure_iUnion_eq_zero {ι : Sort*} [Countable ι] (hμ : IsCCRegular μ)
    {s : ι → Set E} (hs : ∀ i, IsCCHypersurface (s i)) : μ (⋃ i, s i) = 0 :=
  measure_iUnion_null fun i => hμ (hs i)

/-- Any set covered by countably many `c - c` hypersurfaces is null for every `c - c`-regular
measure. -/
theorem IsCCRegular.measure_eq_zero_of_subset_sUnion (hμ : IsCCRegular μ) {A : Set E}
    {C : Set (Set E)} (hC : C.Countable) (hs : ∀ s ∈ C, IsCCHypersurface s) (hA : A ⊆ ⋃₀ C) :
    μ A = 0 := measure_mono_null hA (hμ.measure_sUnion_eq_zero hC hs)

/-- The zero measure is `c - c`-regular. -/
@[simp]
theorem isCCRegular_zero : IsCCRegular (0 : Measure E) := fun _ _ => by simp

/-- On a `0`-dimensional inner product space there are no `c - c` hypersurfaces, so every measure is
`c - c`-regular. -/
@[simp]
theorem isCCRegular_of_subsingleton [Subsingleton E] (μ : Measure E) : IsCCRegular μ :=
  fun s hs => (not_isCCHypersurface_of_subsingleton s hs).elim

/-- Absolute continuity transfers `c - c`-regularity downward. -/
theorem IsCCRegular.mono_ac (h : μ ≪ ν) (hν : IsCCRegular ν) : IsCCRegular μ := fun _ s => h (hν s)

/-- Measure domination transfers `c - c`-regularity downward. -/
theorem IsCCRegular.mono (h : μ ≤ ν) (hν : IsCCRegular ν) : IsCCRegular μ :=
  hν.mono_ac (Measure.absolutelyContinuous_of_le h)

/-- Restricting a `c - c`-regular measure to any set preserves `c - c`-regularity. -/
theorem IsCCRegular.restrict (hμ : IsCCRegular μ) (t : Set E) : IsCCRegular (μ.restrict t) :=
  hμ.mono Measure.restrict_le_self

/-- The sum of two `c - c`-regular measures is `c - c`-regular. -/
theorem IsCCRegular.add (hμ : IsCCRegular μ) (hν : IsCCRegular ν) : IsCCRegular (μ + ν) :=
  fun _ hs => by simp [hμ hs, hν hs]

/-- A sum of two measures is `c - c`-regular if and only if both summands are `c - c`-regular. -/
@[simp]
theorem isCCRegular_add_iff : IsCCRegular (μ + ν) ↔ IsCCRegular μ ∧ IsCCRegular ν :=
  ⟨fun h => ⟨fun _ hs => (add_eq_zero.1 (by simpa using h hs)).1,
    fun _ hs => (add_eq_zero.1 (by simpa using h hs)).2⟩, fun ⟨hμ, hν⟩ => hμ.add hν⟩

/-- Scaling a `c - c`-regular measure by any factor in `ℝ≥0∞` preserves `c - c`-regularity. -/
theorem IsCCRegular.smul (hμ : IsCCRegular μ) (c : ℝ≥0∞) : IsCCRegular (c • μ) :=
  fun _ hs => by simp [hμ hs]

/-- A scaled measure `c • μ` is `c - c`-regular if and only if `c = 0` or `μ` is `c - c`-regular. -/
@[simp]
theorem isCCRegular_smul_iff {c : ℝ≥0∞} : IsCCRegular (c • μ) ↔ c = 0 ∨ IsCCRegular μ :=
  ⟨fun h => (em (c = 0)).imp_right fun hc _ hs =>
    (mul_eq_zero.1 (by simpa using h hs)).resolve_left hc,
    fun h => h.elim (fun hc => by simp [hc]) fun hμ => hμ.smul c⟩

/-- A sum of measures is `c - c`-regular if and only if every summand is `c - c`-regular,
provided open sets are measurable (so every `c - c` hypersurface is measurable). -/
@[simp]
theorem isCCRegular_sum_iff [OpensMeasurableSpace E] {ι : Type*} {μ : ι → Measure E} :
    IsCCRegular (Measure.sum μ) ↔ ∀ i, IsCCRegular (μ i) := by
  refine ⟨fun h i _ hs => ?_, fun h _ hs => ?_⟩
  · have h0 := h hs
    rw [Measure.sum_apply _ hs.isClosed.measurableSet] at h0
    exact tsum_eq_zero_iff.1 h0 i
  · rw [Measure.sum_apply _ hs.isClosed.measurableSet]
    exact tsum_eq_zero_iff.2 fun i => h i hs

/-- A countable sum of measures is `c - c`-regular if and only if every summand is
`c - c`-regular. -/
@[simp]
theorem isCCRegular_sum_iff_of_countable {ι : Type*} [Countable ι] {μ : ι → Measure E} :
    IsCCRegular (Measure.sum μ) ↔ ∀ i, IsCCRegular (μ i) := by
  simp only [IsCCRegular, Measure.sum_apply_eq_zero]
  exact ⟨fun h i _ hs => h hs i, fun h _ hs i => h i hs⟩

/-- In a nontrivial real inner product space, a `c - c`-regular measure assigns measure zero to
every singleton. -/
theorem IsCCRegular.measure_singleton [Nontrivial E] (hμ : IsCCRegular μ) (x : E) : μ {x} = 0 := by
  obtain ⟨e, he⟩ := exists_norm_eq E (zero_le_one (α := ℝ))
  exact measure_mono_null (t := {y | inner ℝ y e = inner ℝ x e})
    (singleton_subset_iff.2 (mem_ofPred_eq.mpr rfl))
    (hμ (isCCHypersurface_setOf_inner_eq he (inner ℝ x e)))

/-- In a nontrivial real inner product space, every `c - c`-regular measure has null singletons. -/
theorem IsCCRegular.nullSingletonClass [Nontrivial E] (hμ : IsCCRegular μ) : NullSingletonClass μ :=
  ⟨hμ.measure_singleton⟩

/-- In a nontrivial real inner product space, no Dirac mass is `c - c`-regular. -/
@[simp]
theorem not_isCCRegular_dirac [Nontrivial E] (x : E) : ¬ IsCCRegular (Measure.dirac x) :=
  fun h => by have := h.measure_singleton x; simp at this

/-- On a one-dimensional real inner product space, `c - c` hypersurfaces are singletons, so
`IsCCRegular μ` is equivalent to `NullSingletonClass μ`. -/
theorem isCCRegular_iff_nullSingletonClass (hd : Module.finrank ℝ E = 1) :
    IsCCRegular μ ↔ NullSingletonClass μ :=
  ⟨fun h => ⟨fun x => h ((isCCHypersurface_iff_exists_eq_singleton hd).2 ⟨x, rfl⟩)⟩,
    fun _ _ hs => let ⟨_, hx⟩ := (isCCHypersurface_iff_exists_eq_singleton hd).1 hs
      hx ▸ measure_singleton _⟩

/-- Left translation preserves `c - c`-regularity when the translation is a.e. measurable. -/
theorem isCCRegular_map_add_left_iff_of_aemeasurable [OpensMeasurableSpace E] (v : E)
    (hv : AEMeasurable (v + ·) μ) : IsCCRegular (μ.map (v + ·)) ↔ IsCCRegular μ := by
  have hpre (t : Set E) : (v + ·) ⁻¹' t = (-v) +ᵥ t := by
    ext x; simp [mem_vadd_set_iff_neg_vadd_mem]
  refine ⟨fun h s hs => ?_, fun h s hs => ?_⟩
  · have hvs := hs.vadd v
    simpa [Measure.map_apply₀ hv hvs.isClosed.measurableSet.nullMeasurableSet, hpre]
      using h hvs
  · rw [Measure.map_apply₀ hv hs.isClosed.measurableSet.nullMeasurableSet, hpre]
    exact h (hs.vadd (-v))

/-- Left translation preserves `c - c`-regularity of Borel measures. -/
@[simp]
theorem isCCRegular_map_add_left_iff [BorelSpace E] (v : E) :
    IsCCRegular (μ.map (v + ·)) ↔ IsCCRegular μ :=
  isCCRegular_map_add_left_iff_of_aemeasurable v (continuous_const_add v).measurable.aemeasurable

/-- Right translation preserves `c - c`-regularity when the translation is a.e. measurable. -/
theorem isCCRegular_map_add_right_iff_of_aemeasurable [OpensMeasurableSpace E] (v : E)
    (hv : AEMeasurable (· + v) μ) : IsCCRegular (μ.map (· + v)) ↔ IsCCRegular μ := by
  simpa only [add_comm _ v] using
    isCCRegular_map_add_left_iff_of_aemeasurable (μ := μ) v (by simpa only [add_comm _ v] using hv)

/-- Right translation preserves `c - c`-regularity of Borel measures. -/
@[simp]
theorem isCCRegular_map_add_right_iff [BorelSpace E] (v : E) :
    IsCCRegular (μ.map (· + v)) ↔ IsCCRegular μ :=
  isCCRegular_map_add_right_iff_of_aemeasurable v (continuous_add_const v).measurable.aemeasurable

/-- Pushforward by an a.e. measurable continuous linear equivalence preserves `c - c`-regularity
into a space where open sets are measurable. -/
theorem isCCRegular_map_continuousLinearEquiv_iff_of_aemeasurable {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (L : E ≃L[ℝ] F) (hL : AEMeasurable L μ) :
    IsCCRegular (μ.map L) ↔ IsCCRegular μ := by
  refine ⟨fun h s hs => ?_, fun h s hs => ?_⟩
  · have hLs := hs.image_continuousLinearEquiv L
    simpa [Measure.map_apply₀ hL hLs.isClosed.measurableSet.nullMeasurableSet,
      L.injective.preimage_image s] using h hLs
  · rw [Measure.map_apply₀ hL hs.isClosed.measurableSet.nullMeasurableSet]
    exact h ((isCCHypersurface_preimage_continuousLinearEquiv_iff L).2 hs)

/-- Pushforward by a continuous linear equivalence preserves `c - c`-regularity. -/
@[simp]
theorem isCCRegular_map_continuousLinearEquiv_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace E] [BorelSpace F]
    (L : E ≃L[ℝ] F) : IsCCRegular (μ.map L) ↔ IsCCRegular μ :=
  isCCRegular_map_continuousLinearEquiv_iff_of_aemeasurable L L.continuous.measurable.aemeasurable

/-- Pushforward by an a.e. measurable linear isometric equivalence preserves `c - c`-regularity
into a space where open sets are measurable. -/
theorem isCCRegular_map_linearIsometryEquiv_iff_of_aemeasurable {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (L : E ≃ₗᵢ[ℝ] F) (hL : AEMeasurable L μ) :
    IsCCRegular (μ.map L) ↔ IsCCRegular μ := by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    isCCRegular_map_continuousLinearEquiv_iff_of_aemeasurable (μ := μ) L.toContinuousLinearEquiv
      (by simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hL)

/-- Pushforward by a linear isometric equivalence preserves `c - c`-regularity. -/
@[simp]
theorem isCCRegular_map_linearIsometryEquiv_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace E] [BorelSpace F]
    (L : E ≃ₗᵢ[ℝ] F) : IsCCRegular (μ.map L) ↔ IsCCRegular μ :=
  isCCRegular_map_linearIsometryEquiv_iff_of_aemeasurable L L.continuous.measurable.aemeasurable

end Basic

section Separable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace.SeparableSpace E] [MeasurableSpace E]

/-- **Measures null on Lipschitz hypersurfaces are `c - c`-regular.** Every `c - c` hypersurface in
a separable real inner product space is covered by countably many Lipschitz hypersurfaces
(`TauCeti.IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface`), so vanishing on all
Lipschitz hypersurfaces implies `IsCCRegular`. -/
theorem isCCRegular_of_forall_isLipschitzHypersurface {μ : Measure E}
    (h : ∀ ⦃s : Set E⦄, IsLipschitzHypersurface s → μ s = 0) : IsCCRegular μ := fun _ hs =>
  let ⟨_, ht, hsub⟩ := hs.exists_subset_iUnion_isLipschitzHypersurface
  measure_mono_null hsub (measure_iUnion_null fun n => h (ht n))

/-- **Measures vanishing on Lipschitz graphs are `c - c`-regular.** If a measure `μ` on a
separable real inner product space assigns mass zero to every globally Lipschitz graph
`range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over the orthogonal complement of a unit
vector, then `μ` is `c - c`-regular. -/
theorem isCCRegular_of_null_lipschitz_graphs {μ : Measure E}
    (h : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) : IsCCRegular μ :=
  isCCRegular_of_forall_isLipschitzHypersurface fun _ hs => by
    obtain ⟨v, hv, K, g, hg, rfl⟩ := isLipschitzHypersurface_iff_exists_eq_range.1 hs
    exact h v hv K g hg

end Separable

end TauCeti
