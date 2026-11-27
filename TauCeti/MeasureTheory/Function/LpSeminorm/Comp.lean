/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Precomposition by a map with dominated pushforward

Let `f : α → β` be almost everywhere measurable for `μ`. If `μ.map f ≤ C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν` for every `p`
(`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). The codomain only needs a continuous
extended norm. For a normed vector space codomain, `C < ⊤`, and `1 ≤ p`, this estimate gives
boundedness of precomposition from `Lᵖ(ν)` to `Lᵖ(μ)`, with norm at most `C ^ (1/p)`.

For a measure-preserving measurable embedding the bound is an equality, also after restricting to
the preimage of an arbitrary set (`MeasureTheory.MeasurePreserving.eLpNorm_comp_restrict_preimage`).

For `p = ∞` no bound on the pushforward is needed: precomposition with a quasi-measure-preserving
map, such as the projection `Prod.fst` from a product of σ-finite measures, preserves `L^∞`
(`MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`). Conversely, pushing forward along
`f ∈ Lᵖ(μ)` makes the identity lie in `Lᵖ(μ.map f)` on any Borel pseudometrizable codomain, with
no separability assumption (`MeasureTheory.MemLp.id_map`).

## Main declarations

* `MeasureTheory.eLpNorm_comp_le_of_map_le_smul`: the `eLpNorm` bound for precomposition.
* `MeasureTheory.MeasurePreserving.eLpNorm_comp_restrict_preimage`,
  `MeasureTheory.MeasurePreserving.memLp_comp_restrict_preimage_iff`: a measure-preserving
  measurable embedding `f` identifies the `Lᵖ` seminorm of `g ∘ f` on `f ⁻¹' s` with that of `g`
  on `s`.
* `MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`: precomposition with a
  quasi-measure-preserving map preserves `L^∞`.
* `MeasureTheory.MemLp.id_map`: if `f ∈ Lᵖ(μ)` takes values in a Borel pseudometrizable space,
  then `id ∈ Lᵖ(μ.map f)`.
* `ContinuousLinearMap.eLpNorm_comp_le`: postcomposition with a continuous semilinear map scales
  `eLpNorm` by at most its operator norm, with no measurability assumption.
* `MeasureTheory.MemLp.comp_of_norm_le_mul_one_add`: over a finite measure, postcomposition with a
  strongly measurable map of linear growth preserves `Lᵖ`.
* `Isometry.eLpNorm_comp_of_map_zero`, `LinearIsometry.eLpNorm_comp`,
  `LinearIsometryEquiv.eLpNorm_comp`: postcomposition with an isometry fixing zero, such as a
  linear isometry, preserves `eLpNorm`.
* `Homeomorph.memLp_comp_restrict_of_forall_isCompact`: precomposition with a measure-preserving
  homeomorphism preserves `Lᵖ` integrability on compact subsets.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace ε]
  [ContinuousENorm ε] {μ : Measure α} {ν : Measure β} {f : α → β} {g : β → ε}

/-- **`eLpNorm` bound for precomposition.** If `f` pushes `μ` forward to at most `C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν`. No measurability assumption on `g` is
needed: its `eLpNorm` is infinite when it is not almost everywhere strongly measurable. -/
theorem eLpNorm_comp_le_of_map_le_smul {C : ℝ≥0∞} (hf : AEMeasurable f μ) (hmap : μ.map f ≤ C • ν)
    (p : ℝ≥0∞) :
    eLpNorm (g ∘ f) p μ ≤ C ^ (1 / p).toReal * eLpNorm g p ν := by
  by_cases hg : AEStronglyMeasurable g ν
  · rw [← eLpNorm_map_measure (hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)) hf]
    exact eLpNorm_le_of_measure_le_smul hmap
  rcases eq_or_ne C 0 with rfl | hC
  · -- `μ.map f ≤ 0` forces `μ = 0`.
    have hμ : μ = 0 := (Measure.map_eq_zero_iff hf).1 (le_antisymm (by simpa using hmap) bot_le)
    simp [hμ]
  simp [eLpNorm_of_not_aestronglyMeasurable hg, hC]

/-- **Measure-preserving change of variables on a preimage.** If `f` is a measurable embedding
carrying `μ` to `ν`, then the `Lᵖ` seminorm of `g ∘ f` on `f ⁻¹' s` is that of `g` on `s`. Neither
`g` nor `s` needs to be measurable. -/
theorem MeasurePreserving.eLpNorm_comp_restrict_preimage (hf : MeasurePreserving f μ ν)
    (he : MeasurableEmbedding f) (g : β → ε) (p : ℝ≥0∞) (s : Set β) :
    eLpNorm (g ∘ f) p (μ.restrict (f ⁻¹' s)) = eLpNorm g p (ν.restrict s) := by
  rw [← he.eLpNorm_map_measure, (hf.restrict_preimage_emb he s).map_eq]

/-- **Measure-preserving change of variables in `Lᵖ` on a preimage.** If `f` is a measurable
embedding carrying `μ` to `ν`, then `g ∘ f` is `Lᵖ` on `f ⁻¹' s` exactly when `g` is `Lᵖ` on
`s`. -/
theorem MeasurePreserving.memLp_comp_restrict_preimage_iff (hf : MeasurePreserving f μ ν)
    (he : MeasurableEmbedding f) {g : β → ε} {p : ℝ≥0∞} {s : Set β} :
    MemLp (g ∘ f) p (μ.restrict (f ⁻¹' s)) ↔ MemLp g p (ν.restrict s) := by
  rw [← he.memLp_map_measure_iff, (hf.restrict_preimage_emb he s).map_eq]

/-- **Precomposition preserves `L^∞`.** If `g ∈ L^∞(ν)` and `f` is quasi-measure-preserving
from `μ` to `ν`, then `g ∘ f ∈ L^∞(μ)`. -/
theorem MemLp.comp_quasiMeasurePreserving_top (hg : MemLp g ∞ ν)
    (hf : QuasiMeasurePreserving f μ ν) : MemLp (g ∘ f) ∞ μ := by
  have hgm := hg.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_exponent_top hgm] at hg
  rw [memLp_iff, eLpNorm_exponent_top (hgm.comp_quasiMeasurePreserving hf)]
  exact (eLpNormEssSup_le_of_ae_eNorm_bound (hf.ae ae_le_eLpNormEssSup)).trans_lt hg

/-- **Pushforward into `Lᵖ` of the law.** If `f` lies in `Lᵖ(μ)` with values in a Borel
pseudometrizable space, then the identity lies in `Lᵖ(μ.map f)`. No separability assumption on the
codomain is needed. -/
theorem MemLp.id_map [TopologicalSpace.PseudoMetrizableSpace ε] [MeasurableSpace ε] [BorelSpace ε]
    {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp id p (μ.map f) :=
  (memLp_map_measure_iff hf.aestronglyMeasurable.aestronglyMeasurable_id_map hf.aemeasurable).mpr hf

/-- **`eLpNorm` bound for postcomposition.** A continuous semilinear map of the codomain scales
`eLpNorm` by at most its operator norm. No measurability assumption is needed: a function that
is not almost everywhere strongly measurable has infinite `eLpNorm`. -/
theorem _root_.ContinuousLinearMap.eLpNorm_comp_le {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] {u : α → E}
    {p : ℝ≥0∞} (A : E →SL[σ₁₂] F) :
    eLpNorm (fun x => A (u x)) p μ ≤ ‖A‖ₑ * eLpNorm u p μ := by
  by_cases hu : AEStronglyMeasurable u μ
  · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p (A.continuous.comp_aestronglyMeasurable hu)
      (.of_forall fun x => A.le_opENorm (u x))
  by_cases hA : ‖A‖ₑ = 0
  · -- Each `A (u x)` has norm zero, so is inseparable from `0`: the constant function `0`
    -- approximates `A ∘ u`, which is thus strongly measurable with `eLpNorm` zero.
    have h0 (x : α) : ‖A (u x)‖ₑ = 0 := by simpa [hA] using A.le_opENorm (u x)
    have hm : StronglyMeasurable fun x => A (u x) := ⟨fun _ => 0, fun x => by
      have : ‖A (u x)‖ = 0 := by simpa [eNorm_eq_nnNorm, ← NNReal.coe_eq_zero] using h0 x
      rw [(inseparable_zero_iff_norm.2 this).nhds_eq]
      exact tendsto_const_nhds⟩
    simp [eLpNorm_zero_of_ae_eNorm_zero' hm.aestronglyMeasurable (.of_forall h0)]
  rw [eLpNorm_of_not_aestronglyMeasurable hu, ENNReal.mul_top hA]
  exact le_top

/-- **Postcomposition with a map of linear growth.** A strongly measurable map `v` that grows at
most linearly, `‖v x‖ ≤ C (1 + ‖x‖)`, maps `Lᵖ` into `Lᵖ` over a finite measure: for
`u ∈ Lᵖ(μ; E)`, the function `v ∘ u` lies in `Lᵖ(μ; F)`. -/
theorem MemLp.comp_of_norm_le_mul_one_add {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [IsFiniteMeasure μ] {p : ℝ≥0∞} {u : α → E} {v : E → F}
    {C : ℝ} (hu : MemLp u p μ) (hv : StronglyMeasurable v) (hvC : ∀ x, ‖v x‖ ≤ C * (1 + ‖x‖)) :
    MemLp (fun a ↦ v (u a)) p μ := by
  have hbound : MemLp (fun a ↦ C * (1 + ‖u a‖)) p μ :=
    ((memLp_const (1 : ℝ)).add hu.norm).const_mul C
  refine hbound.of_le (hv.aestronglyMeasurable.comp_aemeasurable hu.aemeasurable)
    (.of_forall fun a ↦ ?_)
  rw [Real.norm_eq_abs]
  exact (hvC (u a)).trans (le_abs_self _)

end MeasureTheory

open MeasureTheory Set

/-- **`eLpNorm` is invariant under postcomposition with an isometry fixing zero.** No measurability
assumption is needed: `u` and `f ∘ u` are almost everywhere strongly measurable together, since `f`
is an embedding. -/
theorem Isometry.eLpNorm_comp_of_map_zero {α F G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [SeminormedAddCommGroup G] {f : F → G} (hf : Isometry f)
    (hf0 : f 0 = 0) (u : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (fun x => f (u x)) p μ = eLpNorm u p μ := by
  have hm : AEStronglyMeasurable (fun x => f (u x)) μ ↔ AEStronglyMeasurable u μ :=
    hf.isEmbedding.aestronglyMeasurable_comp_iff
  by_cases hu : AEStronglyMeasurable u μ
  · refine eLpNorm_congr_eNorm_ae (hm.2 hu) hu (ae_of_all _ fun x => ?_)
    rw [← ofReal_norm, ← ofReal_norm, hf.norm_map_of_map_zero hf0]
  · rw [eLpNorm_of_not_aestronglyMeasurable hu, eLpNorm_of_not_aestronglyMeasurable (mt hm.1 hu)]

variable {α R R₂ F G : Type*} [MeasurableSpace α] [Semiring R] [Semiring R₂] {σ : R →+* R₂}
  {σ' : R₂ →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [NormedAddCommGroup F] [Module R F] [SeminormedAddCommGroup G] [Module R₂ G]

/-- **`eLpNorm` is invariant under postcomposition with a linear isometry.** -/
@[simp]
theorem LinearIsometry.eLpNorm_comp (L : F →ₛₗᵢ[σ] G) (u : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (fun x => L (u x)) p μ = eLpNorm u p μ :=
  L.isometry.eLpNorm_comp_of_map_zero L.map_zero u p μ

/-- **`eLpNorm` is invariant under postcomposition with a linear isometric equivalence.** -/
@[simp]
theorem LinearIsometryEquiv.eLpNorm_comp (L : F ≃ₛₗᵢ[σ] G) (u : α → F) (p : ℝ≥0∞)
    (μ : Measure α) : eLpNorm (fun x => L (u x)) p μ = eLpNorm u p μ :=
  L.toLinearIsometry.eLpNorm_comp u p μ

namespace Homeomorph

variable {α β ε : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {ν : Measure β}

/-- **Local `Lᵖ` integrability under a measure-preserving homeomorphism.** If `g` lies in `Lᵖ(ν)`
on every compact subset of `U` and the homeomorphism `e` carries `μ` to `ν`, then `g ∘ e` lies in
`Lᵖ(μ)` on every compact subset of `e⁻¹(U)`. -/
theorem memLp_comp_restrict_of_forall_isCompact (e : α ≃ₜ β) (he : MeasurePreserving e μ ν)
    {U : Set β} {g : β → ε} {p : ℝ≥0∞}
    (hg : ∀ K, IsCompact K → K ⊆ U → MemLp g p (ν.restrict K)) {K : Set α} (hK : IsCompact K)
    (hKU : K ⊆ e ⁻¹' U) : MemLp (g ∘ e) p (μ.restrict K) := by
  rw [← e.preimage_image K]
  exact (hg _ (hK.image e.continuous) (image_subset_iff.2 hKU)).comp_measurePreserving
    (he.restrict_preimage_emb e.measurableEmbedding _)

end Homeomorph
