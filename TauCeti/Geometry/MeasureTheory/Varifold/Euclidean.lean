/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Measure.Restrict
public import TauCeti.MeasureTheory.Measure.Subtype
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Topology.Grassmannian.StarProjection.Basic
public import TauCeti.Topology.Sets.Opens

/-!
# Varifolds on an open subset of a Euclidean space

Let `E` be a finite-dimensional real inner product space, `W ⊆ E` open and `k : ℕ`. A
`k`-varifold on `W` is a Radon measure `V` on `W × G(E, k)`, where `G(E, k)` is the Grassmannian
`Euclidean.grassmannian ℝ E k` of orthogonal projections onto the `k`-planes of `E`: in Lean, a
`Measure (W × grassmannian ℝ E k)` with `IsFiniteMeasureOnCompacts`. It records where a
`k`-dimensional surface carries its area and which tangent planes it has there. The product is
Hausdorff, second countable and locally compact (`W` is, by
`TopologicalSpace.Opens.instLocallyCompactSpace`), so such measures are regular and are
determined by their integrals of compactly supported continuous functions: Mathlib's
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` applies to them directly.

The **weight** `‖V‖ = π_* V` (`Euclidean.weight`) is the image of `V` under the projection
`π (x, P) = x`, read as a measure on `E` carried by `W`. It is finite on the compact subsets of `W`,
its integrals are those of the functions `φ ∘ π` against `V`, and it commutes with sums, scalar
multiples, Dirac measures and restriction `V⌞A = V.restrict (π ⁻¹' A)` to a Borel set `A`. The mass
`𝐌(V) = V univ` is `‖V‖ W`. The varifold `V` is carried by the pairs whose base point lies in the
support `spt ‖V‖` of the weight (`Euclidean.ae_mem_support_weight`).

For an open `W' ⊆ W`, the **restriction** `Euclidean.restrictOpens V h` of `V` to `W' × G(E, k)`
is again a varifold, now on `W'`. Restriction is transitive, commutes with sums, scalar multiples
and `⌞A`, has weight `‖V‖⌞W'`, and its support is `spt ‖V‖ ∩ W'` relative to `W'`. A varifold is
determined by its restrictions to the sets of an open cover of `W`
(`Euclidean.ext_of_restrictOpens`).

## Main definitions

* `Euclidean.weight V`: the weight `‖V‖` of a varifold on `W`, a measure on `E` carried by `W`.
* `Euclidean.restrictOpens V h`: the restriction of a varifold on `W` to an open `W' ⊆ W`.

## Main results

* `Euclidean.lintegral_weight`, `Euclidean.integral_weight`: `∫ φ d‖V‖ = ∫ φ ∘ π dV`.
* `Euclidean.weight_restrict`: `‖V⌞A‖ = ‖V‖⌞A`.
* `Euclidean.weight_lt_top_of_isCompact`: `‖V‖` is finite on the compact subsets of `W`.
* `Euclidean.ae_mem_support_weight`: `V` is carried by `π ⁻¹' spt ‖V‖`.
* `Euclidean.weight_restrictOpens`, `Euclidean.support_weight_restrictOpens_inter`: the weight
  and the support of a restriction to an open subset.
* `Euclidean.ext_of_restrictOpens`: a varifold is determined by its restrictions to an open cover.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 3.
* L. Simon, *Lectures on Geometric Measure Theory*, §38.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {k : ℕ}
  {W W' W'' : Opens E}

variable [MeasurableSpace E]

/-! ### The weight of a varifold -/

/-- The **weight** `‖V‖ = π_* V` of a varifold `V` on an open set `W` of a Euclidean space: the
image of `V` under the projection `(x, P) ↦ x`, read as a measure on `E` carried by `W`
(Allard, *On the first variation of a varifold*, 3.1; Simon, *Lectures on Geometric Measure
Theory*, §38). -/
noncomputable def weight (V : Measure (W × grassmannian ℝ E k)) : Measure E :=
  V.map fun p ↦ (p.1 : E)

private theorem measurable_coe_fst : Measurable fun p : W × grassmannian ℝ E k ↦ (p.1 : E) :=
  measurable_subtypeVal.comp measurable_fst

variable {V V₁ V₂ : Measure (W × grassmannian ℝ E k)}

/-- The weight is the pushforward of `V` under the projection `(x, P) ↦ x`. -/
theorem weight_def (V : Measure (W × grassmannian ℝ E k)) :
    weight V = V.map fun p ↦ (p.1 : E) :=
  (rfl)

/-- The weight of a Borel set `A` is the mass that `V` gives to the pairs with base point in
`A`. -/
theorem weight_apply {A : Set E} (hA : MeasurableSet A) :
    weight V A = V (Prod.fst ⁻¹' (Subtype.val ⁻¹' A)) :=
  Measure.map_apply measurable_coe_fst hA

/-- The total mass of the weight is the mass of the varifold. -/
@[simp]
theorem weight_univ : weight V univ = V univ := by
  rw [weight_apply MeasurableSet.univ]
  simp

@[simp]
theorem weight_zero : weight (0 : Measure (W × grassmannian ℝ E k)) = 0 :=
  Measure.map_zero _

@[simp]
theorem weight_add (V₁ V₂ : Measure (W × grassmannian ℝ E k)) :
    weight (V₁ + V₂) = weight V₁ + weight V₂ :=
  Measure.map_add _ _ measurable_coe_fst

@[simp]
theorem weight_smul (c : ℝ≥0∞) (V : Measure (W × grassmannian ℝ E k)) :
    weight (c • V) = c • weight V :=
  Measure.map_smul c measurable_coe_fst.aemeasurable

/-- The Dirac varifold `δ_{(x, P)}` has weight `δ_x`. -/
@[simp]
theorem weight_dirac (p : W × grassmannian ℝ E k) : weight (Measure.dirac p) = .dirac (p.1 : E) :=
  Measure.map_dirac' measurable_coe_fst p

/-- Integrals against the weight: `∫⁻ φ d‖V‖ = ∫⁻ φ ∘ π dV`. -/
theorem lintegral_weight {φ : E → ℝ≥0∞} (hφ : AEMeasurable φ (weight V)) :
    ∫⁻ x, φ x ∂weight V = ∫⁻ p, φ p.1 ∂V :=
  lintegral_map' hφ measurable_coe_fst.aemeasurable

/-- Integrals against the weight: `∫ φ d‖V‖ = ∫ φ ∘ π dV`. -/
theorem integral_weight {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : E → G}
    (hφ : AEStronglyMeasurable φ (weight V)) :
    ∫ x, φ x ∂weight V = ∫ p, φ p.1 ∂V :=
  integral_map measurable_coe_fst.aemeasurable hφ

/-- The weight of the restriction `V⌞A` of a varifold to the pairs with base point in a Borel set
`A` is the restriction `‖V‖⌞A` of its weight. -/
theorem weight_restrict {A : Set E} (hA : MeasurableSet A) :
    weight (V.restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' A))) = (weight V).restrict A :=
  (Measure.restrict_map measurable_coe_fst hA).symm

/-! ### Restriction to an open subset -/

/-- The **restriction** of a varifold on `W` to an open set `W' ⊆ W`: the varifold on `W'` that
agrees with `V` on the pairs with base point in `W'` (Simon, *Lectures on Geometric Measure
Theory*, §38). -/
noncomputable def restrictOpens (V : Measure (W × grassmannian ℝ E k)) (h : W' ≤ W) :
    Measure (W' × grassmannian ℝ E k) :=
  V.comap (Prod.map (inclusion h) id)

/-- The restriction to `W'` is the pullback of `V` along the inclusion of `W' × G(E, k)`. -/
theorem restrictOpens_def (V : Measure (W × grassmannian ℝ E k)) (h : W' ≤ W) :
    restrictOpens V h = V.comap (Prod.map (inclusion h) id) :=
  (rfl)

/-- Restricting a varifold to the whole of `W` does nothing. -/
@[simp]
theorem restrictOpens_self : restrictOpens V le_rfl = V := by
  have : (Prod.map (inclusion le_rfl) id : W × grassmannian ℝ E k → W × grassmannian ℝ E k) =
      fun p ↦ p := by
    ext p <;> simp
  rw [restrictOpens, this, Measure.comap_id]

@[simp]
theorem restrictOpens_zero (h : W' ≤ W) :
    restrictOpens (0 : Measure (W × grassmannian ℝ E k)) h = 0 :=
  Measure.comap_zero _

@[simp]
theorem restrictOpens_smul (c : ℝ≥0∞) (V : Measure (W × grassmannian ℝ E k)) (h : W' ≤ W) :
    restrictOpens (c • V) h = c • restrictOpens V h :=
  Measure.comap_smul c

/-! ### Mass, support and extensionality -/

/-- The weight is carried by `W`. -/
@[simp]
theorem weight_compl_opens [OpensMeasurableSpace E] : weight V (W : Set E)ᶜ = 0 := by
  rw [weight_apply W.isOpen.measurableSet.compl, preimage_compl, Subtype.coe_preimage_self]
  simp

/-- The mass `𝐌(V) = V univ` of a varifold is the weight of `W`. -/
@[simp]
theorem weight_opens [OpensMeasurableSpace E] : weight V W = V univ := by
  rw [weight_apply W.isOpen.measurableSet, Subtype.coe_preimage_self, preimage_univ]

variable [BorelSpace E]

/-- The weight of a varifold is finite on the compact subsets of `W`. -/
theorem weight_lt_top_of_isCompact [FiniteDimensional ℝ E] [IsFiniteMeasureOnCompacts V]
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) : weight V K < ∞ := by
  rw [weight_apply hK.measurableSet, ← prod_univ]
  refine IsCompact.measure_lt_top (IsCompact.prod ?_ isCompact_univ)
  rwa [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.mpr hKW]

/-- A varifold is carried by the pairs whose base point lies in the support of its weight:
`V(G_k(W ∖ spt ‖V‖)) = 0`. -/
theorem ae_mem_support_weight [SecondCountableTopology E] :
    ∀ᵐ p ∂V, (p.1 : E) ∈ (weight V).support :=
  (ae_map_iff measurable_coe_fst.aemeasurable Measure.isClosed_support.measurableSet).mp
    Measure.support_mem_ae

/-! ### Restriction to an open subset: weight, support and gluing -/

/-- For open `W' ⊆ W`, the inclusion `W' × G(E, k) → W × G(E, k)` is a measurable embedding. -/
theorem measurableEmbedding_inclusion_prodMap (h : W' ≤ W) :
    MeasurableEmbedding
      (Prod.map (inclusion h) id : W' × grassmannian ℝ E k → W × grassmannian ℝ E k) :=
  (W'.isOpen.measurableSet.measurableEmbedding_inclusion h).prodMap .id

/-- The restriction to `W'` gives a set of pairs over `W'` the mass that `V` gives to it. -/
theorem restrictOpens_apply (h : W' ≤ W) (s : Set (W' × grassmannian ℝ E k)) :
    restrictOpens V h s = V (Prod.map (inclusion h) id '' s) :=
  (measurableEmbedding_inclusion_prodMap h).comap_apply V s

/-- Pushing the restriction to `W'` forward to `W` gives the restriction of `V` to the pairs with
base point in `W'`. -/
theorem map_restrictOpens (h : W' ≤ W) :
    (restrictOpens V h).map (Prod.map (inclusion h) id) =
      V.restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' W')) := by
  rw [restrictOpens, (measurableEmbedding_inclusion_prodMap h).map_comap, range_prodMap,
    range_inclusion h, range_id, prod_univ]
  exact congrArg V.restrict (ext fun p ↦ by simp)

/-- The restriction of a varifold to an open subset is a varifold. -/
instance isFiniteMeasureOnCompacts_restrictOpens [IsFiniteMeasureOnCompacts V] (h : W' ≤ W) :
    IsFiniteMeasureOnCompacts (restrictOpens V h) :=
  IsFiniteMeasureOnCompacts.comap' V ((continuous_inclusion h).prodMap continuous_id)
    (measurableEmbedding_inclusion_prodMap h)

/-- Restriction to open subsets is transitive. -/
@[simp]
theorem restrictOpens_restrictOpens (h' : W'' ≤ W') (h : W' ≤ W) :
    restrictOpens (restrictOpens V h) h' = restrictOpens V (h'.trans h) := by
  rw [restrictOpens, restrictOpens, restrictOpens, Measure.comap_comap
    (measurableEmbedding_inclusion_prodMap h').measurableSet_image'
    (measurableEmbedding_inclusion_prodMap h).injective
    (measurableEmbedding_inclusion_prodMap h).measurableSet_image', Prod.map_comp_map,
    inclusion_comp_inclusion h' h, Function.id_comp]

@[simp]
theorem restrictOpens_add (V₁ V₂ : Measure (W × grassmannian ℝ E k)) (h : W' ≤ W) :
    restrictOpens (V₁ + V₂) h = restrictOpens V₁ h + restrictOpens V₂ h :=
  (measurableEmbedding_inclusion_prodMap h).comap_add V₁ V₂

/-- Restriction to an open subset commutes with the restriction `V⌞A` to the pairs with base point
in a set `A`. -/
@[simp]
theorem restrictOpens_restrict (h : W' ≤ W) (A : Set E) :
    restrictOpens (V.restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' A))) h =
      (restrictOpens V h).restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' A)) :=
  (measurableEmbedding_inclusion_prodMap h).comap_restrict V _

/-- The weight of the restriction of `V` to an open `W' ⊆ W` is the restriction `‖V‖⌞W'` of the
weight of `V`. -/
@[simp]
theorem weight_restrictOpens (h : W' ≤ W) :
    weight (restrictOpens V h) = (weight V).restrict W' := by
  rw [← weight_restrict W'.isOpen.measurableSet, ← map_restrictOpens h, weight, weight,
    Measure.map_map measurable_coe_fst (measurableEmbedding_inclusion_prodMap h).measurable]
  simp [Function.comp_def]

/-- The support of the weight of the restriction of `V` to an open `W' ⊆ W`, taken relative to
`W'`, is `spt ‖V‖ ∩ W'`. -/
theorem support_weight_restrictOpens_inter (h : W' ≤ W) :
    (weight (restrictOpens V h)).support ∩ W' = (weight V).support ∩ W' := by
  rw [weight_restrictOpens, Measure.support_restrict_inter_of_isOpen _ W'.isOpen]

/-- A varifold on `W` is determined by its restrictions to the sets of an open cover of `W`. -/
theorem ext_of_restrictOpens [SecondCountableTopology E] {ι : Type*} {U : ι → Opens E}
    (hU : ∀ i, U i ≤ W) (hcover : W ≤ ⨆ i, U i)
    (h : ∀ i, restrictOpens V₁ (hU i) = restrictOpens V₂ (hU i)) : V₁ = V₂ := by
  refine Measure.ext_of_restrict_preimage (Prod.fst : W × grassmannian ℝ E k → W)
    (U := fun i ↦ Subtype.val ⁻¹' (U i : Set E))
    (fun i ↦ (U i).isOpen.preimage continuous_subtypeVal)
    (eq_univ_of_forall fun x ↦ ?_) fun i ↦ ?_
  · simpa [← SetLike.mem_coe, Opens.coe_iSup] using hcover x.property
  · rw [← map_restrictOpens (hU i), ← map_restrictOpens (hU i), h]

end Euclidean
