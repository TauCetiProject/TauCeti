/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import TauCeti.MeasureTheory.Measure.Restrict
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Topology.FiberBundle.Countable
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.VectorBundle.GrassmannBundle.Basic
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Varifolds on the Grassmann bundle

Let `E → B` be a real vector bundle with model fibre `F` whose fibres are real inner product
spaces, for instance the tangent bundle of a Riemannian manifold `(M, g)`, and let
`G_k(E) = TauCeti.grassmannBundle F E k` be its Grassmann bundle of `k`-planes in projection form,
with projection `π : G_k(E) → B`. A `k`-varifold is a Radon measure `V` on `G_k(E)`: in Lean, a
`Measure (grassmannBundle F E k)` with `IsFiniteMeasureOnCompacts` (Simon, *Lectures on Geometric
Measure Theory*, §38; Allard, *On the first variation of a varifold*, Section 3).

The **weight** `‖V‖ = π_* V` (`TauCeti.grassmannBundle.weight`) is a measure on `B`, the **mass**
of `V` is `V(G_k(E)) = ‖V‖(B)` (`TauCeti.grassmannBundle.weight_univ`), and `spt ‖V‖` is the
support of the weight. For a Borel set `A ⊆ B`, `V⌞A` is `V.restrict (π ⁻¹' A)`.

* The weight is additive, positively homogeneous, sends `δ_{(x, P)}` to `δ_x`, integrates as
  `∫ φ d‖V‖ = ∫ φ ∘ π dV` (`TauCeti.grassmannBundle.lintegral_weight`), and commutes with `⌞A`
  (`TauCeti.grassmannBundle.weight_restrict`).
* For a finite-rank bundle with continuous fibre norm `π` is proper, so the weight of a varifold
  is finite on compact sets (`TauCeti.grassmannBundle.isFiniteMeasureOnCompacts_weight`).
* `V` is carried by `G_k(spt ‖V‖)` (`TauCeti.grassmannBundle.ae_mem_support_weight`), and for
  open `W' ⊆ B`, `spt ‖V⌞W'‖ ∩ W' = spt ‖V‖ ∩ W'`
  (`TauCeti.grassmannBundle.support_weight_restrict_inter`).
* For a finite-rank bundle with continuous fibre norm over a Hausdorff, second-countable, locally
  compact base, two varifolds are equal when they have the same integrals of compactly supported
  continuous functions on `G_k(E)` (`TauCeti.grassmannBundle.ext_of_integral_eq`).
* Over a Lindelöf base, two varifolds are equal when they agree on the parts over the sets of an
  open cover (`TauCeti.grassmannBundle.ext_of_restrict_preimage`).

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 3.
* L. Simon, *Lectures on Geometric Measure Theory*, §38.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Bundle
open scoped ENNReal

namespace TauCeti.grassmannBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : ℕ} {V V₁ V₂ : Measure (grassmannBundle F E k)}

/-- **Locality of varifolds.** Over a Lindelöf base, two varifolds that agree on the planes over
each set of an open cover of `B` are equal. -/
theorem ext_of_restrict_preimage [LindelofSpace B] {ι : Type*} {U : ι → Set B}
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (h : ∀ i, V₁.restrict (proj ⁻¹' U i) = V₂.restrict (proj ⁻¹' U i)) : V₁ = V₂ :=
  Measure.ext_of_restrict_preimage proj hU hcover h

/-! ### The weight of a varifold -/

variable [MeasurableSpace B]

/-- The **weight** `‖V‖ = π_* V` of a varifold `V` on the Grassmann bundle `G_k(E)`: the image of
`V` under the projection to the base (Allard, *On the first variation of a varifold*, 3.1;
Simon, *Lectures on Geometric Measure Theory*, §38). -/
def weight (V : Measure (grassmannBundle F E k)) : Measure B :=
  V.map proj

/-- The weight is the pushforward of `V` under the projection to the base. -/
theorem weight_def (V : Measure (grassmannBundle F E k)) : weight V = V.map proj :=
  (rfl)

@[simp]
theorem weight_zero : weight (0 : Measure (grassmannBundle F E k)) = 0 :=
  Measure.map_zero _

variable [BorelSpace B]

/-- The weight of a Borel set `A` is the mass that `V` gives to the planes over `A`. -/
theorem weight_apply {A : Set B} (hA : MeasurableSet A) : weight V A = V (proj ⁻¹' A) :=
  Measure.map_apply measurable_proj hA

/-- The total mass of the weight is the mass `V(G_k(E))` of the varifold. -/
@[simp]
theorem weight_univ : weight V univ = V univ := by
  rw [weight_apply MeasurableSet.univ, preimage_univ]


@[simp]
theorem weight_add (V₁ V₂ : Measure (grassmannBundle F E k)) :
    weight (V₁ + V₂) = weight V₁ + weight V₂ :=
  Measure.map_add _ _ measurable_proj

@[simp]
theorem weight_smul (c : ℝ≥0∞) (V : Measure (grassmannBundle F E k)) :
    weight (c • V) = c • weight V :=
  Measure.map_smul c measurable_proj.aemeasurable

/-- The Dirac varifold `δ_{(x, P)}` has weight `δ_x`. -/
@[simp]
theorem weight_dirac (p : grassmannBundle F E k) : weight (Measure.dirac p) = .dirac (proj p) :=
  Measure.map_dirac' measurable_proj p

/-- Integrals against the weight: `∫⁻ φ d‖V‖ = ∫⁻ φ ∘ π dV`. -/
theorem lintegral_weight {φ : B → ℝ≥0∞} (hφ : AEMeasurable φ (weight V)) :
    ∫⁻ x, φ x ∂weight V = ∫⁻ p, φ (proj p) ∂V :=
  lintegral_map' hφ measurable_proj.aemeasurable

/-- Integrals against the weight: `∫ φ d‖V‖ = ∫ φ ∘ π dV`. -/
theorem integral_weight {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : B → G}
    (hφ : AEStronglyMeasurable φ (weight V)) :
    ∫ x, φ x ∂weight V = ∫ p, φ (proj p) ∂V :=
  integral_map measurable_proj.aemeasurable hφ

/-- The weight of the restriction `V⌞A` of a varifold to the planes over a Borel set `A` is the
restriction `‖V‖⌞A` of its weight. -/
theorem weight_restrict {A : Set B} (hA : MeasurableSet A) :
    weight (V.restrict (proj ⁻¹' A)) = (weight V).restrict A :=
  (Measure.restrict_map measurable_proj hA).symm

/-- The support of the weight of the restriction `V⌞W'` to the planes over an open `W'` agrees
with `spt ‖V‖` on `W'`. -/
theorem support_weight_restrict_inter {W' : Set B} (hW' : IsOpen W') :
    (weight (V.restrict (proj ⁻¹' W'))).support ∩ W' = (weight V).support ∩ W' := by
  rw [weight_restrict hW'.measurableSet, Measure.support_restrict_inter_of_isOpen _ hW']

/-- A varifold is carried by the planes over the support of its weight:
`V(G_k(B ∖ spt ‖V‖)) = 0`. -/
theorem ae_mem_support_weight [HereditarilyLindelofSpace B] :
    ∀ᵐ p ∂V, proj p ∈ (weight V).support :=
  (ae_map_iff measurable_proj.aemeasurable Measure.isClosed_support.measurableSet).mp
    Measure.support_mem_ae

/-! ### Varifolds over a finite-rank bundle -/

section FiniteRank

variable [FiniteDimensional ℝ F] [ContinuousFiberNorm F E]

/-- **The weight of a varifold is a Radon measure**: the projection `π` is proper, so the planes
over a compact set form a compact set. -/
instance isFiniteMeasureOnCompacts_weight [T2Space B] [IsFiniteMeasureOnCompacts V] :
    IsFiniteMeasureOnCompacts (weight V) :=
  Measure.isFiniteMeasureOnCompacts_map_of_isProperMap V (isProperMap_proj F E k)

variable [T2Space B] [SecondCountableTopology B] [LocallyCompactSpace B]

omit [MeasurableSpace B] [BorelSpace B] in
/-- **Extensionality of varifolds.** For a finite-rank bundle with continuous fibre norm over a
Hausdorff, second-countable, locally compact base, two varifolds with the same integrals of every
compactly supported continuous function on `G_k(E)` are equal. -/
theorem ext_of_integral_eq [IsFiniteMeasureOnCompacts V₁] [IsFiniteMeasureOnCompacts V₂]
    (h : ∀ f : CompactlySupportedContinuousMap (grassmannBundle F E k) ℝ,
      ∫ p, f p ∂V₁ = ∫ p, f p ∂V₂) : V₁ = V₂ := by
  -- Instance search does not find the metrizability of the bundle unaided.
  have : LocallyCompactSpace (grassmannBundle F E k) := inferInstance
  have : PseudoMetrizableSpace (grassmannBundle F E k) := inferInstance
  exact Measure.ext_of_integral_eq_on_compactlySupported h

end FiniteRank

end TauCeti.grassmannBundle
