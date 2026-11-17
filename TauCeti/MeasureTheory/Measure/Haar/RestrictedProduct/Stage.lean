/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Measure.Haar.InfinitePi
import TauCeti.MeasureTheory.Measure.Subtype

/-!
# Stage measures on restricted products

This file provides the auxiliary compactness, measurability, and stage-product measure
constructions used to build Haar measures on restricted products `Πʳ i, [G i, B i]`.

For any family of measurable spaces `G i`, `SetLike` subsets `B i`, measures `μ i`, and finite
index set `T : Finset ι`:

* `TauCeti.stageTailMeasure B T μ` is the infinite product `Measure.infinitePi` of the pullbacks
  `(μ j.1).comap (↑)` on the tail `∀ j : {i // i ∉ T}, B j.1`. It requires no group structure,
  topology, or proof arguments; when `B i` is measurable and `μ i (B i) = 1` outside `T`, it is a
  probability measure (`TauCeti.isProbabilityMeasure_stageTailMeasure`).
* `TauCeti.stageMeasure B T μ` is the product measure
  `(Measure.pi fun i : T ↦ μ i.1).prod (stageTailMeasure B T μ)` on the decomposed stage
  `(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`.

In the topological-group setting, open subgroups `B i` of finite mass under left-invariant measures
positive on nonempty open sets are automatically compact
(`TauCeti.eventually_isCompact_of_isMulLeftInvariant`), giving local compactness of the restricted
product (`TauCeti.locallyCompactSpace_of_isMulLeftInvariant`) without an explicit compactness or
Hausdorff hypothesis. Both `stageTailMeasure` and `stageMeasure` inherit `IsHaarMeasure` (with
`@[to_additive]` counterparts).

## Main definitions

* `TauCeti.stageTailMeasure`: the infinite product measure `Measure.infinitePi` of the coordinate
  pullbacks `(μ j.1).comap (↑)` on `∀ j : {i // i ∉ T}, B j.1`.
* `TauCeti.stageMeasure`: the product measure `(Measure.pi ...).prod (stageTailMeasure ...)` on
  `(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`.

## Main results

* `TauCeti.eventually_isCompact_of_isMulLeftInvariant` and
  `TauCeti.locallyCompactSpace_of_isMulLeftInvariant`: openness of `B i` and cofinite finiteness of
  `μ i (B i)` imply cofinite compactness of `B i` and local compactness of `Πʳ i, [G i, B i]`.
* `TauCeti.measurableSet_restrictedProduct_box`: a countable box `{x | ∀ i, x i ∈ C i}` of
  measurable sets is measurable in `Πʳ i, [G i, B i]`.
* `TauCeti.isProbabilityMeasure_stageTailMeasure`, `TauCeti.stageTailMeasure_pi`,
  `TauCeti.stageTailMeasure_pi_univ`: probability measure and cylinder/box formulas on the tail.
* `TauCeti.stageMeasure_apply_prod`, `TauCeti.stageMeasure_prod_box_countable`,
  `TauCeti.stageMeasure_prod_box`: product and box mass formulas for `stageMeasure`.
* `TauCeti.isHaarMeasure_stageTailMeasure`, `TauCeti.isHaarMeasure_stageMeasure`: Haar-measure
  inheritance on the tail and decomposed stage (with `@[to_additive]` counterparts).

## References

* J. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory* (1967), §3.3.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Springer (1999),
  Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set TopologicalSpace Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

namespace TauCeti

section LocalCompactness

variable {ι : Type*} {G S : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
  {B : ∀ i, S i}

/-- In a family of locally compact topological groups with open subgroups `B i` and left-invariant
measures `μ i` positive on nonempty open sets, cofinite finiteness of `μ i (B i)` automatically
implies cofinite compactness of `B i`. -/
@[to_additive /-- In a family of locally compact topological additive groups with open subgroups
`B i` and left-invariant measures `μ i` positive on nonempty open sets, cofinite finiteness of
`μ i (B i)` automatically implies cofinite compactness of `B i`. -/]
theorem eventually_isCompact_of_isMulLeftInvariant
    (hBopen : ∀ i, IsOpen (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsOpenPosMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) ≠ ∞) :
    ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)) :=
  hμ.mono fun i hi ↦ (hBopen i).isCompact_of_isMulLeftInvariant hi

/-- A restricted product of locally compact topological groups relative to open subgroups `B i`
is locally compact whenever cofinitely many `B i` have finite mass under left-invariant measures
positive on nonempty open sets. -/
@[to_additive /-- A restricted product of locally compact topological additive groups relative to
open subgroups `B i` is locally compact whenever cofinitely many `B i` have finite mass under
left-invariant measures positive on nonempty open sets. -/]
theorem locallyCompactSpace_of_isMulLeftInvariant
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsOpenPosMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) ≠ ∞) :
    LocallyCompactSpace (Πʳ i, [G i, B i]) :=
  RestrictedProduct.locallyCompactSpace_of_group G
    (eventually_isCompact_of_isMulLeftInvariant hBopen.out μ hμ)

end LocalCompactness

section MeasurableBox

variable {ι : Type*} {G : ι → Type*} {A : ∀ i, Set (G i)}
  [Countable ι] [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, BorelSpace (G i)]
  [MeasurableSpace (Πʳ i, [G i, A i])] [OpensMeasurableSpace (Πʳ i, [G i, A i])]

/-- A countable box `{x | ∀ i, x i ∈ C i}` of measurable sets is measurable in
`Πʳ i, [G i, A i]`. -/
theorem measurableSet_restrictedProduct_box
    {C : ∀ i, Set (G i)} (hCm : ∀ i, MeasurableSet (C i)) :
    MeasurableSet {x : Πʳ i, [G i, A i] | ∀ i, x i ∈ C i} := by
  have h : {x : Πʳ i, [G i, A i] | ∀ i, x i ∈ C i} =
      ⋂ i, (fun x : Πʳ j, [G j, A j] ↦ x i) ⁻¹' C i := by
    ext x; simp
  rw [h]
  exact MeasurableSet.iInter fun i ↦ (RestrictedProduct.continuous_eval i).measurable (hCm i)

end MeasurableBox

section StageMeasure

variable {ι : Type*} {G S : ι → Type*} [∀ i, MeasurableSpace (G i)] [∀ i, SetLike (S i) (G i)]
  {B : ∀ i, S i}

/-- The infinite product measure `Measure.infinitePi` of the pullbacks `(μ j.1).comap (↑)` on the
tail `∀ j : {i // i ∉ T}, B j.1`. When `B i` is measurable and `μ i (B i) = 1` outside `T`, this
is a probability measure (`isProbabilityMeasure_stageTailMeasure`). -/
def stageTailMeasure (B : ∀ i, S i) (T : Finset ι) (μ : ∀ i, Measure (G i)) :
    Measure (∀ j : {i // i ∉ (T : Set ι)}, B j.1) :=
  Measure.infinitePi fun j : {i // i ∉ (T : Set ι)} ↦
    (μ j.1).comap ((↑) : B j.1 → G j.1)

/-- Characterization of `stageTailMeasure` as `Measure.infinitePi` of the coordinate pullbacks. -/
theorem stageTailMeasure_eq_infinitePi (B : ∀ i, S i) (T : Finset ι) (μ : ∀ i, Measure (G i)) :
    stageTailMeasure B T μ =
      Measure.infinitePi fun j : {i // i ∉ (T : Set ι)} ↦
        (μ j.1).comap ((↑) : B j.1 → G j.1) :=
  (rfl)

/-- `stageTailMeasure B T μ` is a probability measure whenever each `B i` outside `T` is measurable
and has `μ i`-mass `1`. -/
theorem isProbabilityMeasure_stageTailMeasure {T : Finset ι}
    (hBm : ∀ i ∉ T, MeasurableSet (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) (hT : ∀ i ∉ T, μ i (B i) = 1) :
    IsProbabilityMeasure (stageTailMeasure B T μ) := by
  have : ∀ j : {i // i ∉ (T : Set ι)},
      IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBm j.1 j.2) (hT j.1 j.2)
  rw [stageTailMeasure_eq_infinitePi]
  infer_instance

/-- Evaluation of `stageTailMeasure` on a finite cylinder. -/
theorem stageTailMeasure_pi (B : ∀ i, S i) {T : Finset ι}
    (hBm : ∀ i ∉ T, MeasurableSet (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) (hT : ∀ i ∉ T, μ i (B i) = 1)
    (s : Finset {i // i ∉ (T : Set ι)})
    {t : ∀ j : {i // i ∉ (T : Set ι)}, Set (B j.1)}
    (ht : ∀ j ∈ s, MeasurableSet (t j)) :
    stageTailMeasure B T μ (Set.pi s t) =
      ∏ j ∈ s, (μ j.1) (((↑) : B j.1 → G j.1) '' t j) := by
  have : ∀ j : {i // i ∉ (T : Set ι)},
      IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBm j.1 j.2) (hT j.1 j.2)
  rw [stageTailMeasure_eq_infinitePi, Measure.infinitePi_pi _ ht]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have hcoe : MeasurableEmbedding ((↑) : B j.1 → G j.1) :=
    MeasurableEmbedding.subtype_coe (hBm j.1 j.2)
  exact hcoe.comap_apply _ _

/-- Evaluation of `stageTailMeasure` on a countable product of measurable sets. -/
theorem stageTailMeasure_pi_univ [Countable ι] (B : ∀ i, S i) {T : Finset ι}
    (hBm : ∀ i ∉ T, MeasurableSet (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) (hT : ∀ i ∉ T, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hC : ∀ i ∉ T, MeasurableSet (C i)) :
    stageTailMeasure B T μ
        (Set.univ.pi fun j : {i // i ∉ (T : Set ι)} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) =
      ∏' j : {i // i ∉ (T : Set ι)}, μ j.1 (C j.1 ∩ B j.1) := by
  have : ∀ j : {i // i ∉ (T : Set ι)},
      IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBm j.1 j.2) (hT j.1 j.2)
  rw [stageTailMeasure_eq_infinitePi,
    Measure.infinitePi_pi_univ _ fun j ↦ measurable_subtype_coe (hC j.1 j.2)]
  congr 1
  ext j
  have hcoe : MeasurableEmbedding ((↑) : B j.1 → G j.1) :=
    MeasurableEmbedding.subtype_coe (hBm j.1 j.2)
  rw [hcoe.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe]

/-- The product measure on the decomposed `T`-stage
`(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`, equal to the finite product `Measure.pi` on `T`
times `stageTailMeasure` outside `T`. -/
def stageMeasure (B : ∀ i, S i) (T : Finset ι) (μ : ∀ i, Measure (G i)) :
    Measure ((∀ i : T, G i) × (∀ j : {i // i ∉ (T : Set ι)}, B j.1)) :=
  (Measure.pi fun i : T ↦ μ i.1).prod (stageTailMeasure B T μ)

/-- Characterization of `stageMeasure` as the product of `Measure.pi` and `stageTailMeasure`. -/
theorem stageMeasure_eq_prod (B : ∀ i, S i) (T : Finset ι) (μ : ∀ i, Measure (G i)) :
    stageMeasure B T μ =
      (Measure.pi fun i : T ↦ μ i.1).prod (stageTailMeasure B T μ) :=
  (rfl)

/-- Product mass identity for `stageMeasure`. -/
theorem stageMeasure_apply_prod {T : Finset ι}
    (hBm : ∀ i ∉ T, MeasurableSet (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) (hT : ∀ i ∉ T, μ i (B i) = 1)
    {s : Set (∀ i : T, G i)} {t : Set (∀ j : {i // i ∉ (T : Set ι)}, B j.1)} :
    stageMeasure B T μ (s ×ˢ t) =
      (Measure.pi fun i : T ↦ μ i.1) s * stageTailMeasure B T μ t := by
  have : IsProbabilityMeasure (stageTailMeasure B T μ) :=
    isProbabilityMeasure_stageTailMeasure hBm μ hT
  rw [stageMeasure_eq_prod, Measure.prod_prod]

/-- Evaluation of `stageMeasure` on a countable measurable box. -/
theorem stageMeasure_prod_box_countable [Countable ι] {T : Finset ι}
    (hBm : ∀ i ∉ T, MeasurableSet (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (hT : ∀ i ∉ T, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hC : ∀ i, MeasurableSet (C i)) :
    stageMeasure B T μ
      ((Set.univ.pi fun i : T ↦ C i.1) ×ˢ
        (Set.univ.pi fun j : {i // i ∉ (T : Set ι)} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1)) =
      (∏ i ∈ T, μ i (C i)) * ∏' j : {i // i ∉ (T : Set ι)}, μ j.1 (C j.1 ∩ B j.1) := by
  rw [stageMeasure_apply_prod hBm μ hT, Measure.pi_pi,
    stageTailMeasure_pi_univ B hBm μ hT fun i _ ↦ hC i]
  congr 1
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach T fun i ↦ μ i (C i)

/-- Evaluation of `stageMeasure` on a box whose coordinates outside `T` equal `B i`. -/
theorem stageMeasure_prod_box {T : Finset ι}
    (hBm : ∀ i ∉ T, MeasurableSet (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (hT : ∀ i ∉ T, μ i (B i) = 1)
    (C : ∀ i, Set (G i)) :
    stageMeasure B T μ ((Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ) =
      ∏ i ∈ T, μ i (C i) := by
  have : IsProbabilityMeasure (stageTailMeasure B T μ) :=
    isProbabilityMeasure_stageTailMeasure hBm μ hT
  rw [stageMeasure_apply_prod hBm μ hT, Measure.pi_pi, measure_univ, mul_one, Finset.univ_eq_attach]
  exact Finset.prod_attach T fun i ↦ μ i (C i)

end StageMeasure

section StageHaar

variable {ι : Type*} {G S : ι → Type*}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
  {B : ∀ i, S i}

/-- `stageTailMeasure` is a Haar measure on `∀ j : {i // i ∉ T}, B j.1` when each `B i` outside
`T` is open and each `μ i` is a Haar measure. -/
@[to_additive /-- `stageTailMeasure` is an additive Haar measure on `∀ j : {i // i ∉ T}, B j.1`
when each `B i` outside `T` is open and each `μ i` is an additive Haar measure. -/]
theorem isHaarMeasure_stageTailMeasure {T : Finset ι}
    (hBopen : ∀ i ∉ T, IsOpen (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hT : ∀ i ∉ T, μ i (B i) = 1) :
    (stageTailMeasure B T μ).IsHaarMeasure := by
  have : ∀ i, IsTopologicalGroup (B i) :=
    fun i ↦ IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype (B i))
  have : ∀ j : {i // i ∉ (T : Set ι)},
      IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBopen j.1 j.2).measurableSet (hT j.1 j.2)
  have : ∀ j : {i // i ∉ (T : Set ι)},
      ((μ j.1).comap ((↑) : B j.1 → G j.1)).IsHaarMeasure :=
    fun j ↦ (μ j.1).isHaarMeasure_comap_subtype_of_isOpen (hBopen j.1 j.2)
  rw [stageTailMeasure_eq_infinitePi]
  infer_instance

/-- `stageMeasure` is a Haar measure on `(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`. -/
@[to_additive /-- `stageMeasure` is an additive Haar measure on
`(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`. -/]
theorem isHaarMeasure_stageMeasure [Countable ι]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    {T : Finset ι} (hBopen : ∀ i ∉ T, IsOpen (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hT : ∀ i ∉ T, μ i (B i) = 1) :
    (stageMeasure B T μ).IsHaarMeasure := by
  have : ∀ i, IsTopologicalGroup (B i) :=
    fun i ↦ IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype (B i))
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  have : IsProbabilityMeasure (stageTailMeasure B T μ) :=
    isProbabilityMeasure_stageTailMeasure (fun i hi ↦ (hBopen i hi).measurableSet) μ hT
  have : (stageTailMeasure B T μ).IsHaarMeasure :=
    isHaarMeasure_stageTailMeasure hBopen μ hT
  have : (Measure.pi fun i : T ↦ μ i.1).IsHaarMeasure := inferInstance
  rw [stageMeasure_eq_prod]
  infer_instance

end StageHaar

end TauCeti
