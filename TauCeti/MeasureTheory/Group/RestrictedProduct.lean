/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Group.InfinitePi
public import TauCeti.MeasureTheory.Group.Measure
public import TauCeti.MeasureTheory.Measure.Subtype
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Stage
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Restricted products of Haar measures

Let `ι` be a countable index type and, for each `i : ι`, let `G i` be a second-countable locally
compact topological group equipped with an open subgroup `B i` and a Haar measure `μ i`. When
`B i` is compact for all but finitely many `i` and `μ i (B i) = 1` for all but finitely many `i`,
the restricted product `Πʳ i, [G i, B i]` is a second-countable locally compact topological group,
and there is a unique Haar measure `ν = Measure.restrictedHaar B hB μ hμ` on it assigning to every
Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i` for all but finitely many `i` the mass
`∏ᶠ i, μ i (C i)`.

## Decomposition on open subgroup stages and Fubini

For a finite set `S` of indices, the homomorphism `TauCeti.stageEmbedding S hS B` embeds
`(∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)` as the open subgroup
`{x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i}`. Whenever `μ i (B i) = 1` for every `i ∉ S` (in
particular when `S` contains the finite set of indices where `B i` is not compact or
`μ i (B i) ≠ 1`), each pullback `(μ j.1).comap ((↑) : B j.1 → G j.1)` is a left-invariant
probability measure, and pulling `Measure.restrictedHaar B hB μ hμ` back along
`stageEmbedding S hS B` yields the product of the finite product measure `Measure.pi` over `S`
with the infinite product measure `Measure.infinitePi` away from `S`. Consequently Tonelli and
Fubini apply on `{x | ∀ i ∉ S, x i ∈ B i}`, factoring integrals of separated integrands into a
finite product integral at `S` times an infinite-product integral over the subgroups away from `S`.
When `S` omits an index `i` with `μ i (B i) ≠ 1`, the corresponding restriction to `B i` is not a
probability measure (`MeasureTheory.Measure.isProbabilityMeasure_comap_subtype_iff`).

All definitions and theorems carry `@[to_additive]` counterparts (`Measure.restrictedAddHaar`,
`exists_unique_restrictedAddHaar`, …).

## Main definitions and results

* `TauCeti.measurableEmbedding_stageEmbedding`: `stageEmbedding S hS B` is a measurable embedding
  over countable index types with second-countable Borel factors whenever `B i` is open away from
  `S`.
* `MeasureTheory.Measure.restrictedHaar`, `MeasureTheory.Measure.restrictedAddHaar`: the restricted
  product of the local Haar measures `μ i` (requiring neither countability nor second countability
  to construct or to verify `IsHaarMeasure`).
* `MeasureTheory.Measure.comap_stageEmbedding_restrictedHaar`: pullback of `restrictedHaar` to an
  open stage where `μ i (B i) = 1` outside `S` is `(Measure.pi …).prod (Measure.infinitePi …)`.
* `MeasureTheory.Measure.setLIntegral_stage_restrictedHaar`,
  `MeasureTheory.Measure.setIntegral_stage_restrictedHaar`,
  `MeasureTheory.Measure.setIntegral_stage_fst_restrictedHaar`,
  `MeasureTheory.Measure.setIntegral_stage_smul_restrictedHaar`,
  `MeasureTheory.Measure.setIntegral_stage_mul_restrictedHaar`: Tonelli and Fubini on an open
  stage, including functions depending only on `S` and factorizable integrands.
* `MeasureTheory.Measure.restrictedHaar_forall_mem`,
  `MeasureTheory.Measure.restrictedHaar_eq_smul_of_eq_away`,
  `MeasureTheory.Measure.restrictedHaar_forall_mem_eq_top_of_infinite`, and
  `TauCeti.exists_unique_restrictedHaar` (additively `TauCeti.exists_unique_restrictedAddHaar`):
  the box formula, single-factor rescaling, divergence of unrestricted infinite boxes, and
  existence and uniqueness of the restricted Haar measure.

## References

* J. T. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, 1967, §3.3.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Graduate Texts in
  Mathematics 186, Springer, 1999, Chapter 5.
* A. Weil, *Basic Number Theory*, Classics in Mathematics, Springer, 1995.
-/

public section

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal RestrictedProduct

@[to_additive]
private instance instSecondCountableTopologySubgroup {H : Type*} [Group H] [TopologicalSpace H]
    [SecondCountableTopology H] (U : Subgroup H) : SecondCountableTopology U :=
  Subtype.secondCountableTopology (U : Set H)

namespace TauCeti

/-- Over a countable index type with second-countable Borel factors, `stageEmbedding S hS B` is a
measurable embedding whenever `B i` is open away from `S`. -/
@[to_additive measurableEmbedding_addStageEmbedding /-- Over a countable index type with
second-countable Borel factors, `addStageEmbedding S hS B` is a measurable embedding whenever `B i`
is open away from `S`. -/]
theorem measurableEmbedding_stageEmbedding {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] {S : Set ι} {hS : S.Finite} {B : ∀ i, Subgroup (G i)}
    [Countable ι] [∀ i, SecondCountableTopology (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (hBopen : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    MeasurableEmbedding (stageEmbedding S hS B) :=
  (isOpenEmbedding_stageEmbedding hBopen).measurableEmbedding

end TauCeti

/-! ### Restricted product of Haar measures -/

namespace MeasureTheory.Measure

open TauCeti

section RestrictedHaar

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- Private helper: the finite exceptional set `S₀` where `B i` fails to be compact or fails to
have mass `1`. -/
@[to_additive]
private theorem finite_not_isCompact_or_measure_ne_one (B : ∀ i, Subgroup (G i))
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    [∀ i, MeasurableSpace (G i)] (μ : ∀ i, Measure (G i))
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1}.Finite :=
  Set.Finite.union hB hμ

/-- Private helper: reference compact box inside the `S`-stage with positive finite `ν`-mass for
every Haar measure `ν` on `Πʳ i, [G i, B i]`. -/
@[to_additive]
private noncomputable def restrictedHaarRefBox [∀ i, LocallyCompactSpace (G i)]
    (B : ∀ i, Subgroup (G i)) {S : Set ι} (hS : S.Finite) :
    Set (Πʳ i, [G i, B i]) :=
  stageEmbedding S hS B ''
    ((univ.pi fun i : S ↦
      closure (Classical.arbitrary (PositiveCompacts (G i.1)) : Set (G i.1))) ×ˢ univ)

/-- Private helper: coordinatewise factors of `restrictedHaarRefBox B hS`. -/
@[to_additive]
private noncomputable def restrictedHaarRefSet [∀ i, LocallyCompactSpace (G i)]
    (B : ∀ i, Subgroup (G i)) (S : Set ι) [DecidablePred (· ∈ S)] (i : ι) : Set (G i) :=
  if i ∈ S then closure (Classical.arbitrary (PositiveCompacts (G i)) : Set (G i)) else B i

@[to_additive]
private theorem restrictedHaarRefBox_eq [∀ i, LocallyCompactSpace (G i)]
    (B : ∀ i, Subgroup (G i)) {S : Set ι} [DecidablePred (· ∈ S)] (hS : S.Finite) :
    restrictedHaarRefBox B hS =
      {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ restrictedHaarRefSet B S i} := by
  rw [restrictedHaarRefBox, image_stageEmbedding_prod_univ]
  ext x
  simp only [mem_ofPred_eq, restrictedHaarRefSet]
  exact ⟨fun ⟨h1, h2⟩ i ↦ if hi : i ∈ S then by simpa [hi] using h1 ⟨i, hi⟩
    else by simpa [hi] using h2 i hi,
    fun h ↦ ⟨fun i ↦ by simpa [i.2] using h i.1, fun i hi ↦ by simpa [hi] using h i⟩⟩

@[to_additive]
private theorem preimage_stageEmbedding_restrictedHaarRefSet [∀ i, LocallyCompactSpace (G i)]
    (B : ∀ i, Subgroup (G i)) {S T : Set ι} [DecidablePred (· ∈ S)] (hT : T.Finite) (hST : S ⊆ T) :
    stageEmbedding T hT B ⁻¹' {x | ∀ i, x i ∈ restrictedHaarRefSet B S i} =
      (univ.pi fun i : T ↦ restrictedHaarRefSet B S i.1) ×ˢ univ := by
  rw [preimage_stageEmbedding_forall_mem]
  congr 1
  ext z
  simp only [mem_univ_pi, mem_preimage, mem_univ, iff_true]
  intro j
  have hj : j.1 ∉ S := fun hs ↦ j.2 (hST hs)
  simp [restrictedHaarRefSet, hj]

@[to_additive]
private theorem isCompact_restrictedHaarRefBox [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] (B : ∀ i, Subgroup (G i))
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))] {S : Set ι} (hS : S.Finite)
    (hBS : ∀ i ∉ S, IsCompact (B i : Set (G i))) :
    IsCompact (restrictedHaarRefBox B hS) := by
  have _ : Finite S := hS.to_subtype
  have _ (j : {i // i ∉ S}) : CompactSpace (B j.1) := isCompact_iff_compactSpace.1 (hBS j.1 j.2)
  exact ((isCompact_univ_pi fun i : S ↦
    (Classical.arbitrary (PositiveCompacts (G i.1))).isCompact.closure).prod isCompact_univ).image
    (isOpenEmbedding_stageEmbedding fun i _ ↦ hBopen.out i).continuous

@[to_additive]
private theorem measure_restrictedHaarRefBox_pos [∀ i, LocallyCompactSpace (G i)]
    (B : ∀ i, Subgroup (G i)) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] {S : Set ι} (hS : S.Finite)
    (ν : Measure (Πʳ i, [G i, B i])) [ν.IsHaarMeasure] :
    0 < ν (restrictedHaarRefBox B hS) := by
  have _ : Finite S := hS.to_subtype
  let U : Set ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) :=
    (univ.pi fun i : S ↦
      interior (Classical.arbitrary (PositiveCompacts (G i.1)) : Set (G i.1))) ×ˢ univ
  have hUopen : IsOpen (stageEmbedding S hS B '' U) :=
    (isOpenEmbedding_stageEmbedding fun i _ ↦ hBopen.out i).isOpenMap U
      ((isOpen_set_pi finite_univ fun _ _ ↦ isOpen_interior).prod isOpen_univ)
  have hUne : (stageEmbedding S hS B '' U).Nonempty := by
    refine Nonempty.image _ ⟨(fun i ↦
      (Classical.arbitrary (PositiveCompacts (G i.1))).interior_nonempty.some, 1), ?_, mem_univ _⟩
    exact fun i _ ↦ (Classical.arbitrary (PositiveCompacts (G i.1))).interior_nonempty.some_mem
  refine (hUopen.measure_pos ν hUne).trans_le (measure_mono (image_mono ?_))
  exact Set.prod_mono (pi_mono fun i _ ↦ interior_subset.trans subset_closure) Subset.rfl

@[to_additive]
private noncomputable def restrictedHaarRefMass [∀ i, LocallyCompactSpace (G i)]
    [∀ i, MeasurableSpace (G i)] (S : Set ι) [Fintype S] (μ : ∀ i, Measure (G i)) : ℝ≥0 :=
  ∏ i : S, (μ i.1 (closure (Classical.arbitrary (PositiveCompacts (G i.1)) : Set (G i.1)))).toNNReal

@[to_additive]
private theorem restrictedHaarRefMass_ne_zero [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)]
    (S : Set ι) [Fintype S] (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] :
    restrictedHaarRefMass S μ ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ ↦ ENNReal.toNNReal_ne_zero.2 ⟨?_, ?_⟩
  · exact ((isOpen_interior.measure_pos (μ i.1)
      (Classical.arbitrary (PositiveCompacts (G i.1))).interior_nonempty).trans_le
      (measure_mono (interior_subset.trans subset_closure))).ne'
  · exact (Classical.arbitrary (PositiveCompacts (G i.1))).isCompact.closure.measure_lt_top.ne

@[to_additive]
private theorem coe_restrictedHaarRefMass [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)]
    (S : Set ι) [Fintype S] (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] :
    (restrictedHaarRefMass S μ : ℝ≥0∞) =
      ∏ i : S, μ i.1 (closure (Classical.arbitrary (PositiveCompacts (G i.1)) : Set (G i.1))) := by
  rw [restrictedHaarRefMass]
  push_cast
  refine Finset.prod_congr rfl fun i _ ↦ ENNReal.coe_toNNReal ?_
  exact (Classical.arbitrary (PositiveCompacts (G i.1))).isCompact.closure.measure_lt_top.ne

@[to_additive]
private theorem prod_measure_restrictedHaarRefSet [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)]
    (B : ∀ i, Subgroup (G i)) {S T : Set ι} [DecidablePred (· ∈ S)] [Fintype S] [Fintype T]
    (hST : S ⊆ T) (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ i ∈ T, i ∉ S → μ i (B i) = 1) :
    (∏ i : T, μ i.1 (restrictedHaarRefSet B S i.1)) = restrictedHaarRefMass S μ := by
  rw [coe_restrictedHaarRefMass]
  symm
  refine Finset.prod_bij_ne_one (fun (i : S) _ _ ↦ (⟨i.1, hST i.2⟩ : T))
    (fun _ _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
    (fun b _ hb ↦ ?_) fun i _ _ ↦ by simp [restrictedHaarRefSet, i.2]
  have hbS : b.1 ∈ S := by
    by_contra h
    exact hb (by simp [restrictedHaarRefSet, h, hμ b.1 b.2 h])
  exact ⟨⟨b.1, hbS⟩, Finset.mem_univ _, by simpa [restrictedHaarRefSet, hbS] using hb, rfl⟩

variable [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, MeasurableSpace (G i)] (B : ∀ i, Subgroup (G i))
  [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
  [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]

/-- **The restricted product of Haar measures.** Given local Haar measures `μ i` on locally compact
groups `G i` with open subgroups `B i` that are compact and of `μ i`-mass `1` for all but finitely
many `i`, `Measure.restrictedHaar B hB μ hμ` is the Haar measure on `Πʳ i, [G i, B i]` obtained by
normalizing Haar measure on the restricted product so that the reference compact box over
`{i | ¬ IsCompact (B i) ∨ μ i (B i) ≠ 1}` has the product of its local masses. -/
@[to_additive /-- **The restricted product of additive Haar measures.** Given local additive Haar
measures `μ i` on locally compact additive groups `G i` with open subgroups `B i` that are compact
and of `μ i`-mass `1` for all but finitely many `i`, `Measure.restrictedAddHaar B hB μ hμ` is the
additive Haar measure on `Πʳ i, [G i, B i]` obtained by normalizing additive Haar measure on the
restricted product so that the reference compact box over
`{i | ¬ IsCompact (B i) ∨ μ i (B i) ≠ 1}` has the product of its local masses. -/]
noncomputable def restrictedHaar (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    Measure (Πʳ i, [G i, B i]) :=
  letI : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let hS₀ := finite_not_isCompact_or_measure_ne_one B hB μ hμ
  letI : Fintype {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1} := hS₀.fintype
  let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
  (restrictedHaarRefMass {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1} μ /
      (ν₀ (restrictedHaarRefBox B hS₀)).toNNReal) • ν₀

/-- `Measure.restrictedHaar B hB μ hμ` is a Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `Measure.restrictedAddHaar B hB μ hμ` is an additive Haar measure on
`Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_restrictedHaar (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    (restrictedHaar B hB μ hμ).IsHaarMeasure := by
  let _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let hS₀ := finite_not_isCompact_or_measure_ne_one B hB μ hμ
  let _ : Fintype {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1} := hS₀.fintype
  have hK := isCompact_restrictedHaarRefBox B hS₀ fun i hi ↦ not_not.1 fun h ↦ hi (Or.inl h)
  refine IsHaarMeasure.nnreal_smul Measure.haar (div_ne_zero (restrictedHaarRefMass_ne_zero _ μ) ?_)
  exact ENNReal.toNNReal_ne_zero.2 ⟨(measure_restrictedHaarRefBox_pos B hS₀ Measure.haar).ne',
    hK.measure_lt_top.ne⟩

@[to_additive]
private theorem restrictedHaar_refBox_S₀ (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    let hS₀ := finite_not_isCompact_or_measure_ne_one B hB μ hμ
    letI : Fintype {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1} := hS₀.fintype
    restrictedHaar B hB μ hμ (restrictedHaarRefBox B hS₀) =
      ∏ i : {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1},
        μ i.1 (closure (Classical.arbitrary (PositiveCompacts (G i.1)) : Set (G i.1))) := by
  let _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let hS₀ := finite_not_isCompact_or_measure_ne_one B hB μ hμ
  let _ : Fintype {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1} := hS₀.fintype
  have hK := isCompact_restrictedHaarRefBox B hS₀ fun i hi ↦ not_not.1 fun h ↦ hi (Or.inl h)
  have hpos : (Measure.haar : Measure (Πʳ i, [G i, B i])) (restrictedHaarRefBox B hS₀) ≠ 0 :=
    (measure_restrictedHaarRefBox_pos B hS₀ Measure.haar).ne'
  have htop : (Measure.haar : Measure (Πʳ i, [G i, B i])) (restrictedHaarRefBox B hS₀) ≠ ∞ :=
    hK.measure_lt_top.ne
  change ((restrictedHaarRefMass _ μ /
      ((Measure.haar : Measure (Πʳ i, [G i, B i])) (restrictedHaarRefBox B hS₀)).toNNReal : ℝ≥0) :
        ℝ≥0∞) * (Measure.haar : Measure (Πʳ i, [G i, B i])) (restrictedHaarRefBox B hS₀) = _
  rw [ENNReal.coe_div (ENNReal.toNNReal_ne_zero.2 ⟨hpos, htop⟩), ENNReal.coe_toNNReal htop,
    ENNReal.div_mul_cancel hpos htop, coe_restrictedHaarRefMass]

variable [Countable ι] [∀ i, SecondCountableTopology (G i)] [∀ i, BorelSpace (G i)]

/-- `Measure.restrictedHaar B hB μ hμ` is σ-finite (since the restricted product is locally compact
and second countable). -/
@[to_additive /-- `Measure.restrictedAddHaar B hB μ hμ` is σ-finite. -/]
instance sigmaFinite_restrictedHaar (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    SigmaFinite (restrictedHaar B hB μ hμ) := by
  let _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  infer_instance

/-- Private helper: stage pullback identity when `T` contains the exceptional set `S₀`. -/
@[to_additive]
private theorem comap_stageEmbedding_restrictedHaar_of_subset {T : Set ι} (hT : T.Finite)
    [Fintype T] (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    (hsub : {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1} ⊆ T)
    [∀ j : {i // i ∉ T}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))] :
    (restrictedHaar B hB μ hμ).comap (stageEmbedding T hT B) =
      (Measure.pi fun i : T ↦ μ i.1).prod
        (Measure.infinitePi fun j : {i // i ∉ T} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1)) := by
  classical
  set S₀ : Set ι := {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1}
  have hS₀ : S₀.Finite := finite_not_isCompact_or_measure_ne_one B hB μ hμ
  let _ : Fintype S₀ := hS₀.fintype
  have hemb := measurableEmbedding_stageEmbedding (S := T) (hS := hT) (B := B)
    fun i _ ↦ hBopen.out i
  have _ : SigmaFinite ((restrictedHaar B hB μ hμ).comap (stageEmbedding T hT B)) :=
    hemb.measurable.sigmaFinite_comap _
  have _ : ((restrictedHaar B hB μ hμ).comap (stageEmbedding T hT B)).IsMulLeftInvariant :=
    isMulLeftInvariant_comap _ (stageEmbedding T hT B)
  set E : Set ((∀ i : T, G i.1) × (∀ j : {i // i ∉ T}, B j.1)) :=
    stageEmbedding T hT B ⁻¹' {x | ∀ i, x i ∈ restrictedHaarRefSet B S₀ i}
  have himg : stageEmbedding T hT B '' E = restrictedHaarRefBox B hS₀ := by
    rw [restrictedHaarRefBox_eq, image_preimage_eq_iff, range_stageEmbedding]
    intro x hx i hiT
    have hiS₀ : i ∉ S₀ := fun h ↦ hiT (hsub h)
    simpa [restrictedHaarRefSet, hiS₀] using hx i
  have hcomapE : (restrictedHaar B hB μ hμ).comap (stageEmbedding T hT B) E =
      restrictedHaarRefMass S₀ μ := by
    rw [hemb.comap_apply, himg, restrictedHaar_refBox_S₀, coe_restrictedHaarRefMass]
  have hprodE : ((Measure.pi fun i : T ↦ μ i.1).prod
      (Measure.infinitePi fun j : {i // i ∉ T} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))) E =
      restrictedHaarRefMass S₀ μ := by
    rw [show E = _ from preimage_stageEmbedding_restrictedHaarRefSet B hT hsub,
      prod_prod, pi_pi, measure_univ, mul_one]
    exact prod_measure_restrictedHaarRefSet B hsub μ fun i _ hi ↦ not_not.1 fun hm ↦ hi (Or.inr hm)
  have hne0 : (restrictedHaarRefMass S₀ μ : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (restrictedHaarRefMass_ne_zero S₀ μ)
  rw [measure_eq_div_smul ((restrictedHaar B hB μ hμ).comap (stageEmbedding T hT B)) _
    (hprodE ▸ hne0) (hprodE ▸ ENNReal.coe_ne_top), hcomapE, hprodE,
    ENNReal.div_self hne0 ENNReal.coe_ne_top, one_smul]

/-- **Stage decomposition of the restricted Haar measure.** For any finite set `S` of indices
outside which `μ i (B i) = 1` (encoded as `IsProbabilityMeasure` on the subgroup pullbacks), pulling
`Measure.restrictedHaar B hB μ hμ` back along `stageEmbedding S hS B` gives the product of the
finite product measure `Measure.pi` over `S` with the infinite product measure `Measure.infinitePi`
away from `S`. -/
@[to_additive /-- **Stage decomposition of the restricted additive Haar measure.** For any finite
set `S` of indices outside which `μ i (B i) = 1` (encoded as `IsProbabilityMeasure` on the subgroup
pullbacks), pulling `Measure.restrictedAddHaar B hB μ hμ` back along `addStageEmbedding S hS B`
gives the product of the finite product measure `Measure.pi` over `S` with the infinite product
measure `Measure.infinitePi` away from `S`. -/]
theorem comap_stageEmbedding_restrictedHaar {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [hprob : ∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))] :
    (restrictedHaar B hB μ hμ).comap (stageEmbedding S hS B) =
      (Measure.pi fun i : S ↦ μ i.1).prod
        (Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1)) := by
  classical
  -- Enlarge `S` to `T = S ∪ S₀` so the auxiliary theorem applies on `T`, then compare on a single
  -- reference box over `S` using `measure_eq_div_smul`.
  let T : Set ι := S ∪ {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1}
  have hT : T.Finite := hS.union (finite_not_isCompact_or_measure_ne_one B hB μ hμ)
  let _ : Fintype T := hT.fintype
  have _ (j : {i // i ∉ T}) : IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    hprob ⟨j.1, fun hs ↦ j.2 (Or.inl hs)⟩
  have hembS := measurableEmbedding_stageEmbedding (S := S) (hS := hS) (B := B)
    fun i _ ↦ hBopen.out i
  have hembT := measurableEmbedding_stageEmbedding (S := T) (hS := hT) (B := B)
    fun i _ ↦ hBopen.out i
  have _ : SigmaFinite ((restrictedHaar B hB μ hμ).comap (stageEmbedding S hS B)) :=
    hembS.measurable.sigmaFinite_comap _
  have _ : ((restrictedHaar B hB μ hμ).comap (stageEmbedding S hS B)).IsMulLeftInvariant :=
    isMulLeftInvariant_comap _ (stageEmbedding S hS B)
  let ES : Set ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) :=
    (univ.pi fun i : S ↦
      closure (Classical.arbitrary (PositiveCompacts (G i.1)) : Set (G i.1))) ×ˢ univ
  have hprodES : ((Measure.pi fun i : S ↦ μ i.1).prod
      (Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))) ES =
      restrictedHaarRefMass S μ := by
    rw [prod_prod, pi_pi, measure_univ, mul_one, coe_restrictedHaarRefMass]
  have hcomapES : (restrictedHaar B hB μ hμ).comap (stageEmbedding S hS B) ES =
      restrictedHaarRefMass S μ := by
    have hsubT : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ restrictedHaarRefSet B S i} ⊆
        range (stageEmbedding T hT B) := by
      rw [range_stageEmbedding]
      intro x hx i hiT
      have hiS : i ∉ S := fun hs ↦ hiT (Or.inl hs)
      simpa [restrictedHaarRefSet, hiS] using hx i
    rw [hembS.comap_apply, show stageEmbedding S hS B '' ES = _ from restrictedHaarRefBox_eq B hS,
      ← image_preimage_eq_of_subset hsubT, ← hembT.comap_apply,
      comap_stageEmbedding_restrictedHaar_of_subset B hT hB μ hμ subset_union_right,
      preimage_stageEmbedding_restrictedHaarRefSet B hT subset_union_left,
      prod_prod, pi_pi, measure_univ, mul_one]
    exact prod_measure_restrictedHaarRefSet B subset_union_left μ fun i _ hi ↦
      (isProbabilityMeasure_comap_subtype_iff (hBopen.out i).measurableSet (μ i)).1 (hprob ⟨i, hi⟩)
  have hne0 : (restrictedHaarRefMass S μ : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (restrictedHaarRefMass_ne_zero S μ)
  rw [measure_eq_div_smul ((restrictedHaar B hB μ hμ).comap (stageEmbedding S hS B)) _
    (hprodES ▸ hne0) (hprodES ▸ ENNReal.coe_ne_top), hcomapES, hprodES,
    ENNReal.div_self hne0 ENNReal.coe_ne_top, one_smul]

/-- Pushing the stage product measure forward along `stageEmbedding S hS B` gives the restriction
of `Measure.restrictedHaar B hB μ hμ` to the open subgroup `{x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive /-- Pushing the stage product measure forward along `addStageEmbedding S hS B` gives
the restriction of `Measure.restrictedAddHaar B hB μ hμ` to the open additive subgroup
`{x | ∀ i ∉ S, x i ∈ B i}`. -/]
theorem map_stageEmbedding_eq_restrict_restrictedHaar {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))] :
    ((Measure.pi fun i : S ↦ μ i.1).prod
      (Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))).map
        (stageEmbedding S hS B) =
      (restrictedHaar B hB μ hμ).restrict {x | ∀ i ∉ S, x i ∈ B i} := by
  rw [← comap_stageEmbedding_restrictedHaar B hS hB μ hμ,
    (measurableEmbedding_stageEmbedding fun i _ ↦ hBopen.out i).map_comap, range_stageEmbedding]

/-- **Tonelli's theorem on an open subgroup stage.** For a measurable function `f` into `ℝ≥0∞`,
its Lebesgue integral on `{x | ∀ i ∉ S, x i ∈ B i}` splits as an iterated integral over
`∀ i : S, G i` against `Measure.pi` and `∀ j : {i // i ∉ S}, B j` against `Measure.infinitePi`. -/
@[to_additive /-- **Tonelli's theorem on an open additive-subgroup stage.** For a measurable
function `f` into `ℝ≥0∞`, its Lebesgue integral on `{x | ∀ i ∉ S, x i ∈ B i}` splits as an iterated
integral over `∀ i : S, G i` against `Measure.pi` and `∀ j : {i // i ∉ S}, B j` against
`Measure.infinitePi`. -/]
theorem setLIntegral_stage_restrictedHaar {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))]
    {f : Πʳ i, [G i, B i] → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in {x | ∀ i ∉ S, x i ∈ B i}, f x ∂restrictedHaar B hB μ hμ =
      ∫⁻ y, ∫⁻ z, f (stageEmbedding S hS B (y, z))
        ∂Measure.infinitePi (fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))
        ∂Measure.pi fun i : S ↦ μ i.1 := by
  have hemb := measurableEmbedding_stageEmbedding (S := S) (hS := hS) (B := B)
    fun i _ ↦ hBopen.out i
  rw [← map_stageEmbedding_eq_restrict_restrictedHaar B hS hB μ hμ,
    lintegral_map hf hemb.measurable,
    lintegral_prod (fun p ↦ f (stageEmbedding S hS B p)) (hf.comp hemb.measurable).aemeasurable]

/-- **Factorizable Lebesgue integral on an open subgroup stage.** -/
@[to_additive setLIntegral_stage_mul_restrictedAddHaar
  /-- **Factorizable Lebesgue integral on an open additive-subgroup stage.** -/]
theorem setLIntegral_stage_mul_restrictedHaar {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))]
    {f : (∀ i : S, G i.1) → ℝ≥0∞} {g : (∀ j : {i // i ∉ S}, G j.1) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x in {x | ∀ i ∉ S, x i ∈ B i},
        f (fun i : S ↦ x i.1) * g (fun j : {i // i ∉ S} ↦ x j.1) ∂restrictedHaar B hB μ hμ =
      (∫⁻ y, f y ∂Measure.pi fun i : S ↦ μ i.1) *
        ∫⁻ z, g (fun j ↦ (z j : G j.1))
          ∂Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1) := by
  have hmS : Measurable fun x : Πʳ i, [G i, B i] ↦ fun i : S ↦ x i.1 :=
    Measurable.of_eval fun i : S ↦ (RestrictedProduct.continuous_eval i.1).measurable
  have hmSc : Measurable fun x : Πʳ i, [G i, B i] ↦ fun j : {i // i ∉ S} ↦ x j.1 :=
    Measurable.of_eval fun j : {i // i ∉ S} ↦ (RestrictedProduct.continuous_eval j.1).measurable
  have hm : Measurable (fun x : Πʳ i, [G i, B i] ↦
      f (fun i : S ↦ x i.1) * g (fun j : {i // i ∉ S} ↦ x j.1)) :=
    (hf.comp hmS).mul (hg.comp hmSc)
  rw [← map_stageEmbedding_eq_restrict_restrictedHaar B hS hB μ hμ,
    lintegral_map hm (measurableEmbedding_stageEmbedding fun i _ ↦ hBopen.out i).measurable]
  let g' : (∀ j : {i // i ∉ S}, B j.1) → ℝ≥0∞ := fun z ↦ g fun j ↦ (z j : G j.1)
  have hg' : Measurable g' :=
    hg.comp (Measurable.of_eval fun j ↦ measurable_subtype_coe.comp (measurable_pi_apply j))
  have hcomp : (fun p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1) ↦
      f (fun i : S ↦ stageEmbedding S hS B p i.1) *
        g (fun j : {i // i ∉ S} ↦ stageEmbedding S hS B p j.1)) =
      fun p ↦ f p.1 * g' p.2 := by
    ext ⟨y, z⟩
    simp [g']
  rw [hcomp, lintegral_prod_mul hf.aemeasurable hg'.aemeasurable]

/-- **Fubini's theorem on an open subgroup stage.** For a Banach-space-valued function `f`
integrable on `{x | ∀ i ∉ S, x i ∈ B i}`, its Bochner integral splits into the finite product
integral over `S` and the infinite-product integral away from `S`. -/
@[to_additive /-- **Fubini's theorem on an open additive-subgroup stage.** For a Banach-space-valued
function `f` integrable on `{x | ∀ i ∉ S, x i ∈ B i}`, its Bochner integral splits into the finite
product integral over `S` and the infinite-product integral away from `S`. -/]
theorem setIntegral_stage_restrictedHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))]
    {f : Πʳ i, [G i, B i] → E}
    (hf : IntegrableOn f {x | ∀ i ∉ S, x i ∈ B i} (restrictedHaar B hB μ hμ)) :
    ∫ x in {x | ∀ i ∉ S, x i ∈ B i}, f x ∂restrictedHaar B hB μ hμ =
      ∫ y, ∫ z, f (stageEmbedding S hS B (y, z))
        ∂Measure.infinitePi (fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))
        ∂Measure.pi fun i : S ↦ μ i.1 := by
  have hemb := measurableEmbedding_stageEmbedding (S := S) (hS := hS) (B := B)
    fun i _ ↦ hBopen.out i
  have hmap := map_stageEmbedding_eq_restrict_restrictedHaar B hS hB μ hμ
  rw [IntegrableOn, ← hmap, hemb.integrable_map_iff] at hf
  rw [← hmap, hemb.integral_map, integral_prod (fun p ↦ f (stageEmbedding S hS B p)) hf]

/-- **Factorizable Bochner integral on an open subgroup stage (scalar action)**, with no
integrability hypothesis needed (matching Mathlib's `MeasureTheory.integral_prod_smul`). -/
@[to_additive (dont_translate := 𝕜 E) setIntegral_stage_smul_restrictedAddHaar
  /-- **Factorizable Bochner integral on an open additive-subgroup stage (scalar action)**, with no
  integrability hypothesis needed (matching Mathlib's `MeasureTheory.integral_prod_smul`). -/]
theorem setIntegral_stage_smul_restrictedHaar {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))]
    (f : (∀ i : S, G i.1) → 𝕜) (g : (∀ j : {i // i ∉ S}, G j.1) → E) :
    ∫ x in {x | ∀ i ∉ S, x i ∈ B i},
        f (fun i : S ↦ x i.1) • g (fun j : {i // i ∉ S} ↦ x j.1) ∂restrictedHaar B hB μ hμ =
      (∫ y, f y ∂Measure.pi fun i : S ↦ μ i.1) •
        ∫ z, g (fun j ↦ (z j : G j.1))
          ∂Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1) := by
  have hemb := measurableEmbedding_stageEmbedding (S := S) (hS := hS) (B := B)
    fun i _ ↦ hBopen.out i
  rw [← map_stageEmbedding_eq_restrict_restrictedHaar B hS hB μ hμ, hemb.integral_map]
  let g' : (∀ j : {i // i ∉ S}, B j.1) → E := fun z ↦ g fun j ↦ (z j : G j.1)
  have hcomp : (fun p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1) ↦
      f (fun i : S ↦ stageEmbedding S hS B p i.1) •
        g (fun j : {i // i ∉ S} ↦ stageEmbedding S hS B p j.1)) =
      fun p ↦ f p.1 • g' p.2 := by
    ext ⟨y, z⟩
    simp [g']
  rw [hcomp, integral_prod_smul f g']

/-- **Factorizable Bochner integral on an open subgroup stage (scalar multiplication)** over `ℝ` or
`ℂ`, with no integrability hypothesis needed. -/
@[to_additive (dont_translate := L) setIntegral_stage_mul_restrictedAddHaar
  /-- **Factorizable Bochner integral on an open additive-subgroup stage (scalar multiplication)**
  over `ℝ` or `ℂ`, with no integrability hypothesis needed. -/]
theorem setIntegral_stage_mul_restrictedHaar {L : Type*} [RCLike L]
    {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))]
    (f : (∀ i : S, G i.1) → L) (g : (∀ j : {i // i ∉ S}, G j.1) → L) :
    ∫ x in {x | ∀ i ∉ S, x i ∈ B i},
        f (fun i : S ↦ x i.1) * g (fun j : {i // i ∉ S} ↦ x j.1) ∂restrictedHaar B hB μ hμ =
      (∫ y, f y ∂Measure.pi fun i : S ↦ μ i.1) *
        ∫ z, g (fun j ↦ (z j : G j.1))
          ∂Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1) :=
  setIntegral_stage_smul_restrictedHaar B hS hB μ hμ f g

/-- **Bochner integral of a function depending only on `S` over an open subgroup stage**, with no
integrability hypothesis needed: since `Measure.infinitePi` away from `S` is a probability measure,
the integral over `{x | ∀ i ∉ S, x i ∈ B i}` reduces to `∫ y, f y ∂Measure.pi (fun i : S ↦ μ i.1)`.
-/
@[to_additive (dont_translate := E)
  /-- **Bochner integral of a function depending only on `S` over an open additive-subgroup stage**,
  with no integrability hypothesis needed: since `Measure.infinitePi` away from `S` is a probability
  measure, the integral over `{x | ∀ i ∉ S, x i ∈ B i}` reduces to
  `∫ y, f y ∂Measure.pi (fun i : S ↦ μ i.1)`. -/]
theorem setIntegral_stage_fst_restrictedHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set ι} (hS : S.Finite) [Fintype S]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    [∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1))]
    (f : (∀ i : S, G i.1) → E) :
    ∫ x in {x | ∀ i ∉ S, x i ∈ B i}, f (fun i : S ↦ x i.1) ∂restrictedHaar B hB μ hμ =
      ∫ y, f y ∂Measure.pi fun i : S ↦ μ i.1 := by
  have hemb := measurableEmbedding_stageEmbedding (S := S) (hS := hS) (B := B)
    fun i _ ↦ hBopen.out i
  rw [← map_stageEmbedding_eq_restrict_restrictedHaar B hS hB μ hμ, hemb.integral_map]
  have hcomp : (fun p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1) ↦
      f (fun i : S ↦ stageEmbedding S hS B p i.1)) = fun p ↦ f p.1 := by
    ext ⟨y, z⟩
    simp
  have h1 : (fun q : (∀ j : {i // i ∉ S}, B j.1) × (∀ i : S, G i.1) ↦ f q.swap.1) =
      fun q ↦ (1 : ℝ) • f q.2 := by
    ext
    simp
  rw [hcomp, ← integral_prod_swap, h1, integral_prod_smul (fun _ ↦ (1 : ℝ)) f]
  simp

/-- **The box formula for the restricted Haar measure.** Every box `{x | ∀ i, x i ∈ C i}` with
`C i = B i` for all but finitely many `i` has mass `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **The box formula for the restricted additive Haar measure.** Every box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` for all but finitely many `i` has mass
`∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_forall_mem (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in Filter.cofinite, C i = B i) :
    restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  classical
  set S : Set ι := {i | C i ≠ B i ∨ μ i (B i) ≠ 1}
  have hS : S.Finite := Set.Finite.union hCB hμ
  let _ : Fintype S := hS.fintype
  have _ (j : {i // i ∉ S}) : IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    (isProbabilityMeasure_comap_subtype_iff (hBopen.out j.1).measurableSet (μ j.1)).2
      (not_not.1 fun h ↦ j.2 (Or.inr h))
  have hemb := measurableEmbedding_stageEmbedding (S := S) (hS := hS) (B := B)
    fun i _ ↦ hBopen.out i
  have hsub : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} ⊆ range (stageEmbedding S hS B) := by
    rw [range_stageEmbedding]
    intro x hx i hiS
    have hCi : C i = B i := not_not.1 fun h ↦ hiS (Or.inl h)
    exact SetLike.mem_coe.1 (hCi ▸ hx i)
  rw [← image_preimage_eq_of_subset hsub, ← hemb.comap_apply,
    comap_stageEmbedding_restrictedHaar B hS hB μ hμ, preimage_stageEmbedding_forall_mem]
  have h2 : (univ.pi fun j : {i // i ∉ S} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) = univ := by
    ext z
    simp only [mem_univ_pi, mem_preimage, mem_univ, iff_true]
    intro j
    have hCj : C j.1 = B j.1 := not_not.1 fun h ↦ j.2 (Or.inl h)
    rw [hCj]
    exact (z j).2
  rw [h2, prod_prod, pi_pi, measure_univ, mul_one,
    finprod_eq_prod_of_mulSupport_subset _ (s := hS.toFinset) fun i hi ↦ hS.mem_toFinset.2 ?_]
  · refine Finset.prod_bij (fun (i : S) _ ↦ i.1) (fun i _ ↦ hS.mem_toFinset.2 i.2)
      (fun a _ b _ h ↦ Subtype.ext h)
      (fun b hb ↦ ⟨⟨b, hS.mem_toFinset.1 hb⟩, Finset.mem_univ _, rfl⟩) fun _ _ ↦ rfl
  · by_contra hnotS
    have hCi : C i = B i := not_not.1 fun h ↦ hnotS (Or.inl h)
    have hμi : μ i (B i) = 1 := not_not.1 fun h ↦ hnotS (Or.inr h)
    exact hi (by dsimp only; rw [hCi, hμi])

/-- **Uniqueness of the restricted Haar measure.** Any Haar measure on `Πʳ i, [G i, B i]` agreeing
with the product formula on measurable boxes equals `Measure.restrictedHaar B hB μ hμ`. -/
@[to_additive /-- **Uniqueness of the restricted additive Haar measure.** Any additive Haar measure
on `Πʳ i, [G i, B i]` agreeing with the product formula on measurable boxes equals
`Measure.restrictedAddHaar B hB μ hμ`. -/]
theorem eq_restrictedHaar_of_forall_mem (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {ν : Measure (Πʳ i, [G i, B i])} [ν.IsHaarMeasure]
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
      (∀ᶠ i in Filter.cofinite, C i = B i) → ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B hB μ hμ := by
  classical
  let _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  set S₀ : Set ι := {i | ¬ IsCompact (B i : Set (G i)) ∨ μ i (B i) ≠ 1}
  have hS₀ : S₀.Finite := finite_not_isCompact_or_measure_ne_one B hB μ hμ
  have hC₀_meas (i : ι) : MeasurableSet (restrictedHaarRefSet B S₀ i) := by
    dsimp only [restrictedHaarRefSet]
    split_ifs
    · exact isClosed_closure.measurableSet
    · exact (hBopen.out i).measurableSet
  have hC₀_cof : ∀ᶠ i in Filter.cofinite, restrictedHaarRefSet B S₀ i = B i :=
    Filter.eventually_cofinite.2
      (hS₀.subset fun i hi ↦ by by_contra h; exact hi (by simp [restrictedHaarRefSet, h]))
  have hK := isCompact_restrictedHaarRefBox B hS₀ fun i hi ↦ not_not.1 fun h ↦ hi (Or.inl h)
  have hpos : restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ restrictedHaarRefSet B S₀ i} ≠ 0 := by
    rw [← restrictedHaarRefBox_eq B hS₀]
    exact (measure_restrictedHaarRefBox_pos B hS₀ _).ne'
  have htop : restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ restrictedHaarRefSet B S₀ i} ≠ ∞ := by
    rw [← restrictedHaarRefBox_eq B hS₀]
    exact hK.measure_lt_top.ne
  have heq : ν {x | ∀ i, x i ∈ restrictedHaarRefSet B S₀ i} =
      restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ restrictedHaarRefSet B S₀ i} := by
    rw [hν _ hC₀_meas hC₀_cof, restrictedHaar_forall_mem B hB μ hμ hC₀_cof]
  rw [measure_eq_div_smul ν (restrictedHaar B hB μ hμ) hpos htop, heq,
    ENNReal.div_self hpos htop, one_smul]

/-- **Rescaling one local Haar measure.** Scaling `μ i₀` by `c : ℝ≥0` while leaving `μ i` unchanged
for `i ≠ i₀` scales `Measure.restrictedHaar` globally by `c` (`c ≠ 0` is forced by
`[(μ' i₀).IsHaarMeasure]`). -/
@[to_additive restrictedAddHaar_eq_smul_of_eq_away
  /-- **Rescaling one local additive Haar measure.** Scaling `μ i₀` by `c : ℝ≥0` while leaving
  `μ i` unchanged for `i ≠ i₀` scales `Measure.restrictedAddHaar` globally by `c` (`c ≠ 0` is
  forced by `[(μ' i₀).IsAddHaarMeasure]`). -/]
theorem restrictedHaar_eq_smul_of_eq_away
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ μ' : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ' i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    (hμ' : ∀ᶠ i in Filter.cofinite, μ' i (B i) = 1)
    (i₀ : ι) {c : ℝ≥0} (hi₀ : μ' i₀ = c • μ i₀)
    (hne : ∀ i ≠ i₀, μ' i = μ i) :
    restrictedHaar B hB μ' hμ' = c • restrictedHaar B hB μ hμ := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact isOpen_univ.measure_ne_zero (μ' i₀) ⟨1, mem_univ 1⟩ (by simp [hi₀])
  have _ : (c • restrictedHaar B hB μ hμ).IsHaarMeasure := IsHaarMeasure.nnreal_smul _ hc
  symm
  refine eq_restrictedHaar_of_forall_mem B hB μ' hμ' fun C _ hCB ↦ ?_
  rw [smul_apply, nnreal_smul_coe_apply, restrictedHaar_forall_mem B hB μ hμ hCB]
  have hsupp (ν : ∀ i, Measure (G i)) (hν : ∀ᶠ i in Filter.cofinite, ν i (B i) = 1) :
      HasFiniteMulSupport fun i ↦ ν i (C i) :=
    (Set.Finite.union hCB hν).subset fun i hi ↦ by
      by_contra h
      exact hi (by
        dsimp only
        rw [show C i = B i from not_not.1 (h ∘ Or.inl), not_not.1 (h ∘ Or.inr)])
  rw [← mul_finprod_cond_ne i₀ (hsupp μ hμ), ← mul_finprod_cond_ne i₀ (hsupp μ' hμ'), hi₀,
    smul_apply, nnreal_smul_coe_apply, mul_assoc]
  congr 2
  exact finprod_congr fun i ↦ finprod_congr fun hi ↦ by rw [hne i hi]

@[to_additive]
private theorem pow_two_mul_le_restrictedHaar_forall_mem
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hBC : ∀ i, (B i : Set (G i)) ⊆ C i)
    (hinf : {i | 2 ≤ μ i (C i)}.Infinite) (n : ℕ) :
    (2 : ℝ≥0∞) ^ n * (∏ i ∈ hμ.toFinset, μ i (B i)) ≤
      restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i} := by
  classical
  obtain ⟨T, hTI, rfl⟩ := (hinf.sdiff hμ).exists_subset_card_eq n
  let D : ∀ i, Set (G i) := fun i ↦ if i ∈ T then C i else B i
  have hDC : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ D i} ⊆ {x | ∀ i, x i ∈ C i} := fun x hx i ↦ by
    have hxi := hx i
    dsimp only [D] at hxi
    split_ifs at hxi <;> [exact hxi; exact hBC i hxi]
  have hDB : ∀ᶠ i in Filter.cofinite, D i = B i :=
    Filter.Eventually.mono T.finite_toSet.compl_mem_cofinite fun i (hi : i ∉ T) ↦ by simp [D, hi]
  have hdisj : Disjoint T hμ.toFinset :=
    Finset.disjoint_left.2 fun i hiT hiS₀ ↦ (hTI hiT).2 (hμ.mem_toFinset.1 hiS₀)
  refine le_trans ?_ ((restrictedHaar_forall_mem B hB μ hμ hDB).symm.trans_le (measure_mono hDC))
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T ∪ hμ.toFinset) fun i hi ↦ ?_,
    Finset.prod_union hdisj]
  · refine mul_le_mul' ?_ (le_of_eq (Finset.prod_congr rfl fun i hi ↦ ?_))
    · simpa using Finset.prod_le_prod fun i hi ↦
        (by simpa [D, hi] using (hTI hi).1 : (2 : ℝ≥0∞) ≤ μ i (D i))
    · simp [D, Finset.disjoint_right.1 hdisj hi]
  · by_cases hiT : i ∈ T
    · exact Finset.mem_union_left _ hiT
    · exact Finset.mem_union_right _ (hμ.mem_toFinset.2 (by simpa [D, hiT] using hi))

/-- **Divergence of boxes violating `C i = B i` cofinitely.** If `(B i : Set (G i)) ⊆ C i` for
every `i` and `2 ≤ μ i (C i)` for infinitely many `i`, then `{x | ∀ i, x i ∈ C i}` has infinite
`restrictedHaar` measure (whereas `∏ᶠ i, μ i (C i) = 1` because its multiplicative support is
infinite). -/
@[to_additive /-- **Divergence of boxes violating `C i = B i` cofinitely.** If
`(B i : Set (G i)) ⊆ C i` for every `i` and `2 ≤ μ i (C i)` for infinitely many `i`, then
`{x | ∀ i, x i ∈ C i}` has infinite `restrictedAddHaar` measure (whereas `∏ᶠ i, μ i (C i) = 1`
because its multiplicative support is infinite). -/]
theorem restrictedHaar_forall_mem_eq_top_of_infinite
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hBC : ∀ i, (B i : Set (G i)) ⊆ C i)
    (hinf : {i | 2 ≤ μ i (C i)}.Infinite) :
    restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i} = ∞ := by
  set M := restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i}
  set c₀ : ℝ≥0∞ := ∏ i ∈ hμ.toFinset, μ i (B i)
  have hc₀ : c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦
    ((hBopen.out i).measure_pos (μ i) ⟨1, (B i).one_mem⟩).ne'
  have hbound (n : ℕ) : (2 : ℝ≥0∞) ^ n * c₀ ≤ M :=
    pow_two_mul_le_restrictedHaar_forall_mem B hB μ hμ hBC hinf n
  by_contra hM
  have hc₀_top : c₀ ≠ ∞ := fun h ↦ hM (top_unique (by simpa [h] using hbound 0))
  have hdiv : M / c₀ ≠ ∞ := ENNReal.div_ne_top hM hc₀
  obtain ⟨n, hn⟩ := exists_nat_gt (M / c₀).toNNReal
  have hle : (2 : ℝ≥0∞) ^ n ≤ M / c₀ :=
    (ENNReal.le_div_iff_mul_le (.inl hc₀) (.inl hc₀_top)).2 (hbound n)
  have hlt : M / c₀ < (2 : ℝ≥0∞) ^ n :=
    calc M / c₀ = ((M / c₀).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hdiv).symm
      _ < (n : ℝ≥0∞) := by exact_mod_cast hn
      _ ≤ (2 : ℝ≥0∞) ^ n := by exact_mod_cast n.lt_two_pow_self.le
  exact hlt.not_ge hle

end RestrictedHaar

end MeasureTheory.Measure

namespace TauCeti

section ExistsUnique

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  {B : ∀ i, Subgroup (G i)}

/-- **Existence and uniqueness of restricted products of Haar measures.** When `ι` is countable,
each `G i` is a second-countable locally compact topological group, each `B i` is an open subgroup
compact for all but finitely many `i`, and `μ i` are local Haar measures with `μ i (B i) = 1` for
all but finitely many `i`, there is a unique Haar measure on `Πʳ i, [G i, B i]` assigning to every
Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the product `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Existence and uniqueness of restricted products of additive Haar measures.**
When `ι` is countable, each `G i` is a second-countable locally compact additive topological group,
each `B i` is an open subgroup compact for all but finitely many `i`, and `μ i` are local additive
Haar measures with `μ i (B i) = 1` for all but finitely many `i`, there is a unique additive Haar
measure on `Πʳ i, [G i, B i]` assigning to every Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
cofinitely the product `∏ᶠ i, μ i (C i)`. -/]
theorem exists_unique_restrictedHaar [Countable ι] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (hB : ∀ᶠ i in Filter.cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in Filter.cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in Filter.cofinite, C i = B i) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) :=
  ⟨Measure.restrictedHaar B hB μ hμ,
    ⟨inferInstance, fun _ _ hCB ↦ Measure.restrictedHaar_forall_mem B hB μ hμ hCB⟩,
    fun _ ⟨hHaar, hbox⟩ ↦
      letI := hHaar
      Measure.eq_restrictedHaar_of_forall_mem B hB μ hμ hbox⟩

end ExistsUnique

end TauCeti
