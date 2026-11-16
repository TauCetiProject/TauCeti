/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.UrysohnsLemma
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Separation.PerfectlyNormal
import TauCeti.MeasureTheory.Constructions.BorelSpace.Prod

/-!
# Baire sets and hulls

The Baire σ-algebra is the smallest σ-algebra making every continuous real-valued function
measurable. It is contained in the Borel σ-algebra, and coincides with it on perfectly normal
(in particular pseudometrizable) spaces, though the two need not coincide without countability or
separation assumptions. Every Baire set is pulled back from a Borel subset of `ℕ → ℝ` along a
countable sequence of continuous real-valued functions, and every clopen set is Baire measurable
with subtype Baire σ-algebra induced from the ambient space. Because continuous real-valued
functions on `X × Y` are measurable for the product σ-algebra when `X` and `Y` are σ-compact with
`Y` Hausdorff (or when `X` is σ-compact and `Y` is compact), any continuous map out of such a
product is measurable into the Baire σ-algebra of its target. This notion is different from having
the Baire property (agreement with an open set modulo a meagre set).

For an outer regular measure on a locally compact Hausdorff space, every compact set of
finite measure has a compact Baire-measurable superset of the same measure, inside any
prescribed open neighbourhood. The hull is a countable intersection of level sets of compactly
supported continuous functions. This supplies compact Baire approximations for comparing Borel
and Baire measure theory, in particular for Haar measures on groups without second countability.
For measures finite on compact sets, countable unions of these hulls give σ-compact Baire
hulls of σ-compact sets with null excess.

## References

* D. H. Fremlin, *Measure Theory*, §443, for the Baire and Borel comparison for Haar measures.
-/

public section

open Set MeasureTheory Filter Topology TopologicalSpace

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The Baire σ-algebra: the smallest σ-algebra making continuous real-valued functions
measurable. This is not the σ-algebra of sets with the Baire property. -/
@[instance_reducible]
def baire (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  ⨆ f : C(X, ℝ), MeasurableSpace.comap f (borel ℝ)

/-- The defining universal property of the Baire σ-algebra. -/
theorem baire_le_iff {m : MeasurableSpace X} :
    baire X ≤ m ↔ ∀ f : C(X, ℝ), Measurable[m] f := by
  simp only [baire, iSup_le_iff, measurable_iff_comap_le, BorelSpace.measurable_eq]

/-- Every Baire set is Borel. -/
theorem baire_le_borel : baire X ≤ borel X :=
  baire_le_iff.2 fun f => f.continuous.borel_measurable

/-- Every Baire set is measurable in any `OpensMeasurableSpace`. -/
theorem baire_le [MeasurableSpace X] [OpensMeasurableSpace X] :
    baire X ≤ ‹MeasurableSpace X› :=
  baire_le_iff.2 fun f => f.continuous.measurable

/-- A continuous real-valued function is measurable for the Baire σ-algebra. -/
theorem _root_.ContinuousMap.measurable_baire (f : C(X, ℝ)) :
    Measurable[TauCeti.baire X] f :=
  measurable_iff_comap_le.2 (le_iSup (fun f : C(X, ℝ) =>
    MeasurableSpace.comap f (borel ℝ)) f)

/-- Continuous maps are measurable between Baire σ-algebras. -/
theorem _root_.Continuous.measurable_baire {f : X → Y} (hf : Continuous f) :
    @Measurable X Y (TauCeti.baire X) (TauCeti.baire Y) f := by
  rw [measurable_iff_le_map, baire_le_iff]
  intro g
  exact (g.comp ⟨f, hf⟩).measurable_baire

/-- On a perfectly normal space (for instance, any pseudometrizable space), the Baire and Borel
σ-algebras coincide. -/
theorem baire_eq_borel [PerfectlyNormalSpace X] : baire X = borel X := by
  refine le_antisymm baire_le_borel ?_
  rw [borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun s hs => ?_
  obtain ⟨f, rfl, -⟩ := perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.1 ‹_› s hs
  exact f.measurable_baire (measurableSet_singleton 0)

/-- Every Baire set is the preimage of a measurable subset of `ℕ → ℝ` under a sequence of
continuous real-valued functions. -/
theorem measurableSet_baire_iff_exists_continuousMap {s : Set X} :
    MeasurableSet[baire X] s ↔
      ∃ (f : ℕ → C(X, ℝ)) (t : Set (ℕ → ℝ)), MeasurableSet t ∧
        s = (fun x k => f k x) ⁻¹' t := by
  refine ⟨?_, ?_⟩
  · let m : MeasurableSpace X :=
      { MeasurableSet' u := ∃ (f : ℕ → C(X, ℝ)) (t : Set (ℕ → ℝ)), MeasurableSet t ∧
          u = (fun x k => f k x) ⁻¹' t
        measurableSet_empty := ⟨fun _ => ContinuousMap.const X 0, ∅, MeasurableSet.empty, rfl⟩
        measurableSet_compl := fun u ⟨f, t, ht, hu⟩ =>
          ⟨f, tᶜ, ht.compl, by rw [hu, preimage_compl]⟩
        measurableSet_iUnion := fun u hu => by
          choose f t ht hu_eq using hu
          let e := Nat.pairEquiv.symm
          refine ⟨fun k => f (e k).1 (e k).2,
            ⋃ n, (fun (v : ℕ → ℝ) k => v (e.symm (n, k))) ⁻¹' t n,
            MeasurableSet.iUnion fun n =>
              (measurable_pi_iff.2 fun _ => measurable_pi_apply _) (ht n), ?_⟩
          ext x
          simp [hu_eq, e] }
    have hm : baire X ≤ m := baire_le_iff.2 fun g u hu =>
      ⟨fun _ => g, (fun v : ℕ → ℝ => v 0) ⁻¹' u, measurable_pi_apply 0 hu, rfl⟩
    exact fun hs => hm s hs
  · rintro ⟨f, t, ht, rfl⟩
    let _ : MeasurableSpace X := baire X
    exact (measurable_pi_iff.2 fun k => (f k).measurable_baire) ht

/-- Every clopen set is Baire measurable. -/
theorem _root_.IsClopen.measurableSet_baire {s : Set X} (hs : IsClopen s) :
    MeasurableSet[TauCeti.baire X] s := by
  let f : C(X, ℝ) :=
    ⟨s.indicator 1, continuous_indicator (by simp [hs]) continuous_const.continuousOn⟩
  have hsf : s = f ⁻¹' {1} := by
    ext x
    by_cases hx : x ∈ s <;> simp [f, hx]
  rw [hsf]
  exact f.measurable_baire (measurableSet_singleton 1)

/-- On a clopen subset `s`, the intrinsic Baire σ-algebra `baire s` coincides with the subtype
pullback of `baire X`. -/
theorem _root_.IsClopen.baire_subtype {s : Set X} (hs : IsClopen s) :
    TauCeti.baire s = (TauCeti.baire X).comap ((↑) : s → X) := by
  refine le_antisymm (baire_le_iff.2 fun g u hu => ?_)
    continuous_subtype_val.measurable_baire.comap_le
  classical
  let F : C(X, ℝ) :=
    { toFun x := if hx : x ∈ s then g ⟨x, hx⟩ else 0
      continuous_toFun := by
        refine continuous_def.2 fun V hV => ?_
        have hpre : (fun x => if hx : x ∈ s then g ⟨x, hx⟩ else 0) ⁻¹' V =
            ((↑) : s → X) '' (g ⁻¹' V) ∪ (if (0 : ℝ) ∈ V then sᶜ else ∅) := by
          ext x
          by_cases hxs : x ∈ s
          · lift x to s using hxs
            simp
          · simp [hxs]
        rw [hpre]
        refine (hs.2.isOpenMap_subtype_val _ (g.continuous.isOpen_preimage V hV)).union ?_
        split_ifs
        · exact hs.1.isOpen_compl
        · exact isOpen_empty }
  refine ⟨F ⁻¹' u, F.measurable_baire hu, ?_⟩
  ext x
  simp [F]

/-- The inclusion of a clopen subset `s` into `X` is a measurable embedding between Baire
σ-algebras. -/
theorem _root_.IsClopen.measurableEmbedding_baire_subtype_coe {s : Set X} (hs : IsClopen s) :
    @MeasurableEmbedding s X (TauCeti.baire s) (TauCeti.baire X) ((↑) : s → X) := by
  let _ : MeasurableSpace X := TauCeti.baire X
  exact hs.baire_subtype ▸ MeasurableEmbedding.subtype_coe hs.measurableSet_baire

/-- A continuous map from a product `X × Y` with `X` σ-compact and `Y` compact into any topological
space `Z` is measurable from the product σ-algebra into the Baire σ-algebra `TauCeti.baire Z`. -/
theorem _root_.Continuous.measurable_baire_prod_of_sigmaCompact_of_compact
    [SigmaCompactSpace X] [CompactSpace Y] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X × Y → Z} (hf : Continuous f) :
    @Measurable (X × Y) Z Prod.instMeasurableSpace (TauCeti.baire Z) f := by
  rw [measurable_iff_le_map, baire_le_iff]
  intro g
  exact (g.continuous.comp hf).measurable_prod_of_sigmaCompact_of_compact

/-- A continuous map from a product `X × Y` of σ-compact spaces, with `Y` Hausdorff, into any
topological space `Z` is measurable from the product σ-algebra into `TauCeti.baire Z`. -/
theorem _root_.Continuous.measurable_baire_prod_of_sigmaCompact
    [SigmaCompactSpace X] [SigmaCompactSpace Y] [T2Space Y]
    [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {f : X × Y → Z} (hf : Continuous f) :
    @Measurable (X × Y) Z Prod.instMeasurableSpace (TauCeti.baire Z) f := by
  rw [measurable_iff_le_map, baire_le_iff]
  intro g
  exact (g.continuous.comp hf).measurable_prod_of_sigmaCompact

/-- A compact set admits a compact Baire-measurable hull inside any open neighbourhood,
with null excess for any outer regular measure for which the compact set has finite measure.
No σ-finiteness or countability assumption on the space is needed. -/
theorem _root_.IsCompact.exists_baire_hull [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [μ.OuterRegular]
    {K U : Set X} (hK : IsCompact K) (hμK : μ K ≠ ⊤) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ B : Set X, K ⊆ B ∧ B ⊆ U ∧ IsCompact B ∧ MeasurableSet[baire X] B ∧
      μ (B \ K) = 0 := by
  -- Approximate from outside at errors tending to zero, then insert continuous cutoffs.
  have hopen (n : ℕ) := hK.measurableSet.exists_isOpen_sdiff_lt
    (μ := μ) hμK
    (ε := ENNReal.ofReal (1 / ((n : ℝ) + 1))) (by positivity)
  choose V hKV hV _ hVerr using hopen
  have hcut (n : ℕ) := exists_continuous_one_zero_of_isCompact hK
    ((hV n).inter hU).isClosed_compl
    (disjoint_compl_right_iff_subset.2 (subset_inter (hKV n) hKU))
  choose f hfK hfzero hfsupp _ using hcut
  let B : Set X := ⋂ n, (f n) ⁻¹' {1}
  have hKB : K ⊆ B := fun x hx => mem_iInter.2 fun n => hfK n hx
  have hBV (n : ℕ) : B ⊆ V n ∩ U := by
    intro x hx
    by_contra h
    have h1 : f n x = 1 := mem_iInter.1 hx n
    have h0 : f n x = 0 := hfzero n h
    exact zero_ne_one (h0.symm.trans h1)
  have hBclosed : IsClosed B := isClosed_iInter fun n =>
    isClosed_singleton.preimage (f n).continuous
  have hBcompact : IsCompact B := (hfsupp 0).of_isClosed_subset hBclosed fun x hx => by
    apply subset_tsupport (f 0)
    have hx1 : f 0 x = 1 := mem_iInter.1 hx 0
    simp [hx1]
  refine ⟨B, hKB, (hBV 0).trans inter_subset_right, hBcompact,
    MeasurableSet.iInter fun n => (f n).measurable_baire (measurableSet_singleton 1), ?_⟩
  have hbound (n : ℕ) : μ (B \ K) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (measure_mono (sdiff_subset_sdiff_left ((hBV n).trans inter_subset_left))).trans
      (hVerr n).le
  apply le_zero_iff.1
  simpa only [ENNReal.ofReal_zero] using ge_of_tendsto'
    (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat) hbound

/-- A σ-compact set has a σ-compact Baire-measurable hull with null excess, inside any
prescribed open neighbourhood. No σ-finiteness assumption on the measure is needed. -/
theorem _root_.IsSigmaCompact.exists_baire_hull [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    [μ.OuterRegular] [IsFiniteMeasureOnCompacts μ] {s U : Set X} (hs : IsSigmaCompact s)
    (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ B : Set X, s ⊆ B ∧ B ⊆ U ∧ IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire X] B ∧
      μ (B \ s) = 0 := by
  obtain ⟨K, hK, rfl⟩ := hs
  have hhull (n : ℕ) := (hK n).exists_baire_hull (μ := μ) (hK n).measure_ne_top hU
    ((subset_iUnion K n).trans hsU)
  choose B hKB hBU hBc hBm hBμ using hhull
  refine ⟨⋃ n, B n, iUnion_mono hKB, iUnion_subset hBU,
    isSigmaCompact_iUnion_of_isCompact B hBc, MeasurableSet.iUnion hBm, ?_⟩
  refine measure_mono_null ?_ (measure_iUnion_null hBμ)
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx.1
  exact mem_iUnion.2 ⟨n, hn, fun hxn => hx.2 (mem_iUnion.2 ⟨n, hxn⟩)⟩

end TauCeti
