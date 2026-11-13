/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.GDelta.Basic
public import TauCeti.MeasureTheory.Constructions.Baire.Regular
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Metrizable.ContinuousMap
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Measure.Typeclasses.SFinite
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.Group.SigmaCompact
import TauCeti.Topology.GDelta.Basic

/-!
# Completion regularity of Haar measure

On a locally compact Hausdorff group without second countability, the Baire σ-algebra
`TauCeti.baire G` can be strictly smaller than `borel G`, and `borel (G × G)` can be strictly larger
than `borel G × borel G`. While `MeasureTheory.NullMeasurableSet.exists_baire_ae_eq` gives a Baire
representative modulo a `μ`-null symmetric difference, that exceptional null set is a priori only
Borel, so it need not pull back to a measurable set in `borel X × borel Y` along continuous maps
`Φ : X × Y → G` out of σ-compact products (such as group multiplication in convolution).

This file proves that a regular Haar measure `μ` on a locally compact Hausdorff group `G` is
*completion regular*: every open set `U` with `[SigmaFinite (μ.restrict U)]` has an open Baire
superset almost everywhere equal to it, every `μ`-null set is contained in a `Gδ` Baire `μ`-null
set, every `μ`-null-measurable set `s` with `[SigmaFinite (μ.restrict s)]` differs from a σ-compact
Baire set by a subset of a `Gδ` Baire `μ`-null set, and on σ-compact groups every almost everywhere
strongly measurable function agrees outside a `Gδ` Baire `μ`-null set with a function strongly
measurable for `TauCeti.baire G`. Enclosing exceptional sets inside Baire `μ`-null sets lets
continuous maps into `G` pull both the representative and the null error back into the product
σ-algebra.

When `G` is σ-compact, an open Baire superset almost everywhere equal to an open set `U ⊆ G` is
constructed as follows:

1. Choose a Baire set `V =ᵐ[μ] U` (`MeasureTheory.NullMeasurableSet.exists_baire_ae_eq`), written as
   the preimage of a Borel subset of `ℕ → ℝ` under a sequence `f : ℕ → C(G, ℝ)`.
2. Let `N = ⨅ k, TauCeti.rightTranslationStabilizer (f k)`. Right translation descends to a
   continuous injection from `G ⧸ N` into the metrizable space `ℕ → C(G, ℝ)`.
3. The saturated open set `W = π ⁻¹' (π '' U)` (`π : G → G ⧸ N`) has σ-compact complement image in
   `ℕ → C(G, ℝ)`, so `W` is Baire measurable; inner regularity and right quasi-invariance of `μ`
   force `μ (W \ V) = 0` (`IsOpen.measure_mul_sdiff_eq_zero`), hence `W =ᵐ[μ] U`.

On an arbitrary (not necessarily σ-compact) locally compact Hausdorff group, every set `s` with
`[SigmaFinite (μ.restrict s)]`—in particular every finite-measure open set and every `μ`-null
set—lies in a single σ-compact open subgroup
(`MeasureTheory.exists_openSubgroup_isSigmaCompact_of_sigmaFinite_restrict`), transferring open
Baire hulls, Baire null envelopes, and Baire representatives without ambient σ-compactness.

## Main results

* `IsOpen.exists_isOpen_baire_superset_ae_eq`: on any locally compact Hausdorff group with a regular
  Haar measure `μ`, every open set `U` with `[SigmaFinite (μ.restrict U)]` has an open Baire
  superset almost everywhere equal to it.
* `MeasureTheory.exists_baire_superset_of_null`: on any locally compact Hausdorff group, every null
  set for a regular Haar measure `μ` is contained in a `Gδ` Baire `μ`-null set.
* `MeasureTheory.NullMeasurableSet.exists_baire_symmDiff_subset_null`,
  `MeasurableSet.exists_baire_symmDiff_subset_null`, and
  `MeasureTheory.NullMeasurableSet.exists_baire_symmDiff_subset_null_of_subset_isSigmaCompact`:
  on any locally compact Hausdorff group with a regular Haar measure `μ`, every `μ`-null-measurable
  (or Borel) set `s` with `[SigmaFinite (μ.restrict s)]`—in particular when `G` is σ-compact or `s`
  lies in a σ-compact set—differs from a σ-compact Baire set by a subset of a `Gδ` Baire `μ`-null
  set.
* `MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_baire`: on a σ-compact locally
  compact Hausdorff group with a regular Haar measure `μ`, every `μ`-almost everywhere strongly
  measurable function agrees outside a `Gδ` Baire `μ`-null set with a Baire strongly measurable
  function.

## References

* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443M.
* P. R. Halmos, *Measure Theory*, Van Nostrand (1950), §64.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise symmDiff

section SigmaCompactSaturation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Saturating an open set `U` along the joint right-translation stabilizer of a sequence
`f : ℕ → C(G, ℝ)` produces a Baire-measurable set, because the σ-compact quotient embeds
continuously and injectively into the metrizable space `ℕ → C(G, ℝ)`. -/
private theorem measurableSet_baire_saturation (f : ℕ → C(G, ℝ)) {U : Set G} (hU : IsOpen U) :
    let N : Subgroup G := ⨅ k, TauCeti.rightTranslationStabilizer (f k)
    let π : G → G ⧸ N := QuotientGroup.mk
    MeasurableSet[TauCeti.baire G] (π ⁻¹' (π '' U)) := by
  intro N π
  let Φ (k : ℕ) : C(G × G, ℝ) :=
    ⟨fun p => f k (p.2 * p.1), (f k).continuous.comp (continuous_snd.mul continuous_fst)⟩
  let Ψ : G → ℕ → C(G, ℝ) := fun g k => (Φ k).curry g
  have hΨ_cont : Continuous Ψ := continuous_pi fun k => (Φ k).curry.continuous
  have hΨ_eq (x y : G) : Ψ x = Ψ y ↔ π x = π y := by
    simp only [π, N, QuotientGroup.eq, Subgroup.mem_iInf, TauCeti.mem_rightTranslationStabilizer]
    refine ⟨fun hxy k z => ?_, fun hxy => ?_⟩
    · have hk := congrFun (congrArg (fun φ : ℕ → C(G, ℝ) => (φ k : G → ℝ)) hxy) (z * x⁻¹)
      simpa [Ψ, Φ, mul_assoc] using hk.symm
    · ext k z
      simpa [Ψ, Φ, mul_assoc] using (hxy k (z * x)).symm
  have hΨ_rel (x y : G) (hxy : (QuotientGroup.leftRel N) x y) : Ψ x = Ψ y :=
    (hΨ_eq x y).2 (Quotient.sound hxy)
  let Ψbar : G ⧸ N → ℕ → C(G, ℝ) := Quotient.lift Ψ hΨ_rel
  have hΨbar_cont : Continuous Ψbar := hΨ_cont.quotient_lift _
  have hΨbar_inj : Injective Ψbar := Quotient.ind₂ fun x y hxy => (hΨ_eq x y).1 hxy
  have hcomp : Ψ = Ψbar ∘ π :=
    funext fun x => (Quotient.lift_mk (s := QuotientGroup.leftRel N) Ψ hΨ_rel x).symm
  let F : Set (G ⧸ N) := (π '' U)ᶜ
  have hF_closed : IsClosed F := (QuotientGroup.isOpenMap_coe (N := N) U hU).isClosed_compl
  obtain ⟨K, hKc, hKF⟩ :=
    (isSigmaCompact_univ.of_isClosed_subset hF_closed (subset_univ F)).image hΨbar_cont
  let _ : MeasurableSpace (ℕ → C(G, ℝ)) := borel (ℕ → C(G, ℝ))
  have _ : BorelSpace (ℕ → C(G, ℝ)) := ⟨rfl⟩
  have hΨF_borel : MeasurableSet (Ψbar '' F) :=
    hKF ▸ MeasurableSet.iUnion fun m => (hKc m).isClosed.measurableSet
  have hΨF_baire : MeasurableSet[TauCeti.baire (ℕ → C(G, ℝ))] (Ψbar '' F) := by
    rwa [TauCeti.baire_eq_borel]
  have hWc : (π ⁻¹' (π '' U))ᶜ = Ψ ⁻¹' (Ψbar '' F) := by
    rw [hcomp, preimage_comp, preimage_image_eq _ hΨbar_inj, preimage_compl]
  let _ : MeasurableSpace G := TauCeti.baire G
  exact MeasurableSet.of_compl (hWc ▸ hΨ_cont.measurable_baire hΨF_baire)

private theorem exists_isOpen_baire_superset_ae_eq_of_sigmaCompact {U : Set G} (hU : IsOpen U)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ W : Set G, U ⊆ W ∧ IsOpen W ∧ MeasurableSet[TauCeti.baire G] W ∧ W =ᵐ[μ] U := by
  obtain ⟨V, -, hV_baire, hVU⟩ := hU.measurableSet.nullMeasurableSet.exists_baire_ae_eq (μ := μ)
  obtain ⟨f, t, -, hVt⟩ := TauCeti.measurableSet_baire_iff_exists_continuousMap.1 hV_baire
  let N : Subgroup G := ⨅ k, TauCeti.rightTranslationStabilizer (f k)
  let π : G → G ⧸ N := QuotientGroup.mk
  have hVN : V * (N : Set G) ⊆ V := by
    rintro _ ⟨x, hx, n, hn, rfl⟩
    simpa [hVt, fun k => TauCeti.mem_rightTranslationStabilizer.1 (Subgroup.mem_iInf.1 hn k) x]
      using hx
  have hW_open : IsOpen (π ⁻¹' (π '' U)) :=
    (QuotientGroup.isOpenMap_coe (N := N) U hU).preimage QuotientGroup.continuous_mk
  have hW_baire : MeasurableSet[TauCeti.baire G] (π ⁻¹' (π '' U)) :=
    measurableSet_baire_saturation f hU
  have hUW : U ⊆ π ⁻¹' (π '' U) := subset_preimage_image π U
  have hW_diff_V : μ (π ⁻¹' (π '' U) \ V) = 0 := by
    rw [QuotientGroup.preimage_image_mk_eq_mul]
    exact hU.measure_mul_sdiff_eq_zero (TauCeti.baire_le V hV_baire).nullMeasurableSet hVN
      (ae_eq_set.1 hVU).2
  exact ⟨π ⁻¹' (π '' U), hUW, hW_open, hW_baire,
    ((ae_subset.2 hW_diff_V).trans hVU.subset).antisymm (Eventually.of_forall fun _ h => hUW h)⟩

end SigmaCompactSaturation

section LocallyCompact

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

omit [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
private theorem measurableSet_baire_image_openSubgroup_coe (H : OpenSubgroup G) {s : Set H}
    (hs : MeasurableSet[TauCeti.baire H] s) :
    MeasurableSet[TauCeti.baire G] (((↑) : H → G) '' s) :=
  (@MeasurableEmbedding.measurableSet_image' H G (TauCeti.baire H) (TauCeti.baire G) _
    H.isClopen.measurableEmbedding_baire_subtype_coe) hs

/-- **Open Baire hull of an open set.** On any locally compact Hausdorff group with a regular Haar
measure `μ`, every open set `U` with `[SigmaFinite (μ.restrict U)]` is contained in an open
Baire-measurable set `W` with `W =ᵐ[μ] U`. -/
theorem _root_.IsOpen.exists_isOpen_baire_superset_ae_eq {U : Set G} (hU : IsOpen U)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite (μ.restrict U)] :
    ∃ W : Set G, U ⊆ W ∧ IsOpen W ∧ MeasurableSet[TauCeti.baire G] W ∧ W =ᵐ[μ] U := by
  obtain ⟨H, hUH, hH⟩ := exists_openSubgroup_isSigmaCompact_of_sigmaFinite_restrict μ U
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  have hcoe : MeasurableEmbedding ((↑) : H → G) :=
    MeasurableEmbedding.subtype_coe H.isOpen.measurableSet
  let ν : Measure H := μ.comap ((↑) : H → G)
  let U₀ : Set H := ((↑) : H → G) ⁻¹' U
  have hU_img : ((↑) : H → G) '' U₀ = U :=
    image_preimage_eq_iff.2 (hUH.trans Subtype.range_coe.symm.subset)
  obtain ⟨W₀, hUW₀, hW₀o, hW₀b, hW₀ae⟩ :=
    exists_isOpen_baire_superset_ae_eq_of_sigmaCompact (hU.preimage continuous_subtype_val) ν
  refine ⟨((↑) : H → G) '' W₀, hU_img ▸ image_mono hUW₀,
    H.isOpen.isOpenMap_subtype_val W₀ hW₀o,
    measurableSet_baire_image_openSubgroup_coe H hW₀b, ?_⟩
  rw [← measure_symmDiff_eq_zero_iff, ← hU_img, ← image_symmDiff Subtype.coe_injective,
    ← hcoe.comap_apply, measure_symmDiff_eq_zero_iff]
  exact hW₀ae

/-- **Haar completion regularity (null sets).** On any locally compact Hausdorff group with a
regular Haar measure `μ`, every `μ`-null set is contained in a `Gδ` Baire-measurable `μ`-null
set. -/
theorem exists_baire_superset_of_null {s : Set G} (hs : μ s = 0) :
    ∃ N : Set G, s ⊆ N ∧ IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 := by
  have hopen (k : ℕ) : ∃ U ⊇ s, IsOpen U ∧ μ U < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
    s.exists_isOpen_lt_of_lt _ (by simp [hs])
  choose U hsU hUo hUμ using hopen
  have _ (k : ℕ) : IsFiniteMeasure (μ.restrict (U k)) :=
    isFiniteMeasure_restrict.2 ((hUμ k).trans_le (by simp)).ne
  choose W hUW hWo hWb hWae using fun k => (hUo k).exists_isOpen_baire_superset_ae_eq μ
  refine ⟨⋂ k, W k, subset_iInter fun k => (hsU k).trans (hUW k), IsGδ.iInter_of_isOpen hWo,
    MeasurableSet.iInter hWb, ?_⟩
  have hbound (k : ℕ) : μ (⋂ n, W n) ≤ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
    (measure_mono (iInter_subset W k)).trans ((measure_congr (hWae k)).trans_le (hUμ k).le)
  exact nonpos_iff_eq_zero.1 <| ge_of_tendsto'
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) hbound

private theorem exists_baire_symmDiff_subset_null_of_sigmaCompact [SigmaCompactSpace G] {s : Set G}
    (hs : NullMeasurableSet s μ) :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ s ∆ B ⊆ N := by
  obtain ⟨B, hB_sc, hB_baire, hBs⟩ := hs.exists_baire_ae_eq
  obtain ⟨N, hNB, hNg, hNb, hN0⟩ :=
    exists_baire_superset_of_null (measure_symmDiff_eq_zero_iff.2 hBs.symm)
  exact ⟨B, N, hB_sc, hB_baire, hNg, hNb, hN0, hNB⟩

/-- **Haar completion regularity (null-measurable sets).** On any locally compact Hausdorff group
with a regular Haar measure `μ`, every `μ`-null-measurable set `s` with
`[SigmaFinite (μ.restrict s)]` differs from a σ-compact Baire set by a subset of a `Gδ` Baire
`μ`-null set. -/
theorem NullMeasurableSet.exists_baire_symmDiff_subset_null {s : Set G}
    (hs : NullMeasurableSet s μ) [SigmaFinite (μ.restrict s)] :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ s ∆ B ⊆ N := by
  obtain ⟨H, hsH, hH⟩ := exists_openSubgroup_isSigmaCompact_of_sigmaFinite_restrict μ s
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  have hcoe : MeasurableEmbedding ((↑) : H → G) :=
    MeasurableEmbedding.subtype_coe H.isOpen.measurableSet
  let ν : Measure H := μ.comap ((↑) : H → G)
  have hqmp : QuasiMeasurePreserving ((↑) : H → G) ν μ :=
    (measurePreserving_subtype_coe (μa := μ)
      H.isOpen.measurableSet).quasiMeasurePreserving.mono_right
      Measure.restrict_le_self.absolutelyContinuous
  let s₀ : Set H := ((↑) : H → G) ⁻¹' s
  have hs_img : ((↑) : H → G) '' s₀ = s :=
    image_preimage_eq_iff.2 (hsH.trans Subtype.range_coe.symm.subset)
  obtain ⟨B₀, N₀, hB₀sc, hB₀b, hN₀g, hN₀b, hN₀0, hsymm₀⟩ :=
    exists_baire_symmDiff_subset_null_of_sigmaCompact (hs.preimage hqmp)
  refine ⟨((↑) : H → G) '' B₀, ((↑) : H → G) '' N₀, hB₀sc.image continuous_subtype_val,
    measurableSet_baire_image_openSubgroup_coe H hB₀b,
    H.isOpen.isOpenEmbedding_subtypeVal.isGδ_image hN₀g,
    measurableSet_baire_image_openSubgroup_coe H hN₀b,
    by rw [← hcoe.comap_apply, hN₀0], ?_⟩
  rw [← hs_img, ← image_symmDiff Subtype.coe_injective]
  exact image_mono hsymm₀

/-- **Haar completion regularity (Borel sets).** On any locally compact Hausdorff group with a
regular Haar measure `μ`, every measurable set `s` with `[SigmaFinite (μ.restrict s)]` differs from
a σ-compact Baire set by a subset of a `Gδ` Baire `μ`-null set. -/
theorem _root_.MeasurableSet.exists_baire_symmDiff_subset_null {s : Set G} (hs : MeasurableSet s)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite (μ.restrict s)] :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ s ∆ B ⊆ N :=
  hs.nullMeasurableSet.exists_baire_symmDiff_subset_null

/-- On an arbitrary locally compact Hausdorff group with a regular Haar measure `μ`, any
`μ`-null-measurable subset of a σ-compact set differs from a σ-compact Baire set by a subset of a
`Gδ` Baire `μ`-null set. -/
theorem NullMeasurableSet.exists_baire_symmDiff_subset_null_of_subset_isSigmaCompact {s t : Set G}
    (hs : NullMeasurableSet s μ) (ht : IsSigmaCompact t) (hst : s ⊆ t) :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ s ∆ B ⊆ N := by
  have _ : SigmaFinite (μ.restrict t) := ht.sigmaFinite_restrict
  have _ : SigmaFinite (μ.restrict s) :=
    Measure.sigmaFinite_of_le (μ.restrict t) (Measure.restrict_mono hst le_rfl)
  exact hs.exists_baire_symmDiff_subset_null

end MeasureTheory

end LocallyCompact

section SigmaCompactFunctions

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

/-- **Baire representatives of almost everywhere strongly measurable functions.** On a σ-compact
locally compact Hausdorff group with a regular Haar measure `μ`, every `μ`-almost everywhere
strongly measurable function `f : G → β` agrees outside a `Gδ` Baire `μ`-null set `N` with a
function `g : G → β` that is strongly measurable for `TauCeti.baire G`. -/
theorem AEStronglyMeasurable.exists_stronglyMeasurable_baire {β : Type*} [TopologicalSpace β]
    {f : G → β} (hf : AEStronglyMeasurable f μ) :
    ∃ (g : G → β) (N : Set G), StronglyMeasurable[TauCeti.baire G] g ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ {x : G | f x ≠ g x} ⊆ N := by
  classical
  let b₀ : β := f 1
  obtain ⟨fs, hfs⟩ := hf.stronglyMeasurable_mk
  choose hs hhs using fun n => (fs n).exists_baire_ae_eq μ
  let S : Set G := {x | f x ≠ hf.mk f x} ∪ ⋃ n, {x | hs n x ≠ fs n x}
  have hS_null : μ S = 0 :=
    measure_union_null hf.ae_eq_mk (measure_iUnion_null hhs)
  obtain ⟨N, hSN, hNg, hNb, hN0⟩ := exists_baire_superset_of_null hS_null
  let gs : ℕ → @SimpleFunc G (TauCeti.baire G) β := fun n =>
    @SimpleFunc.piecewise G β (TauCeti.baire G) N hNb
      (@SimpleFunc.const G β (TauCeti.baire G) b₀) (hs n)
  let g : G → β := fun x => if x ∈ N then b₀ else f x
  have hg_sm : StronglyMeasurable[TauCeti.baire G] g := by
    let _ : MeasurableSpace G := TauCeti.baire G
    have hgs_eq (n : ℕ) (x : G) : gs n x = if x ∈ N then b₀ else hs n x := by
      dsimp only [gs]
      rw [SimpleFunc.piecewise_apply, SimpleFunc.const_apply]
    refine ⟨gs, fun x => ?_⟩
    by_cases hxN : x ∈ N
    · simpa [g, hxN, hgs_eq] using tendsto_const_nhds
    · have hxS : x ∉ S := fun hm => hxN (hSN hm)
      have hfx : f x = hf.mk f x := not_not.1 fun hne => hxS (Or.inl hne)
      have hhs_eq (n : ℕ) : hs n x = fs n x :=
        not_not.1 fun hne => hxS (Or.inr (mem_iUnion.2 ⟨n, hne⟩))
      simpa [g, hxN, hfx, hgs_eq, hhs_eq] using hfs x
  refine ⟨g, N, hg_sm, hNg, hNb, hN0, fun x hx => ?_⟩
  by_contra hxN
  exact hx (by simp [g, hxN])

end MeasureTheory

end SigmaCompactFunctions
