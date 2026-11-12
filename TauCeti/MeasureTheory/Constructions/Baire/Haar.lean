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
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Metrizable.ContinuousMap
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.Topology.Algebra.Group.OpenSubgroup.SigmaCompact

/-!
# Completion regularity of Haar measure

On a locally compact Hausdorff group without second countability, the Baire σ-algebra
`TauCeti.baire G` can be strictly smaller than `borel G`. Nevertheless, a regular Haar measure `μ`
on a σ-compact locally compact Hausdorff group `G` is *completion regular*: every `μ`-null set is
contained in a `Gδ` Baire `μ`-null set, every null-measurable (in particular Borel) set differs
from a σ-compact Baire set by a subset of a `Gδ` Baire `μ`-null set, and every almost everywhere
strongly measurable function agrees outside a `Gδ` Baire `μ`-null set with a function strongly
measurable for `TauCeti.baire G`.

The core step (`IsOpen.exists_baire_superset_ae_eq`) constructs an open Baire hull with null excess
for an arbitrary open set `U ⊆ G`:

1. Choose a Baire set `V =ᵐ[μ] U` (`MeasureTheory.NullMeasurableSet.exists_baire_ae_eq`), written as
   the preimage of a Borel subset of `ℕ → ℝ` under a sequence `f : ℕ → C(G, ℝ)`.
2. Let `N ≤ G` be the joint right-translation stabilizer `{n : G | ∀ k z, f k (z * n) = f k z}`.
   Right translation `g ↦ (k ↦ (z ↦ f k (z * g)))` descends to a continuous injection from `G ⧸ N`
   into the metrizable space `ℕ → C(G, ℝ)`.
3. The saturated open set `W = π ⁻¹' (π '' U)` (`π : G → G ⧸ N`) has `σ`-compact complement image
   in `ℕ → C(G, ℝ)`, so `W` is Baire measurable; inner regularity and right quasi-invariance of `μ`
   force `μ (W \ V) = 0`, hence `μ (W \ U) = 0`.

On an arbitrary (not necessarily σ-compact) locally compact Hausdorff group, passing to a σ-compact
open subgroup yields the same `Gδ` Baire null envelopes and Baire representatives for any subset of
a σ-compact set.

## Main results

* `IsOpen.exists_baire_superset_ae_eq`: every open set in a σ-compact locally compact Hausdorff
  group has an open Baire superset with null excess for a regular Haar measure.
* `MeasureTheory.exists_baire_superset_of_null`: every Haar-null set in a σ-compact locally compact
  Hausdorff group is contained in a `Gδ` Baire Haar-null set.
* `MeasureTheory.NullMeasurableSet.exists_baire_symmDiff_subset_null` and
  `MeasurableSet.exists_baire_symmDiff_subset_null`: every null-measurable or Borel set differs from
  a σ-compact Baire set by a subset of a `Gδ` Baire Haar-null set.
* `MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_baire`: every almost everywhere
  strongly measurable function agrees outside a `Gδ` Baire Haar-null set with a Baire strongly
  measurable function.
* `MeasureTheory.exists_baire_superset_of_null_of_subset_isSigmaCompact` and
  `MeasureTheory.NullMeasurableSet.exists_baire_symmDiff_subset_null_of_subset_isSigmaCompact`:
  counterparts on non-σ-compact locally compact Hausdorff groups for subsets of σ-compact sets.

## References

* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443M.
* P. R. Halmos, *Measure Theory*, Van Nostrand (1950), §64.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

section SigmaCompact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Open Baire hull of an open set.** On a σ-compact locally compact Hausdorff group with a
regular Haar measure `μ`, every open set `U` is contained in an open Baire-measurable set `W` with
`μ (W \ U) = 0`. -/
theorem _root_.IsOpen.exists_baire_superset_ae_eq {U : Set G} (hU : IsOpen U)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ W : Set G, U ⊆ W ∧ IsOpen W ∧ MeasurableSet[TauCeti.baire G] W ∧ μ (W \ U) = 0 := by
  obtain ⟨V, -, hV_baire, hVU⟩ := hU.measurableSet.nullMeasurableSet.exists_baire_ae_eq (μ := μ)
  obtain ⟨hV_diff_U, hU_diff_V⟩ := ae_eq_set.1 hVU
  obtain ⟨f, t, -, hVt⟩ := TauCeti.measurableSet_baire_iff_exists_continuousMap.1 hV_baire
  -- Right-translation stabilizer of the sequence `f : ℕ → C(G, ℝ)` defining `V`.
  let N : Subgroup G :=
    { carrier := {n : G | ∀ k z, f k (z * n) = f k z}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb k z => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha k z => by simpa using (ha k (z * a⁻¹)).symm }
  have hVN {x n : G} (hn : n ∈ N) : x * n ∈ V ↔ x ∈ V := by
    simp [hVt, fun k => hn k x]
  -- Embed `G ⧸ N` continuously and injectively into the metrizable space `ℕ → C(G, ℝ)`.
  let Φ (k : ℕ) : C(G × G, ℝ) :=
    ⟨fun p => f k (p.2 * p.1), (f k).continuous.comp (continuous_snd.mul continuous_fst)⟩
  let Ψ : G → ℕ → C(G, ℝ) := fun g k => (Φ k).curry g
  have hΨ_cont : Continuous Ψ := continuous_pi fun k => (Φ k).curry.continuous
  have hΨ_eq (x y : G) : Ψ x = Ψ y ↔ (QuotientGroup.mk x : G ⧸ N) = QuotientGroup.mk y := by
    rw [QuotientGroup.eq]
    constructor
    · intro hxy k z
      have hk := congrFun (congrArg (fun φ : ℕ → C(G, ℝ) => (φ k : G → ℝ)) hxy) (z * x⁻¹)
      simpa [Ψ, Φ, mul_assoc] using hk.symm
    · intro hxy
      ext k z
      simpa [Ψ, Φ, mul_assoc] using (hxy k (z * x)).symm
  let π : G → G ⧸ N := QuotientGroup.mk
  let Ψbar : G ⧸ N → ℕ → C(G, ℝ) :=
    Quotient.lift Ψ fun x y hxy => (hΨ_eq x y).2 (Quotient.sound hxy)
  have hΨbar_cont : Continuous Ψbar := hΨ_cont.quotient_lift _
  have hΨbar_inj : Injective Ψbar := by
    refine Quotient.ind₂ fun x y hxy => ?_
    exact (hΨ_eq x y).1 hxy
  -- Saturate `U` along the cosets of `N`.
  let W : Set G := π ⁻¹' (π '' U)
  have hUW : U ⊆ W := subset_preimage_image π U
  have hW_open : IsOpen W :=
    (QuotientGroup.isOpenMap_coe (N := N) U hU).preimage QuotientGroup.continuous_mk
  -- `Wᶜ` pulls back from a σ-compact (hence Borel = Baire) subset of `ℕ → C(G, ℝ)` along `Ψ`.
  have hW_baire : MeasurableSet[TauCeti.baire G] W := by
    let F : Set (G ⧸ N) := (π '' U)ᶜ
    have hF_closed : IsClosed F := (QuotientGroup.isOpenMap_coe (N := N) U hU).isClosed_compl
    have hF_union : F = ⋃ m : ℕ, F ∩ π '' compactCovering G m := by
      have hsurj : Surjective π := Quotient.mk''_surjective
      rw [← inter_iUnion, ← image_iUnion, iUnion_compactCovering, image_univ,
        range_eq_univ.2 hsurj, inter_univ]
    let _ : MeasurableSpace (ℕ → C(G, ℝ)) := borel (ℕ → C(G, ℝ))
    have _ : BorelSpace (ℕ → C(G, ℝ)) := ⟨rfl⟩
    have hΨF_borel : MeasurableSet (Ψbar '' F) := by
      rw [hF_union, image_iUnion]
      refine MeasurableSet.iUnion fun m => ?_
      have hKm : IsCompact (F ∩ π '' compactCovering G m) :=
        ((isCompact_compactCovering G m).image QuotientGroup.continuous_mk).inter_left hF_closed
      exact (hKm.image hΨbar_cont).isClosed.measurableSet
    have hΨF_baire : MeasurableSet[TauCeti.baire (ℕ → C(G, ℝ))] (Ψbar '' F) := by
      rwa [TauCeti.baire_eq_borel]
    have hWc : Wᶜ = Ψ ⁻¹' (Ψbar '' F) := by
      have hcomp : Ψ = Ψbar ∘ π := rfl
      rw [hcomp, preimage_comp, preimage_image_eq _ hΨbar_inj]
      rfl
    let _ : MeasurableSpace G := TauCeti.baire G
    exact MeasurableSet.of_compl (hWc ▸ hΨ_cont.measurable_baire hΨF_baire)
  -- Any compact subset of `W \ V` is covered by finitely many right translates of `U \ V`, hence
  -- has measure zero; inner regularity forces `μ (W \ V) = 0`.
  have hW_union : W = ⋃ n : N, (· * (n : G)⁻¹) ⁻¹' U := by
    ext x
    simp only [W, π, mem_preimage, mem_image, QuotientGroup.eq, mem_iUnion, Subtype.exists]
    constructor
    · rintro ⟨u, hu, hux⟩
      exact ⟨u⁻¹ * x, hux, by simpa [mul_assoc] using hu⟩
    · rintro ⟨n, hn, hxn⟩
      exact ⟨x * n⁻¹, hxn, by simp [mul_assoc, hn]⟩
  have hW_diff_V : μ (W \ V) = 0 := by
    by_contra hne
    have hWV_meas : MeasurableSet (W \ V) :=
      hW_open.measurableSet.diff (TauCeti.baire_le V hV_baire)
    obtain ⟨K, hKWV, hK, hKpos⟩ := hWV_meas.exists_lt_isCompact (pos_iff_ne_zero.2 hne)
    have hKcov : K ⊆ ⋃ n : N, (· * (n : G)⁻¹) ⁻¹' U :=
      hKWV.trans (sdiff_subset.trans hW_union.subset)
    obtain ⟨s, hsK⟩ := hK.elim_finite_subcover (fun n : N => (· * (n : G)⁻¹) ⁻¹' U)
      (fun n => hU.preimage (continuous_mul_const _)) hKcov
    have hKsub : K ⊆ ⋃ n : s, (· * ((n : N) : G)⁻¹) ⁻¹' (U \ V) := by
      intro x hx
      have hxV : x ∉ V := (hKWV hx).2
      obtain ⟨n, hn, hxnU⟩ := mem_iUnion₂.1 (hsK hx)
      refine mem_iUnion.2 ⟨⟨n, hn⟩, hxnU, fun hxnV => hxV ?_⟩
      have hx_eq : (x * (n : G)⁻¹) * (n : G) = x := by simp [mul_assoc]
      exact hx_eq ▸ (hVN n.2).2 hxnV
    have hKzero : μ K = 0 :=
      measure_mono_null hKsub (measure_iUnion_null fun n : s =>
        (Measure.measure_mul_right_null_of_regular μ ((n : N) : G)⁻¹).2 hU_diff_V)
    exact hKpos.ne' hKzero
  refine ⟨W, hUW, hW_open, hW_baire, ?_⟩
  refine measure_mono_null (t := W \ V ∪ V \ U) (fun x hx => ?_)
    (measure_union_null hW_diff_V hV_diff_U)
  by_cases hxV : x ∈ V
  · exact Or.inr ⟨hxV, hx.2⟩
  · exact Or.inl ⟨hx.1, hxV⟩

namespace MeasureTheory

variable {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

/-- **Haar completion regularity (null sets).** On a σ-compact locally compact Hausdorff group with
a regular Haar measure `μ`, every `μ`-null set is contained in a `Gδ` Baire-measurable `μ`-null
set. -/
theorem exists_baire_superset_of_null {s : Set G} (hs : μ s = 0) :
    ∃ N : Set G, s ⊆ N ∧ IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 := by
  have hopen (k : ℕ) : ∃ U ⊇ s, IsOpen U ∧ μ U < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
    s.exists_isOpen_lt_of_lt _ (by simp [hs])
  choose U hsU hUo hUμ using hopen
  have hbaire (k : ℕ) := (hUo k).exists_baire_superset_ae_eq μ
  choose W hUW hWo hWb hWdiff using hbaire
  refine ⟨⋂ k, W k, subset_iInter fun k => (hsU k).trans (hUW k), IsGδ.iInter_of_isOpen hWo,
    MeasurableSet.iInter hWb, ?_⟩
  have hbound (k : ℕ) : μ (⋂ n, W n) ≤ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    calc μ (⋂ n, W n) ≤ μ (W k) := measure_mono (iInter_subset W k)
      _ ≤ μ (U k ∪ W k \ U k) :=
          measure_mono (subset_union_right.trans union_sdiff_self.symm.subset)
      _ ≤ μ (U k) + μ (W k \ U k) := measure_union_le _ _
      _ = μ (U k) := by rw [hWdiff k, add_zero]
      _ ≤ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := (hUμ k).le
  exact nonpos_iff_eq_zero.1 <| ge_of_tendsto'
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) hbound

/-- **Haar completion regularity (null-measurable sets).** On a σ-compact locally compact Hausdorff
group with a regular Haar measure `μ`, every `μ`-null-measurable set differs from a σ-compact Baire
set by a subset of a `Gδ` Baire `μ`-null set. -/
theorem NullMeasurableSet.exists_baire_symmDiff_subset_null {s : Set G}
    (hs : NullMeasurableSet s μ) :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ symmDiff s B ⊆ N := by
  obtain ⟨B, hB_sc, hB_baire, hBs⟩ := hs.exists_baire_ae_eq
  obtain ⟨hsB, hBs'⟩ := ae_eq_set.1 hBs.symm
  have hsymm : μ (symmDiff s B) = 0 := by
    rw [symmDiff_def]
    exact measure_union_null hsB hBs'
  obtain ⟨N, hNB, hNg, hNb, hN0⟩ := exists_baire_superset_of_null hsymm
  exact ⟨B, N, hB_sc, hB_baire, hNg, hNb, hN0, hNB⟩

/-- **Haar completion regularity (Borel sets).** Every measurable set on a σ-compact locally compact
Hausdorff group differs from a σ-compact Baire set by a subset of a `Gδ` Baire Haar-null set. -/
theorem _root_.MeasurableSet.exists_baire_symmDiff_subset_null {s : Set G} (hs : MeasurableSet s)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ symmDiff s B ⊆ N :=
  hs.nullMeasurableSet.exists_baire_symmDiff_subset_null

/-- Replace a Borel simple function on `G` almost everywhere by a simple function measurable for
`TauCeti.baire G`. -/
private theorem exists_simpleFunc_baire_ae_eq {β : Type*} (s : SimpleFunc G β) (b₀ : β) :
    ∃ s' : @SimpleFunc G (TauCeti.baire G) β, (s' : G → β) =ᵐ[μ] s := by
  classical
  have hfib (y : β) := (s.measurableSet_fiber y).nullMeasurableSet.exists_baire_ae_eq (μ := μ)
  choose B _ hBb hBae using hfib
  let build : List β → @SimpleFunc G (TauCeti.baire G) β := fun L =>
    let _ : MeasurableSpace G := TauCeti.baire G
    L.foldr (fun y acc => @SimpleFunc.piecewise G β (TauCeti.baire G) (B y) (hBb y)
      (@SimpleFunc.const G β (TauCeti.baire G) y) acc)
      (@SimpleFunc.const G β (TauCeti.baire G) b₀)
  have hbuild_eq : ∀ (L : List β) (x : G),
      (∀ y ∈ L, x ∈ B y ↔ s x = y) → s x ∈ L → build L x = s x := by
    let _ : MeasurableSpace G := TauCeti.baire G
    intro L
    induction L with
    | nil => simp
    | cons y L ih =>
      intro x hxB hxL
      change @SimpleFunc.piecewise G β (TauCeti.baire G) (B y) (hBb y)
        (@SimpleFunc.const G β (TauCeti.baire G) y) (build L) x = s x
      rw [SimpleFunc.piecewise_apply]
      by_cases hxy : s x = y
      · have hxBy : x ∈ B y := (hxB y List.mem_cons_self).2 hxy
        simp [hxBy, hxy]
      · have hxBy : x ∉ B y := fun hm => hxy ((hxB y List.mem_cons_self).1 hm)
        have hxL' : s x ∈ L := (List.mem_cons.1 hxL).resolve_left hxy
        simp only [hxBy, ↓reduceIte]
        exact ih x (fun z hz => hxB z (List.mem_cons_of_mem y hz)) hxL'
  refine ⟨build s.range.toList, ?_⟩
  have hae : ∀ᵐ x ∂μ, ∀ y ∈ (s.range : Set β), x ∈ B y ↔ s x = y := by
    refine (eventually_all_finite s.range.finite_toSet).2 fun y _ => ?_
    filter_upwards [hBae y] with x hx
    simpa [eq_comm] using hx
  filter_upwards [hae] with x hx
  exact hbuild_eq s.range.toList x (fun y hy => hx y (Finset.mem_coe.2 (Finset.mem_toList.1 hy)))
    (Finset.mem_toList.2 (s.mem_range_self x))

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
  choose hs hhs using fun n => exists_simpleFunc_baire_ae_eq (μ := μ) (fs n) b₀
  let S : Set G := {x | f x ≠ hf.mk f x} ∪ ⋃ n, {x | hs n x ≠ fs n x}
  have hS_null : μ S = 0 :=
    measure_union_null hf.ae_eq_mk (measure_iUnion_null hhs)
  obtain ⟨N, hSN, hNg, hNb, hN0⟩ := exists_baire_superset_of_null hS_null
  let gs : ℕ → @SimpleFunc G (TauCeti.baire G) β := fun n =>
    let _ : MeasurableSpace G := TauCeti.baire G
    @SimpleFunc.piecewise G β (TauCeti.baire G) N hNb
      (@SimpleFunc.const G β (TauCeti.baire G) b₀) (hs n)
  let g : G → β := fun x => if x ∈ N then b₀ else f x
  have hg_sm : StronglyMeasurable[TauCeti.baire G] g := by
    let _ : MeasurableSpace G := TauCeti.baire G
    refine ⟨gs, fun x => ?_⟩
    by_cases hxN : x ∈ N
    · have hgs_eq (n : ℕ) : gs n x = b₀ := by
        change @SimpleFunc.piecewise G β (TauCeti.baire G) N hNb _ (hs n) x = b₀
        simp [SimpleFunc.piecewise_apply, hxN]
      simpa [g, hxN, hgs_eq] using tendsto_const_nhds
    · have hxS : x ∉ S := fun hm => hxN (hSN hm)
      have hfx : f x = hf.mk f x := not_not.1 fun hne => hxS (Or.inl hne)
      have hhs_eq (n : ℕ) : hs n x = fs n x :=
        not_not.1 fun hne => hxS (Or.inr (mem_iUnion.2 ⟨n, hne⟩))
      have hgs_eq (n : ℕ) : gs n x = fs n x := by
        change @SimpleFunc.piecewise G β (TauCeti.baire G) N hNb _ (hs n) x = fs n x
        simp [SimpleFunc.piecewise_apply, hxN, hhs_eq n]
      simpa [g, hxN, hfx, hgs_eq] using hfs x
  refine ⟨g, N, hg_sm, hNg, hNb, hN0, fun x hx => ?_⟩
  by_contra hxN
  exact hx (by simp [g, hxN])

end MeasureTheory

end SigmaCompact

section LocallyCompact

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] in
private theorem isGδ_image_openSubgroup_coe (H : OpenSubgroup G) {s : Set H} (hs : IsGδ s) :
    IsGδ (((↑) : H → G) '' s) := by
  obtain ⟨U, hUo, rfl⟩ := hs.eq_iInter_nat
  rw [Subtype.coe_injective.injOn.image_iInter_eq]
  exact IsGδ.iInter_of_isOpen fun n => H.isOpen.isOpenMap_subtype_val _ (hUo n)

/-- On an arbitrary locally compact Hausdorff group with a regular Haar measure `μ`, any `μ`-null
set contained in a σ-compact set is contained in a `Gδ` Baire-measurable `μ`-null set. -/
theorem exists_baire_superset_of_null_of_subset_isSigmaCompact {s t : Set G}
    (ht : IsSigmaCompact t) (hst : s ⊆ t) (hs : μ s = 0) :
    ∃ N : Set G, s ⊆ N ∧ IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 := by
  obtain ⟨H, htH, hH⟩ := ht.exists_openSubgroup
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  have hcoe : MeasurableEmbedding ((↑) : H → G) :=
    MeasurableEmbedding.subtype_coe H.isOpen.measurableSet
  let ν : Measure H := μ.comap ((↑) : H → G)
  let s₀ : Set H := ((↑) : H → G) ⁻¹' s
  have hs_img : ((↑) : H → G) '' s₀ = s :=
    image_preimage_eq_iff.2 ((hst.trans htH).trans Subtype.range_coe.symm.subset)
  have hs₀ : ν s₀ = 0 := by rw [hcoe.comap_apply, hs_img, hs]
  obtain ⟨N₀, hsN₀, hN₀g, hN₀b, hN₀0⟩ := exists_baire_superset_of_null hs₀
  refine ⟨((↑) : H → G) '' N₀, hs_img ▸ image_mono hsN₀, isGδ_image_openSubgroup_coe H hN₀g,
    (@MeasurableEmbedding.measurableSet_image' H G (TauCeti.baire H) (TauCeti.baire G) _
      H.isClopen.measurableEmbedding_baire_subtype_coe) hN₀b,
    by rw [← hcoe.comap_apply, hN₀0]⟩

/-- On an arbitrary locally compact Hausdorff group with a regular Haar measure `μ`, any
`μ`-null-measurable subset of a σ-compact set differs from a σ-compact Baire set by a subset of a
`Gδ` Baire `μ`-null set. -/
theorem NullMeasurableSet.exists_baire_symmDiff_subset_null_of_subset_isSigmaCompact {s t : Set G}
    (hs : NullMeasurableSet s μ) (ht : IsSigmaCompact t) (hst : s ⊆ t) :
    ∃ B N : Set G, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire G] B ∧
      IsGδ N ∧ MeasurableSet[TauCeti.baire G] N ∧ μ N = 0 ∧ symmDiff s B ⊆ N := by
  obtain ⟨H, htH, hH⟩ := ht.exists_openSubgroup
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
    image_preimage_eq_iff.2 ((hst.trans htH).trans Subtype.range_coe.symm.subset)
  obtain ⟨B₀, N₀, hB₀sc, hB₀b, hN₀g, hN₀b, hN₀0, hsymm₀⟩ :=
    (hs.preimage hqmp).exists_baire_symmDiff_subset_null
  refine ⟨((↑) : H → G) '' B₀, ((↑) : H → G) '' N₀, hB₀sc.image continuous_subtype_val,
    (@MeasurableEmbedding.measurableSet_image' H G (TauCeti.baire H) (TauCeti.baire G) _
      H.isClopen.measurableEmbedding_baire_subtype_coe) hB₀b,
    isGδ_image_openSubgroup_coe H hN₀g,
    (@MeasurableEmbedding.measurableSet_image' H G (TauCeti.baire H) (TauCeti.baire G) _
      H.isClopen.measurableEmbedding_baire_subtype_coe) hN₀b,
    by rw [← hcoe.comap_apply, hN₀0], ?_⟩
  have himg : ((↑) : H → G) '' symmDiff s₀ B₀ = symmDiff s (((↑) : H → G) '' B₀) := by
    rw [symmDiff_def, symmDiff_def, image_union, image_sdiff Subtype.coe_injective,
      image_sdiff Subtype.coe_injective, hs_img]
  exact himg ▸ image_mono hsymm₀

end MeasureTheory

end LocallyCompact
