/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.MeasureTheory.Constructions.Baire.Basic
public import TauCeti.Topology.Algebra.Group.KakutaniKodaira
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UrysohnsLemma
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.Topology.Algebra.Group.Quotient.Basic

/-!
# Haar completion regularity and quotient Borel sandwiching on σ-compact groups

Let `G` be a σ-compact locally compact topological group equipped with its Borel σ-algebra, and
let `μ` be a locally finite left-invariant Borel measure on `G` that is inner regular on sets of
finite measure with respect to compact sets (in particular, any regular left Haar measure on `G`).
Even when `G` is neither metrizable nor second countable, its measure theory reduces up to
`μ`-null sets to second-countable metrizable quotients `G ⧸ K` by closed compact normal subgroups
`K`:

1. **Quotient Borel sandwiching**: every countable family of `μ`-null-measurable sets `E i ⊆ G` is
   simultaneously sandwiched as `π ⁻¹' (A' i) ⊆ E i ⊆ π ⁻¹' (B' i)` for a single closed compact
   normal subgroup `K` with metrizable second-countable quotient `G ⧸ K` and sets `A' i ⊆ B' i` in
   `borel (G ⧸ K)` satisfying `μ (π ⁻¹' (B' i \ A' i)) = 0`.
2. **Haar completion regularity** (Fremlin §443M): because `borel (G ⧸ K)` pulls back into the
   Baire σ-algebra `TauCeti.baire G` (`Continuous.comap_borel_le_baire`), every Borel (or
   `μ`-null-measurable) set `E ⊆ G` is sandwiched between two Baire sets whose difference has
   `μ`-measure zero, and therefore differs from a Baire set by a subset of a Baire `μ`-null set.
   Unlike `MeasureTheory.NullMeasurableSet.exists_baire_ae_eq`, this supplies a Baire-measurable
   null envelope for the error and requires neither `[T2Space G]` nor `[μ.OuterRegular]`.
3. **Quotient factorization of `AEStronglyMeasurable` functions**: every `μ`-almost everywhere
   strongly measurable function `f : G → β` into a metrizable space agrees outside `π ⁻¹' Z'`
   (`Z' ∈ borel (G ⧸ K)`, `μ (π ⁻¹' Z') = 0`) with `g ∘ π` for a `borel (G ⧸ K)`-strongly
   measurable map `g : G ⧸ K → β`, and is consequently `AEStronglyMeasurable` with respect to
   `TauCeti.baire G`.

The key step is a right-`K` saturation lemma for open sets: if `U ⊆ G` is open and `A' ⊆ G ⧸ K` is
a Borel set with `π ⁻¹' A' ⊆ U` and `μ (U \ π ⁻¹' A') = 0`, then for every `k ∈ K` the right
translate `((· * k⁻¹) ⁻¹' U) ∩ π ⁻¹' ((π '' U) \ A')` is contained in `(· * k⁻¹) ⁻¹' (U \ π ⁻¹' A')`
and hence has `μ`-measure zero by right quasi-invariance of `μ`. Compact subsets of
`π ⁻¹' ((π '' U) \ A')` are covered by finitely many such translates and therefore have measure
zero; inner regularity and σ-finiteness then yield `μ (π ⁻¹' ((π '' U) \ A')) = 0`.

## Main results

* `TauCeti.exists_compact_normal_subgroup_forall_quotient_borel_sandwich`: simultaneous quotient
  Borel sandwiching of a countable family of `NullMeasurableSet`s.
* `MeasureTheory.NullMeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich` and
  `MeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich`: single-set quotient Borel
  sandwiching.
* `MeasureTheory.NullMeasurableSet.exists_baire_sandwich` and
  `MeasurableSet.exists_baire_sandwich`: Haar completion regularity in sandwich form.
* `MeasureTheory.NullMeasurableSet.exists_baire_symmDiff_subset_null_of_innerRegular` and
  `MeasurableSet.exists_baire_symmDiff_subset_null_of_innerRegular`: Haar completion regularity in
  symmetric-difference form (Fremlin §443M).
* `MeasureTheory.AEStronglyMeasurable.exists_compact_normal_subgroup_quotient_eq_off_null`:
  factorization of `AEStronglyMeasurable` functions outside a pullback Haar-null set through a
  metrizable second-countable quotient `G ⧸ K`.
* `MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_baire`: every
  `AEStronglyMeasurable` function into a metrizable space is a.e. strongly measurable with respect
  to `TauCeti.baire G`.

## References

* P. R. Halmos, *Measure Theory*, Van Nostrand (1950), §64.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979),
  §19.29–19.30.
* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443M.
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal MeasureTheory NNReal symmDiff Topology

namespace TauCeti

section BorelHelpers

/-- Construct a simple function on an abstract measurable space `Q` from a finite list of values
`l : List β` and corresponding measurable sets `A : β → Set Q`. -/
private noncomputable def liftSimpleList {Q β : Type*} [MeasurableSpace Q] (A : β → Set Q)
    (hA : ∀ b, MeasurableSet (A b)) (b₀ : β) : List β → SimpleFunc Q β
  | [] => SimpleFunc.const Q b₀
  | b :: bs => SimpleFunc.piecewise (A b) (hA b) (SimpleFunc.const Q b) (liftSimpleList A hA b₀ bs)

private theorem liftSimpleList_apply_of_unique {Q β : Type*} [MeasurableSpace Q]
    {A : β → Set Q} (hA : ∀ b, MeasurableSet (A b)) (b₀ : β) {l : List β} {q : Q} {v : β}
    (hv : v ∈ l) (hqv : q ∈ A v) (huniq : ∀ b ∈ l, q ∈ A b → b = v) :
    liftSimpleList A hA b₀ l q = v := by
  induction l with
  | nil => cases hv
  | cons b bs ih =>
    classical
    simp only [liftSimpleList, SimpleFunc.piecewise_apply, SimpleFunc.const_apply]
    split_ifs with hqb
    · exact huniq b List.mem_cons_self hqb
    · have hvb : v ≠ b := fun h ↦ hqb (h ▸ hqv)
      exact ih (List.mem_of_ne_of_mem hvb hv) fun c hc hqc ↦
        huniq c (List.mem_cons_of_mem b hc) hqc

/-- Given a sequence of sets `A : ℕ → β → Set Q` on an abstract measurable space `(Q, mQ)` and a
bad set `Z' : Set Q`, assemble the pointwise limit of lifted simple functions when the lifted
sequence converges outside `Z'`. -/
private theorem exists_stronglyMeasurable_of_quotient_fibers {Q G β : Type*}
    [mQ : MeasurableSpace Q] [TopologicalSpace β] [MetrizableSpace β] (π : G → Q)
    (hπ : Function.Surjective π) (b₀ : β) (vals : ℕ → List β) (A : ℕ → β → Set Q)
    (hA : ∀ n b, MeasurableSet (A n b)) (Z' : Set Q) (hZ' : MeasurableSet Z') (f₀ : G → β)
    (hconv : ∀ x, x ∉ π ⁻¹' Z' → Tendsto (fun n ↦
      liftSimpleList (A n) (hA n) b₀ (vals n) (π x)) atTop (𝓝 (f₀ x))) :
    ∃ g : Q → β, StronglyMeasurable g ∧ ∀ x, x ∉ π ⁻¹' Z' → g (π x) = f₀ x := by
  classical
  let s' : ℕ → SimpleFunc Q β := fun n ↦
    SimpleFunc.piecewise Z' hZ' (SimpleFunc.const Q b₀) (liftSimpleList (A n) (hA n) b₀ (vals n))
  let g : Q → β := fun q ↦ if q ∈ Z' then b₀ else f₀ (hπ q).choose
  have hs'_bad {q : Q} (hq : q ∈ Z') (n : ℕ) : s' n q = b₀ := by
    simp only [s', SimpleFunc.piecewise_apply, hq, ite_true, SimpleFunc.const_apply]
  have hs'_good {q : Q} (hq : q ∉ Z') (n : ℕ) :
      s' n q = liftSimpleList (A n) (hA n) b₀ (vals n) q := by
    simp only [s', SimpleFunc.piecewise_apply, hq, ite_false]
  have htend (q : Q) : Tendsto (fun n ↦ s' n q) atTop (𝓝 (g q)) := by
    by_cases hq : q ∈ Z'
    · simp only [g, hq, ite_true, hs'_bad hq]
      exact tendsto_const_nhds
    · simp only [g, hq, ite_false]
      have hsec : π (hπ q).choose = q := (hπ q).choose_spec
      have hxZ' : (hπ q).choose ∉ π ⁻¹' Z' := by
        simpa [mem_preimage, hsec] using hq
      simpa [hs'_good hq, hsec] using hconv (hπ q).choose hxZ'
  refine ⟨g, stronglyMeasurable_of_tendsto atTop (fun n ↦ (s' n).stronglyMeasurable)
    (tendsto_pi_nhds.mpr htend), fun x hx ↦ ?_⟩
  have hc : Tendsto (fun n ↦ s' n (π x)) atTop (𝓝 (f₀ x)) := by
    simpa [hs'_good hx] using hconv x hx
  exact tendsto_nhds_unique (htend (π x)) hc

/-- Extend a family of sets indexed by `↥s.range` to all of `β` by `∅` outside `s.range`. -/
private noncomputable def extendSimpleRange {Q G β : Type*} [MeasurableSpace G] (s : SimpleFunc G β)
    (A : ↥s.range → Set Q) (b : β) : Set Q :=
  open Classical in if hb : b ∈ s.range then A ⟨b, hb⟩ else ∅

private theorem measurableSet_extendSimpleRange {Q G β : Type*} [mQ : MeasurableSpace Q]
    [MeasurableSpace G] (s : SimpleFunc G β) {A : ↥s.range → Set Q}
    (hA : ∀ b, MeasurableSet (A b)) (b : β) :
    MeasurableSet (extendSimpleRange s A b) := by
  classical
  dsimp only [extendSimpleRange]
  split_ifs with hb
  · exact hA ⟨b, hb⟩
  · exact .empty

/-- Outside the quotient sandwich error sets `B b \ A b`, the lifted simple function built from `A`
agrees with `s` along `π`. -/
private theorem liftSimpleList_apply_eq {Q G β : Type*} [mQ : MeasurableSpace Q]
    [MeasurableSpace G] (π : G → Q) (s : SimpleFunc G β) (b₀ : β) {A B : ↥s.range → Set Q}
    (hA : ∀ b, MeasurableSet (A b)) (hpreA : ∀ b, π ⁻¹' A b ⊆ s ⁻¹' {b.1})
    (hpreB : ∀ b, s ⁻¹' {b.1} ⊆ π ⁻¹' B b) {x : G} (hx : ∀ b : ↥s.range, π x ∉ B b \ A b) :
    liftSimpleList (extendSimpleRange s A) (measurableSet_extendSimpleRange s hA) b₀
      s.range.toList (π x) = s x := by
  have hmem : s x ∈ s.range := s.mem_range_self x
  refine liftSimpleList_apply_of_unique _ b₀ (Finset.mem_toList.mpr hmem) ?_ ?_
  · classical
    simp only [extendSimpleRange, hmem, dite_true]
    exact not_not.mp fun hxA ↦ hx ⟨s x, hmem⟩ ⟨hpreB ⟨s x, hmem⟩ rfl, hxA⟩
  · intro b hb hπb
    have hb_mem : b ∈ s.range := Finset.mem_toList.mp hb
    classical
    simp only [extendSimpleRange, hb_mem, dite_true] at hπb
    exact (mem_singleton_iff.mp (hpreA ⟨b, hb_mem⟩ hπb)).symm

/-- Assemble the quotient Borel null set `Z'` collecting the upper sandwich of a null set `N₀` and
the sandwich remainders `B' (Sum.inr i) \ A' (Sum.inr i)` of a countable family of fibers. -/
private theorem exists_quotient_null_error_set {Q G ι : Type*} [mQ : MeasurableSpace Q]
    [MeasurableSpace G] [Countable ι] {μ : Measure G} (π : G → Q) {N₀ : Set G}
    (hN₀ : μ N₀ = 0) {A' B' : Unit ⊕ ι → Set Q} (hA' : ∀ i, MeasurableSet (A' i))
    (hB' : ∀ i, MeasurableSet (B' i)) (hpreA₀ : π ⁻¹' A' (Sum.inl ()) ⊆ N₀)
    (hpreB₀ : N₀ ⊆ π ⁻¹' B' (Sum.inl ())) (hnull : ∀ i, μ (π ⁻¹' (B' i \ A' i)) = 0) :
    ∃ Z' : Set Q, MeasurableSet Z' ∧ μ (π ⁻¹' Z') = 0 ∧ N₀ ⊆ π ⁻¹' Z' ∧
      ∀ i, B' (Sum.inr i) \ A' (Sum.inr i) ⊆ Z' := by
  let Z' : Set Q := B' (Sum.inl ()) ∪ ⋃ i : ι, B' (Sum.inr i) \ A' (Sum.inr i)
  have hZ'_meas : MeasurableSet Z' :=
    (hB' (Sum.inl ())).union <|
      MeasurableSet.iUnion fun i ↦ (hB' (Sum.inr i)).diff (hA' (Sum.inr i))
  have hB₀_null : μ (π ⁻¹' B' (Sum.inl ())) = 0 := by
    have hA₀ : μ (π ⁻¹' A' (Sum.inl ())) = 0 := measure_mono_null hpreA₀ hN₀
    have hsub : π ⁻¹' B' (Sum.inl ()) ⊆
        π ⁻¹' A' (Sum.inl ()) ∪ π ⁻¹' (B' (Sum.inl ()) \ A' (Sum.inl ())) := fun x hx ↦
      em (x ∈ π ⁻¹' A' (Sum.inl ())) |>.imp id fun hxA ↦ ⟨hx, hxA⟩
    exact measure_mono_null hsub (measure_union_null hA₀ (hnull (Sum.inl ())))
  have hZ'_null : μ (π ⁻¹' Z') = 0 := by
    rw [preimage_union]
    refine measure_union_null hB₀_null ?_
    rw [preimage_iUnion]
    exact measure_iUnion_null fun i ↦ hnull (Sum.inr i)
  exact ⟨Z', hZ'_meas, hZ'_null, hpreB₀.trans (preimage_mono subset_union_left),
    fun i ↦ (subset_iUnion (fun j ↦ B' (Sum.inr j) \ A' (Sum.inr j)) i).trans
      subset_union_right⟩

end BorelHelpers

section Helpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- **Right-`K` saturation of null open remainders**: if `K` is a normal subgroup of `G`,
`U ⊆ G` is open, `A' ⊆ G ⧸ K` is Borel, and `μ (U \ π ⁻¹' A') = 0`, then the saturated remainder
`π ⁻¹' ((π '' U) \ A')` also has `μ`-measure zero. -/
private theorem measure_preimage_image_diff_eq_zero {K : Subgroup G} [K.Normal]
    {U : Set G} (hU : IsOpen U) {A' : Set (G ⧸ K)}
    (hA' : MeasurableSet[borel (G ⧸ K)] A')
    (hnull : μ (U \ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A') = 0) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' ((QuotientGroup.mk : G → G ⧸ K) '' U \ A')) = 0 := by
  let π : G → G ⧸ K := QuotientGroup.mk
  have hB' : MeasurableSet[borel (G ⧸ K)] (π '' U) :=
    MeasurableSpace.measurableSet_generateFrom (QuotientGroup.isOpenMap_coe (N := K) U hU)
  let S : Set G := π ⁻¹' (π '' U \ A')
  have h_borelG : (‹MeasurableSpace G› : MeasurableSpace G) = borel G := BorelSpace.measurable_eq
  have hS_meas : MeasurableSet S := by
    rw [h_borelG]
    exact (QuotientGroup.continuous_mk (N := K)).borel_measurable (hB'.diff hA')
  -- Every `K`-translate of `U` meets `S` inside a `K`-translate of the null set `U \ π ⁻¹' A'`.
  have htrans {k : G} (hk : k ∈ K) : μ (((· * k⁻¹) ⁻¹' U) ∩ S) = 0 := by
    refine measure_mono_null (fun x ⟨hxU, hxS⟩ ↦ ?_)
      ((μ.measure_mul_right_null_of_innerRegular k⁻¹).mpr hnull)
    refine ⟨hxU, fun hxA' ↦ hxS.2 ?_⟩
    have hπk : (QuotientGroup.mk k : G ⧸ K) = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    have hπeq : π (x * k⁻¹) = π x := by
      simp [π, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπk]
    rwa [← hπeq]
  -- Every compact subset of `S` is covered by finitely many such translates, so has measure `0`.
  have hcomp {C : Set G} (hC : IsCompact C) (hCS : C ⊆ S) : μ C = 0 := by
    have hcov : C ⊆ ⋃ k ∈ (K : Set G), (· * k⁻¹) ⁻¹' U := by
      intro x hxC
      obtain ⟨u, huU, huπ⟩ := (hCS hxC).1
      have hk : u⁻¹ * x ∈ K := QuotientGroup.eq.mp huπ
      refine mem_iUnion₂.mpr ⟨u⁻¹ * x, hk, ?_⟩
      -- Since `k = u⁻¹ * x`, right multiplication by `k⁻¹` sends `x` back to `u ∈ U`.
      simpa [mul_inv_rev] using huU
    obtain ⟨t, htK, ht_fin, htC⟩ := hC.elim_finite_subcover_image
      (fun k _ ↦ hU.preimage (continuous_mul_const k⁻¹)) hcov
    have hsub : C ⊆ ⋃ k ∈ t, ((· * k⁻¹) ⁻¹' U) ∩ S := fun x hxC ↦ by
      obtain ⟨k, hkt, hxk⟩ := mem_iUnion₂.mp (htC hxC)
      exact mem_iUnion₂.mpr ⟨k, hkt, hxk, hCS hxC⟩
    exact measure_mono_null hsub
      ((measure_biUnion_null_iff ht_fin.countable).mpr fun k hkt ↦ htrans (htK hkt))
  rw [hS_meas.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  exact fun C hCS hC ↦ hcomp hC hCS

/-- Internal predicate: a set `E ⊆ G` is sandwiched between pullbacks of Borel sets on a metrizable
second-countable quotient `G ⧸ K` by a closed compact normal subgroup `K`. -/
private def IsQuotientSandwiched (μ : Measure G) (E : Set G) : Prop :=
  ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
    (𝓝 (1 : G ⧸ K)).IsCountablyGenerated ∧ MetrizableSpace (G ⧸ K) ∧
    SecondCountableTopology (G ⧸ K) ∧
    ∃ A' B' : Set (G ⧸ K), MeasurableSet[borel (G ⧸ K)] A' ∧ MeasurableSet[borel (G ⧸ K)] B' ∧
      A' ⊆ B' ∧ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A' ⊆ E ∧
      E ⊆ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' B' ∧
      μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' \ A')) = 0

/-- Every open set of finite `μ`-measure satisfies `IsQuotientSandwiched μ`. -/
private theorem isQuotientSandwiched_of_isOpen_lt_top {U : Set G} (hU : IsOpen U)
    (hμU : μ U < ∞) : IsQuotientSandwiched μ U := by
  have happrox (j : ℕ) : ∃ C, C ⊆ U ∧ IsCompact C ∧ μ (U \ C) < (j : ℝ≥0∞)⁻¹ := by
    obtain ⟨C, hCU, hCco, _, hμC⟩ := hU.measurableSet.exists_isCompact_isClosed_sdiff_lt hμU.ne
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top j))
    exact ⟨C, hCU, hCco, hμC⟩
  choose C hCU hC hμC using happrox
  have hury (j : ℕ) : ∃ f : C(G, ℝ), EqOn f 0 (C j) ∧ EqOn f 1 Uᶜ := by
    obtain ⟨f, hf0, hf1, _⟩ := exists_continuous_zero_one_of_isCompact (hC j) hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCU j))
    exact ⟨f, hf0, hf1⟩
  choose f hf0 hf1 using hury
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, hfac⟩ :=
    exists_compact_normal_subgroup_factor_continuous (fun j : ℕ ↦ (f j : G → ℝ))
      fun j ↦ (f j).continuous
  choose g hg_cont hgf using hfac
  let π : G → G ⧸ K := QuotientGroup.mk
  let A' : Set (G ⧸ K) := ⋃ j : ℕ, {q : G ⧸ K | g j q < 1}
  let B' : Set (G ⧸ K) := π '' U
  have hA'_meas : MeasurableSet[borel (G ⧸ K)] A' :=
    MeasurableSpace.measurableSet_generateFrom
      (isOpen_iUnion fun j ↦ isOpen_lt (hg_cont j) continuous_const)
  have hB'_meas : MeasurableSet[borel (G ⧸ K)] B' :=
    MeasurableSpace.measurableSet_generateFrom (QuotientGroup.isOpenMap_coe (N := K) U hU)
  have hpreA' : π ⁻¹' A' ⊆ U := by
    rintro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hgj : g j (π x) = f j x := congr_fun (hgf j) x
    have hfx : f j x < 1 := hgj ▸ hj
    by_contra hxU
    exact hfx.ne (hf1 j hxU)
  have hU_diff : μ (U \ π ⁻¹' A') = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) zero_le
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    have hsub : U \ π ⁻¹' A' ⊆ U \ C j := sdiff_subset_sdiff_right fun x hxC ↦
      mem_iUnion.mpr ⟨j, ((congr_fun (hgf j) x).trans (hf0 j hxC)).trans_lt zero_lt_one⟩
    simpa only [zero_add] using (measure_mono hsub).trans ((hμC j).le.trans hj.le)
  have hAB' : A' ⊆ B' := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact mem_image_of_mem π (hpreA' hq)
  exact ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, A', B', hA'_meas, hB'_meas, hAB',
    hpreA', subset_preimage_image π U,
    measure_preimage_image_diff_eq_zero hU hA'_meas hU_diff⟩

omit [BorelSpace G] [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] in
/-- Simultaneous quotient Borel sandwiching for a countable family of sets already known to satisfy
`IsQuotientSandwiched μ`. -/
private theorem exists_forall_of_isQuotientSandwiched {ι : Type*} [Countable ι] {E : ι → Set G}
    (hE : ∀ i, IsQuotientSandwiched μ (E i)) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      (𝓝 (1 : G ⧸ K)).IsCountablyGenerated ∧ MetrizableSpace (G ⧸ K) ∧
      SecondCountableTopology (G ⧸ K) ∧
      ∃ A' B' : ι → Set (G ⧸ K),
        (∀ i, MeasurableSet[borel (G ⧸ K)] (A' i)) ∧
        (∀ i, MeasurableSet[borel (G ⧸ K)] (B' i)) ∧
        (∀ i, A' i ⊆ B' i) ∧
        (∀ i, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A' i ⊆ E i) ∧
        (∀ i, E i ⊆ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' B' i) ∧
        ∀ i, μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' i \ A' i)) = 0 := by
  choose L hL_norm _ hL_cl hL_cg _ _ A₁ B₁ hA₁ hB₁ hAB₁ hpreA₁ hpreB₁ hnull₁ using
    fun i ↦ (hE i)
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hKL, hK_cg, hK_met, hK_sc⟩ :=
    exists_compact_normal_subgroup_le L hL_norm hL_cl hL_cg
  let p : ∀ i, G ⧸ K →* G ⧸ L i := fun i ↦
    have := hL_norm i
    QuotientGroup.mapOfLE (hKL i)
  have hp_meas (i : ι) :
      @Measurable (G ⧸ K) (G ⧸ L i) (borel (G ⧸ K)) (borel (G ⧸ L i)) (p i) := by
    have := hL_norm i
    exact (QuotientGroup.continuous_mapOfLE (hKL i)).borel_measurable
  have hp_mk (i : ι) : (p i : G ⧸ K → G ⧸ L i) ∘ (QuotientGroup.mk : G → G ⧸ K) =
      (QuotientGroup.mk : G → G ⧸ L i) := by
    have := hL_norm i
    ext x
    exact QuotientGroup.mapOfLE_mk (hKL i) x
  refine ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc,
    fun i ↦ p i ⁻¹' A₁ i, fun i ↦ p i ⁻¹' B₁ i,
    fun i ↦ hp_meas i (hA₁ i), fun i ↦ hp_meas i (hB₁ i),
    fun i ↦ preimage_mono (hAB₁ i), ?_, ?_, ?_⟩
  · intro i
    rw [← preimage_comp, hp_mk i]
    exact hpreA₁ i
  · intro i
    rw [← preimage_comp, hp_mk i]
    exact hpreB₁ i
  · intro i
    rw [← preimage_sdiff, ← preimage_comp, hp_mk i]
    exact hnull₁ i

/-- Every Borel set `E ⊆ G` satisfies `IsQuotientSandwiched μ`. -/
private theorem isQuotientSandwiched_of_measurableSet {E : Set G} (hE : MeasurableSet E) :
    IsQuotientSandwiched μ E := by
  have hempty : IsQuotientSandwiched μ ∅ := by
    obtain ⟨K, hK_norm, hK_cp, hK_cl, _, hK_cg, hK_met, hK_sc⟩ :=
      exists_compact_normal_subgroup_quotient_metrizable (fun _ : Unit ↦ (univ : Set G))
        fun _ ↦ univ_mem
    exact ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, ∅, ∅,
      @MeasurableSet.empty _ (borel (G ⧸ K)), @MeasurableSet.empty _ (borel (G ⧸ K)),
      Subset.rfl, empty_subset _, empty_subset _, by simp⟩
  have hcompl {S : Set G} (hS : IsQuotientSandwiched μ S) : IsQuotientSandwiched μ Sᶜ := by
    obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, A', B', hA', hB', hAB',
      hpreA', hpreB', hnull⟩ := hS
    refine ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, B'ᶜ, A'ᶜ, hB'.compl, hA'.compl,
      compl_subset_compl.mpr hAB', compl_subset_compl.mpr hpreB', compl_subset_compl.mpr hpreA', ?_⟩
    have heq : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' (A'ᶜ \ B'ᶜ) =
        (QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' \ A') := by
      ext x
      simp [and_comm]
    rwa [heq]
  have hiUnion {S : ℕ → Set G} (hS : ∀ n, IsQuotientSandwiched μ (S n)) :
      IsQuotientSandwiched μ (⋃ n, S n) := by
    obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, A', B', hA', hB', hAB',
      hpreA', hpreB', hnull⟩ := exists_forall_of_isQuotientSandwiched hS
    refine ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, ⋃ n, A' n, ⋃ n, B' n,
      MeasurableSet.iUnion hA', MeasurableSet.iUnion hB', iUnion_mono hAB',
      by rw [preimage_iUnion]; exact iUnion_mono hpreA',
      by rw [preimage_iUnion]; exact iUnion_mono hpreB', ?_⟩
    have hdiff : (⋃ n, B' n) \ (⋃ n, A' n) ⊆ ⋃ n, (B' n \ A' n) := by
      rintro q ⟨hqB, hqA⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hqB
      exact mem_iUnion.mpr ⟨n, hn, fun hnA ↦ hqA (mem_iUnion.mpr ⟨n, hnA⟩)⟩
    refine measure_mono_null (preimage_mono hdiff) ?_
    rw [preimage_iUnion]
    exact measure_iUnion_null hnull
  -- Every open set is a countable union of open finite-measure sets via `compactCovering G`.
  have hisOpen {O : Set G} (hO : IsOpen O) : IsQuotientSandwiched μ O := by
    choose W hCW hWo hμW using fun n ↦
      (isCompact_compactCovering G n).exists_open_superset_measure_lt_top μ
    have hcover : O = ⋃ n, O ∩ W n := by
      refine Subset.antisymm (fun x hx ↦ ?_) (iUnion_subset fun _ ↦ inter_subset_left)
      obtain ⟨n, hn⟩ := exists_mem_compactCovering x
      exact mem_iUnion.mpr ⟨n, hx, hCW n hn⟩
    rw [hcover]
    exact hiUnion fun n ↦ isQuotientSandwiched_of_isOpen_lt_top (hO.inter (hWo n))
      ((measure_mono inter_subset_right).trans_lt (hμW n))
  -- Conclude for all Borel sets via `MeasurableSpace.generateFrom` on open sets.
  have h_borel : (‹MeasurableSpace G› : MeasurableSpace G) = borel G := BorelSpace.measurable_eq
  let m : MeasurableSpace G :=
    { MeasurableSet' := IsQuotientSandwiched μ
      measurableSet_empty := hempty
      measurableSet_compl := fun _ ↦ hcompl
      measurableSet_iUnion := fun _ ↦ hiUnion }
  have hle : borel G ≤ m := MeasurableSpace.generateFrom_le fun _ hO ↦ hisOpen hO
  exact hle E (h_borel ▸ hE)

/-- Every `μ`-null-measurable set `E ⊆ G` satisfies `IsQuotientSandwiched μ`. -/
private theorem isQuotientSandwiched_of_nullMeasurableSet {E : Set G}
    (hE : NullMeasurableSet E μ) : IsQuotientSandwiched μ E := by
  let E₂ : Set G := toMeasurable μ E
  let E₁ : Set G := (toMeasurable μ Eᶜ)ᶜ
  have hE₁_sub : E₁ ⊆ E := compl_subset_comm.mp (subset_toMeasurable μ Eᶜ)
  have hE₂_sup : E ⊆ E₂ := subset_toMeasurable μ E
  have hE₁_meas : MeasurableSet E₁ := (measurableSet_toMeasurable μ Eᶜ).compl
  have hE₂_meas : MeasurableSet E₂ := measurableSet_toMeasurable μ E
  have hdiff_null : μ (E₂ \ E₁) = 0 := by
    have hae₁ : E₁ =ᵐ[μ] E := by
      simpa [E₁] using (hE.compl.toMeasurable_ae_eq).compl
    have hae₂ : E₂ =ᵐ[μ] E := hE.toMeasurable_ae_eq
    exact ae_subset.mp (hae₂.trans hae₁.symm).subset
  let pair : Bool → Set G := fun b ↦ cond b E₁ E₂
  have hpair : ∀ b, IsQuotientSandwiched μ (pair b)
    | true => isQuotientSandwiched_of_measurableSet hE₁_meas
    | false => isQuotientSandwiched_of_measurableSet hE₂_meas
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, A', B', hA', hB', _,
    hpreA', hpreB', hnull⟩ := exists_forall_of_isQuotientSandwiched hpair
  let π : G → G ⧸ K := QuotientGroup.mk
  have hAtrue_sub_Bfalse : A' true ⊆ B' false := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hpreB' false (hE₂_sup (hE₁_sub (hpreA' true hq)))
  refine ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, A' true, B' false,
    hA' true, hB' false, hAtrue_sub_Bfalse, (hpreA' true).trans hE₁_sub,
    hE₂_sup.trans (hpreB' false), ?_⟩
  have hsub : π ⁻¹' (B' false \ A' true) ⊆
      π ⁻¹' (B' false \ A' false) ∪ (E₂ \ E₁) ∪ π ⁻¹' (B' true \ A' true) := by
    rintro x ⟨hxBf, hxAt⟩
    by_cases hxE₂ : x ∈ E₂
    · by_cases hxE₁ : x ∈ E₁
      · exact Or.inr ⟨hpreB' true hxE₁, hxAt⟩
      · exact Or.inl (Or.inr ⟨hxE₂, hxE₁⟩)
    · exact Or.inl (Or.inl ⟨hxBf, fun hxAf ↦ hxE₂ (hpreA' false hxAf)⟩)
  exact measure_mono_null hsub <|
    measure_union_null (measure_union_null (hnull false) hdiff_null) (hnull true)

end Helpers

/-- **Simultaneous quotient Borel sandwiching** for a countable family of `μ`-null-measurable sets
on a σ-compact locally compact topological group: all sets in the family are sandwiched up to
`μ`-null sets by Borel sets over a single metrizable second-countable quotient `G ⧸ K` by a closed
compact normal subgroup `K`. -/
theorem exists_compact_normal_subgroup_forall_quotient_borel_sandwich {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] {ι : Type*} [Countable ι]
    {E : ι → Set G} (hE : ∀ i, NullMeasurableSet (E i) μ) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) ∧
      ∃ A' B' : ι → Set (G ⧸ K),
        (∀ i, MeasurableSet[borel (G ⧸ K)] (A' i)) ∧
        (∀ i, MeasurableSet[borel (G ⧸ K)] (B' i)) ∧
        (∀ i, A' i ⊆ B' i) ∧
        (∀ i, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A' i ⊆ E i) ∧
        (∀ i, E i ⊆ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' B' i) ∧
        ∀ i, μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' i \ A' i)) = 0 := by
  obtain ⟨K, hK_norm, hK_cp, hK_cl, _, hK_met, hK_sc, rest⟩ :=
    exists_forall_of_isQuotientSandwiched fun i ↦ isQuotientSandwiched_of_nullMeasurableSet (hE i)
  exact ⟨K, hK_norm, hK_cp, hK_cl, hK_met, hK_sc, rest⟩

end TauCeti

namespace MeasureTheory

section CompletionRegular

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- **Quotient Borel sandwiching** for a `μ`-null-measurable set `E` on a σ-compact locally compact
group `G`: there exist a closed compact normal subgroup `K` with metrizable second-countable
quotient `G ⧸ K` and Borel sets `A' ⊆ B'` in `G ⧸ K` such that `π ⁻¹' A' ⊆ E ⊆ π ⁻¹' B'` and
`μ (π ⁻¹' (B' \ A')) = 0`. -/
theorem NullMeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich {E : Set G}
    (hE : NullMeasurableSet E μ) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) ∧
      ∃ A' B' : Set (G ⧸ K), MeasurableSet[borel (G ⧸ K)] A' ∧ MeasurableSet[borel (G ⧸ K)] B' ∧
        A' ⊆ B' ∧ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A' ⊆ E ∧
        E ⊆ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' B' ∧
        μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' \ A')) = 0 := by
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_met, hK_sc, A', B', hA', hB', hAB', hpreA', hpreB',
    hnull⟩ := TauCeti.exists_compact_normal_subgroup_forall_quotient_borel_sandwich
      (fun _ : Unit ↦ hE)
  exact ⟨K, hK_norm, hK_cp, hK_cl, hK_met, hK_sc, A' (), B' (), hA' (), hB' (), hAB' (),
    hpreA' (), hpreB' (), hnull ()⟩

/-- **Quotient Borel sandwiching** for a Borel set `E` on a σ-compact locally compact group `G`. -/
theorem _root_.MeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich {E : Set G}
    (hE : MeasurableSet E) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) ∧
      ∃ A' B' : Set (G ⧸ K), MeasurableSet[borel (G ⧸ K)] A' ∧ MeasurableSet[borel (G ⧸ K)] B' ∧
        A' ⊆ B' ∧ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A' ⊆ E ∧
        E ⊆ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' B' ∧
        μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' \ A')) = 0 :=
  hE.nullMeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich

/-- **Haar completion regularity** (sandwich form): every `μ`-null-measurable set `E` on a
σ-compact locally compact group `G` is sandwiched between two Baire sets `A ⊆ E ⊆ B` in
`TauCeti.baire G` with `μ (B \ A) = 0`. -/
theorem NullMeasurableSet.exists_baire_sandwich {E : Set G}
    (hE : NullMeasurableSet E μ) :
    ∃ A B : Set G, MeasurableSet[TauCeti.baire G] A ∧ MeasurableSet[TauCeti.baire G] B ∧
      A ⊆ E ∧ E ⊆ B ∧ μ (B \ A) = 0 := by
  obtain ⟨K, _, _, _, _, _, A', B', hA', hB', _, hpreA', hpreB', hnull⟩ :=
    hE.exists_compact_normal_subgroup_quotient_borel_sandwich
  have hle := (QuotientGroup.continuous_mk (N := K)).comap_borel_le_baire
  exact ⟨QuotientGroup.mk ⁻¹' A', QuotientGroup.mk ⁻¹' B',
    hle _ ⟨A', hA', rfl⟩, hle _ ⟨B', hB', rfl⟩, hpreA', hpreB', hnull⟩

/-- **Haar completion regularity** (sandwich form) for Borel sets. -/
theorem _root_.MeasurableSet.exists_baire_sandwich {E : Set G} (hE : MeasurableSet E) :
    ∃ A B : Set G, MeasurableSet[TauCeti.baire G] A ∧ MeasurableSet[TauCeti.baire G] B ∧
      A ⊆ E ∧ E ⊆ B ∧ μ (B \ A) = 0 :=
  hE.nullMeasurableSet.exists_baire_sandwich

/-- **Haar completion regularity** (Fremlin §443M): every `μ`-null-measurable set `E` on a
σ-compact locally compact group `G` differs from a Baire set `A` by a subset of a Baire `μ`-null
set `N` in `TauCeti.baire G`. -/
theorem NullMeasurableSet.exists_baire_symmDiff_subset_null_of_innerRegular {E : Set G}
    (hE : NullMeasurableSet E μ) :
    ∃ A N : Set G, MeasurableSet[TauCeti.baire G] A ∧ MeasurableSet[TauCeti.baire G] N ∧
      E ∆ A ⊆ N ∧ μ N = 0 := by
  obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := hE.exists_baire_sandwich
  refine ⟨A, B \ A, hA, hB.diff hA, ?_, hnull⟩
  rintro x (⟨hxE, hxA⟩ | ⟨hxA, hxE⟩)
  · exact ⟨hEB hxE, hxA⟩
  · exact False.elim (hxE (hAE hxA))

/-- **Haar completion regularity** (Fremlin §443M) for Borel sets. -/
theorem _root_.MeasurableSet.exists_baire_symmDiff_subset_null_of_innerRegular {E : Set G}
    (hE : MeasurableSet E) :
    ∃ A N : Set G, MeasurableSet[TauCeti.baire G] A ∧ MeasurableSet[TauCeti.baire G] N ∧
      E ∆ A ⊆ N ∧ μ N = 0 :=
  hE.nullMeasurableSet.exists_baire_symmDiff_subset_null_of_innerRegular

/-- **Quotient factorization of `AEStronglyMeasurable` functions**: every `μ`-a.e. strongly
measurable function `f : G → β` into a metrizable space agrees outside `π ⁻¹' Z'` (`Z'` Borel in
`G ⧸ K` with `μ (π ⁻¹' Z') = 0`) with `g ∘ π` for a closed compact normal subgroup `K` with
metrizable second-countable quotient `G ⧸ K` and a `borel (G ⧸ K)`-strongly measurable function
`g : G ⧸ K → β`. -/
theorem AEStronglyMeasurable.exists_compact_normal_subgroup_quotient_eq_off_null {β : Type*}
    [TopologicalSpace β] [MetrizableSpace β] {f : G → β} (hf : AEStronglyMeasurable f μ) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) ∧
      ∃ (g : G ⧸ K → β) (Z' : Set (G ⧸ K)),
        StronglyMeasurable[borel (G ⧸ K)] g ∧ MeasurableSet[borel (G ⧸ K)] Z' ∧
        μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' Z') = 0 ∧
        ∀ x, x ∉ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' Z' →
          f x = g (QuotientGroup.mk x) := by
  let f₀ : G → β := hf.mk f
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  let s : ℕ → SimpleFunc G β := hf₀.approx
  let N₀ : Set G := {x | f x ≠ f₀ x}
  have hN₀_null : μ N₀ = 0 := hf.ae_eq_mk
  -- Index `N₀` and all fibers `(s n) ⁻¹' {b}` over a single countable sum type.
  let idx := Unit ⊕ Σ n : ℕ, ↥(s n).range
  let fam : idx → Set G
    | Sum.inl () => N₀
    | Sum.inr ⟨n, b⟩ => s n ⁻¹' {(b : β)}
  have hfam (i : idx) : NullMeasurableSet (fam i) μ := by
    cases i with
    | inl _ => exact NullMeasurableSet.of_null hN₀_null
    | inr p => exact ((s p.1).measurableSet_fiber p.2.1).nullMeasurableSet
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_met, hK_sc, A', B', hA', hB', _, hpreA', hpreB',
    hnull⟩ := TauCeti.exists_compact_normal_subgroup_forall_quotient_borel_sandwich hfam
  let π : G → G ⧸ K := QuotientGroup.mk
  obtain ⟨Z', hZ'_meas, hZ'_null, hN₀_sub, hdiff_sub⟩ :=
    TauCeti.exists_quotient_null_error_set (mQ := borel (G ⧸ K)) π hN₀_null hA' hB'
      (hpreA' (Sum.inl ())) (hpreB' (Sum.inl ())) hnull
  obtain ⟨g, hg_meas, hg_eq⟩ := TauCeti.exists_stronglyMeasurable_of_quotient_fibers
    (mQ := borel (G ⧸ K)) π QuotientGroup.mk_surjective (f 1)
    (fun n ↦ (s n).range.toList)
    (fun n ↦ TauCeti.extendSimpleRange (s n) (fun b ↦ A' (Sum.inr ⟨n, b⟩)))
    (fun n ↦ TauCeti.measurableSet_extendSimpleRange (mQ := borel (G ⧸ K)) (s n)
      (fun b ↦ hA' (Sum.inr ⟨n, b⟩)))
    Z' hZ'_meas f₀ fun x hxZ' ↦ by
      have hval (n : ℕ) := TauCeti.liftSimpleList_apply_eq (mQ := borel (G ⧸ K)) π (s n) (f 1)
        (fun b ↦ hA' (Sum.inr ⟨n, b⟩)) (fun b ↦ hpreA' (Sum.inr ⟨n, b⟩))
        (fun b ↦ hpreB' (Sum.inr ⟨n, b⟩)) fun b hb ↦ hxZ' (hdiff_sub ⟨n, b⟩ hb)
      simpa [hval] using hf₀.tendsto_approx x
  refine ⟨K, hK_norm, hK_cp, hK_cl, hK_met, hK_sc, g, Z', hg_meas, hZ'_meas, hZ'_null,
    fun x hxZ' ↦ ?_⟩
  have hfx : f x = f₀ x := not_not.mp fun hxN ↦ hxZ' (hN₀_sub hxN)
  rw [hfx, hg_eq x hxZ']

/-- Every `μ`-a.e. strongly measurable function from a σ-compact locally compact group `G` into a
metrizable space is `AEStronglyMeasurable` with respect to the Baire σ-algebra `TauCeti.baire G`. -/
theorem AEStronglyMeasurable.aestronglyMeasurable_baire {β : Type*}
    [TopologicalSpace β] [MetrizableSpace β] {f : G → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[TauCeti.baire G] f μ := by
  obtain ⟨K, _, _, _, _, _, g, Z', hg, _, hZ'_null, hfg⟩ :=
    hf.exists_compact_normal_subgroup_quotient_eq_off_null
  have hcomap : MeasurableSpace.comap (QuotientGroup.mk : G → G ⧸ K) (borel (G ⧸ K)) ≤
      TauCeti.baire G :=
    (QuotientGroup.continuous_mk (N := K)).comap_borel_le_baire
  have hg_baire :
      StronglyMeasurable[TauCeti.baire G] (g ∘ (QuotientGroup.mk : G → G ⧸ K)) :=
    (hg.comp_measurable (@Measurable.of_comap_le G (G ⧸ K)
      (MeasurableSpace.comap (QuotientGroup.mk : G → G ⧸ K) (borel (G ⧸ K))) (borel (G ⧸ K)) _
      le_rfl)).mono hcomap
  refine ⟨g ∘ QuotientGroup.mk, hg_baire, ?_⟩
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) hZ'_null
  by_contra hxZ'
  exact hx (hfg x hxZ')

end CompletionRegular

end MeasureTheory

end
