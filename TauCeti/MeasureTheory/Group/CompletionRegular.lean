/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Metrizable
public import TauCeti.Topology.Algebra.Group.KakutaniKodaira
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Topology.UrysohnsLemma
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
   Baire σ-algebra `⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance`, every Borel (or
   `μ`-null-measurable) set `E ⊆ G` is sandwiched between two Baire sets whose difference has
   `μ`-measure zero, and therefore differs from a Baire set by a subset of a Baire `μ`-null set.
3. **Quotient factorization of `AEStronglyMeasurable` functions**: every `μ`-almost everywhere
   strongly measurable function `f : G → β` into a metrizable space agrees outside `π ⁻¹' Z'`
   (`Z' ∈ borel (G ⧸ K)`, `μ (π ⁻¹' Z') = 0`) with `g ∘ π` for a `borel (G ⧸ K)`-strongly
   measurable map `g : G ⧸ K → β`, and is consequently `AEStronglyMeasurable` with respect to the
   Baire σ-algebra on `G`.

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
  `MeasureTheory.MeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich`: single-set
  quotient Borel sandwiching.
* `MeasureTheory.NullMeasurableSet.exists_mem_iSup_comap_continuousMap_sandwich` and
  `MeasureTheory.MeasurableSet.exists_mem_iSup_comap_continuousMap_sandwich`: Haar completion
  regularity in sandwich form.
* `MeasureTheory.NullMeasurableSet.exists_mem_iSup_comap_continuousMap_symmDiff_subset_null` and
  `MeasureTheory.MeasurableSet.exists_mem_iSup_comap_continuousMap_symmDiff_subset_null`: Haar
  completion regularity in symmetric-difference form (Fremlin §443M).
* `MeasureTheory.AEStronglyMeasurable.exists_compact_normal_subgroup_quotient_eq_off_null`:
  factorization of `AEStronglyMeasurable` functions outside a pullback Haar-null set through a
  metrizable second-countable quotient `G ⧸ K`.
* `MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_iSup_comap_continuousMap`: every
  `AEStronglyMeasurable` function into a metrizable space is Baire a.e. strongly measurable.

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

/-- Every open set is measurable in `borel X`, without assuming an ambient `MeasurableSpace X`. -/
private theorem isOpen_measurableSet_borel {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsOpen s) : MeasurableSet[borel X] s :=
  MeasurableSpace.measurableSet_generateFrom hs

/-- Any continuous map is measurable between explicit `borel` σ-algebras, avoiding typeclass
clashes when the codomain or domain already carries another `MeasurableSpace` instance. -/
private theorem continuous_measurable_borel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : @Measurable X Y (borel X) (borel Y) f := by
  let _ : MeasurableSpace X := borel X
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace X := ⟨rfl⟩
  have : BorelSpace Y := ⟨rfl⟩
  exact hf.measurable

/-- Construct a simple function on an abstract measurable space `Q` from a finite list of values
`l : List β` and corresponding measurable sets `A : β → Set Q`. -/
private noncomputable def liftSimpleList {Q β : Type*} [MeasurableSpace Q] (A : β → Set Q)
    (hA : ∀ b, MeasurableSet (A b)) (b₀ : β) : List β → SimpleFunc Q β
  | [] => SimpleFunc.const Q b₀
  | b :: bs => SimpleFunc.piecewise (A b) (hA b) (SimpleFunc.const Q b) (liftSimpleList A hA b₀ bs)

private theorem liftSimpleList_apply_of_unique {Q β : Type*} [MeasurableSpace Q] {A : β → Set Q}
    (hA : ∀ b, MeasurableSet (A b)) (b₀ : β) {l : List β} {q : Q} {v : β} (hv : v ∈ l)
    (hqv : q ∈ A v) (huniq : ∀ b ∈ l, q ∈ A b → b = v) :
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
private theorem exists_stronglyMeasurable_of_quotient_fibers {Q G β : Type*} [MeasurableSpace Q]
    [TopologicalSpace β] [MetrizableSpace β] (π : G → Q) (hπ : Function.Surjective π) (b₀ : β)
    (vals : ℕ → List β) (A : ℕ → β → Set Q) (hA : ∀ n b, MeasurableSet (A n b))
    (Z' : Set Q) (hZ' : MeasurableSet Z') (f₀ : G → β)
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

end BorelHelpers

section Helpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- Right multiplication preserves `μ`-null sets on a σ-compact locally compact group, without
requiring `[μ.IsOpenPosMeasure]` or `[μ.Regular]`: either `μ = 0` or `μ` is an inner-regular Haar
measure. -/
private theorem measure_mul_right_null_of_sigmaCompact (g : G) {s : Set G} :
    μ ((· * g) ⁻¹' s) = 0 ↔ μ s = 0 := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp
  · have : μ.IsOpenPosMeasure := ⟨fun U hU ⟨x₀, hx₀⟩ hU0 ↦ hμ0 <| by
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering G]
      refine measure_iUnion_null fun n ↦ ?_
      obtain ⟨t, ht⟩ := (isCompact_compactCovering G n).elim_finite_subcover
        (fun c : G ↦ ((x₀ * c⁻¹) * ·) ⁻¹' U) (fun c ↦ hU.preimage (continuous_const_mul _))
        fun c _ ↦ mem_iUnion.mpr ⟨c, by simp [hx₀]⟩
      refine measure_mono_null ht ((measure_biUnion_null_iff t.countable_toSet).mpr fun c _ ↦ ?_)
      rw [measure_preimage_mul, hU0]⟩
    have : μ.IsHaarMeasure := {}
    have hmap := (MeasurableEquiv.mulRight g).map_apply (μ := μ) s
    rw [MeasurableEquiv.coe_mulRight, Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
      smul_apply, Measure.nnreal_smul_coe_apply] at hmap
    have hpos : Measure.modularCharacterFun g ≠ 0 := (Measure.modularCharacterFun_pos g).ne'
    simp [← hmap, hpos]

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
    isOpen_measurableSet_borel (QuotientGroup.isOpenMap_coe (N := K) U hU)
  let S : Set G := π ⁻¹' (π '' U \ A')
  have h_borelG : (‹MeasurableSpace G› : MeasurableSpace G) = borel G := BorelSpace.measurable_eq
  have hS_meas : MeasurableSet S := by
    rw [h_borelG]
    exact continuous_measurable_borel (QuotientGroup.continuous_mk (N := K)) (hB'.diff hA')
  -- Every `K`-translate of `U` meets `S` inside a `K`-translate of the null set `U \ π ⁻¹' A'`.
  have htrans {k : G} (hk : k ∈ K) : μ (((· * k⁻¹) ⁻¹' U) ∩ S) = 0 := by
    refine measure_mono_null (fun x ⟨hxU, hxS⟩ ↦ ?_)
      ((measure_mul_right_null_of_sigmaCompact k⁻¹).mpr hnull)
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
  -- Exhaust `S` by finite-measure pieces via `spanningSets μ` and apply inner regularity.
  have hspan : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' ((QuotientGroup.mk : G → G ⧸ K) '' U \ A') =
      ⋃ n, S ∩ spanningSets μ n := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rw [hspan]
  refine measure_iUnion_null fun n ↦ ?_
  have hmeas_n : MeasurableSet (S ∩ spanningSets μ n) :=
    hS_meas.inter (measurableSet_spanningSets μ n)
  have hfin_n : μ (S ∩ spanningSets μ n) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
  rw [hmeas_n.measure_eq_iSup_isCompact_of_ne_top hfin_n]
  simp only [ENNReal.iSup_eq_zero]
  intro C hCSn hC
  exact hcomp hC (hCSn.trans inter_subset_left)

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
  have happrox (j : ℕ) : ∃ C, C ⊆ U ∧ IsCompact C ∧ μ (U \ C) < 1 / ((j : ℝ≥0∞) + 1) := by
    have hε : (1 / ((j : ℝ≥0∞) + 1)) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨one_ne_zero, by simp⟩
    obtain ⟨C, hCU, hCco, _, hμC⟩ := hU.measurableSet.exists_isCompact_isClosed_sdiff_lt hμU.ne hε
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
    isOpen_measurableSet_borel (isOpen_iUnion fun j ↦ isOpen_lt (hg_cont j) continuous_const)
  have hB'_meas : MeasurableSet[borel (G ⧸ K)] B' :=
    isOpen_measurableSet_borel (QuotientGroup.isOpenMap_coe (N := K) U hU)
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
    have hj' : (1 : ℝ≥0∞) / ((j : ℝ≥0∞) + 1) ≤ ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      simp [one_div]
    have hlt : ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ε := by
      have h1 : (((j + 1 : ℕ) : ℝ≥0∞))⁻¹ ≤ (j : ℝ≥0∞)⁻¹ := by
        rcases j with _ | j
        · exact False.elim (by simp at hj)
        · gcongr; omega
      exact h1.trans hj.le
    calc μ (U \ π ⁻¹' A') ≤ μ (U \ C j) := measure_mono hsub
      _ ≤ 1 / ((j : ℝ≥0∞) + 1) := (hμC j).le
      _ ≤ ε := hj'.trans hlt
      _ = 0 + ε := (zero_add ε).symm
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
    exact continuous_measurable_borel (QuotientGroup.continuous_mapOfLE (hKL i))
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
    exact ae_le_set.mp (hae₂.trans hae₁.symm).le
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
theorem MeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich {E : Set G}
    (hE : MeasurableSet E) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) ∧
      ∃ A' B' : Set (G ⧸ K), MeasurableSet[borel (G ⧸ K)] A' ∧ MeasurableSet[borel (G ⧸ K)] B' ∧
        A' ⊆ B' ∧ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' A' ⊆ E ∧
        E ⊆ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' B' ∧
        μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (B' \ A')) = 0 :=
  hE.nullMeasurableSet.exists_compact_normal_subgroup_quotient_borel_sandwich

/-- **Haar completion regularity** (sandwich form): every `μ`-null-measurable set `E` on a
σ-compact locally compact group `G` is sandwiched between two sets `A ⊆ E ⊆ B` in the Baire
σ-algebra `⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance` with `μ (B \ A) = 0`. -/
theorem NullMeasurableSet.exists_mem_iSup_comap_continuousMap_sandwich {E : Set G}
    (hE : NullMeasurableSet E μ) :
    ∃ A B : Set G,
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] A ∧
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] B ∧
      A ⊆ E ∧ E ⊆ B ∧ μ (B \ A) = 0 := by
  obtain ⟨K, _, _, _, _, _, A', B', hA', hB', _, hpreA', hpreB', hnull⟩ :=
    hE.exists_compact_normal_subgroup_quotient_borel_sandwich
  have hle :=
    (QuotientGroup.continuous_mk (N := K)).comap_borel_le_iSup_comap_continuousMap
  exact ⟨QuotientGroup.mk ⁻¹' A', QuotientGroup.mk ⁻¹' B',
    hle _ ⟨A', hA', rfl⟩, hle _ ⟨B', hB', rfl⟩, hpreA', hpreB', hnull⟩

/-- **Haar completion regularity** (sandwich form) for Borel sets. -/
theorem MeasurableSet.exists_mem_iSup_comap_continuousMap_sandwich {E : Set G}
    (hE : MeasurableSet E) :
    ∃ A B : Set G,
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] A ∧
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] B ∧
      A ⊆ E ∧ E ⊆ B ∧ μ (B \ A) = 0 :=
  hE.nullMeasurableSet.exists_mem_iSup_comap_continuousMap_sandwich

/-- **Haar completion regularity** (Fremlin §443M): every `μ`-null-measurable set `E` on a
σ-compact locally compact group `G` differs from a Baire set `A` by a subset of a Baire `μ`-null
set `N`, where the Baire σ-algebra is generated by `C(G, ℝ)`. -/
theorem NullMeasurableSet.exists_mem_iSup_comap_continuousMap_symmDiff_subset_null {E : Set G}
    (hE : NullMeasurableSet E μ) :
    ∃ A N : Set G,
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] A ∧
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] N ∧
      E ∆ A ⊆ N ∧ μ N = 0 := by
  obtain ⟨A, B, hA, hB, hAE, hEB, hnull⟩ := hE.exists_mem_iSup_comap_continuousMap_sandwich
  refine ⟨A, B \ A, hA, hB.diff hA, ?_, hnull⟩
  rintro x (⟨hxE, hxA⟩ | ⟨hxA, hxE⟩)
  · exact ⟨hEB hxE, hxA⟩
  · exact False.elim (hxE (hAE hxA))

/-- **Haar completion regularity** (Fremlin §443M) for Borel sets. -/
theorem MeasurableSet.exists_mem_iSup_comap_continuousMap_symmDiff_subset_null {E : Set G}
    (hE : MeasurableSet E) :
    ∃ A N : Set G,
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] A ∧
      MeasurableSet[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] N ∧
      E ∆ A ⊆ N ∧ μ N = 0 :=
  hE.nullMeasurableSet.exists_mem_iSup_comap_continuousMap_symmDiff_subset_null

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
  classical
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
  -- Assemble the Borel null set `Z'` in `G ⧸ K` collecting the error of `N₀` and all fibers.
  let Z' : Set (G ⧸ K) :=
    B' (Sum.inl ()) ∪ ⋃ (n : ℕ) (b : ↥(s n).range), (B' (Sum.inr ⟨n, b⟩) \ A' (Sum.inr ⟨n, b⟩))
  have hZ'_meas : MeasurableSet[borel (G ⧸ K)] Z' :=
    (hB' (Sum.inl ())).union <|
      MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun b ↦
        (hB' (Sum.inr ⟨n, b⟩)).diff (hA' (Sum.inr ⟨n, b⟩))
  have hB₀_null : μ (π ⁻¹' B' (Sum.inl ())) = 0 := by
    have hA₀ : μ (π ⁻¹' A' (Sum.inl ())) = 0 := measure_mono_null (hpreA' (Sum.inl ())) hN₀_null
    have hsub : π ⁻¹' B' (Sum.inl ()) ⊆
        π ⁻¹' A' (Sum.inl ()) ∪ π ⁻¹' (B' (Sum.inl ()) \ A' (Sum.inl ())) := by
      intro x hx
      by_cases hxA : x ∈ π ⁻¹' A' (Sum.inl ())
      · exact Or.inl hxA
      · exact Or.inr ⟨hx, hxA⟩
    exact measure_mono_null hsub (measure_union_null hA₀ (hnull (Sum.inl ())))
  have hZ'_null : μ (π ⁻¹' Z') = 0 := by
    rw [preimage_union]
    refine measure_union_null hB₀_null ?_
    simp_rw [preimage_iUnion]
    exact measure_iUnion_null fun n ↦ measure_iUnion_null fun b ↦ hnull (Sum.inr ⟨n, b⟩)
  -- Lift the approximating simple functions to `(G ⧸ K, borel (G ⧸ K))`.
  let Aq : ℕ → β → Set (G ⧸ K) := fun n b ↦
    if hb : b ∈ (s n).range then A' (Sum.inr ⟨n, ⟨b, hb⟩⟩) else ∅
  have hAq (n : ℕ) (b : β) : MeasurableSet[borel (G ⧸ K)] (Aq n b) := by
    dsimp only [Aq]
    split_ifs with hb
    · exact hA' (Sum.inr ⟨n, ⟨b, hb⟩⟩)
    · exact @MeasurableSet.empty _ (borel (G ⧸ K))
  obtain ⟨g, hg_meas, hg_eq⟩ := @TauCeti.exists_stronglyMeasurable_of_quotient_fibers
    (G ⧸ K) G β (borel (G ⧸ K)) _ _ π QuotientGroup.mk_surjective (f 1)
    (fun n ↦ (s n).range.toList) Aq hAq Z' hZ'_meas f₀ fun x hxZ' ↦ by
      have hval (n : ℕ) :
          @TauCeti.liftSimpleList (G ⧸ K) β (borel (G ⧸ K)) (Aq n) (hAq n) (f 1)
            (s n).range.toList (π x) = s n x := by
        have hmem : s n x ∈ (s n).range := (s n).mem_range_self x
        refine @TauCeti.liftSimpleList_apply_of_unique (G ⧸ K) β (borel (G ⧸ K)) (Aq n) (hAq n)
          (f 1) (s n).range.toList (π x) (s n x) (Finset.mem_toList.mpr hmem) ?_ ?_
        · simp only [Aq, hmem, dite_true]
          have hxB : π x ∈ B' (Sum.inr ⟨n, ⟨s n x, hmem⟩⟩) :=
            hpreB' (Sum.inr ⟨n, ⟨s n x, hmem⟩⟩) rfl
          by_contra hxA
          exact hxZ' (Or.inr (mem_iUnion₂.mpr ⟨n, ⟨s n x, hmem⟩, hxB, hxA⟩))
        · intro b hb hπb
          have hb_mem : b ∈ (s n).range := Finset.mem_toList.mp hb
          simp only [Aq, hb_mem, dite_true] at hπb
          exact (mem_singleton_iff.mp (hpreA' (Sum.inr ⟨n, ⟨b, hb_mem⟩⟩) hπb)).symm
      simpa [hval] using hf₀.tendsto_approx x
  refine ⟨K, hK_norm, hK_cp, hK_cl, hK_met, hK_sc, g, Z', hg_meas, hZ'_meas, hZ'_null,
    fun x hxZ' ↦ ?_⟩
  have hxN₀ : x ∉ N₀ := fun hxN ↦ hxZ' (Or.inl (hpreB' (Sum.inl ()) hxN))
  have hfx : f x = f₀ x := not_not.mp hxN₀
  rw [hfx, hg_eq x hxZ']

/-- Every `μ`-a.e. strongly measurable function from a σ-compact locally compact group `G` into a
metrizable space is `AEStronglyMeasurable` with respect to the Baire σ-algebra
`⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance`. -/
theorem AEStronglyMeasurable.aestronglyMeasurable_iSup_comap_continuousMap {β : Type*}
    [TopologicalSpace β] [MetrizableSpace β] {f : G → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance] f μ := by
  obtain ⟨K, _, _, _, _, _, g, Z', hg, _, hZ'_null, hfg⟩ :=
    hf.exists_compact_normal_subgroup_quotient_eq_off_null
  have hcomap : MeasurableSpace.comap (QuotientGroup.mk : G → G ⧸ K) (borel (G ⧸ K)) ≤
      ⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance :=
    (QuotientGroup.continuous_mk (N := K)).comap_borel_le_iSup_comap_continuousMap
  have hg_baire :
      StronglyMeasurable[⨆ φ : C(G, ℝ), MeasurableSpace.comap φ inferInstance]
        (g ∘ (QuotientGroup.mk : G → G ⧸ K)) :=
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
