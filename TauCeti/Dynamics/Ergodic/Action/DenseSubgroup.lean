/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Group.AEStabilizer
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Translation by a dense subgroup is ergodic

Let `G` be a locally compact topological group with a left Haar measure `μ`, and let `Γ` be a
dense subgroup of `G`, acting on `G` by left multiplication. This file proves that the action is
ergodic (`TauCeti.ergodicSMul_dense_subgroup` for countable `Γ`): every measurable set that is
invariant up to null sets under left translation by each element of `Γ` is null or conull.
By `ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`, equivalently every `Γ`-invariant
measurable function, in particular every `Γ`-invariant class in `L∞(G, μ)`, is almost everywhere
constant. Neither finiteness of `μ` nor second countability of `G` is assumed: the group may be
noncompact and nonmetrizable, for instance the power of the circle indexed by the reals, which is
separable.

The proof has three steps.

* **The a.e. stabilizer is closed** (`MulAction.isClosed_aestabilizer`). For a continuous
  measure-preserving action of a topological group on a space with a σ-finite locally finite
  measure that is inner regular on sets of finite measure, the elements `g` with `g • s =ᵐ[μ] s`
  form a closed subgroup, whatever the measure of `s`. Mathlib's
  `isClosed_setOfPred_preimage_ae_eq` gives this when `μ s` is finite; here `s` is tested against
  sets `E` of finite measure, using `μ (g • s ∩ E) = μ (s ∩ (g • ·) ⁻¹' E)` and the continuity of
  `g ↦ (g • ·) ⁻¹' E` in measure.
* **Left translation of `G` on itself is ergodic** (`TauCeti.ergodicSMul_self_of_isHaarMeasure`).
  If `s` is invariant up to null sets under every left translation, the restriction `μ.restrict s`
  is a left-invariant measure, so uniqueness of Haar measure makes it a multiple `c • μ`; then `s`
  is null if `c = 0` and conull otherwise. Mathlib's instance for `ErgodicSMul G G μ` instead uses
  Fubini's theorem, so it needs multiplication to be measurable for the product σ-algebra on
  `G × G`, which Mathlib supplies for topological groups only under second countability.
* **Density** (`TauCeti.ergodicSMul_of_dense`). The a.e. stabilizer of a `Γ`-invariant set
  contains `Γ`, so by the first step it is all of `G`, and the second step applies. A countable
  dense subgroup makes `G` separable, hence σ-compact, so every Haar measure on `G` is σ-finite.

As instances, Haar measure on a compact group with a countable dense subgroup and the translation
action of `ℚ` on `ℝ` (`TauCeti.ergodicVAdd_rat_real`) are ergodic.

## Main results

* `MulAction.isClosed_aestabilizer`: the a.e. stabilizer of a set is closed.
* `TauCeti.isMulLeftInvariant_restrict`: restricting a left-invariant measure to an a.e.
  left-invariant set gives a left-invariant measure.
* `TauCeti.ergodicSMul_self_of_isHaarMeasure`: left translation is ergodic for a σ-finite Haar
  measure that is inner regular on sets of finite measure.
* `TauCeti.ergodicSMul_of_dense`, `TauCeti.ergodicSMul_dense_subgroup`: translation by a dense
  subgroup, respectively a countable dense subgroup, is ergodic.
* `TauCeti.ergodicVAdd_rat_real`: translation of `ℝ` by `ℚ` is ergodic for Lebesgue measure.

## References

* V. F. R. Jones, *Von Neumann Algebras*, lecture notes, §11.2, p. 75 (translation by a countable
  dense subgroup of a compact group) and Example 11.2.21, p. 76 (`ℚ` acting on `ℝ`).
-/

public section

open Filter Set MeasureTheory Measure Topology
open scoped Pointwise ENNReal symmDiff

namespace TauCeti

section Closed

variable {G X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [SMulInvariantMeasure G X μ] [μ.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure μ]

/-- If `g` lies in the closure of the a.e. stabilizer of `s`, then `g • s` and `s` meet every
set of finite measure in the same measure. This holds even when `s` has infinite measure. -/
@[to_additive /-- If `g` lies in the closure of the additive a.e. stabilizer of `s`, then
`g +ᵥ s` and `s` meet every set of finite measure in the same measure. This holds even when `s`
has infinite measure. -/]
theorem measure_smul_inter_eq_of_mem_closure_aestabilizer {s E : Set X} {g : G}
    (hg : g ∈ closure (MulAction.aestabilizer G μ s : Set G)) (hE : NullMeasurableSet E μ)
    (hμE : μ E ≠ ∞) : μ (g • s ∩ E) = μ (s ∩ E) := by
  -- Move the translation from `s` onto the finite-measure set `E`.
  have key (h : G) : μ (h • s ∩ E) = μ (s ∩ (h • ·) ⁻¹' E) := by
    rw [← measure_smul μ h (s ∩ _), smul_set_inter, preimage_smul, smul_inv_smul]
  -- Moving `E` changes the measure of `s ∩ E` by at most that of the symmetric difference.
  have le_add (A B : Set X) : μ (s ∩ A) ≤ μ (s ∩ B) + μ (A ∆ B) := by
    refine (measure_mono (show s ∩ A ⊆ s ∩ B ∪ A ∆ B from fun x ⟨hxs, hxA⟩ ↦ ?_)).trans
      (measure_union_le _ _)
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hxs, hxB⟩
    · exact Or.inr (mem_symmDiff.2 (Or.inl ⟨hxA, hxB⟩))
  -- The preimages of `E` under the translations depend continuously on the translation.
  let F : C(G, C(X, X)) := (⟨fun p : G × X ↦ p.1 • p.2, continuous_smul⟩ : C(G × X, X)).curry
  have hF : Tendsto (fun h ↦ μ (((h • ·) ⁻¹' E) ∆ ((g • ·) ⁻¹' E))) (𝓝 g) (𝓝 0) :=
    tendsto_measure_symmDiff_preimage_nhds_zero (f := F) (F.continuous.tendsto g)
      (.of_forall fun h ↦ measurePreserving_smul h μ) (measurePreserving_smul g μ) hE hμE
  -- For every `ε > 0` there is an element of the a.e. stabilizer moving `E` by less than `ε`.
  have approx (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ h ∈ MulAction.aestabilizer G μ s,
      μ (((h • ·) ⁻¹' E) ∆ ((g • ·) ⁻¹' E)) < ε :=
    ((mem_closure_iff_frequently.1 hg).and_eventually (hF.eventually (gt_mem_nhds hε))).exists
  -- On the a.e. stabilizer the translated measure is `μ (s ∩ E)`.
  have hstab {h : G} (hh : h ∈ MulAction.aestabilizer G μ s) :
      μ (s ∩ (h • ·) ⁻¹' E) = μ (s ∩ E) := by
    rw [← key]
    exact measure_congr ((MulAction.mem_aestabilizer.1 hh).inter (.refl _ _ : E =ᵐ[μ] E))
  rw [key]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
  · obtain ⟨h, hh, hlt⟩ := approx ε (by exact_mod_cast hε)
    calc μ (s ∩ (g • ·) ⁻¹' E)
        ≤ μ (s ∩ (h • ·) ⁻¹' E) + μ (((g • ·) ⁻¹' E) ∆ ((h • ·) ⁻¹' E)) := le_add _ _
      _ ≤ μ (s ∩ E) + ε := by
        rw [hstab hh, symmDiff_comm]
        gcongr
  · obtain ⟨h, hh, hlt⟩ := approx ε (by exact_mod_cast hε)
    calc μ (s ∩ E) = μ (s ∩ (h • ·) ⁻¹' E) := (hstab hh).symm
      _ ≤ μ (s ∩ (g • ·) ⁻¹' E) + μ (((h • ·) ⁻¹' E) ∆ ((g • ·) ⁻¹' E)) := le_add _ _
      _ ≤ μ (s ∩ (g • ·) ⁻¹' E) + ε := by gcongr

/-- **The a.e. stabilizer of a set is closed.** For a continuous measure-preserving action of a
topological group on an R₁ space with a σ-finite locally finite measure that is inner regular on
sets of finite measure, the elements `g` with `g • s =ᵐ[μ] s` form a closed subgroup. The set `s`
may have infinite measure; compare `isClosed_setOfPred_preimage_ae_eq`, which needs `μ s ≠ ∞`. -/
@[to_additive /-- **The additive a.e. stabilizer of a set is closed.** For a continuous
measure-preserving additive action of a topological additive group on an R₁ space with a σ-finite
locally finite measure that is inner regular on sets of finite measure, the elements `g` with
`g +ᵥ s =ᵐ[μ] s` form a closed subgroup, whatever the measure of `s`. -/]
theorem _root_.MulAction.isClosed_aestabilizer [SigmaFinite μ] {s : Set X}
    (hs : NullMeasurableSet s μ) : IsClosed (MulAction.aestabilizer G μ s : Set G) := by
  refine closure_subset_iff_isClosed.1 fun g hg ↦ ?_
  have ht : NullMeasurableSet (g • s) μ := hs.smul g
  have key {E : Set X} (hE : NullMeasurableSet E μ) (hμE : μ E ≠ ∞) :
      μ (g • s ∩ E) = μ (s ∩ E) :=
    measure_smul_inter_eq_of_mem_closure_aestabilizer hg hE hμE
  -- Two sets meeting every set of finite measure in the same measure are a.e. equal.
  have diff_null {u v : Set X} (hu : NullMeasurableSet u μ) (hv : NullMeasurableSet v μ)
      (huv : ∀ E, NullMeasurableSet E μ → μ E ≠ ∞ → μ (u ∩ E) = μ (v ∩ E)) :
      μ (u \ v) = 0 := by
    rw [← inter_univ (u \ v), ← iUnion_spanningSets μ, inter_iUnion]
    refine measure_iUnion_null fun n ↦ ?_
    have hE : NullMeasurableSet ((u \ v) ∩ spanningSets μ n) μ :=
      (hu.diff hv).inter (measurableSet_spanningSets μ n).nullMeasurableSet
    have hμE : μ ((u \ v) ∩ spanningSets μ n) ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
    have hu' : u ∩ ((u \ v) ∩ spanningSets μ n) = (u \ v) ∩ spanningSets μ n :=
      inter_eq_right.2 fun x hx ↦ hx.1.1
    have hv' : v ∩ ((u \ v) ∩ spanningSets μ n) = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hx.2.1.2 hx.1
    rw [← hu', huv _ hE hμE, hv', measure_empty]
  refine ae_eq_set.2 ⟨diff_null ht hs fun E hE hμE ↦ key hE hμE,
    diff_null hs ht fun E hE hμE ↦ (key hE hμE).symm⟩

end Closed

section Restrict

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- Restricting a left-invariant measure to a set that is invariant up to null sets under every
left translation gives a left-invariant measure. -/
@[to_additive /-- Restricting an additive left-invariant measure to a set that is invariant up to
null sets under every left translation gives an additive left-invariant measure. -/]
theorem isMulLeftInvariant_restrict (μ : Measure G) [μ.IsMulLeftInvariant] {s : Set G}
    (hs : MeasurableSet s) (h : ∀ g : G, g • s =ᵐ[μ] s) : (μ.restrict s).IsMulLeftInvariant := by
  refine ⟨fun g ↦ ?_⟩
  have hpre : (g * ·) ⁻¹' s =ᵐ[μ] s := by
    simpa only [← smul_eq_mul, preimage_smul] using h g⁻¹
  have hmap := ((measurePreserving_mul_left μ g).restrict_preimage hs).map_eq
  rwa [restrict_congr_set hpre] at hmap

end Restrict

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]
  [SigmaFinite μ]

/-- **Left translation of a locally compact group on itself is ergodic** for every σ-finite Haar
measure that is inner regular on sets of finite measure. Unlike Mathlib's instance for
`ErgodicSMul G G μ`, this needs no measurability of multiplication on `G × G`, hence no second
countability: the proof applies uniqueness of Haar measure to the restriction of `μ` to an
invariant set instead of Fubini's theorem. -/
@[to_additive /-- **Translation of a locally compact additive group on itself is ergodic** for
every σ-finite additive Haar measure that is inner regular on sets of finite measure, with no
measurability assumption on addition on `G × G`. -/]
instance (priority := 100) ergodicSMul_self_of_isHaarMeasure : ErgodicSMul G G μ := by
  refine ⟨fun {s} hs h ↦ ?_⟩
  have hinv (g : G) : g • s =ᵐ[μ] s := by simpa only [preimage_smul_inv] using h g⁻¹
  have := isMulLeftInvariant_restrict μ hs hinv
  -- On compact sets `μ.restrict s` is `c • μ` for the Haar scalar factor `c`.
  have hK {K : Set G} (hK : IsCompact K) :
      μ (K ∩ s) = haarScalarFactor (μ.restrict s) μ * μ K := by
    rw [← restrict_apply' hs]
    exact measure_isMulLeftInvariant_eq_smul_of_ne_top (μ.restrict s) μ
      hK.measure_lt_top.ne hK.measure_lt_top.ne
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ]
  by_cases hc : haarScalarFactor (μ.restrict s) μ = 0
  · -- `s` carries no mass on compact sets, so it is null by inner regularity.
    left
    rw [hs.measure_eq_iSup_isCompact]
    refine ENNReal.iSup_eq_zero.2 fun K ↦ ENNReal.iSup_eq_zero.2 fun hKs ↦
      ENNReal.iSup_eq_zero.2 fun hKc ↦ ?_
    rw [← inter_eq_left.2 hKs, hK hKc, hc, ENNReal.coe_zero, zero_mul]
  · -- The complement of `s` carries no mass on compact sets, so it is null.
    right
    rw [hs.compl.measure_eq_iSup_isCompact]
    refine ENNReal.iSup_eq_zero.2 fun K ↦ ENNReal.iSup_eq_zero.2 fun hKs ↦
      ENNReal.iSup_eq_zero.2 fun hKc ↦ ?_
    have h0 : μ (K ∩ s) = 0 := by
      rw [disjoint_iff_inter_eq_empty.1 (subset_compl_iff_disjoint_right.1 hKs), measure_empty]
    rw [hK hKc] at h0
    exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hc)

/-- **Translation by a dense subgroup is ergodic.** If `Γ` is a dense subgroup of a locally
compact group `G` with a σ-finite Haar measure `μ` that is inner regular on sets of finite
measure, then the action of `Γ` on `G` by left multiplication is ergodic. -/
@[to_additive /-- **Translation by a dense additive subgroup is ergodic.** If `Γ` is a dense
additive subgroup of a locally compact additive group `G` with a σ-finite additive Haar measure
`μ` that is inner regular on sets of finite measure, then the action of `Γ` on `G` by translation
is ergodic. -/]
theorem ergodicSMul_of_dense (Γ : Subgroup G) (hΓ : Dense (Γ : Set G)) :
    ErgodicSMul Γ G μ := by
  refine ⟨fun {s} hs h ↦ ?_⟩
  have hle : Γ ≤ MulAction.aestabilizer G μ s := fun g hg ↦ by
    simpa only [MulAction.mem_aestabilizer, Subgroup.smul_def, InvMemClass.coe_inv,
      preimage_smul_inv] using h ⟨g, hg⟩⁻¹
  have htop' : MulAction.aestabilizer G μ s = ⊤ := by
    refine eq_top_iff.2 fun g _ ↦ ?_
    refine (MulAction.isClosed_aestabilizer hs.nullMeasurableSet).closure_subset_iff.2 hle ?_
    rw [hΓ.closure_eq]
    exact mem_univ g
  exact MulAction.aeconst_of_aestabilizer_eq_top G hs.nullMeasurableSet htop'

omit [SigmaFinite μ] in
/-- **Translation by a countable dense subgroup is ergodic.** If `Γ` is a countable dense subgroup
of a locally compact group `G` and `μ` is a Haar measure on `G` that is inner regular on sets of
finite measure (for instance a regular Haar measure), then the action of `Γ` on `G` by left
multiplication is ergodic. No second countability of `G` and no finiteness of `μ` is assumed:
`G` is separable, hence σ-compact, so `μ` is σ-finite. -/
@[to_additive /-- **Translation by a countable dense additive subgroup is ergodic.** If `Γ` is a
countable dense additive subgroup of a locally compact additive group `G` and `μ` is an additive
Haar measure on `G` that is inner regular on sets of finite measure, then the action of `Γ` on `G`
by translation is ergodic. -/]
theorem ergodicSMul_dense_subgroup (Γ : Subgroup G) [Countable Γ] (hΓ : Dense (Γ : Set G)) :
    ErgodicSMul Γ G μ := by
  have : TopologicalSpace.SeparableSpace G := ⟨⟨Γ, Set.countable_coe_iff.1 ‹_›, hΓ⟩⟩
  exact ergodicSMul_of_dense μ Γ hΓ

end Haar

/-- **Translation of `ℝ` by `ℚ` is ergodic** for Lebesgue measure: every measurable set of reals
that is invariant up to null sets under all rational translations is null or conull. -/
theorem ergodicVAdd_rat_real : ErgodicVAdd (Rat.castHom ℝ).toAddMonoidHom.range ℝ volume := by
  have hrange : ((Rat.castHom ℝ).toAddMonoidHom.range : Set ℝ) = range ((↑) : ℚ → ℝ) :=
    AddMonoidHom.coe_range _
  have : Countable (Rat.castHom ℝ).toAddMonoidHom.range :=
    Set.countable_coe_iff.2 (hrange ▸ countable_range _)
  exact ergodicVAdd_dense_addSubgroup volume _ (hrange ▸ Rat.denseRange_cast)

end TauCeti
