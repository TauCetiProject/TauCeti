/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Algebra.Order.Archimedean
public import TauCeti.MeasureTheory.Group.AEStabilizer
public import TauCeti.MeasureTheory.Group.Measure

/-!
# Translation by a dense subgroup is ergodic

Let `G` be a locally compact topological group with a left Haar measure `μ`, and let `Γ` be a
dense subgroup of `G`, acting on `G` by left multiplication. This file proves that the action is
ergodic (`Subgroup.ergodicSMul_dense_subgroup` for countable `Γ`): every measurable set that is
invariant up to null sets under left translation by each element of `Γ` is null or conull.
Consequently, by `ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`, every `Γ`-invariant
null-measurable function into a countably separated space (for instance `ℝ` or `ℂ`), in
particular every `Γ`-invariant class in `L∞(G, μ)`, is almost everywhere constant. Neither
finiteness of `μ` nor second countability of `G` is assumed. For instance the power of the circle
indexed by the reals is compact, nonmetrizable and separable, and its product with `ℝ` is
noncompact, nonmetrizable and separable; both have countable dense subgroups.

The proof has three steps.

* **The a.e. stabilizer is closed** (`TauCeti.isClosed_aestabilizer`). For a continuous
  measure-preserving action of a topological group on a space with a σ-finite locally finite
  measure that is inner regular on sets of finite measure, the elements `g` with `g • s =ᵐ[μ] s`
  form a closed subgroup, whatever the measure of `s`.
* **Left translation of `G` on itself is ergodic**
  (`MeasureTheory.Measure.ergodicSMul_self_of_isHaarMeasure`). If `s` is invariant up to null
  sets under every left translation, the restriction `μ.restrict s` is a left-invariant measure
  (`MeasureTheory.Measure.isMulLeftInvariant_restrict`), so uniqueness of Haar measure makes it a
  multiple `c • μ`; then `s` is null if `c = 0` and conull otherwise.
  Mathlib's instance for `ErgodicSMul G G μ` instead uses Fubini's theorem, so it needs
  multiplication to be measurable for the product σ-algebra on `G × G`, which Mathlib supplies for
  topological groups only under second countability.
* **Density** (`Subgroup.ergodicSMul_of_dense`). For any ergodic action of `G` on a space `X` as in
  the first step, the a.e. stabilizer of a `Γ`-invariant set contains `Γ`, so by the first step it
  is all of `G`, and the set is null or conull. The second step supplies the ergodic action of `G`
  on itself. A countable dense subgroup makes `G` separable, hence σ-compact, so every Haar measure
  on `G` is σ-finite.

As instances, Haar measure on a compact group with a countable dense subgroup and the translation
action of `ℚ` on `ℝ` (`TauCeti.ergodicVAdd_rat_real`) are ergodic.

## Main results

* `MeasureTheory.Measure.ergodicSMul_self_of_isHaarMeasure`: left translation is ergodic for a
  σ-finite Haar measure that is inner regular on sets of finite measure.
* `Subgroup.ergodicSMul_of_dense`: if `G` acts ergodically on `X`, so does every dense subgroup.
* `Subgroup.ergodicSMul_dense_subgroup`: translation by a countable dense subgroup of a locally
  compact group is ergodic.
* `TauCeti.ergodicVAdd_rat_real`: translation of `ℝ` by `ℚ` is ergodic for Lebesgue measure.

## References

* V. F. R. Jones, *Von Neumann Algebras*, lecture notes, §11.2, p. 75 (translation by a countable
  dense subgroup of a compact group) and Example 11.2.21, p. 76 (`ℚ` acting on `ℝ`).
-/

public section

open Filter Set MeasureTheory Measure Topology
open scoped Pointwise ENNReal

section Dense

variable {G X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [SigmaFinite μ]
  [ErgodicSMul G X μ]

/-- **A dense subgroup of an ergodic group acts ergodically.** If a topological group `G` acts
continuously and ergodically on an R₁ space with a σ-finite locally finite measure that is inner
regular on sets of finite measure, then every dense subgroup `Γ` of `G` acts ergodically. -/
@[to_additive /-- **A dense additive subgroup of an ergodic additive group acts ergodically.** If
a topological additive group `G` acts continuously and ergodically on an R₁ space with a σ-finite
locally finite measure that is inner regular on sets of finite measure, then every dense additive
subgroup `Γ` of `G` acts ergodically. -/]
theorem Subgroup.ergodicSMul_of_dense (Γ : Subgroup G) (hΓ : Dense (Γ : Set G)) :
    ErgodicSMul Γ X μ := by
  refine ⟨fun {s} hs h ↦ ?_⟩
  have hle : Γ ≤ MulAction.aestabilizer G μ s := fun g hg ↦ by
    simpa only [MulAction.mem_aestabilizer, Subgroup.smul_def, InvMemClass.coe_inv,
      preimage_smul_inv] using h ⟨g, hg⟩⁻¹
  refine MulAction.aeconst_of_aestabilizer_eq_top G hs.nullMeasurableSet (eq_top_iff.2 ?_)
  refine fun g _ ↦
    (TauCeti.isClosed_aestabilizer hs.nullMeasurableSet).closure_subset_iff.2 hle ?_
  rw [hΓ.closure_eq]
  exact mem_univ g

end Dense

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
instance (priority := 100) MeasureTheory.Measure.ergodicSMul_self_of_isHaarMeasure :
    ErgodicSMul G G μ := by
  refine ⟨fun {s} hs h ↦ ?_⟩
  have hinv (g : G) : g • s =ᵐ[μ] s := by simpa only [preimage_smul_inv] using h g⁻¹
  have := isMulLeftInvariant_restrict μ hinv
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
    by_contra hne
    obtain ⟨K, hKs, hKc, hpos⟩ := hs.exists_lt_isCompact (pos_iff_ne_zero.2 hne)
    rw [← inter_eq_left.2 hKs, hK hKc, hc, ENNReal.coe_zero, zero_mul] at hpos
    exact hpos.false
  · -- The complement of `s` carries no mass on compact sets, so it is null.
    right
    by_contra hne
    obtain ⟨K, hKs, hKc, hpos⟩ := hs.compl.exists_lt_isCompact (pos_iff_ne_zero.2 hne)
    have h0 : μ (K ∩ s) = 0 := by
      rw [disjoint_iff_inter_eq_empty.1 (subset_compl_iff_disjoint_right.1 hKs), measure_empty]
    rw [hK hKc] at h0
    exact hpos.ne' ((mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hc))

omit [SigmaFinite μ] in
variable {μ} in
/-- **Translation by a countable dense subgroup is ergodic.** If `Γ` is a countable dense subgroup
of a locally compact group `G` and `μ` is a Haar measure on `G` that is inner regular on sets of
finite measure (for instance a regular Haar measure), then the action of `Γ` on `G` by left
multiplication is ergodic. No second countability of `G` and no finiteness of `μ` is assumed:
`G` is separable, hence σ-compact, so `μ` is σ-finite. -/
@[to_additive /-- **Translation by a countable dense additive subgroup is ergodic.** If `Γ` is a
countable dense additive subgroup of a locally compact additive group `G` and `μ` is an additive
Haar measure on `G` that is inner regular on sets of finite measure, then the action of `Γ` on `G`
by translation is ergodic. -/]
theorem Subgroup.ergodicSMul_dense_subgroup (Γ : Subgroup G) [Countable Γ]
    (hΓ : Dense (Γ : Set G)) :
    ErgodicSMul Γ G μ := by
  have : TopologicalSpace.SeparableSpace G := ⟨⟨Γ, Set.countable_coe_iff.1 ‹_›, hΓ⟩⟩
  exact Γ.ergodicSMul_of_dense hΓ

end Haar

namespace TauCeti

/-- **Translation of `ℝ` by `ℚ` is ergodic** for Lebesgue measure: every measurable set of reals
that is invariant up to null sets under all rational translations is null or conull. -/
theorem ergodicVAdd_rat_real : ErgodicVAdd (Rat.castHom ℝ).toAddMonoidHom.range ℝ volume := by
  have hrange : ((Rat.castHom ℝ).toAddMonoidHom.range : Set ℝ) = range ((↑) : ℚ → ℝ) :=
    AddMonoidHom.coe_range _
  have : Countable (Rat.castHom ℝ).toAddMonoidHom.range :=
    Set.countable_coe_iff.2 (hrange ▸ countable_range _)
  exact AddSubgroup.ergodicVAdd_dense_addSubgroup _ (hrange ▸ Rat.denseRange_cast)

end TauCeti
