/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.WithDensity
-- Proof-only: right translation of an inner regular Haar measure scales by the modular character.
import Mathlib.MeasureTheory.Group.ModularCharacter
-- Proof-only: change of variables in set integrals along a measurable embedding.
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import TauCeti.MeasureTheory.Group.Arithmetic
-- Proof-only: pushing a measure forward along a measurable embedding.
import TauCeti.MeasureTheory.Measure.AEMeasurable

/-!
# Measures and the group operations

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells. Dually, a set that each point sees
in only boundedly many of infinitely many translates inside a subgroup of finite measure is null
in that subgroup; over a local field this shows without Fubini's theorem that a set meeting every
line of a fixed direction in boundedly many points is null. It also records that inverting or
negating a probability measure gives a probability measure, so that the law of `X⁻¹` or `-X` can
be used wherever a probability law is expected, that pulling a left- or right-invariant measure
back along a group homomorphism, in particular to a subgroup, keeps it left- or right-invariant
without any measurability hypotheses (for subgroups as typeclass instances), and that restricting
an inversion-invariant measure to a symmetric set, or weighting it by an even density, keeps it
inversion-invariant. Finally, for an inner regular measure whose right translations are
quasi-measure-preserving—in particular any inner regular Haar measure on a locally compact
group—if an open set `U` lies up to a null set inside a null-measurable set `V` satisfying
`V * s ⊆ V`, then `U * s` (such as the subgroup saturation
`(QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' U) = U * N`) also lies in `V` up to a
null set.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
* `Measure.measure_inter_addSubgroup_eq_zero_of_encard_le`: if `x + w j ∈ Z` holds for at most
  `D` indices `j`, for every `x`, where the translations `w j` range over infinitely many indices
  in a subgroup `H` of finite measure, then `Z ∩ H` is null.
* `Measure.isProbabilityMeasure_inv`, `Measure.isProbabilityMeasure_neg`: the inverse and the
  negation of a probability measure are probability measures.
* `Measure.map_inv_comp`, `Measure.map_neg_comp`: composing a pushforward from the inverted or
  negated measure with inversion or negation recovers the original pushforward.
* `Measure.ae_inv_mem_preimage`, `Measure.ae_neg_mem_preimage`: a full-mass set reflects to a
  full-mass set for the inverted or negated measure.
* `Measure.isInvInvariant_restrict`, `Measure.isNegInvariant_restrict`,
  `Measure.isInvInvariant_withDensity`, `Measure.isNegInvariant_withDensity`: restriction to a
  symmetric set and an even density preserve inversion or negation invariance.
* `Measure.isMulLeftInvariant_comap`, `Measure.isAddLeftInvariant_comap`,
  `Measure.isMulRightInvariant_comap`, `Measure.isAddRightInvariant_comap`: the pullback of a
  left- or right-invariant measure along a group homomorphism is left- or right-invariant, without
  measurability hypotheses on the homomorphism.
* `Measure.isMulLeftInvariant_comap_subtype`, `Measure.isAddLeftInvariant_comap_subtype`,
  `Measure.isMulRightInvariant_comap_subtype`, `Measure.isAddRightInvariant_comap_subtype`: the
  instances for the pullback of an invariant measure to a subgroup, without measurability
  hypotheses on the subgroup.
* `IsOpen.measure_mul_sdiff_eq_zero_of_quasiMeasurePreserving`,
  `IsOpen.measure_add_sdiff_eq_zero_of_quasiMeasurePreserving`,
  `IsOpen.measure_mul_sdiff_eq_zero`, `IsOpen.measure_add_sdiff_eq_zero`: if an open set `U` has
  `μ (U \ V) = 0` for a `μ`-null-measurable set `V` invariant under right multiplication (or
  addition) by `s`, then `μ ((U * s) \ V) = 0` (or `μ ((U + s) \ V) = 0`) for any inner regular
  measure with quasi-measure-preserving right translations, and in particular for any inner
  regular Haar measure on a locally compact group.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem _root_.MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h]
      exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
    have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
    rw [h, measure_preimage_add_right]
  simp_rw [htranslate]
  simp

/-- A set that every point sees in boundedly many translates is null inside a subgroup of finite
measure. Precisely, let `w : ι → E` be a family, indexed by an infinite type, of elements of a
measurable subgroup `H` of finite measure, and suppose that for every `x` at most `D` indices `j`
have `x + w j ∈ Z`. Then `Z ∩ H` is null for every right-invariant measure. -/
theorem _root_.MeasureTheory.Measure.measure_inter_addSubgroup_eq_zero_of_encard_le
    {ι : Type*} [Infinite ι] (μ : Measure E) [μ.IsAddRightInvariant] {Z : Set E}
    (hZ : MeasurableSet Z) {H : AddSubgroup E} (hH : MeasurableSet (H : Set E))
    (hμH : μ H ≠ ∞) {w : ι → E} (hw : ∀ j, w j ∈ H) {D : ℕ}
    (hD : ∀ x, {j | x + w j ∈ Z}.encard ≤ D) :
    μ (Z ∩ H) = 0 := by
  classical
  have hZH : MeasurableSet (Z ∩ H) := hZ.inter hH
  -- The translates `(· + w j) ⁻¹' (Z ∩ H)` all have the measure of `Z ∩ H` and lie in `H`, and no
  -- point lies in more than `D` of them. Integrating the number of them containing `x`, for `j` in
  -- a finite set `s`, bounds `#s` copies of `μ (Z ∩ H)` by `D` copies of `μ H`.
  have key (s : Finset ι) : (s.card : ℝ≥0∞) * μ (Z ∩ H) ≤ D * μ H := by
    calc (s.card : ℝ≥0∞) * μ (Z ∩ H)
        = ∑ j ∈ s, μ ((· + w j) ⁻¹' (Z ∩ H)) := by
          rw [Finset.sum_congr rfl fun j _ ↦ measure_preimage_add_right μ (w j) (Z ∩ H)]
          simp
      _ = ∫⁻ x, ∑ j ∈ s, ((· + w j) ⁻¹' (Z ∩ H)).indicator 1 x ∂μ := by
          rw [lintegral_finsetSum _ fun j _ ↦
            (measurable_one.indicator (measurable_add_const (w j) hZH))]
          simp_rw [lintegral_indicator_one (measurable_add_const _ hZH)]
      _ ≤ ∫⁻ x, (H : Set E).indicator (fun _ ↦ (D : ℝ≥0∞)) x ∂μ := by
          refine lintegral_mono fun x ↦ ?_
          by_cases hx : x ∈ H
          · rw [indicator_of_mem hx]
            calc ∑ j ∈ s, ((· + w j) ⁻¹' (Z ∩ H)).indicator 1 x
                = ((s.filter fun j ↦ x + w j ∈ Z ∩ H).card : ℝ≥0∞) := by
                  simp [indicator_apply, Finset.sum_boole]
              _ ≤ D := by
                  have := (encard_le_encard (s := ↑(s.filter fun j ↦ x + w j ∈ Z ∩ H))
                    (t := {j | x + w j ∈ Z}) fun j hj ↦ by
                      simp only [Finset.coe_filter, mem_ofPred_eq] at hj
                      exact hj.2.1).trans (hD x)
                  rw [encard_coe_eq_coe_finsetCard] at this
                  exact_mod_cast this
          · rw [indicator_of_notMem hx]
            refine (Finset.sum_eq_zero fun j _ ↦ indicator_of_notMem ?_ _).le
            exact fun h ↦ hx ((H.add_mem_cancel_right (hw j)).mp h.2)
      _ = D * μ H := lintegral_indicator_const hH _
  by_contra h0
  have htop : (D : ℝ≥0∞) * μ H / μ (Z ∩ H) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hμH) h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt htop
  obtain ⟨s, rfl⟩ := Infinite.exists_subset_card_eq ι N
  exact ((ENNReal.le_div_iff_mul_le (Or.inl h0)
    (Or.inl (ne_top_of_le_ne_top hμH (measure_mono inter_subset_right)))).mpr (key s)).not_gt hN

end TauCeti

namespace MeasureTheory.Measure

/-- **The pullback of a left-invariant measure along a group homomorphism is left-invariant**,
without any measurability assumption on the homomorphism: if the pullback is undefined, it is the
zero measure. -/
@[to_additive /-- **The pullback of a left-invariant measure along an additive group homomorphism
is left-invariant**, without any measurability assumption on the homomorphism: if the pullback is
undefined, it is the zero measure. -/]
theorem isMulLeftInvariant_comap {G H F : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group H] [MeasurableSpace H] [MeasurableMul H] [FunLike F G H] [MonoidHomClass F G H]
    (μ : Measure H) [μ.IsMulLeftInvariant] (f : F) : (μ.comap f).IsMulLeftInvariant := by
  -- Adapted from Mathlib's `Measure.IsMulLeftInvariant.comap` (the image/preimage identity and
  -- the invariance computation); the new case is the undefined pullback, which is the zero
  -- measure and so trivially invariant.
  refine ⟨fun h ↦ ?_⟩
  by_cases hc : Function.Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [Measure.map_apply (by fun_prop) hs,
      Measure.comap_apply₀ _ _ hc.1 hc.2 (hs.preimage (by fun_prop)).nullMeasurableSet,
      Measure.comap_apply₀ _ _ hc.1 hc.2 hs.nullMeasurableSet]
    have himg : f '' ((h * ·) ⁻¹' s) = (f h * ·) ⁻¹' (f '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h * y, hy, by simp⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨h⁻¹ * y, by simpa using hy, by simp [hyx]⟩
    rw [himg, measure_preimage_mul]
  · rw [Measure.comap_undef hc, Measure.map_zero]

/-- **The pullback of a right-invariant measure along a group homomorphism is right-invariant**,
without any measurability assumption on the homomorphism: if the pullback is undefined, it is the
zero measure. -/
@[to_additive /-- **The pullback of a right-invariant measure along an additive group homomorphism
is right-invariant**, without any measurability assumption on the homomorphism: if the pullback is
undefined, it is the zero measure. -/]
theorem isMulRightInvariant_comap {G H F : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group H] [MeasurableSpace H] [MeasurableMul H] [FunLike F G H] [MonoidHomClass F G H]
    (μ : Measure H) [μ.IsMulRightInvariant] (f : F) : (μ.comap f).IsMulRightInvariant := by
  -- Adapted from Mathlib's `Measure.IsMulRightInvariant.comap`, as for
  -- `isMulLeftInvariant_comap` above.
  refine ⟨fun h ↦ ?_⟩
  by_cases hc : Function.Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [Measure.map_apply (by fun_prop) hs,
      Measure.comap_apply₀ _ _ hc.1 hc.2 (hs.preimage (by fun_prop)).nullMeasurableSet,
      Measure.comap_apply₀ _ _ hc.1 hc.2 hs.nullMeasurableSet]
    have himg : f '' ((· * h) ⁻¹' s) = (· * f h) ⁻¹' (f '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * h, hy, by simp⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨y * h⁻¹, by simpa using hy, by simp [hyx]⟩
    rw [himg, measure_preimage_mul_right]
  · rw [Measure.comap_undef hc, Measure.map_zero]

/-- **The pullback of a left-invariant measure to a subgroup is left-invariant**, without any
measurability assumption on the subgroup. -/
@[to_additive /-- **The pullback of a left-invariant measure to an additive subgroup is
left-invariant**, without any measurability assumption on the subgroup. -/]
instance isMulLeftInvariant_comap_subtype {G S : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [SetLike S G] [SubgroupClass S G] (H : S) (μ : Measure G)
    [μ.IsMulLeftInvariant] : (μ.comap ((↑) : H → G)).IsMulLeftInvariant :=
  isMulLeftInvariant_comap μ (SubgroupClass.subtype H)

/-- **The pullback of a right-invariant measure to a subgroup is right-invariant**, without any
measurability assumption on the subgroup. -/
@[to_additive /-- **The pullback of a right-invariant measure to an additive subgroup is
right-invariant**, without any measurability assumption on the subgroup. -/]
instance isMulRightInvariant_comap_subtype {G S : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [SetLike S G] [SubgroupClass S G] (H : S) (μ : Measure G)
    [μ.IsMulRightInvariant] : (μ.comap ((↑) : H → G)).IsMulRightInvariant :=
  isMulRightInvariant_comap μ (SubgroupClass.subtype H)

/-- The inverse of a probability measure is a probability measure. -/
@[to_additive /-- The negation of a probability measure is a probability measure. -/]
instance isProbabilityMeasure_inv {G : Type*} [MeasurableSpace G] [Inv G] (μ : Measure G)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure μ.inv := by
  rw [inv_def]
  infer_instance

/-- Pushing an inverted measure forward along `f` after inversion gives the pushforward of the
original measure along `f`. -/
@[to_additive /-- Pushing a negated measure forward along `f` after negation gives the pushforward
of the original measure along `f`. -/]
theorem map_inv_comp {G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [InvolutiveInv G]
    [MeasurableInv G] (μ : Measure G) {f : G → H} :
    μ.inv.map (f ∘ Inv.inv) = μ.map f := by
  have h : (μ.inv.map Inv.inv).map f = μ.inv.map (f ∘ Inv.inv) :=
    measurableEmbedding_inv.map_map_measure μ.inv f
  rw [← inv_def, Measure.inv_inv] at h
  exact h.symm

/-- A set of full measure reflects to a set of full measure for the inverted measure. -/
@[to_additive /-- A set of full measure reflects to a set of full measure for the negated
measure. -/]
theorem ae_inv_mem_preimage {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G]
    (μ : Measure G) {s : Set G} (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ.inv, x ∈ Inv.inv ⁻¹' s := by
  have he : MeasurableEmbedding (Inv.inv : G → G) := (MeasurableEquiv.inv G).measurableEmbedding
  rw [inv_def, he.ae_map_iff]
  simpa only [Set.mem_preimage, inv_inv] using hμs

section InvolutiveInv

variable {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] {μ : Measure G}

/-- The restriction of an inversion-invariant measure to a set closed under inversion is
inversion-invariant. -/
@[to_additive /-- The restriction of a negation-invariant measure to a set closed under negation
is negation-invariant. -/]
theorem isInvInvariant_restrict [μ.IsInvInvariant] {s : Set G} (hs : s⁻¹ = s) :
    (μ.restrict s).IsInvInvariant := by
  refine ⟨Measure.ext fun t ht ↦ ?_⟩
  rw [inv_apply, restrict_apply ht.inv, restrict_apply ht, ← measure_inv μ, Set.inter_inv,
    inv_inv, hs]

/-- An inversion-invariant measure weighted by a density invariant under inversion is
inversion-invariant. -/
@[to_additive /-- A negation-invariant measure weighted by an even density is
negation-invariant. -/]
theorem isInvInvariant_withDensity [μ.IsInvInvariant] {f : G → ℝ≥0∞} (hf : ∀ x, f x⁻¹ = f x) :
    (μ.withDensity f).IsInvInvariant := by
  refine ⟨Measure.ext fun t ht ↦ ?_⟩
  rw [inv_apply, withDensity_apply _ ht.inv, withDensity_apply _ ht, ← Set.inv_preimage]
  simpa only [hf] using (measurePreserving_inv μ).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.inv G).measurableEmbedding f t

end InvolutiveInv

end MeasureTheory.Measure

section MulSdiff

/-- On a group with continuous multiplication and measurable open sets, if `U` is open, `V` is
`μ`-null-measurable with `V * s ⊆ V`, right multiplication by `g⁻¹` is quasi-measure-preserving for
an inner regular measure `μ` for every `g ∈ s`, and `μ (U \ V) = 0`, then `μ ((U * s) \ V) = 0`. -/
@[to_additive /-- On an additive group with continuous addition and measurable open sets, if `U` is
open, `V` is `μ`-null-measurable with `V + s ⊆ V`, right addition by `-g` is
quasi-measure-preserving for an inner regular measure `μ` for every `g ∈ s`, and `μ (U \ V) = 0`,
then `μ ((U + s) \ V) = 0`. -/]
theorem IsOpen.measure_mul_sdiff_eq_zero_of_quasiMeasurePreserving
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {μ : Measure G} [μ.InnerRegular]
    {U V s : Set G} (hU : IsOpen U) (hV : NullMeasurableSet V μ) (hVs : V * s ⊆ V)
    (hqmp : ∀ g ∈ s, QuasiMeasurePreserving (· * g⁻¹) μ μ) (hUV : μ (U \ V) = 0) :
    μ ((U * s) \ V) = 0 := by
  by_contra hne
  obtain ⟨E, hEWV, hEm, hEae⟩ :=
    (hU.mul_right.measurableSet.nullMeasurableSet.diff hV).exists_measurable_subset_ae_eq
  obtain ⟨K, hKE, hK, hKpos⟩ :=
    hEm.exists_lt_isCompact (pos_iff_ne_zero.2 ((measure_congr hEae).trans_ne hne))
  have hKWV : K ⊆ (U * s) \ V := hKE.trans hEWV
  have hKcov : K ⊆ ⋃ g : s, (· * (g : G)⁻¹) ⁻¹' U := fun x hx ↦ by
    obtain ⟨u, hu, g, hg, rfl⟩ := mem_mul.1 (hKWV hx).1
    exact mem_iUnion.2 ⟨⟨g, hg⟩, by simpa using hu⟩
  obtain ⟨t, htK⟩ := hK.elim_finite_subcover (fun g : s ↦ (· * (g : G)⁻¹) ⁻¹' U)
    (fun g ↦ hU.preimage (continuous_mul_const _)) hKcov
  have hKsub : K ⊆ ⋃ g : t, (· * ((g : s) : G)⁻¹) ⁻¹' (U \ V) := fun x hx ↦ by
    obtain ⟨g, hgt, hxgU⟩ := mem_iUnion₂.1 (htK hx)
    exact mem_iUnion.2 ⟨⟨g, hgt⟩, hxgU,
      fun hxgV ↦ (hKWV hx).2 (by simpa using hVs (mul_mem_mul hxgV g.2))⟩
  have hKzero : μ K = 0 :=
    measure_mono_null hKsub (measure_iUnion_null fun g : t ↦ (hqmp _ g.1.2).preimage_null hUV)
  exact hKpos.ne' hKzero

/-- For an inner regular Haar measure `μ` on a locally compact topological group `G`, if `U` is
open, `V` is `μ`-null-measurable with `V * s ⊆ V`, and `μ (U \ V) = 0`, then
`μ ((U * s) \ V) = 0`. -/
@[to_additive /-- For an inner regular additive Haar measure `μ` on a locally compact additive
topological group `G`, if `U` is open, `V` is `μ`-null-measurable with `V + s ⊆ V`, and
`μ (U \ V) = 0`, then `μ ((U + s) \ V) = 0`. -/]
theorem IsOpen.measure_mul_sdiff_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] [μ.InnerRegular]
    {U V s : Set G} (hU : IsOpen U) (hV : NullMeasurableSet V μ) (hVs : V * s ⊆ V)
    (hUV : μ (U \ V) = 0) :
    μ ((U * s) \ V) = 0 :=
  hU.measure_mul_sdiff_eq_zero_of_quasiMeasurePreserving hV hVs
    (fun g _ ↦ ⟨(continuous_mul_const g⁻¹).measurable.aemeasurable, by
      rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
      exact Measure.smul_absolutelyContinuous⟩) hUV

end MulSdiff
