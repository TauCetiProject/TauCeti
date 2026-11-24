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
inversion-invariant. A left-invariant probability measure gives mass `n⁻¹` to a measurable
subgroup of finite index `n`, since its `n` cosets have equal mass and partition the group, and a
surjective homomorphism onto a finite group with measurable kernel splits a left-invariant measure
evenly among its fibres, the translates of the kernel. Finally, for an
inner regular measure whose right translations are quasi-measure-preserving—in particular any
inner regular Haar measure on a locally compact group—if an open set `U` lies up to a null set
inside a null-measurable set `V` satisfying `V * s ⊆ V`, then `U * s` (such as the subgroup
saturation `(QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' U) = U * N`) also lies in `V`
up to a null set. In a first-countable topological group with measurable open sets and measurable
multiplication, a compact set of positive measure for a left-invariant measure finite on compact
sets forces the group to be locally compact
(`IsCompact.locallyCompactSpace_of_measure_ne_zero_of_group`).

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
* `Subgroup.measure_eq_inv_index`, `AddSubgroup.measure_eq_inv_index`: a left-invariant
  probability measure gives mass `n⁻¹` to a measurable subgroup of finite index `n`.
* `IsOpen.measure_mul_sdiff_eq_zero_of_quasiMeasurePreserving`,
  `IsOpen.measure_add_sdiff_eq_zero_of_quasiMeasurePreserving`,
  `IsOpen.measure_mul_sdiff_eq_zero`, `IsOpen.measure_add_sdiff_eq_zero`: if an open set `U` has
  `μ (U \ V) = 0` for a `μ`-null-measurable set `V` invariant under right multiplication (or
  addition) by `s`, then `μ ((U * s) \ V) = 0` (or `μ ((U + s) \ V) = 0`) for any inner regular
  measure with quasi-measure-preserving right translations, and in particular for any inner
  regular Haar measure on a locally compact group.
* `measure_preimage_monoidHom`, `measure_preimage_addMonoidHom`: for a surjective homomorphism
  `φ : G → F` onto a finite group with measurable kernel and a left-invariant measure `μ` on `G`,
  the preimage of `T ⊆ F` has measure `#T / #F · μ G`.
* `IsCompact.locallyCompactSpace_of_measure_ne_zero_of_group`,
  `IsCompact.locallyCompactSpace_of_measure_ne_zero_of_addGroup`: in a first-countable
  topological group with measurable open sets and measurable multiplication (or addition), a
  compact set of positive measure for a left-invariant measure finite on compact sets forces the
  group to be locally compact.
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

/-- A left-invariant probability measure on a group gives mass `n⁻¹` to a measurable subgroup of
finite index `n`: its `n` left cosets have equal mass and partition the group
(`Subgroup.index_mul_measure`). -/
@[to_additive /-- A left-invariant probability measure on an additive group gives mass `n⁻¹` to a
measurable additive subgroup of finite index `n`: its `n` cosets have equal mass and partition the
group (`AddSubgroup.index_mul_measure`). -/]
theorem Subgroup.measure_eq_inv_index {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (K : Subgroup G) [K.FiniteIndex] (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] : μ K = (K.index : ℝ≥0∞)⁻¹ := by
  have h := K.index_mul_measure hK μ
  rw [measure_univ, mul_comm] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left h

namespace MeasureTheory

/-- **Measure of a preimage under a homomorphism onto a finite group.** If `φ : G →* F` is
surjective onto a finite group and has measurable kernel, then for every left-invariant measure `μ`
on `G` the preimage of `T ⊆ F` has measure `#T / #F · μ univ`: the fibres of `φ` are the
translates of its kernel, which all have the same measure. -/
@[to_additive /-- **Measure of a preimage under an additive homomorphism onto a finite group.** If
`φ : G →+ F` is surjective onto a finite group and has measurable kernel, then for every
left-invariant measure `μ` on `G` the preimage of `T ⊆ F` has measure `#T / #F · μ univ`: the
fibres of `φ` are the translates of its kernel, which all have the same measure. -/]
theorem measure_preimage_monoidHom {G F : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group F] [Finite F] (μ : Measure G) [μ.IsMulLeftInvariant] (φ : G →* F)
    (hφ : Function.Surjective φ) (hker : MeasurableSet (φ.ker : Set G)) (T : Set F) :
    μ (φ ⁻¹' T) = Nat.card T / Nat.card F * μ univ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hfib (t : F) : ∃ a, φ ⁻¹' {t} = (fun h => a⁻¹ * h) ⁻¹' (φ.ker : Set G) := by
    obtain ⟨a, rfl⟩ := hφ t
    exact ⟨a, by ext x; simp only [mem_preimage, mem_singleton_iff, SetLike.mem_coe,
      MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]; exact eq_comm⟩
  have hfibm (t : F) : MeasurableSet (φ ⁻¹' {t}) := by
    obtain ⟨a, ha⟩ := hfib t
    rw [ha]
    exact hker.preimage (measurable_const_mul _)
  have hfibμ (t : F) : μ (φ ⁻¹' {t}) = μ φ.ker := by
    obtain ⟨a, ha⟩ := hfib t
    rw [ha, measure_preimage_mul]
  have hpre (S : Set F) : μ (φ ⁻¹' S) = Nat.card S * μ φ.ker := by
    have hS : φ ⁻¹' S = ⋃ t ∈ S.toFinset, φ ⁻¹' {t} := by ext; simp
    rw [hS, measure_biUnion_finset (fun s _ t _ hst => (disjoint_singleton.2 hst).preimage φ)
      fun t _ => hfibm t]
    simp [hfibμ]
  have hindex : φ.ker.index = Nat.card F := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top]
  have : φ.ker.FiniteIndex := ⟨by rw [hindex]; exact Nat.card_pos.ne'⟩
  have huniv := Subgroup.index_mul_measure φ.ker hker μ
  rw [hindex] at huniv
  have hF0 : (Nat.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [hpre, ← huniv, ← mul_assoc, ENNReal.div_mul_cancel hF0 (ENNReal.natCast_ne_top _)]

end MeasureTheory

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
      fun hxgV ↦ (hKWV hx).2 (by simpa using hVs (mul_mem_mul hxgV g.property))⟩
  have hKzero : μ K = 0 :=
    measure_mono_null hKsub (measure_iUnion_null fun g : t ↦ (hqmp _ g.val.property).preimage_null
        hUV)
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

section LocallyCompact

open Filter Function

open scoped Topology

/-- In a first-countable topological group `G` with measurable open sets and measurable
multiplication, if a left-invariant measure `μ` finite on compact sets assigns positive measure to a
compact set `K`, then `G` is locally compact. -/
@[to_additive /-- In a first-countable additive topological group `G` with measurable open sets
and measurable addition, if a left-invariant measure `μ` finite on compact sets assigns positive
measure to a compact set `K`, then `G` is locally compact. -/]
theorem IsCompact.locallyCompactSpace_of_measure_ne_zero_of_group
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [FirstCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {K : Set G} (hK : IsCompact K) (hμ : μ K ≠ 0) : LocallyCompactSpace G := by
  classical
  by_contra hlc
  -- Replace `K` by its closure, which is closed, compact (since `G` is regular), and has positive
  -- measure.
  set C : Set G := closure K
  have hC : IsCompact C := hK.closure
  have hC_closed : IsClosed C := isClosed_closure
  have hCμ : μ C ≠ 0 := fun h ↦ hμ (measure_mono_null subset_closure h)
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  -- Outside any finite union of translates of `C * C⁻¹`, every neighbourhood `U n` of `1` has a
  -- point; otherwise that compact union would be a neighbourhood of `1`, making `G` locally
  -- compact.
  have hstep (n : ℕ) (s : Finset G) : ∃ y ∈ U n, ∀ g ∈ s, y ∉ (g * ·) '' (C * C⁻¹) := by
    by_contra! h
    have hcomp : IsCompact (⋃ g ∈ s, (g * ·) '' (C * C⁻¹)) :=
      s.isCompact_biUnion fun g _ ↦ (hC.mul hC.inv).image (continuous_const_mul g)
    have hmem : (⋃ g ∈ s, (g * ·) '' (C * C⁻¹)) ∈ 𝓝 (1 : G) :=
      Filter.mem_of_superset (hU.mem n) fun y hy ↦ by
        obtain ⟨g, hg, hyg⟩ := h y hy
        exact Set.mem_biUnion hg hyg
    exact hlc (hcomp.locallyCompactSpace_of_mem_nhds_of_group hmem)
  choose next hnextU hnextF using hstep
  -- Recursively choose `x n ∈ U n` disjoint from all earlier `x j * (C * C⁻¹)`.
  let S : ℕ → Finset G := Nat.rec ∅ fun n s ↦ insert (next n s) s
  let x : ℕ → G := fun n ↦ next n (S n)
  have hS_mono : Monotone S := monotone_nat_of_le_succ fun n ↦ Finset.subset_insert _ _
  have hxS {j n : ℕ} (hjn : j < n) : x j ∈ S n :=
    hS_mono hjn (Finset.mem_insert_self (x j) (S j))
  -- The sequence `x` converges to `1`, so `insert 1 (range x) * C` is compact.
  have hx_tendsto : Tendsto x atTop (𝓝 (1 : G)) :=
    hU.tendsto_right_iff.2 fun n _ ↦
      eventually_atTop.2 ⟨n, fun m hm ↦ hU.antitone hm (hnextU m (S m))⟩
  have hcompact : IsCompact (insert 1 (Set.range x) * C) :=
    hx_tendsto.isCompact_insert_range.mul hC
  -- The translates `x n * C` are measurable, pairwise disjoint, and lie inside that compact set.
  have hdisj : Pairwise (Disjoint on fun n ↦ (fun y ↦ (x n)⁻¹ * y) ⁻¹' C) := by
    have aux {j k : ℕ} (hjk : j < k) :
        Disjoint ((fun y ↦ (x j)⁻¹ * y) ⁻¹' C) ((fun y ↦ (x k)⁻¹ * y) ⁻¹' C) := by
      refine Set.disjoint_left.2 fun z hzj hzk ↦ hnextF k (S k) (x j) (hxS hjk) ?_
      refine ⟨((x j)⁻¹ * z) * ((x k)⁻¹ * z)⁻¹, Set.mul_mem_mul hzj (Set.inv_mem_inv.2 hzk), ?_⟩
      simp [mul_assoc, x]
    intro j k hjk
    rcases hjk.lt_or_gt with h | h
    · exact aux h
    · exact (aux h).symm
  have hmeas (n : ℕ) : MeasurableSet ((fun y ↦ (x n)⁻¹ * y) ⁻¹' C) :=
    (hC_closed.preimage (continuous_const_mul _)).measurableSet
  have hsub : (⋃ n, (fun y ↦ (x n)⁻¹ * y) ⁻¹' C) ⊆ insert 1 (Set.range x) * C :=
    Set.iUnion_subset fun n z hz ↦
      ⟨x n, Set.mem_insert_of_mem _ ⟨n, rfl⟩, (x n)⁻¹ * z, hz, mul_inv_cancel_left _ _⟩
  have hle : (∑' _ : ℕ, μ C) ≤ μ (insert 1 (Set.range x) * C) := by
    calc (∑' _ : ℕ, μ C) = ∑' n : ℕ, μ ((fun y ↦ (x n)⁻¹ * y) ⁻¹' C) := by
          simp only [measure_preimage_mul]
      _ = μ (⋃ n, (fun y ↦ (x n)⁻¹ * y) ⁻¹' C) := (measure_iUnion hdisj hmeas).symm
      _ ≤ μ (insert 1 (Set.range x) * C) := measure_mono hsub
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hCμ] at hle
  exact hcompact.measure_lt_top.not_ge hle

end LocallyCompact
