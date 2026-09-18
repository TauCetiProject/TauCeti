/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Bigrading
public import TauCeti.Geometry.Hodge.Mixed.Substructure
public import TauCeti.Geometry.Hodge.SubquotientModel

/-!
# Mixed Hodge structures induced on rational subspaces

A rational subspace of a mixed Hodge structure which is spanned by its intersections with
Deligne's bigrading inherits a mixed Hodge structure. Its integral carrier consists of the
integral vectors lying in the subspace, while its complex carrier is the complexification of the
rational subspace. Both filtrations and every bigrading piece are obtained by intersection with
the corresponding ambient subspace in the construction.

This construction turns the subspace criterion
`TauCeti.Hodge.MixedHodgeStructure.IsSubstructure` into an actual object. In particular, since
the rational kernel and range of every mixed Hodge morphism satisfy that criterion, they can now
be equipped with their induced mixed Hodge structures. This is the object-level construction
needed for categorical kernels and images.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.hodgeStructure`: the mixed Hodge structure
  induced on a rational subspace.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.inclusion`: the inclusion of the induced
  structure into the ambient mixed Hodge structure.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Chapter 3.
-/

public section

namespace TauCeti.Hodge

universe u v w

namespace MixedHodgeStructure.IsSubstructure

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {mhs : MixedHodgeStructure hℚ hℂ} {U : Submodule ℚ Vℚ}

private def subWeightFiltration (mhs : MixedHodgeStructure hℚ hℂ) (U : Submodule ℚ Vℚ)
    (k : ℤ) : Submodule ℚ U :=
  (mhs.WQ k).comap U.subtype

private noncomputable def subHodgeFiltration (mhs : MixedHodgeStructure hℚ hℂ)
    (U : Submodule ℚ Vℚ) (p : ℤ) :
    Submodule ℂ (rationalToComplexSubmodule hℚ hℂ U) :=
  (mhs.F p).comap (rationalToComplexSubmodule hℚ hℂ U).subtype

private noncomputable def subBigrading (mhs : MixedHodgeStructure hℚ hℂ)
    (U : Submodule ℚ Vℚ) (pq : ℤ × ℤ) :
    Submodule ℂ (rationalToComplexSubmodule hℚ hℂ U) :=
  (mhs.deligneSplittingFamily pq).comap
    (rationalToComplexSubmodule hℚ hℂ U).subtype

variable (hU : mhs.IsSubstructure U)

/-- Complexifying an induced weight step gives the intersection of the ambient complex weight
step with the complexification of the subspace. -/
private theorem rationalToComplexSubmodule_subWeightFiltration (k : ℤ) :
    rationalToComplexSubmodule (isBaseChange_integralSubmoduleToRational hℚ U)
      (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) (subWeightFiltration mhs U k) =
      (mhs.WC k).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  apply Submodule.map_injective_of_injective
    (rationalToComplexSubmodule hℚ hℂ U).subtype_injective
  conv_lhs =>
    rw [← rationalMapToComplex_subtype hℚ hℂ U, map_rationalToComplexSubmodule]
  rw [subWeightFiltration, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    rationalToComplexSubmodule_inf, MixedHodgeStructure.WC_def]

/-- Conjugation exchanges the restricted bigrading pieces modulo the induced lower weight
filtration. -/
private theorem map_latticeConj_subBigrading_le (hU : mhs.IsSubstructure U) (pq : ℤ × ℤ) :
    (subBigrading mhs U pq).map
        (latticeConj (isBaseChange_integralSubmoduleToComplex hℚ hℂ U)) ≤
      subBigrading mhs U pq.swap ⊔
        rationalToComplexSubmodule (isBaseChange_integralSubmoduleToRational hℚ U)
          (isBaseChange_integralSubmoduleToComplex hℚ hℂ U)
          (subWeightFiltration mhs U (pq.1 + pq.2 - 1)) := by
  rw [← latticeConjugation_toLinearMap,
    latticeConjugation_integralSubmoduleToComplex,
    subBigrading,
    Conjugation.map_restrict_comap_subtype]
  rw [rationalToComplexSubmodule_subWeightFiltration (mhs := mhs) (U := U)]
  rw [← Submodule.map_le_map_iff_of_injective
    (rationalToComplexSubmodule hℚ hℂ U).subtype_injective]
  simp only [Submodule.map_sup, Submodule.map_comap_subtype, subBigrading]
  simp only [MixedHodgeStructure.deligneSplittingFamily_apply, Prod.fst_swap,
    Prod.snd_swap, latticeConjugation_toLinearMap]
  let P : ℤ × ℤ → Prop := fun rs ↦
    rs = pq.swap ∨ rs.1 + rs.2 ≤ pq.1 + pq.2 - 1
  have hsup : mhs.deligneSplitting pq.2 pq.1 ⊔ mhs.WC (pq.1 + pq.2 - 1) ≤
      ⨆ (rs : ℤ × ℤ) (_ : P rs), mhs.deligneSplitting rs.1 rs.2 := by
    refine sup_le (le_iSup₂_of_le pq.swap (Or.inl rfl) ?_) ?_
    · simpa only [Prod.fst_swap, Prod.snd_swap] using
        (le_rfl : mhs.deligneSplitting pq.2 pq.1 ≤ mhs.deligneSplitting pq.2 pq.1)
    rw [mhs.WC_eq_iSup_deligneSplitting]
    exact iSup₂_le fun rs hrs ↦ le_iSup₂_of_le rs (Or.inr hrs) le_rfl
  calc
    rationalToComplexSubmodule hℚ hℂ U ⊓
        (mhs.deligneSplitting pq.1 pq.2).map (latticeConj hℂ) ≤
        rationalToComplexSubmodule hℚ hℂ U ⊓
          (mhs.deligneSplitting pq.2 pq.1 ⊔ mhs.WC (pq.1 + pq.2 - 1)) :=
      inf_le_inf_left _ <| (mhs.map_latticeConj_deligneSplitting_le_sup_WC pq.1 pq.2).trans
        (sup_le_sup_left (mhs.WC_monotone
          (by omega : pq.1 + pq.2 - 2 ≤ pq.1 + pq.2 - 1)) _)
    _ ≤ rationalToComplexSubmodule hℚ hℂ U ⊓
        ⨆ (rs : ℤ × ℤ) (_ : P rs), mhs.deligneSplitting rs.1 rs.2 :=
      inf_le_inf_left _ hsup
    _ = (⨆ (rs : ℤ × ℤ) (_ : P rs), mhs.deligneSplitting rs.1 rs.2) ⊓
        rationalToComplexSubmodule hℚ hℂ U := inf_comm _ _
    _ = ⨆ (rs : ℤ × ℤ) (_ : P rs),
        rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplitting rs.1 rs.2 := by
      simpa only [MixedHodgeStructure.deligneSplittingFamily_apply] using
        hU.iSup₂_deligneSplittingFamily_inf P
    _ ≤ (rationalToComplexSubmodule hℚ hℂ U ⊓
          mhs.deligneSplitting pq.2 pq.1) ⊔
        (rationalToComplexSubmodule hℚ hℂ U ⊓
          mhs.WC (pq.1 + pq.2 - 1)) := by
      refine iSup₂_le fun rs hrs ↦ ?_
      rcases hrs with rfl | hrs
      · exact le_sup_left
      · exact le_sup_of_le_right (inf_le_inf_left _ <|
          (mhs.deligneSplitting_le_WC rs.1 rs.2).trans (mhs.WC_monotone hrs))

/-- The intersections with the ambient Deligne pieces form a Hodge bigrading for the induced
filtrations. -/
private theorem isHodgeBigrading (hU : mhs.IsSubstructure U) :
    IsHodgeBigrading (isBaseChange_integralSubmoduleToRational hℚ U)
      (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) (subWeightFiltration mhs U)
      (subHodgeFiltration mhs U) (subBigrading mhs U) := by
  refine
    { iSupIndep := ?_
      rationalToComplexSubmodule_eq_iSup := fun k ↦ ?_
      F_eq_iSup := fun p ↦ ?_
      map_latticeConj_le := map_latticeConj_subBigrading_le hU }
  · let e : Submodule ℂ (rationalToComplexSubmodule hℚ hℂ U) ≃o
        Set.Iic (rationalToComplexSubmodule hℚ hℂ U) :=
      (rationalToComplexSubmodule hℚ hℂ U).mapIic
    rw [← iSupIndep_map_orderIso_iff e]
    have he : e ∘ subBigrading mhs U = fun pq ↦
        ⟨mhs.deligneSplittingFamily pq ⊓ rationalToComplexSubmodule hℚ hℂ U,
          Set.mem_Iic.mpr inf_le_right⟩ := by
      funext pq
      apply Subtype.ext
      simp only [Function.comp_apply, e, Submodule.coe_mapIic_apply, subBigrading,
        Submodule.map_comap_subtype]
      rw [inf_comm]
    rw [he]
    exact iSupIndep.of_coe_Iic_comp
      (mhs.iSupIndep_deligneSplittingFamily.mono fun _ ↦ inf_le_left)
  · rw [rationalToComplexSubmodule_subWeightFiltration (mhs := mhs) (U := U)]
    apply Submodule.map_injective_of_injective
      (rationalToComplexSubmodule hℚ hℂ U).subtype_injective
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype, subBigrading]
    rw [inf_comm (rationalToComplexSubmodule hℚ hℂ U),
      hU.WC_inf_eq_iSup_inf_deligneSplitting]
    simp only [MixedHodgeStructure.deligneSplittingFamily_apply]
  · apply Submodule.map_injective_of_injective
      (rationalToComplexSubmodule hℚ hℂ U).subtype_injective
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype, subHodgeFiltration, subBigrading]
    rw [inf_comm (rationalToComplexSubmodule hℚ hℂ U),
      hU.F_inf_eq_iSup_inf_deligneSplitting]
    simp only [MixedHodgeStructure.deligneSplittingFamily_apply]

/-- A rational subspace satisfying the mixed-Hodge substructure criterion inherits a mixed Hodge
structure by intersecting both filtrations with the subspace. -/
noncomputable def hodgeStructure (hU : mhs.IsSubstructure U) :
    MixedHodgeStructure (isBaseChange_integralSubmoduleToRational hℚ U)
      (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) :=
  MixedHodgeStructure.ofIsHodgeBigrading (isHodgeBigrading hU)
    (by
      obtain ⟨k, hk⟩ := mhs.WQ_top
      exact ⟨k, by simp [subWeightFiltration, hk]⟩)
    (by
      obtain ⟨k, hk⟩ := mhs.WQ_bot
      exact ⟨k, by simp [subWeightFiltration, hk]⟩)
    (by
      obtain ⟨p, hp⟩ := mhs.F_top
      exact ⟨p, by simp [subHodgeFiltration, hp]⟩)
    (by
      obtain ⟨p, hp⟩ := mhs.F_bot
      exact ⟨p, by simp [subHodgeFiltration, hp]⟩)

/-- The rational weight filtration of the induced mixed Hodge structure is obtained by
intersection with the ambient weight filtration. -/
@[simp]
theorem hodgeStructure_WQ (k : ℤ) : hU.hodgeStructure.WQ k =
    (mhs.WQ k).comap U.subtype := by
  rw [hodgeStructure, MixedHodgeStructure.ofIsHodgeBigrading_WQ]
  rfl

/-- The Hodge filtration of the induced mixed Hodge structure is obtained by intersection with
the ambient Hodge filtration. -/
@[simp]
theorem hodgeStructure_F (p : ℤ) : hU.hodgeStructure.F p =
    (mhs.F p).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  rw [hodgeStructure, MixedHodgeStructure.ofIsHodgeBigrading_F]
  rfl

/-- The complex weight filtration of the induced mixed Hodge structure is the ambient complex
weight filtration intersected with the complexification of the subspace. -/
theorem hodgeStructure_WC (k : ℤ) : hU.hodgeStructure.WC k =
    (mhs.WC k).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  rw [MixedHodgeStructure.WC_def, hodgeStructure_WQ]
  change rationalToComplexSubmodule
    (isBaseChange_integralSubmoduleToRational hℚ U)
    (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) (subWeightFiltration mhs U k) = _
  exact rationalToComplexSubmodule_subWeightFiltration (mhs := mhs) (U := U) k

/-- The inclusion of an induced mixed Hodge structure into its ambient mixed Hodge structure. -/
noncomputable def inclusion : hU.hodgeStructure.Hom mhs where
  toRatLinearMap := U.subtype
  map_mem_WQ k x hx := by
    rw [hodgeStructure_WQ] at hx
    exact hx
  map_mem_F p x hx := by
    rw [hodgeStructure_F] at hx
    rw [rationalMapToComplex_subtype]
    exact hx

/-- The rational map underlying the inclusion of an induced mixed Hodge structure is the subtype
map. -/
@[simp]
theorem inclusion_toRatLinearMap : hU.inclusion.toRatLinearMap = U.subtype :=
  by rw [inclusion]

/-- On complex vectors, the inclusion of an induced mixed Hodge structure is the subtype map. -/
@[simp]
theorem inclusion_toLinearMap : hU.inclusion.toLinearMap =
    (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  rw [MixedHodgeStructure.Hom.toLinearMap_def, inclusion_toRatLinearMap,
    rationalMapToComplex_subtype]

end MixedHodgeStructure.IsSubstructure

end TauCeti.Hodge
