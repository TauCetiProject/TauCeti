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

* `TauCeti.Hodge.IsHodgeBigrading.comap_subtype`: a Hodge bigrading restricts to a rational
  subspace spanned by its intersections with the pieces.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.hodgeStructure`: the mixed Hodge structure
  induced on a rational subspace.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.inclusion`: the inclusion of the induced
  structure into the ambient mixed Hodge structure.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.hodgeStructure_deligneSplitting`: the Deligne
  bigrading of the induced structure is the intersection with the ambient one.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Chapter 3.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

namespace IsHodgeBigrading

variable {WQ : ℤ → Submodule ℚ Vℚ} {F : ℤ → Submodule ℂ Vℂ} {I : ℤ × ℤ → Submodule ℂ Vℂ}

/-- **Restricting a Hodge bigrading to a rational subspace.** If the complexification of a
rational subspace `U` is spanned by its intersections with the pieces of a Hodge bigrading, then
these intersections form a Hodge bigrading for the filtrations intersected with `U`. -/
theorem comap_subtype (h : IsHodgeBigrading hℚ hℂ WQ F I) {U : Submodule ℚ Vℚ}
    (hU : rationalToComplexSubmodule hℚ hℂ U ≤
      ⨆ pq : ℤ × ℤ, rationalToComplexSubmodule hℚ hℂ U ⊓ I pq) :
    IsHodgeBigrading (isBaseChange_integralSubmoduleToRational hℚ U)
      (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) (fun k ↦ (WQ k).comap U.subtype)
      (fun p ↦ (F p).comap (rationalToComplexSubmodule hℚ hℂ U).subtype)
      (fun pq ↦ (I pq).comap (rationalToComplexSubmodule hℚ hℂ U).subtype) := by
  -- A sum of pieces traces on the complexification of `U` in the sum of the traces of those
  -- pieces.
  have key (P : ℤ × ℤ → Prop) :
      (⨆ (pq : ℤ × ℤ) (_ : P pq), I pq) ⊓ rationalToComplexSubmodule hℚ hℂ U =
        ⨆ (pq : ℤ × ℤ) (_ : P pq), rationalToComplexSubmodule hℚ hℂ U ⊓ I pq := by
    have hUC : rationalToComplexSubmodule hℚ hℂ U =
        ⨆ pq : ℤ × ℤ, rationalToComplexSubmodule hℚ hℂ U ⊓ I pq :=
      le_antisymm hU (iSup_le fun _ ↦ inf_le_left)
    have := TauCeti.iSupIndep.iSup₂_inf_iSup_eq_iSup₂
      (B := fun pq ↦ rationalToComplexSubmodule hℚ hℂ U ⊓ I pq) h.iSupIndep
      (fun _ ↦ inf_le_right) P
    rwa [← hUC] at this
  refine
    { iSupIndep := ?_
      rationalToComplexSubmodule_eq_iSup := fun k ↦ ?_
      F_eq_iSup := fun p ↦ ?_
      map_latticeConj_le := fun pq ↦ ?_ }
  · let e : Submodule ℂ (rationalToComplexSubmodule hℚ hℂ U) ≃o
        Set.Iic (rationalToComplexSubmodule hℚ hℂ U) :=
      (rationalToComplexSubmodule hℚ hℂ U).mapIic
    rw [← iSupIndep_map_orderIso_iff e]
    have he : (e ∘ fun pq ↦ (I pq).comap (rationalToComplexSubmodule hℚ hℂ U).subtype) = fun pq ↦
        ⟨I pq ⊓ rationalToComplexSubmodule hℚ hℂ U, Set.mem_Iic.mpr inf_le_right⟩ := by
      funext pq
      apply Subtype.ext
      simp only [Function.comp_apply, e, Submodule.coe_mapIic_apply,
        Submodule.map_comap_subtype]
      rw [inf_comm]
    rw [he]
    exact iSupIndep.of_coe_Iic_comp (h.iSupIndep.mono fun _ ↦ inf_le_left)
  · rw [rationalToComplexSubmodule_comap_subtype]
    apply Submodule.map_injective_of_injective
      (rationalToComplexSubmodule hℚ hℂ U).subtype_injective
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype]
    rw [inf_comm, h.rationalToComplexSubmodule_eq_iSup, key]
  · apply Submodule.map_injective_of_injective
      (rationalToComplexSubmodule hℚ hℂ U).subtype_injective
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype]
    rw [inf_comm, h.F_eq_iSup, key]
  · rw [← latticeConjugation_toLinearMap, latticeConjugation_integralSubmoduleToComplex,
      Conjugation.map_restrict_comap_subtype, rationalToComplexSubmodule_comap_subtype,
      ← Submodule.map_le_map_iff_of_injective
        (rationalToComplexSubmodule hℚ hℂ U).subtype_injective]
    simp only [Submodule.map_sup, Submodule.map_comap_subtype, latticeConjugation_toLinearMap]
    let P : ℤ × ℤ → Prop := fun rs ↦ rs = pq.swap ∨ rs.1 + rs.2 ≤ pq.1 + pq.2 - 1
    have hsup : I pq.swap ⊔ rationalToComplexSubmodule hℚ hℂ (WQ (pq.1 + pq.2 - 1)) ≤
        ⨆ (rs : ℤ × ℤ) (_ : P rs), I rs := by
      refine sup_le (le_iSup₂_of_le pq.swap (Or.inl rfl) le_rfl) ?_
      rw [h.rationalToComplexSubmodule_eq_iSup]
      exact iSup₂_le fun rs hrs ↦ le_iSup₂_of_le rs (Or.inr hrs) le_rfl
    calc
      rationalToComplexSubmodule hℚ hℂ U ⊓ (I pq).map (latticeConj hℂ) ≤
          rationalToComplexSubmodule hℚ hℂ U ⊓ ⨆ (rs : ℤ × ℤ) (_ : P rs), I rs :=
        inf_le_inf_left _ ((h.map_latticeConj_le pq).trans hsup)
      _ = ⨆ (rs : ℤ × ℤ) (_ : P rs), rationalToComplexSubmodule hℚ hℂ U ⊓ I rs := by
        rw [inf_comm, key]
      _ ≤ rationalToComplexSubmodule hℚ hℂ U ⊓ I pq.swap ⊔
          rationalToComplexSubmodule hℚ hℂ U ⊓
            rationalToComplexSubmodule hℚ hℂ (WQ (pq.1 + pq.2 - 1)) := by
        refine iSup₂_le fun rs hrs ↦ ?_
        rcases hrs with rfl | hrs
        · exact le_sup_left
        · exact le_sup_of_le_right (inf_le_inf_left _ (h.le_rationalToComplexSubmodule hrs))

end IsHodgeBigrading

namespace MixedHodgeStructure.IsSubstructure

variable {mhs : MixedHodgeStructure hℚ hℂ} {U : Submodule ℚ Vℚ}

/-- A rational subspace satisfying the mixed-Hodge substructure criterion inherits a mixed Hodge
structure by intersecting both filtrations with the subspace. -/
noncomputable def hodgeStructure (hU : mhs.IsSubstructure U) :
    MixedHodgeStructure (isBaseChange_integralSubmoduleToRational hℚ U)
      (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) :=
  MixedHodgeStructure.ofIsHodgeBigrading
    (mhs.isHodgeBigrading_deligneSplittingFamily.comap_subtype
      hU.le_iSup_inf_deligneSplittingFamily)
    (by
      obtain ⟨k, hk⟩ := mhs.WQ_top
      exact ⟨k, by simp [hk]⟩)
    (by
      obtain ⟨k, hk⟩ := mhs.WQ_bot
      exact ⟨k, by simp [hk]⟩)
    (by
      obtain ⟨p, hp⟩ := mhs.F_top
      exact ⟨p, by simp [hp]⟩)
    (by
      obtain ⟨p, hp⟩ := mhs.F_bot
      exact ⟨p, by simp [hp]⟩)

variable (hU : mhs.IsSubstructure U)

/-- The rational weight filtration of the induced mixed Hodge structure is obtained by
intersection with the ambient weight filtration. -/
@[simp]
theorem hodgeStructure_WQ (k : ℤ) : hU.hodgeStructure.WQ k =
    (mhs.WQ k).comap U.subtype := by
  rw [hodgeStructure, MixedHodgeStructure.ofIsHodgeBigrading_WQ]

/-- The Hodge filtration of the induced mixed Hodge structure is obtained by intersection with
the ambient Hodge filtration. -/
@[simp]
theorem hodgeStructure_F (p : ℤ) : hU.hodgeStructure.F p =
    (mhs.F p).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  rw [hodgeStructure, MixedHodgeStructure.ofIsHodgeBigrading_F]

/-- The complex weight filtration of the induced mixed Hodge structure is the ambient complex
weight filtration intersected with the complexification of the subspace. -/
theorem hodgeStructure_WC (k : ℤ) : hU.hodgeStructure.WC k =
    (mhs.WC k).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  rw [MixedHodgeStructure.WC_def, hodgeStructure_WQ, rationalToComplexSubmodule_comap_subtype,
    MixedHodgeStructure.WC_def]

/-- The conjugate Hodge filtration of the induced mixed Hodge structure is the ambient conjugate
Hodge filtration intersected with the complexification of the subspace. -/
@[simp]
theorem hodgeStructure_conjF (p : ℤ) : hU.hodgeStructure.conjF p =
    (mhs.conjF p).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  rw [MixedHodgeStructure.conjF_def, hodgeStructure_F, ← latticeConjugation_toLinearMap,
    latticeConjugation_integralSubmoduleToComplex, Conjugation.map_restrict_comap_subtype,
    latticeConjugation_toLinearMap, ← MixedHodgeStructure.conjF_def]

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

/-- The Deligne bigrading of the induced mixed Hodge structure is the ambient Deligne bigrading
intersected with the complexification of the subspace. -/
@[simp]
theorem hodgeStructure_deligneSplittingFamily :
    hU.hodgeStructure.deligneSplittingFamily =
      fun pq ↦
        (mhs.deligneSplittingFamily pq).comap (rationalToComplexSubmodule hℚ hℂ U).subtype :=
  ((mhs.isHodgeBigrading_deligneSplittingFamily.comap_subtype
      hU.le_iSup_inf_deligneSplittingFamily).iSupIndep.le_iff_eq_of_iSup_eq_top
    hU.hodgeStructure.iSup_deligneSplittingFamily_eq_top).1 fun pq ↦ by
    rw [← Submodule.map_le_iff_le_comap, ← inclusion_toLinearMap hU]
    simpa only [deligneSplittingFamily_apply] using
      hU.inclusion.map_deligneSplitting_le pq.1 pq.2

/-- A piece of the Deligne bigrading of the induced mixed Hodge structure is the ambient piece
intersected with the complexification of the subspace. -/
@[simp]
theorem hodgeStructure_deligneSplitting (p q : ℤ) :
    hU.hodgeStructure.deligneSplitting p q =
      (mhs.deligneSplitting p q).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  simpa using congr_fun hU.hodgeStructure_deligneSplittingFamily (p, q)

end MixedHodgeStructure.IsSubstructure

end TauCeti.Hodge
