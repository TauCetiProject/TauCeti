/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Bigrading
public import TauCeti.Geometry.Hodge.Mixed.Substructure
public import TauCeti.Geometry.Hodge.SubquotientModel
import TauCeti.Algebra.DirectSum.Internal

/-!
# Quotients of mixed Hodge structures

A sub-mixed Hodge structure determines a mixed Hodge structure on the quotient. Its integral,
rational, and complex carriers are the corresponding quotients; its weight and Hodge filtrations
are the images of the ambient filtrations. Deligne's bigrading descends componentwise, so the
quotient is again a mixed Hodge structure and the quotient map is a morphism.

This is the object-level quotient construction needed to form cokernels in the category of mixed
Hodge structures. It complements the induced structure on a rational subspace: kernels use that
subobject construction, while cokernels use the quotient by the range.

## Main declarations

* `TauCeti.Hodge.IsHodgeBigrading.map_mkQ`: a Hodge bigrading descends through a subspace spanned
  by its intersections with the bigrading pieces.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.quotient`: the induced mixed Hodge structure
  on the quotient by a sub-mixed Hodge structure.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.projection`: the quotient projection as a
  morphism of mixed Hodge structures.

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

variable {WQ : ℤ → Submodule ℚ Vℚ} {F : ℤ → Submodule ℂ Vℂ}
variable {I : ℤ × ℤ → Submodule ℂ Vℂ}

/-- **Descending a Hodge bigrading to a quotient.** If a rational subspace is spanned by its
intersections with the bigrading pieces, then the images of those pieces form a Hodge bigrading
for the image filtrations on the quotient. -/
theorem map_mkQ (h : IsHodgeBigrading hℚ hℂ WQ F I) {U : Submodule ℚ Vℚ}
    (hU : rationalToComplexSubmodule hℚ hℂ U ≤
      ⨆ pq : ℤ × ℤ, rationalToComplexSubmodule hℚ hℂ U ⊓ I pq) :
    IsHodgeBigrading (isBaseChange_integralQuotientToRational hℚ U)
      (isBaseChange_integralQuotientToComplex hℚ hℂ U)
      (fun k ↦ (WQ k).map U.mkQ)
      (fun p ↦ (F p).map (rationalToComplexSubmodule hℚ hℂ U).mkQ)
      (fun pq ↦ (I pq).map (rationalToComplexSubmodule hℚ hℂ U).mkQ) := by
  refine
    { iSupIndep := TauCeti.Submodule.iSupIndep_map_mkQ h.iSupIndep hU
      rationalToComplexSubmodule_eq_iSup := fun k ↦ ?_
      F_eq_iSup := fun p ↦ ?_
      map_latticeConj_le := fun pq ↦ ?_ }
  · rw [rationalToComplexSubmodule_map_mkQ, h.rationalToComplexSubmodule_eq_iSup,
      Submodule.map_iSup]
    simp only [Submodule.map_iSup]
  · rw [h.F_eq_iSup, Submodule.map_iSup]
    simp only [Submodule.map_iSup]
  · rw [map_latticeConj_integralQuotientToComplex, rationalToComplexSubmodule_map_mkQ,
      ← Submodule.map_sup]
    exact Submodule.map_mono (h.map_latticeConj_le pq)

end IsHodgeBigrading

namespace MixedHodgeStructure.IsSubstructure

variable {mhs : MixedHodgeStructure hℚ hℂ} {U : Submodule ℚ Vℚ}

/-- The mixed Hodge structure induced on the quotient by a sub-mixed Hodge structure. Both
filtrations and every bigrading piece are the images of their ambient counterparts. -/
noncomputable def quotient (hU : mhs.IsSubstructure U) :
    MixedHodgeStructure (isBaseChange_integralQuotientToRational hℚ U)
      (isBaseChange_integralQuotientToComplex hℚ hℂ U) :=
  MixedHodgeStructure.ofIsHodgeBigrading
    (mhs.isHodgeBigrading_deligneSplittingFamily.map_mkQ
      hU.le_iSup_inf_deligneSplittingFamily)
    (by
      obtain ⟨k, hk⟩ := mhs.WQ_top
      exact ⟨k, by simp [hk, Submodule.range_mkQ]⟩)
    (by
      obtain ⟨k, hk⟩ := mhs.WQ_bot
      exact ⟨k, by simp [hk]⟩)
    (by
      obtain ⟨p, hp⟩ := mhs.F_top
      exact ⟨p, by simp [hp, Submodule.range_mkQ]⟩)
    (by
      obtain ⟨p, hp⟩ := mhs.F_bot
      exact ⟨p, by simp [hp]⟩)

variable (hU : mhs.IsSubstructure U)

/-- The rational weight filtration on the quotient is the image of the ambient weight
filtration. -/
@[simp]
theorem quotient_WQ (k : ℤ) : hU.quotient.WQ k = (mhs.WQ k).map U.mkQ := by
  rw [quotient, MixedHodgeStructure.ofIsHodgeBigrading_WQ]

/-- The Hodge filtration on the quotient is the image of the ambient Hodge filtration. -/
@[simp]
theorem quotient_F (p : ℤ) : hU.quotient.F p =
    (mhs.F p).map (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  rw [quotient, MixedHodgeStructure.ofIsHodgeBigrading_F]

/-- The complex weight filtration on the quotient is the image of the ambient complex weight
filtration. -/
theorem quotient_WC (k : ℤ) : hU.quotient.WC k =
    (mhs.WC k).map (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  rw [MixedHodgeStructure.WC_def, quotient_WQ, rationalToComplexSubmodule_map_mkQ,
    MixedHodgeStructure.WC_def]

/-- The conjugate Hodge filtration on the quotient is the image of the ambient conjugate Hodge
filtration. -/
@[simp]
theorem quotient_conjF (p : ℤ) : hU.quotient.conjF p =
    (mhs.conjF p).map (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  rw [MixedHodgeStructure.conjF_def, quotient_F,
    map_latticeConj_integralQuotientToComplex, ← MixedHodgeStructure.conjF_def]

/-- The quotient projection is a morphism of mixed Hodge structures. -/
noncomputable def projection : mhs.Hom hU.quotient where
  toRatLinearMap := U.mkQ
  map_mem_WQ k x hx := by
    rw [quotient_WQ]
    exact ⟨x, hx, rfl⟩
  map_mem_F p x hx := by
    rw [rationalMapToComplex_mkQ, quotient_F]
    exact ⟨x, hx, rfl⟩

/-- The rational map underlying the quotient projection is the canonical quotient map. -/
@[simp]
theorem projection_toRatLinearMap : hU.projection.toRatLinearMap = U.mkQ := by
  rw [projection]

/-- On complex vectors, the quotient projection is the canonical complex quotient map. -/
@[simp]
theorem projection_toLinearMap : hU.projection.toLinearMap =
    (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  rw [MixedHodgeStructure.Hom.toLinearMap_def, projection_toRatLinearMap,
    rationalMapToComplex_mkQ]

/-- The Deligne bigrading of the quotient is the image of the ambient Deligne bigrading. -/
@[simp]
theorem quotient_deligneSplittingFamily :
    hU.quotient.deligneSplittingFamily = fun pq ↦
      (mhs.deligneSplittingFamily pq).map
        (rationalToComplexSubmodule hℚ hℂ U).mkQ :=
  Eq.symm <| (hU.quotient.iSupIndep_deligneSplittingFamily.le_iff_eq_of_iSup_eq_top
    (by
      rw [← Submodule.map_iSup, mhs.iSup_deligneSplittingFamily_eq_top,
        Submodule.map_top, Submodule.range_mkQ])).1 fun pq ↦ by
          simpa only [deligneSplittingFamily_apply, projection_toLinearMap] using
            hU.projection.map_deligneSplitting_le pq.1 pq.2

/-- A Deligne bigrading piece of the quotient is the image of the corresponding ambient piece. -/
@[simp]
theorem quotient_deligneSplitting (p q : ℤ) : hU.quotient.deligneSplitting p q =
    (mhs.deligneSplitting p q).map
      (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  simpa using congr_fun hU.quotient_deligneSplittingFamily (p, q)

end MixedHodgeStructure.IsSubstructure

end TauCeti.Hodge
