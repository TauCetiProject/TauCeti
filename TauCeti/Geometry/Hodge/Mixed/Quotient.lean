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
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.lift`: the universal factorization of a
  morphism annihilating the substructure through the quotient projection.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Chapter 3.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

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
    { iSupIndep := TauCeti.iSupIndep_map_mkQ h.iSupIndep fun _ hx ↦ hU hx.1
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
-- This is already a consequence of the simp lemmas `MixedHodgeStructure.WC_def`, `quotient_WQ`,
-- and `rationalToComplexSubmodule_map_mkQ`, so a simp attribute here would violate `simpNF`.
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

section Lift

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {target : MixedHodgeStructure h'ℚ h'ℂ}

/-- A morphism annihilating a sub-mixed Hodge structure factors through its quotient. -/
noncomputable def lift (f : mhs.Hom target) (hf : U ≤ LinearMap.ker f.toRatLinearMap) :
    hU.quotient.Hom target where
  toRatLinearMap := U.liftQ f.toRatLinearMap hf
  map_mem_WQ k x hx := by
    rw [quotient_WQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using f.map_mem_WQ k y hy
  map_mem_F p x hx := by
    rw [quotient_F] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← rationalMapToComplex_mkQ hℚ hℂ U, ← LinearMap.comp_apply,
      ← rationalMapToComplex_comp, Submodule.liftQ_mkQ]
    exact f.map_mem_F p y hy

/-- The rational map underlying the quotient lift is the usual linear quotient lift. -/
@[simp]
theorem lift_toRatLinearMap (f : mhs.Hom target) (hf : U ≤ LinearMap.ker f.toRatLinearMap) :
    (hU.lift f hf).toRatLinearMap = U.liftQ f.toRatLinearMap hf := by
  rw [lift]

/-- The quotient lift restricts along the quotient projection to the original morphism. -/
@[simp]
theorem lift_comp_projection (f : mhs.Hom target)
    (hf : U ≤ LinearMap.ker f.toRatLinearMap) : (hU.lift f hf).comp hU.projection = f := by
  ext x
  simp

/-- Morphisms out of the quotient are equal when they agree after the quotient projection. -/
@[ext]
theorem quotientHom_ext {f g : hU.quotient.Hom target}
    (hfg : f.comp hU.projection = g.comp hU.projection) : f = g := by
  ext x
  obtain ⟨y, rfl⟩ := U.mkQ_surjective x
  simpa using congrArg (fun q ↦ q.toRatLinearMap y) hfg

/-- The quotient lift is the unique morphism whose composite with the projection is `f`. -/
theorem eq_lift {f : mhs.Hom target} {hf : U ≤ LinearMap.ker f.toRatLinearMap}
    {g : hU.quotient.Hom target} (hg : g.comp hU.projection = f) : g = hU.lift f hf := by
  apply hU.quotientHom_ext
  rw [hg, lift_comp_projection]

end Lift

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
