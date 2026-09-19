/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Bigrading
public import TauCeti.Geometry.Hodge.Mixed.Morphism
import TauCeti.LinearAlgebra.Submodule.Prod

/-!
# Products of mixed Hodge structures

The product of two mixed Hodge structures has componentwise weight and Hodge filtrations.
The product of their Deligne bigradings witnesses purity on the weight-graded pieces.
The two inclusions and projections are mixed Hodge morphisms; their rational maps are the
usual inclusions and projections of vector spaces. These supply the direct sums needed for
the abelian category of mixed Hodge structures.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Ch. 3.
The purity proof uses `MixedHodgeStructure.ofIsHodgeBigrading`.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}

/-- Products of Hodge bigradings are Hodge bigradings for the product filtrations. -/
theorem IsHodgeBigrading.prod
    {W : ℤ → Submodule ℚ Vℚ} {F : ℤ → Submodule ℂ Vℂ}
    {W' : ℤ → Submodule ℚ V'ℚ} {F' : ℤ → Submodule ℂ V'ℂ}
    {I : ℤ × ℤ → Submodule ℂ Vℂ} {I' : ℤ × ℤ → Submodule ℂ V'ℂ}
    (h : IsHodgeBigrading hℚ hℂ W F I) (h' : IsHodgeBigrading h'ℚ h'ℂ W' F' I') :
    IsHodgeBigrading (IsBaseChange.prodMap ιℚ ι'ℚ hℚ h'ℚ)
      (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ) (fun k ↦ (W k).prod (W' k))
      (fun p ↦ (F p).prod (F' p)) (fun pq ↦ (I pq).prod (I' pq)) where
  iSupIndep := TauCeti.iSupIndep.prod h.iSupIndep h'.iSupIndep
  rationalToComplexSubmodule_eq_iSup k := by
    simp only [rationalToComplexSubmodule_prod hℚ hℂ h'ℚ h'ℂ, TauCeti.iSup_prod_submodule,
      h.rationalToComplexSubmodule_eq_iSup, h'.rationalToComplexSubmodule_eq_iSup]
  F_eq_iSup p := by
    simp only [TauCeti.iSup_prod_submodule, h.F_eq_iSup, h'.F_eq_iSup]
  map_latticeConj_le pq := by
    rw [map_latticeConj_prod hℂ h'ℂ, rationalToComplexSubmodule_prod hℚ hℂ h'ℚ h'ℂ,
      Submodule.prod_sup_prod]
    exact Submodule.prod_mono (h.map_latticeConj_le pq) (h'.map_latticeConj_le pq)

namespace MixedHodgeStructure

variable (X : MixedHodgeStructure hℚ hℂ) (Y : MixedHodgeStructure h'ℚ h'ℂ)

/-- The product mixed Hodge structure, with componentwise weight and Hodge filtrations. -/
noncomputable def prod : MixedHodgeStructure (IsBaseChange.prodMap ιℚ ι'ℚ hℚ h'ℚ)
    (IsBaseChange.prodMap ιℂ ι'ℂ hℂ h'ℂ) :=
  ofIsHodgeBigrading
    (X.isHodgeBigrading_deligneSplittingFamily.prod Y.isHodgeBigrading_deligneSplittingFamily)
    (by
      obtain ⟨i, hi⟩ := X.WQ_top
      obtain ⟨j, hj⟩ := Y.WQ_top
      exact ⟨max i j, by
        rw [eq_top_mono (X.WQ_monotone (le_max_left _ _)) hi,
          eq_top_mono (Y.WQ_monotone (le_max_right _ _)) hj, Submodule.prod_top]⟩)
    (by
      obtain ⟨i, hi⟩ := X.WQ_bot
      obtain ⟨j, hj⟩ := Y.WQ_bot
      exact ⟨min i j, by
        rw [eq_bot_mono (X.WQ_monotone (min_le_left _ _)) hi,
          eq_bot_mono (Y.WQ_monotone (min_le_right _ _)) hj, Submodule.prod_bot]⟩)
    (by
      obtain ⟨i, hi⟩ := X.F_top
      obtain ⟨j, hj⟩ := Y.F_top
      exact ⟨min i j, by
        rw [eq_top_mono (X.F_antitone (min_le_left _ _)) hi,
          eq_top_mono (Y.F_antitone (min_le_right _ _)) hj, Submodule.prod_top]⟩)
    (by
      obtain ⟨i, hi⟩ := X.F_bot
      obtain ⟨j, hj⟩ := Y.F_bot
      exact ⟨max i j, by
        rw [eq_bot_mono (X.F_antitone (le_max_left _ _)) hi,
          eq_bot_mono (Y.F_antitone (le_max_right _ _)) hj, Submodule.prod_bot]⟩)

@[simp]
theorem prod_WQ (k : ℤ) : (X.prod Y).WQ k = (X.WQ k).prod (Y.WQ k) := by
  simp [prod]

@[simp]
theorem prod_F (p : ℤ) : (X.prod Y).F p = (X.F p).prod (Y.F p) := by
  simp [prod]

/-- The first projection from the product mixed Hodge structure. -/
noncomputable def fst : Hom (X.prod Y) X where
  toRatLinearMap := LinearMap.fst ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := (prod_WQ X Y _ ▸ hx).1
  map_mem_F _ _ hx := by
    rw [rationalMapToComplex_fst hℚ hℂ h'ℚ h'ℂ]
    exact (prod_F X Y _ ▸ hx).1

/-- The second projection from the product mixed Hodge structure. -/
noncomputable def snd : Hom (X.prod Y) Y where
  toRatLinearMap := LinearMap.snd ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := (prod_WQ X Y _ ▸ hx).2
  map_mem_F _ _ hx := by
    rw [rationalMapToComplex_snd hℚ hℂ h'ℚ h'ℂ]
    exact (prod_F X Y _ ▸ hx).2

/-- The first inclusion into the product mixed Hodge structure. -/
noncomputable def inl : Hom X (X.prod Y) where
  toRatLinearMap := LinearMap.inl ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := by simpa using hx
  map_mem_F _ _ hx := by
    simpa [rationalMapToComplex_inl hℚ hℂ h'ℚ h'ℂ] using hx

/-- The second inclusion into the product mixed Hodge structure. -/
noncomputable def inr : Hom Y (X.prod Y) where
  toRatLinearMap := LinearMap.inr ℚ Vℚ V'ℚ
  map_mem_WQ _ _ hx := by simpa using hx
  map_mem_F _ _ hx := by
    simpa [rationalMapToComplex_inr hℚ hℂ h'ℚ h'ℂ] using hx

@[simp]
theorem fst_toRatLinearMap : (X.fst Y).toRatLinearMap = LinearMap.fst ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem snd_toRatLinearMap : (X.snd Y).toRatLinearMap = LinearMap.snd ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem inl_toRatLinearMap : (X.inl Y).toRatLinearMap = LinearMap.inl ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem inr_toRatLinearMap : (X.inr Y).toRatLinearMap = LinearMap.inr ℚ Vℚ V'ℚ := (rfl)

@[simp]
theorem fst_toLinearMap : (X.fst Y).toLinearMap = LinearMap.fst ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_fst hℚ hℂ h'ℚ h'ℂ]

@[simp]
theorem snd_toLinearMap : (X.snd Y).toLinearMap = LinearMap.snd ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_snd hℚ hℂ h'ℚ h'ℂ]

@[simp]
theorem inl_toLinearMap : (X.inl Y).toLinearMap = LinearMap.inl ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_inl hℚ hℂ h'ℚ h'ℂ]

@[simp]
theorem inr_toLinearMap : (X.inr Y).toLinearMap = LinearMap.inr ℂ Vℂ V'ℂ := by
  simp [Hom.toLinearMap_def, rationalMapToComplex_inr hℚ hℂ h'ℚ h'ℂ]

end MixedHodgeStructure

end TauCeti.Hodge
