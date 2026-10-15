/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Complements on left homology map data

Two facts about `ShortComplex.LeftHomologyMapData`: the compatibility `commf'` follows from the
compatibility `commi` (`CategoryTheory.ShortComplex.LeftHomologyMapData.commf'_of_commi`), and a
variant of `LeftHomologyMapData.homologyMap_comm` where the left homology objects are replaced by
isomorphic objects (`homologyMap_comp_homologyIso_trans_hom`).
-/

public section

namespace CategoryTheory.ShortComplex.LeftHomologyMapData

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {S₁ S₂ : ShortComplex C}

/-- The compatibility `commf'` of a left homology map data follows from the compatibility
`commi`. -/
lemma commf'_of_commi (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    (φK : h₁.K ⟶ h₂.K) (commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂) :
    h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
  rw [← cancel_mono h₂.i, Category.assoc, commi, LeftHomologyData.f'_i_assoc, Category.assoc,
    LeftHomologyData.f'_i, φ.comm₁₂]

/-- A variant of `LeftHomologyMapData.homologyMap_comm` where the left homology objects are
replaced by isomorphic objects. -/
lemma homologyMap_comp_homologyIso_trans_hom [S₁.HasHomology] [S₂.HasHomology] {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData} (γ : LeftHomologyMapData φ h₁ h₂)
    {A₁ A₂ : C} (e₁ : A₁ ≅ h₁.H) (e₂ : A₂ ≅ h₂.H)
    (g : A₁ ⟶ A₂) (hg : e₁.hom ≫ γ.φH = g ≫ e₂.hom) :
    homologyMap φ ≫ (h₂.homologyIso ≪≫ e₂.symm).hom =
      (h₁.homologyIso ≪≫ e₁.symm).hom ≫ g := by
  rw [← cancel_mono e₂.hom]
  simp [reassoc_of% γ.homologyMap_comm, ← hg]

end CategoryTheory.ShortComplex.LeftHomologyMapData
