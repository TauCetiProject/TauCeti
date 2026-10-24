/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Detecting linearity through comparison functors

A faithful linear functor detects linearity of a functor composed with it. Together with
Mathlib's detection by full essentially surjective precomposition, this proves that linearity
passes across a naturally commuting square whose horizontal comparison functors are linear
equivalences. This applies to the naturality squares of equivalences between category-valued
pseudofunctors, without choosing inverse comparison functors.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Functor

variable (R : Type*) [Semiring R]
  {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [CategoryTheory.Linear R E]

/-- A faithful linear functor detects linearity after postcomposition. -/
lemma linear_of_comp_faithful (F : C ⥤ D) (G : D ⥤ E) [G.Linear R] [G.Faithful]
    [(F ⋙ G).Linear R] : F.Linear R where
  map_smul f r := by
    apply G.map_injective
    simpa only [CategoryTheory.Functor.comp_map, G.map_smul] using (F ⋙ G).map_smul r f

/-- Postcomposing with a faithful linear functor preserves and reflects linearity. -/
lemma linear_comp_iff_of_faithful (F : C ⥤ D) (G : D ⥤ E) [G.Linear R] [G.Faithful] :
    (F ⋙ G).Linear R ↔ F.Linear R :=
  ⟨fun _ ↦ linear_of_comp_faithful R F G, fun _ ↦ inferInstance⟩

/-- In a naturally commuting square, linearity passes between the vertical functors when the
source comparison is full and essentially surjective and the target comparison is faithful.
Both comparison functors must be linear. In particular this applies to linear equivalences. -/
lemma linear_iff_of_comp_iso {C' D' : Type*} [Category* C'] [Category* D']
    [Preadditive C'] [Preadditive D'] [CategoryTheory.Linear R C']
    [CategoryTheory.Linear R D'] (F : C ⥤ D) (G : C' ⥤ D')
    (U : C ⥤ C') (V : D ⥤ D') [U.Linear R] [U.Full] [U.EssSurj]
    [V.Linear R] [V.Faithful] (e : F ⋙ V ≅ U ⋙ G) : F.Linear R ↔ G.Linear R := by
  constructor
  · intro h
    let := linear_of_iso R e
    exact linear_of_full_essSurj_comp U G
  · intro h
    let := linear_of_iso R e.symm
    exact linear_of_comp_faithful R F V

end TauCeti
