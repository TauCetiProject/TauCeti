/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Detecting scalar linearity through a comparison square

A faithful scalar-linear functor detects scalar linearity of a functor composed with it.
Together with Mathlib's detection through a full essentially surjective functor on the source,
this proves invariance under a naturally commuting square of scalar-linear comparisons.
In particular, scalar-linear equivalences of source and target preserve linearity.
-/

public section

namespace CategoryTheory.Functor

variable (R : Type*) [Semiring R]
  {C D E C' D' : Type*} [Category* C] [Category* D] [Category* E]
  [Category* C'] [Category* D']
  [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive C'] [Preadditive D']
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [CategoryTheory.Linear R E]
  [CategoryTheory.Linear R C'] [CategoryTheory.Linear R D']

/-- A faithful scalar-linear functor detects linearity of a functor composed with it. -/
lemma linear_of_comp_faithful (F : C ⥤ D) (G : D ⥤ E) [G.Linear R] [G.Faithful]
    [(F ⋙ G).Linear R] : F.Linear R where
  map_smul f r := G.map_injective (by
    simpa only [comp_map, G.map_smul] using (F ⋙ G).map_smul r f)

/-- Scalar linearity is invariant under a naturally commuting square whose source comparison
is full, essentially surjective and linear, and whose target comparison is faithful and linear.
In particular this applies to a square of scalar-linear equivalences. -/
lemma linear_iff_of_comp_iso (F : C ⥤ D) (G : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D')
    [U.Linear R] [U.Full] [U.EssSurj] [V.Linear R] [V.Faithful]
    (e : F ⋙ V ≅ U ⋙ G) : F.Linear R ↔ G.Linear R := by
  constructor
  · intro h
    let := h
    let := linear_of_iso R e
    exact linear_of_full_essSurj_comp U G
  · intro h
    let := h
    let := linear_of_iso R e.symm
    exact linear_of_comp_faithful R F V

end CategoryTheory.Functor
