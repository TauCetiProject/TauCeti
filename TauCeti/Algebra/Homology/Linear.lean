/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Homology commutes with scalar multiplication of chain maps

For a linear category `C`, the map induced on homology by a chain map is linear in the chain
map: `homologyMap (a • φ) i = a • homologyMap φ i`. This is the homological-complex version of
Mathlib's `ShortComplex.homologyMap_smul`, recorded as a TODO in
`Mathlib/Algebra/Homology/Linear.lean`. It identifies, for instance, the map induced by
multiplication by a scalar on a complex of modules with multiplication by that scalar on
homology.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} {c : ComplexShape ι}

/-- The short complex attached to a degree sends a scalar multiple of a chain map to the scalar
multiple of the induced morphism of short complexes. -/
@[simp]
lemma shortComplexFunctor_map_smul (i : ι) (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (shortComplexFunctor C c i).map (a • φ) = a • (shortComplexFunctor C c i).map φ := by
  -- Each component is `smul_f_apply`, stated for the `SMul` instance of the complexes.
  ext <;> exact smul_f_apply _ _ _

/-- The map induced on homology by a scalar multiple of a chain map is the scalar multiple of the
induced map. -/
@[simp]
lemma homologyMap_smul (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    homologyMap (a • φ) i = a • homologyMap φ i := by
  rw [homologyMap, shortComplexFunctor_map_smul]
  exact ShortComplex.homologyMap_smul _ _

end HomologicalComplex
