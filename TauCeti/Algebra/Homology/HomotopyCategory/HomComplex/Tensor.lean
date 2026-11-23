/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Naturality of tensoring homotopies

Tensoring a homotopy of cochain maps with an object is natural in that object. This file
expresses this naturality as an equality of degree `-1` cochains in Mathlib's Hom complex,
independently of internal Hom complexes or closedness of the monoidal category.
-/

public section

open CategoryTheory MonoidalCategory CochainComplex.HomComplex

namespace Homotopy

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] {K₁ K₂ : CochainComplex C ℤ}

/-- Tensoring a homotopy with an object is natural in that object, expressed by composing
the associated degree `-1` cochain with the degree zero cochains induced by whiskering. -/
lemma ofHom_whiskerLeft_comp_ofHomotopy {f f' : K₁ ⟶ K₂} (h : Homotopy f f') {T' T : C}
    (g : T' ⟶ T) :
    (Cochain.ofHom ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app K₁)).comp
        (Cochain.ofHomotopy ((tensorRight T).mapHomotopy h)) (zero_add _) =
      (Cochain.ofHomotopy ((tensorRight T').mapHomotopy h)).comp
        (Cochain.ofHom ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app K₂))
        (add_zero _) := by
  ext p q hpq
  simp [Cochain.ofHomotopy, whisker_exchange]

end Homotopy
