/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Connect

/-!
# Naturality of the negative half of a connected complex

Mathlib's `CochainComplex.ConnectData` connects a chain complex `K` and a cochain complex `L` into a
cochain complex indexed by `ℤ`, and `CochainComplex.ConnectData.restrictionLEIso` identifies its
restriction to the degrees `≤ -1` with `K`. This file shows that this identification is natural
with respect to the morphisms of connected complexes `CochainComplex.ConnectData.map`
(`CochainComplex.ConnectData.restrictionMap_map_comp_restrictionLEIso_hom`). This is what lets
a short exact sequence of connected complexes, restricted to negative degrees, be compared with
the short exact sequence of the chain complexes `K`, for instance in order to compare their
connecting maps.
-/

public section

open CategoryTheory Limits

namespace CochainComplex.ConnectData

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {K K' : ChainComplex C ℕ}
  {L L' : CochainComplex C ℕ} (h : ConnectData K L) (h' : ConnectData K' L')

/-- **The identification of the negative half of a connected complex is natural.** Restricting a
morphism of connected complexes to the degrees `≤ -1` gives, through
`CochainComplex.ConnectData.restrictionLEIso`, the morphism of chain complexes it is built from. -/
@[reassoc]
theorem restrictionMap_map_comp_restrictionLEIso_hom (fK : K ⟶ K') (fL : L ⟶ L')
    (f_comm : fK.f 0 ≫ h'.d₀ = h.d₀ ≫ fL.f 0) :
    HomologicalComplex.restrictionMap (h.map h' fK fL f_comm)
        (ComplexShape.embeddingUpIntLE (-1)) ≫ h'.restrictionLEIso.hom =
      h.restrictionLEIso.hom ≫ fK := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.restrictionMap_f' _ _ (show (ComplexShape.embeddingUpIntLE (-1)).f n =
      Int.negSucc n by simp; lia)]
  -- The two comparisons of the restricted complex of `h'` cancel, and in negative degrees the map
  -- of connected complexes is `fK` by definition. The associativity steps are applied as terms:
  -- the objects of the restricted complexes are only definitionally equal.
  exact (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _)

end CochainComplex.ConnectData
