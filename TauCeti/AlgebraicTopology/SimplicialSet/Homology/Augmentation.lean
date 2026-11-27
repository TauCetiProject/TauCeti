/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration

/-!
# Chains of a trivial Kan augmentation

An augmented simplicial set with a trivial Kan augmentation has a simplicial contraction
onto its base. Applying a functor to a preadditive category gives a homotopy equivalence
between its alternating face complex and the image of the base in degree zero. The proof
combines `SSet.Shrinking.ofRLP` with Mathlib’s simplicial chain homotopy and the extra
degeneracy of a constant augmented simplicial object.
-/

public noncomputable section

universe u

open CategoryTheory Limits MorphismProperty AlgebraicTopology SimplicialObject

namespace SSet.Augmented

/-- Applying a functor degreewise to a trivial Kan augmentation gives a chain homotopy
equivalence to the image of its base concentrated in degree zero. In particular this applies
to free abelian groups. -/
theorem homotopyEquivalences_ε_of_rlp_monomorphisms (X : SSet.Augmented.{u})
    (hX : (monomorphisms SSet).rlp X.hom) {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] (F : Type u ⥤ C) :
    HomologicalComplex.homotopyEquivalences C _
      (AlternatingFaceMapComplex.ε.app (((Augmented.whiskering _ _).obj F).obj X)) := by
  let G := (SimplicialObject.whiskering _ _).obj F ⋙ alternatingFaceMapComplex C
  have := isSplitEpi_of_rlp_monomorphisms hX
  let h := Shrinking.ofRLP hX (section_ X.hom) (IsSplitEpi.id X.hom)
  let e : HomotopyEquiv (G.obj X.left) (G.obj ((SimplicialObject.const _).obj X.right)) :=
    { hom := G.map X.hom
      inv := G.map h.section_
      homotopyHomInvId := by
        rw [← G.map_comp, ← G.map_id]
        exact (h.homotopy.toSimplicialObjectHomotopy.whiskerRight F).toChainHomotopy
      homotopyInvHomId := Homotopy.ofEq (by rw [← G.map_comp, h.section_comp, G.map_id]) }
  let e₀ := ((Augmented.ExtraDegeneracy.const X.right).map F).homotopyEquiv
  refine ⟨e.trans e₀, ?_⟩
  refine (HomotopyEquiv.trans_hom e e₀).trans ?_
  let c : X ⟶ Augmented.const.obj X.right := { left := X.hom, right := 𝟙 _ }
  let W := (Augmented.whiskering _ _).obj F
  -- The first forward map is induced by the whiskered augmentation. The forward map of
  -- ExtraDegeneracy.homotopyEquiv is definitionally the chain augmentation.
  change (alternatingFaceMapComplex C).map (W.map c).left ≫
      AlternatingFaceMapComplex.ε.app (W.obj (Augmented.const.obj X.right)) = _
  refine (AlternatingFaceMapComplex.ε.naturality (W.map c)).trans ?_
  have hid : (ChainComplex.single₀ C).map (F.map (𝟙 X.right)) = 𝟙 _ := by simp
  exact (congrArg (AlternatingFaceMapComplex.ε.app _ ≫ ·) hid).trans (Category.comp_id _)

end SSet.Augmented
