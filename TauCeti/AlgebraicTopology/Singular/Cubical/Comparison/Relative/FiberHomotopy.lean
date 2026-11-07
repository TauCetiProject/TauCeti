/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Homotopy
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv

/-!
# Relative cubical chains and fibre homotopy equivalences

A fibre homotopy equivalence over `B` induces a chain homotopy equivalence of relative
normalized cubical chains, relative to the preimage of any subset of `B`. No openness,
closedness or cofibration assumption on that subset is needed: the inverse homotopies
stay over the base and hence preserve its preimage.

The maps are the relative chain maps of the specified maps of total spaces. This is
useful for relative cell comparisons in a fibrewise homotopy trivialization.
-/

public noncomputable section

open CategoryTheory ContinuousMap

namespace TauCeti.FiberHomotopyEquiv

universe u v

variable {E E' : Type u} {B : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (S : Set B)

/-- The map of pairs of total spaces relative to the preimages of a base subset. -/
def preimagePairMap :
    TopPair.ofSubset (X := TopCat.of E) (p ⁻¹' S) ⟶
      TopPair.ofSubset (X := TopCat.of E') (q ⁻¹' S) :=
  TopPair.ofSubsetMap (TopCat.ofHom Φ.toFun) fun x hx ↦ by
    simpa only [TopCat.hom_ofHom, Set.mem_preimage, ← ContinuousMap.comp_apply,
      Φ.comp_toFun] using hx

@[simp]
theorem preimagePairMap_fst :
    TopPair.Hom.fst (Φ.preimagePairMap S) = TopCat.ofHom Φ.toFun := by
  rw [preimagePairMap]
  exact TopPair.ofSubsetMap_fst (X := TopCat.of E) _ _

/-- The composite of the induced pair maps is homotopic to the identity as a map of pairs.
The homotopy is chosen from the fibre homotopy equivalence, so it preserves the preimage
of every base subset at every time. -/
def preimagePairCompHomotopy :
    TopPair.Homotopy (Φ.preimagePairMap S ≫ Φ.symm.preimagePairMap S) (𝟙 _) := by
  let H := Φ.left_inv.some
  have hS (t : unitInterval) (x : E) (hx : x ∈ p ⁻¹' S) :
      H (t, x) ∈ p ⁻¹' S := by
    simpa only [Set.mem_preimage, apply_homotopyWith H t x] using hx
  convert TopPair.ofSubsetHomotopy
    (g₀ := TopCat.ofHom (Φ.invFun.comp Φ.toFun)) (g₁ := 𝟙 (TopCat.of E))
    H.toHomotopy hS using 1 <;>
    apply TopPair.hom_ext_of_fst
  · simp only [TopPair.Hom.fst_comp, preimagePairMap_fst, symm_toFun]
    exact (TopPair.ofSubsetMap_fst (X := TopCat.of E) _ _).symm
  · exact (TopPair.ofSubsetMap_fst (X := TopCat.of E) _ _).symm

variable (R : Type u) [Ring R]

/-- A fibre homotopy equivalence induces a chain homotopy equivalence on normalized cubical
chains relative to the preimage of any subset of the base. -/
def relativeCubicalChainHomotopyEquiv :
    _root_.HomotopyEquiv
      ((TopPair.ofSubset (X := TopCat.of E) (p ⁻¹' S)).cubicalChainComplex R)
      ((TopPair.ofSubset (X := TopCat.of E') (q ⁻¹' S)).cubicalChainComplex R) where
  hom := TopPair.cubicalChainComplexMap R (Φ.preimagePairMap S)
  inv := TopPair.cubicalChainComplexMap R (Φ.symm.preimagePairMap S)
  homotopyHomInvId := by
    simpa only [TopPair.cubicalChainComplexMap_comp, TopPair.cubicalChainComplexMap_id]
      using (Φ.preimagePairCompHomotopy S).cubicalChainComplexMap R
  homotopyInvHomId := by
    have hs : Φ.symm.symm.preimagePairMap S = Φ.preimagePairMap S := by
      apply TopPair.hom_ext_of_fst
      simp only [preimagePairMap_fst, symm_toFun, symm_invFun]
      rfl
    simpa only [TopPair.cubicalChainComplexMap_comp, TopPair.cubicalChainComplexMap_id, hs]
      using (Φ.symm.preimagePairCompHomotopy S).cubicalChainComplexMap R

@[simp]
theorem relativeCubicalChainHomotopyEquiv_hom :
    (Φ.relativeCubicalChainHomotopyEquiv S R).hom =
      TopPair.cubicalChainComplexMap R (Φ.preimagePairMap S) := (rfl)

@[simp]
theorem relativeCubicalChainHomotopyEquiv_inv :
    (Φ.relativeCubicalChainHomotopyEquiv S R).inv =
      TopPair.cubicalChainComplexMap R (Φ.symm.preimagePairMap S) := (rfl)

end TauCeti.FiberHomotopyEquiv
