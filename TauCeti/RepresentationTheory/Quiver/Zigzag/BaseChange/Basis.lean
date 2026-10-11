/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.BaseChange.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basis

/-!
# Coefficient maps on skew-zigzag bases

The coefficient map fixes the vertex, arrow and chosen-volume basis family of a finite graph
without isolated vertices. The same incident edges are used over both coefficient rings.
-/

public section

namespace SimpleGraph

open TauCeti TauCeti.PathAlgebra TauCeti.DoubledQuiver

universe u w z

variable {k : Type w} {l : Type z} [CommRing k] [CommRing l]
  {V : Type u} (G : SimpleGraph V) [Finite V] (c : SkewZigzagParameter k G)

/-- The coefficient map respects the vertex, arrow and chosen-volume basis family. -/
@[simp]
theorem skewZigzagBaseChange_skewZigzagBasisFun (f : k →+* l)
    (t : ∀ i : V, {j : V // G.Adj i j}) (b : ZigzagBasisIndex G) :
    skewZigzagBaseChange G f c (skewZigzagBasisFun k G c t b) =
      skewZigzagBasisFun l G (c.map (f : k →* l)) t b := by
  rcases b with i | d | i
  · rw [skewZigzagBasisFun_inl, skewZigzagBasisFun_inl, vertexIdempotent_eq_ofPath,
      skewZigzagBaseChange_skewZigzagMk_ofPath, vertexIdempotent_eq_ofPath]
  · rw [skewZigzagBasisFun_inr_inl, skewZigzagBasisFun_inr_inl,
      ofArrow_eq_ofPath_arrowPath, skewZigzagBaseChange_skewZigzagMk_ofPath,
      ofArrow_eq_ofPath_arrowPath]
  · rw [skewZigzagBasisFun_inr_inr, skewZigzagBasisFun_inr_inr, skewZigzagVolume_def,
      skewZigzagVolume_def, backtrackElem_eq_ofPath,
      skewZigzagBaseChange_skewZigzagMk_ofPath, backtrackElem_eq_ofPath]

end SimpleGraph
