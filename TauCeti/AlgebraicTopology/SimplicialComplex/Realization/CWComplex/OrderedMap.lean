/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Characteristic maps under ordered simplicial maps

A simplicial map that is injective on a face sends its cell to a cell of the same dimension
(`AbstractSimplicialComplex.RealizationCell.map`). If it also preserves the order of that face's
vertices, its realization carries the chosen characteristic map to the chosen characteristic map
of the image cell. The hypothesis is local to the face: vertices belonging to different faces
may be identified or have their order reversed. The equality holds on the whole
characteristic-map domain, including the constant extension outside the closed ball.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (simplicial complexes as CW complexes).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Set Metric

namespace PreAbstractSimplicialComplex.SimplicialMap

open AbstractSimplicialComplex

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β} {n : ℕ}

/-- The identity simplicial map is strictly increasing on every cell. -/
theorem strictMonoOn_id_realizationCell (K : AbstractSimplicialComplex α) :
    ∀ n (c : RealizationCell K n),
      StrictMonoOn (SimplicialMap.id K.toPreAbstractSimplicialComplex) (↑c.1.1 : Set α) := by
  intro n c
  simpa only [coe_id] using (strictMonoOn_id (s := (↑c.1.1 : Set α)))

/-- Simplexwise strictly increasing simplicial maps remain so under composition. -/
theorem strictMonoOn_comp_realizationCell {γ : Type*} [LinearOrder γ]
    {P : AbstractSimplicialComplex γ}
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : ∀ n (c : RealizationCell K n), StrictMonoOn f (↑c.1.1 : Set α))
    (g : SimplicialMap L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex)
    (hg : ∀ n (c : RealizationCell L n), StrictMonoOn g (↑c.1.1 : Set β)) :
    ∀ n (c : RealizationCell K n), StrictMonoOn (g.comp f) (↑c.1.1 : Set α) := by
  intro n c
  rw [coe_comp]
  refine (hg n (c.map f (hf n c).injOn)).comp (hf n c) ?_
  simpa only [RealizationCell.coe_map_face] using
    (mapsTo_image f (↑c.1.1 : Set α))

/-- On a cell where the vertex map preserves order strictly, realization carries its
characteristic map to the characteristic map of its image cell. No hypothesis is imposed
on vertices outside that cell. -/
theorem realizationMap_characteristicMap
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (c : RealizationCell K n) (hf : StrictMonoOn f (↑c.1.1 : Set α)) (x : Fin n → ℝ) :
    f.realizationMap (c.characteristicMap x) = (c.map f hf.injOn).characteristicMap x := by
  rw [c.characteristicMap_def, (c.map f hf.injOn).characteristicMap_def]
  apply Subtype.ext
  by_cases hx : x ∈ closedBall 0 1 <;>
    simp only [realizationMap_val, simplexCharacteristicMap_apply,
      simplexCharacteristicMap_apply_of_notMem_closedBall, hx, not_false_eq_true,
      simplexClosedBallHomeomorph_val, ← Finsupp.mapDomain_comp, c.vertexEmbedding_map f hf]

end PreAbstractSimplicialComplex.SimplicialMap
