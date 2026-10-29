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

A simplicial map that is injective on a face sends its cell to a cell of the same dimension.
If it also preserves the order of that face's vertices, its realization carries the chosen
characteristic map to the chosen characteristic map of the image cell, and the image of its
`j`-th deleted-vertex face is the `j`-th face of the image cell. The hypothesis is local
to the face: vertices belonging to different faces may be identified or have their order
reversed. The equality holds on the whole characteristic-map domain, including the constant
extension outside the closed ball.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (simplicial complexes as CW complexes).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Set Metric

namespace AbstractSimplicialComplex.RealizationCell

variable {α β : Type*}
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β} {n : ℕ}

section Map

variable [DecidableEq β]

/-- The image cell of a simplicial cell under a map injective on that cell's vertices. -/
def map (c : RealizationCell K n)
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : InjOn f (↑c.1.1 : Set α)) : RealizationCell L n :=
  ⟨TauCeti.PreAbstractSimplicialComplex.SimplicialMap.faceOrderHom f c.1, by
    rw [TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply,
      Finset.card_image_of_injOn hf, c.2]⟩

/-- The face underlying the image cell is the image of the original face. -/
@[simp]
theorem map_face (c : RealizationCell K n)
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : InjOn f (↑c.1.1 : Set α)) :
    (c.map f hf).1 =
      TauCeti.PreAbstractSimplicialComplex.SimplicialMap.faceOrderHom f c.1 :=
  (rfl)

/-- The identity simplicial map fixes each cell. -/
@[simp]
theorem map_id [DecidableEq α] (c : RealizationCell K n) :
    c.map (PreAbstractSimplicialComplex.SimplicialMap.id K.toPreAbstractSimplicialComplex)
      (by simp) = c := by
  apply Subtype.ext
  simp

/-- Mapping a cell successively agrees with mapping it along the composite simplicial map. -/
theorem map_map {γ : Type*} [DecidableEq γ] {P : AbstractSimplicialComplex γ}
    (c : RealizationCell K n)
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : InjOn f (↑c.1.1 : Set α))
    (g : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex)
    (hg : InjOn g (↑(c.1.1.image f) : Set β)) :
    (c.map f hf).map g (by simpa using hg) =
      c.map (g.comp f) (by
        simpa using hg.comp hf (fun _ ha => Finset.mem_image_of_mem f ha)) := by
  apply Subtype.ext
  simp [TauCeti.PreAbstractSimplicialComplex.SimplicialMap.faceOrderHom_comp]

end Map

variable [LinearOrder α] [LinearOrder β]

/-- A vertex map increasing on a cell carries its increasing enumeration to the increasing
enumeration of the image cell. -/
theorem vertexEmbedding_map (c : RealizationCell K n)
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : StrictMonoOn f (↑c.1.1 : Set α)) :
    ⇑(c.map f hf.injOn).vertexEmbedding = f ∘ c.vertexEmbedding := by
  have hmono : StrictMono (f ∘ c.vertexEmbedding) := fun i j hij =>
    hf (c.vertexEmbedding_mem i) (c.vertexEmbedding_mem j) (c.strictMono_vertexEmbedding hij)
  symm
  apply (hmono.range_inj_of_wellFoundedLT
    (c.map f hf.injOn).strictMono_vertexEmbedding).mp
  have himage : Finset.univ.image (f ∘ c.vertexEmbedding) =
      Finset.univ.image (c.map f hf.injOn).vertexEmbedding := by
    simp [← Finset.image_image]
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    congrArg (fun s : Finset β => (s : Set β)) himage

/-- A vertex map increasing on a cell carries its `j`-th deleted-vertex face to the `j`-th
deleted-vertex face of the image cell. -/
theorem face_map (c : RealizationCell K (n + 1))
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hf : StrictMonoOn f (↑c.1.1 : Set α)) (j : Fin (n + 2)) :
    (c.face j).map f (hf.mono (by simp)).injOn = (c.map f hf.injOn).face j := by
  have hj : StrictMonoOn f (↑(c.face j).1.1 : Set α) := hf.mono (by simp)
  have h : ⇑((c.face j).map f hj.injOn).vertexEmbedding =
      ⇑((c.map f hf.injOn).face j).vertexEmbedding := by
    rw [vertexEmbedding_map _ f hj, vertexEmbedding_face, vertexEmbedding_face,
      vertexEmbedding_map _ f hf]
    rfl
  apply Subtype.ext
  apply Subtype.ext
  rw [← image_vertexEmbedding ((c.face j).map f hj.injOn), h, image_vertexEmbedding]

end AbstractSimplicialComplex.RealizationCell

namespace PreAbstractSimplicialComplex.SimplicialMap

open AbstractSimplicialComplex

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β} {n : ℕ}

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
