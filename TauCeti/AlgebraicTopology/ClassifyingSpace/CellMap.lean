/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardComplex

/-!
# Maps of simplices in Milnor's countable join

A homomorphism sends a simplex of the countable join to a simplex of the same dimension,
even when the homomorphism is not injective: distinct vertices of a simplex have distinct
indices, which the map preserves. The increasing-index orientation is preserved as well.
Consequently the map commutes with deleting vertices and with forgetting indices to obtain
the tuple indexing a standard-resolution generator.

The characteristic-map formula identifies this cell map with the existing continuous map
`MonoidHom.universalGSpaceMap`. These formulas supply the combinatorial input to naturality
of the comparison between join chains and the standard resolution.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapter I.
-/

public section

noncomputable section

open TauCeti AbstractSimplicialComplex

namespace MonoidHom

universe u v w

variable {G : Type u} {H : Type v} {K : Type w} [MulOne G] [MulOne H] [MulOne K]

attribute [local instance] universalGSpaceVertexOrder

-- The vertex-order instance fixes decidable equality differently from indexedJoinMap.
-- Rebuild its simplicial-map structure with that instance for RealizationCell.map.
private def universalGSpaceSimplicialMap (φ : G →* H) :
    PreAbstractSimplicialComplex.SimplicialMap
      (indexedJoin fun _ : ℕ => G).toPreAbstractSimplicialComplex
      (indexedJoin fun _ : ℕ => H).toPreAbstractSimplicialComplex where
  toFun v := ⟨v.1, φ v.2⟩
  map_face' σ hσ := by
    rw [mem_toPreAbstractSimplicialComplex] at hσ ⊢
    rw [mem_indexedJoin_iff] at hσ ⊢
    refine ⟨hσ.1.image _, ?_⟩
    intro v hv w hw heq
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg (fun v : Σ _ : ℕ, G => (⟨v.1, φ v.2⟩ : Σ _ : ℕ, H))
      (hσ.2 hv' hw' heq)

private theorem universalGSpaceMap_strictMonoOn (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    StrictMonoOn (universalGSpaceSimplicialMap φ)
      (c.1.1 : Set (Σ _ : ℕ, G)) := by
  intro v hv w hw hvw
  exact universalGSpaceVertexOrder_lt_of_fst_lt
    ((universalGSpaceVertexOrder_lt_iff c.1.2 hv hw).mp hvw)

/-- Apply a homomorphism to the labels of a simplex, preserving its indices and dimension. -/
def universalGSpaceCellMap (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (indexedJoin fun _ : ℕ => H).RealizationCell n :=
  c.map (universalGSpaceSimplicialMap φ)
    (universalGSpaceMap_strictMonoOn φ c).injOn

/-- The underlying face is the image under relabelling vertices. -/
@[simp]
theorem universalGSpaceCellMap_val [DecidableEq (Σ _ : ℕ, H)] (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (φ.universalGSpaceCellMap c).1.1 =
      c.1.1.image (fun v : Σ _ : ℕ, G => (⟨v.1, φ v.2⟩ : Σ _ : ℕ, H)) := by
  ext v
  simp [universalGSpaceCellMap, RealizationCell.map_face,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply,
    universalGSpaceSimplicialMap]

/-- Relabelling preserves the increasing-index vertex enumeration. -/
@[simp]
theorem universalGSpaceCellMap_vertexEmbedding (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (j : Fin (n + 1)) :
    (φ.universalGSpaceCellMap c).vertexEmbedding j =
      ⟨(c.vertexEmbedding j).1, φ (c.vertexEmbedding j).2⟩ :=
  congrFun (c.vertexEmbedding_map _ (universalGSpaceMap_strictMonoOn φ c)) j

/-- The tuple of labels of an image simplex is the image of its tuple of labels. -/
@[simp]
theorem universalGSpaceCellLabels_universalGSpaceCellMap (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    universalGSpaceCellLabels (φ.universalGSpaceCellMap c) = φ ∘ universalGSpaceCellLabels c := by
  funext j
  simp

/-- Relabelling commutes with deleting the vertex at a specified position. -/
@[simp]
theorem universalGSpaceCellMap_face (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell (n + 1)) (j : Fin (n + 2)) :
    φ.universalGSpaceCellMap (c.face j) = (φ.universalGSpaceCellMap c).face j := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [← RealizationCell.image_vertexEmbedding, ← RealizationCell.image_vertexEmbedding]
  congr 1
  funext i
  simp [RealizationCell.vertexEmbedding_face]

/-- Identity homomorphisms fix simplices. -/
@[simp]
theorem universalGSpaceCellMap_id {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (MonoidHom.id G).universalGSpaceCellMap c = c := by
  refine Subtype.ext (Subtype.ext ?_)
  simp

/-- Relabelling simplices respects composition of homomorphisms. -/
@[simp]
theorem universalGSpaceCellMap_comp (ψ : H →* K) (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (ψ.comp φ).universalGSpaceCellMap c =
      ψ.universalGSpaceCellMap (φ.universalGSpaceCellMap c) := by
  refine Subtype.ext (Subtype.ext ?_)
  simp [Finset.image_image, Function.comp_def]

/-- Relabelling intertwines translation by a group element with translation by its image. -/
@[simp]
theorem universalGSpaceCellMap_smul {G : Type u} {H : Type v} [Group G] [Group H]
    (φ : G →* H) {n : ℕ} (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    φ.universalGSpaceCellMap (g • c) = φ g • φ.universalGSpaceCellMap c := by
  refine Subtype.ext (Subtype.ext ?_)
  simp only [universalGSpaceCellMap_val, smul_realizationCell_face,
    Finset.map_eq_image, Finset.image_image]
  congr 1
  funext ⟨i, g'⟩
  simp

section Group

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

/-- Relabelling simplices as a map equivariant along the group homomorphism. -/
abbrev universalGSpaceCellMulActionHom (φ : G →* H) (n : ℕ) :
    (indexedJoin fun _ : ℕ => G).RealizationCell n →ₑ[φ]
      (indexedJoin fun _ : ℕ => H).RealizationCell n where
  toFun := φ.universalGSpaceCellMap
  map_smul' := universalGSpaceCellMap_smul φ

/-- The identity homomorphism gives the identity equivariant map on simplices. -/
@[simp]
theorem universalGSpaceCellMulActionHom_id (n : ℕ) :
    (MonoidHom.id G).universalGSpaceCellMulActionHom n = MulActionHom.id G :=
  MulActionHom.ext universalGSpaceCellMap_id

/-- Equivariant relabelling of simplices respects composition. -/
@[simp]
theorem universalGSpaceCellMulActionHom_comp (ψ : H →* K) (φ : G →* H) (n : ℕ) :
    (ψ.comp φ).universalGSpaceCellMulActionHom n =
      (ψ.universalGSpaceCellMulActionHom n).comp (φ.universalGSpaceCellMulActionHom n)
        (κ := ⟨rfl⟩) :=
  MulActionHom.ext (universalGSpaceCellMap_comp ψ φ)

end Group

/-- The continuous total-space map carries each characteristic map to the characteristic map
of the relabelled simplex, with the same disk coordinates. -/
theorem universalGSpaceMap_characteristicMap (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (x : Fin n → ℝ) :
    φ.universalGSpaceMap (c.characteristicMap x) =
      (φ.universalGSpaceCellMap c).characteristicMap x := by
  -- The ordered and original simplicial maps use different decidable-equality instances.
  -- Identify their realization maps by coordinates before applying the ordered-cell formula.
  have hmap : φ.universalGSpaceMap = (universalGSpaceSimplicialMap φ).realizationMap :=
    ContinuousMap.ext fun y => Subtype.ext (by simp [universalGSpaceSimplicialMap])
  rw [hmap]
  exact PreAbstractSimplicialComplex.SimplicialMap.realizationMap_characteristicMap _ c
    (universalGSpaceMap_strictMonoOn φ c) x

end MonoidHom
