/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic

/-!
# Simplicial isomorphisms permute CW cells

Mutually inverse simplicial maps induce dimension-preserving equivalences of the cells of
weak realizations. Their realization homeomorphisms carry open cells, closed cells, and cell
frontiers onto the corresponding cells. No compatibility with the chosen vertex orders is
required: those orders parametrize the cells, but do not affect their underlying subsets.

The equivalences respect identities, inverses, and composition, so a simplicial group action
can act on the cells as well as on the realization. This is the cell-permutation input for
constructing CW structures on orbit spaces of simplicial actions.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (simplicial CW structures).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public noncomputable section

open AbstractSimplicialComplex Set Topology
open _root_.PreAbstractSimplicialComplex
open _root_.PreAbstractSimplicialComplex.SimplicialMap

namespace TauCeti.PreAbstractSimplicialComplex.SimplicialMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  {M : AbstractSimplicialComplex γ}
  (f : _root_.PreAbstractSimplicialComplex.SimplicialMap
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
  (g : _root_.PreAbstractSimplicialComplex.SimplicialMap
    L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
  (hgf : g.comp f = SimplicialMap.id K.toPreAbstractSimplicialComplex)
  (hfg : f.comp g = SimplicialMap.id L.toPreAbstractSimplicialComplex)

/-- Inverse simplicial maps give a dimension-preserving equivalence of simplicial CW cells.
The equivalence takes the image of the underlying face and does not use a vertex order. -/
def cellEquiv (n : ℕ) : RealizationCell K n ≃ RealizationCell L n := by
  have hf := injective_of_comp_eq_id f g hgf
  have hg := injective_of_comp_eq_id g f hfg
  exact
    { toFun := fun c => ⟨faceOrderHom f c.1, by
        rw [coe_faceOrderHom_apply, Finset.card_image_of_injective _ hf, c.2]⟩
      invFun := fun c => ⟨faceOrderHom g c.1, by
        rw [coe_faceOrderHom_apply, Finset.card_image_of_injective _ hg, c.2]⟩
      left_inv := fun c => Subtype.ext (congrArg (fun m => m c.1)
        ((faceOrderHom_comp g f).symm.trans (by rw [hgf, faceOrderHom_id])))
      right_inv := fun c => Subtype.ext (congrArg (fun m => m c.1)
        ((faceOrderHom_comp f g).symm.trans (by rw [hfg, faceOrderHom_id]))) }

/-- The face of the image cell is the image of its vertices. -/
@[simp]
theorem cellEquiv_face {n : ℕ} (c : RealizationCell K n) :
    (cellEquiv f g hgf hfg n c).1.1 = c.1.1.image f :=
  coe_faceOrderHom_apply f c.1

/-- The inverse cell equivalence is obtained by exchanging the two simplicial maps. -/
theorem cellEquiv_symm (n : ℕ) :
    (cellEquiv f g hgf hfg n).symm = cellEquiv g f hfg hgf n :=
  -- This definitional inverse is intentional: `cellEquiv` uses `faceOrderHom f` and
  -- `faceOrderHom g` symmetrically, so exchanging the maps swaps `toFun` and `invFun`
  -- exactly as `Equiv.symm` does; proof irrelevance identifies the remaining proof fields.
  (rfl)

/-- The face of an inverse image cell is the image under the inverse vertex map. -/
@[simp]
theorem cellEquiv_symm_face {n : ℕ} (c : RealizationCell L n) :
    ((cellEquiv f g hgf hfg n).symm c).1.1 = c.1.1.image g := by
  rw [cellEquiv_symm, cellEquiv_face]

/-- The identity simplicial map fixes every cell. -/
@[simp]
theorem cellEquiv_id (n : ℕ) :
    cellEquiv (SimplicialMap.id K.toPreAbstractSimplicialComplex)
      (SimplicialMap.id K.toPreAbstractSimplicialComplex)
      (id_comp _) (id_comp _) n = Equiv.refl (RealizationCell K n) := by
  apply Equiv.ext
  intro c
  apply Subtype.ext
  apply Subtype.ext
  simp

/-- Cell equivalences compose in the same order as the simplicial maps. -/
theorem cellEquiv_comp
    (f' : _root_.PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex M.toPreAbstractSimplicialComplex)
    (g' : _root_.PreAbstractSimplicialComplex.SimplicialMap
      M.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (hgf' : g'.comp f' = SimplicialMap.id L.toPreAbstractSimplicialComplex)
    (hfg' : f'.comp g' = SimplicialMap.id M.toPreAbstractSimplicialComplex)
    (n : ℕ) :
    cellEquiv (f'.comp f) (g.comp g')
      (by rw [comp_assoc, ← comp_assoc g' f' f, hgf', id_comp, hgf])
      (by rw [comp_assoc, ← comp_assoc f g g', hfg, id_comp, hfg']) n =
      (cellEquiv f g hgf hfg n).trans (cellEquiv f' g' hgf' hfg' n) := by
  apply Equiv.ext
  intro c
  apply Subtype.ext
  apply Subtype.ext
  simp only [Equiv.trans_apply, cellEquiv_face, coe_comp, Finset.image_comp]

section Realization

variable [LinearOrder α] [LinearOrder β]

/-- A simplicial isomorphism carries an open CW cell onto the cell of the image face. -/
theorem image_realizationMap_openCell {n : ℕ} (c : RealizationCell K n) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    f.realizationMap '' RelCWComplex.openCell n ((realizationCellEquiv K n).symm c) =
      RelCWComplex.openCell n
        ((realizationCellEquiv L n).symm (cellEquiv f g hgf hfg n c)) := by
  rw [openCell_realizationCellEquiv_symm, openCell_realizationCellEquiv_symm]
  apply image_realizationMap_ofPred_support f g hgf hfg
    (P := (· = c.1.1)) (Q := (· = (cellEquiv f g hgf hfg n c).1.1))
  simp only [cellEquiv_face, Finset.image_inj (injective_of_comp_eq_id f g hgf), implies_true]

/-- A simplicial isomorphism carries a closed CW cell onto the closed cell of the image face. -/
theorem image_realizationMap_closedCell {n : ℕ} (c : RealizationCell K n) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    f.realizationMap '' RelCWComplex.closedCell n ((realizationCellEquiv K n).symm c) =
      RelCWComplex.closedCell n
        ((realizationCellEquiv L n).symm (cellEquiv f g hgf hfg n c)) := by
  rw [closedCell_realizationCellEquiv_symm, closedCell_realizationCellEquiv_symm]
  apply image_realizationMap_ofPred_support f g hgf hfg
    (P := (· ⊆ c.1.1)) (Q := (· ⊆ (cellEquiv f g hgf hfg n c).1.1))
  simp only [cellEquiv_face, Finset.image_subset_image_iff (injective_of_comp_eq_id f g hgf),
    implies_true]

/-- A simplicial isomorphism carries a cell frontier onto the frontier of its image cell. -/
theorem image_realizationMap_cellFrontier {n : ℕ} (c : RealizationCell K n) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    f.realizationMap '' RelCWComplex.cellFrontier n ((realizationCellEquiv K n).symm c) =
      RelCWComplex.cellFrontier n
        ((realizationCellEquiv L n).symm (cellEquiv f g hgf hfg n c)) := by
  rw [cellFrontier_realizationCellEquiv_symm, cellFrontier_realizationCellEquiv_symm]
  apply image_realizationMap_ofPred_support f g hgf hfg
    (P := (· ⊂ c.1.1)) (Q := (· ⊂ (cellEquiv f g hgf hfg n c).1.1))
  simp only [cellEquiv_face, Finset.image_ssubset_image (injective_of_comp_eq_id f g hgf),
    implies_true]

end Realization

end TauCeti.PreAbstractSimplicialComplex.SimplicialMap
