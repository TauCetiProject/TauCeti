/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import TauCeti.AlgebraicTopology.SimplexCategory.Endpoint
public import TauCeti.AlgebraicTopology.SimplicialObject.II
public import TauCeti.Order.Hom.Adjoint
import TauCeti.Order.Fin.Basic

/-!
# Finite-ordinal cut duality (`Δ₊ᵒᵖ ≅ Δ_∂`)

This file factors `SimplexCategory.II.leftOp : Δᵒᵖ ⥤ Δ` through the endpoint-preserving
subcategory `TauCeti.SimplexCategory.EndpointPreserving` (`Δ_∂`) and extends it to a strict
category isomorphism `Cat.of AugmentedSimplexCategoryᵒᵖ ≅ Cat.of EndpointPreserving`:

* `TauCeti.SimplexCategory.iiOpToEndpointPreserving`: `Δᵒᵖ ⥤ Δ_∂`, sending `⦋n⦌` to `⦋n + 1⦌`
  and `α` to the cut-counting map `x ↦ #{i | (α i).castSucc < x}`.
* `TauCeti.SimplexCategory.augmentedOpToEndpointPreserving`: `Δ₊ᵒᵖ ⥤ Δ_∂`, obtained via
  `WithInitial.opEquiv` and `WithTerminal.liftToTerminal`.
* `TauCeti.SimplexCategory.EndpointPreserving.cutInv`: right-adjoint inverse on positive-length
  hom-sets `⦋n + 1⦌ ⟶ ⦋m + 1⦌` in `Δ_∂` to `⦋m⦌ ⟶ ⦋n⦌` in `Δ`.
* `TauCeti.SimplexCategory.endpointPreservingToAugmentedOp`: the strict inverse functor
  `Δ_∂ ⥤ Δ₊ᵒᵖ`.
* `TauCeti.SimplexCategory.augmentedOpIsoEndpointPreserving`:
  `Cat.of AugmentedSimplexCategoryᵒᵖ ≅ Cat.of EndpointPreserving`.

## References

* S. Schanuel and R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques **27** (1986), 81–83.
* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Observation 3.3.6 and Remark 3.3.8.
-/

public section

open CategoryTheory Opposite
open scoped Simplicial

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-! ### Factorization of `SimplexCategory.II` through `EndpointPreserving` -/

/-- Factorization of `SimplexCategory.II.leftOp : Δᵒᵖ ⥤ Δ` through the endpoint-preserving
subcategory `EndpointPreserving`. -/
@[expose] def iiOpToEndpointPreserving : _root_.SimplexCategoryᵒᵖ ⥤ EndpointPreserving where
  obj x := ⟨⦋x.unop.len + 1⦌⟩
  map f := ⟨(II.map f.unop).unop,
    (Hom.preservesEndpoints_iff _).mpr ⟨II.map'_zero _, II.map'_last _⟩⟩
  map_id x := WideSubcategory.hom_ext _ <| congrArg Quiver.Hom.unop (II.map_id x.unop)
  map_comp f g :=
    WideSubcategory.hom_ext _ <| congrArg Quiver.Hom.unop (II.map_comp g.unop f.unop)

/-- Object map of `iiOpToEndpointPreserving`. -/
@[simp]
theorem iiOpToEndpointPreserving_obj (x : _root_.SimplexCategoryᵒᵖ) :
    iiOpToEndpointPreserving.obj x = ⟨⦋x.unop.len + 1⦌⟩ :=
  (rfl)

/-- Underlying simplex-category morphism of `iiOpToEndpointPreserving.map f`. -/
@[simp]
theorem iiOpToEndpointPreserving_map_hom {x y : _root_.SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    (iiOpToEndpointPreserving.map f).hom = (II.map f.unop).unop :=
  (rfl)

/-- Composing `iiOpToEndpointPreserving` with the inclusion into `SimplexCategory` recovers
`SimplexCategory.II.leftOp`. -/
@[simp]
theorem iiOpToEndpointPreserving_comp_inclusion :
    iiOpToEndpointPreserving ⋙ wideSubcategoryInclusion preservesEndpoints = II.leftOp :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <| by
    dsimp only [Functor.comp_map, wideSubcategoryInclusion, wideInducedFunctor]
    exact iiOpToEndpointPreserving_map_hom f

/-- `iiOpToEndpointPreserving` sends the opposite coface `(δ i).op : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δᵒᵖ`
to the restricted codegeneracy `EndpointPreserving.σ i : ⦋n + 2⦌ ⟶ ⦋n + 1⦌` in `Δ_∂`. -/
@[simp]
theorem iiOpToEndpointPreserving_map_δ {n : ℕ} (i : Fin (n + 2)) :
    iiOpToEndpointPreserving.map (_root_.SimplexCategory.δ i).op = EndpointPreserving.σ i :=
  WideSubcategory.hom_ext _ <|
    (iiOpToEndpointPreserving_map_hom _).trans <|
      (congrArg Quiver.Hom.unop (II_δ i)).trans (EndpointPreserving.σ_hom i).symm

/-- `iiOpToEndpointPreserving` sends the opposite codegeneracy `(σ i).op : ⦋n⦌ ⟶ ⦋n + 1⦌` in
`Δᵒᵖ` to the restricted interior coface `EndpointPreserving.δ i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` in `Δ_∂`
(omitting `i.succ.castSucc`). -/
@[simp]
theorem iiOpToEndpointPreserving_map_σ {n : ℕ} (i : Fin (n + 1)) :
    iiOpToEndpointPreserving.map (_root_.SimplexCategory.σ i).op = EndpointPreserving.δ i :=
  WideSubcategory.hom_ext _ <|
    (iiOpToEndpointPreserving_map_hom _).trans <|
      (congrArg Quiver.Hom.unop (II_σ i)).trans (EndpointPreserving.δ_hom i).symm

/-! ### Finite-ordinal cut duality (`Δ₊ᵒᵖ ≅ Δ_∂`) -/

/-- The finite-ordinal cut functor `Δ₊ᵒᵖ ⥤ Δ_∂` sending `∅` (`WithInitial.star`) to `⦋0⦌` and
`⦋k⦌` (`WithInitial.of ⦋k⦌`) to `⦋k + 1⦌`. -/
@[expose] def augmentedOpToEndpointPreserving :
    AugmentedSimplexCategoryᵒᵖ ⥤ EndpointPreserving :=
  (WithInitial.opEquiv _root_.SimplexCategory).functor ⋙
    WithTerminal.liftToTerminal iiOpToEndpointPreserving
      (Limits.IsTerminal.ofUnique (⟨⦋0⦌⟩ : EndpointPreserving))

/-- `augmentedOpToEndpointPreserving` sends the empty ordinal `op WithInitial.star` to `⦋0⦌`. -/
@[simp]
theorem augmentedOpToEndpointPreserving_obj_star :
    augmentedOpToEndpointPreserving.obj (op (WithInitial.star : AugmentedSimplexCategory)) =
      ⟨⦋0⦌⟩ :=
  (rfl)

/-- `augmentedOpToEndpointPreserving` sends `op (WithInitial.of x)` to `⦋x.len + 1⦌`. -/
@[simp]
theorem augmentedOpToEndpointPreserving_obj_of (x : _root_.SimplexCategory) :
    augmentedOpToEndpointPreserving.obj (op (WithInitial.of x)) = ⟨⦋x.len + 1⦌⟩ :=
  (rfl)

/-- On morphisms between nonempty ordinals `WithInitial.of y ⟶ WithInitial.of x`,
`augmentedOpToEndpointPreserving` agrees with `iiOpToEndpointPreserving`. -/
@[simp]
theorem augmentedOpToEndpointPreserving_map_of {x y : _root_.SimplexCategory}
    (f : (WithInitial.of y : AugmentedSimplexCategory) ⟶ WithInitial.of x) :
    augmentedOpToEndpointPreserving.map f.op =
      iiOpToEndpointPreserving.map (WithInitial.down f).op :=
  (rfl)

/-- On morphisms in the image of `AugmentedSimplexCategory.inclusion`,
`augmentedOpToEndpointPreserving` agrees with `iiOpToEndpointPreserving`. -/
theorem augmentedOpToEndpointPreserving_map_inclusion {x y : _root_.SimplexCategory} (f : y ⟶ x) :
    augmentedOpToEndpointPreserving.map (AugmentedSimplexCategory.inclusion.map f).op =
      iiOpToEndpointPreserving.map f.op :=
  (rfl)

/-- Precomposing `augmentedOpToEndpointPreserving` with `AugmentedSimplexCategory.inclusion.op`
recovers `iiOpToEndpointPreserving`. -/
@[simp]
theorem inclusion_op_comp_augmentedOpToEndpointPreserving :
    AugmentedSimplexCategory.inclusion.op ⋙ augmentedOpToEndpointPreserving =
      iiOpToEndpointPreserving :=
  (rfl)

/-- `augmentedOpToEndpointPreserving` sends any morphism `op (WithInitial.of x) ⟶ op .star`
to the terminal morphism `EndpointPreserving.constToZero ⦋x.len + 1⦌`. -/
@[simp]
theorem augmentedOpToEndpointPreserving_map_to_star (x : _root_.SimplexCategory)
    (f : (op (WithInitial.of x) : AugmentedSimplexCategoryᵒᵖ) ⟶ op WithInitial.star) :
    augmentedOpToEndpointPreserving.map f = EndpointPreserving.constToZero ⦋x.len + 1⦌ :=
  Subsingleton.elim (α := _ ⟶ (⟨⦋0⦌⟩ : EndpointPreserving)) _ _

/-- `augmentedOpToEndpointPreserving` sends the opposite coface `(inclusion.map (δ i)).op`
(`⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ₊ᵒᵖ`) to `EndpointPreserving.σ i : ⦋n + 2⦌ ⟶ ⦋n + 1⦌`. -/
theorem augmentedOpToEndpointPreserving_map_δ {n : ℕ} (i : Fin (n + 2)) :
    augmentedOpToEndpointPreserving.map
        (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.δ i)).op =
      EndpointPreserving.σ i :=
  (augmentedOpToEndpointPreserving_map_inclusion _).trans (iiOpToEndpointPreserving_map_δ i)

/-- `augmentedOpToEndpointPreserving` sends the opposite codegeneracy `(inclusion.map (σ i)).op`
(`⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ₊ᵒᵖ`) to `EndpointPreserving.δ i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` (omitting
`i.succ.castSucc`). -/
theorem augmentedOpToEndpointPreserving_map_σ {n : ℕ} (i : Fin (n + 1)) :
    augmentedOpToEndpointPreserving.map
        (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.σ i)).op =
      EndpointPreserving.δ i :=
  (augmentedOpToEndpointPreserving_map_inclusion _).trans (iiOpToEndpointPreserving_map_σ i)

private theorem EndpointPreserving.rightAdjoint_castSucc_ne_last {n m : ℕ}
    (g : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩) (y : Fin (m + 1)) :
    g.hom.toOrderHom.rightAdjoint (EndpointPreserving.toOrderHom_zero g) y.castSucc ≠
      Fin.last (n + 1) := by
  intro h
  have hle : g.hom.toOrderHom (Fin.last (n + 1)) ≤ y.castSucc :=
    (OrderHom.le_rightAdjoint_iff _ _).mp h.symm.le
  rw [EndpointPreserving.toOrderHom_last] at hle
  exact (Fin.castSucc_lt_last y).not_ge hle

/-- Given an endpoint-preserving map `g : ⦋n + 1⦌ ⟶ ⦋m + 1⦌`, its right adjoint preserves `Fin.last`
and maps non-last elements below `Fin.last (n + 1)`, hence cuts down to `⦋m⦌ ⟶ ⦋n⦌`. -/
def EndpointPreserving.cutInv {n m : ℕ}
    (g : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩) : ⦋m⦌ ⟶ ⦋n⦌ :=
  Hom.mk
    { toFun y :=
        (g.hom.toOrderHom.rightAdjoint (EndpointPreserving.toOrderHom_zero g) y.castSucc).castPred
          (EndpointPreserving.rightAdjoint_castSucc_ne_last g y)
      monotone' _ _ h :=
        Fin.castSucc_le_castSucc_iff.mp <| by
          simpa only [Fin.castSucc_castPred] using
            (g.hom.toOrderHom.rightAdjoint (EndpointPreserving.toOrderHom_zero g)).monotone
              (Fin.castSucc_le_castSucc_iff.mpr h) }

/-- Embedding `EndpointPreserving.cutInv g y` via `Fin.castSucc` recovers the right adjoint of `g`
at `y.castSucc`. -/
@[simp]
theorem EndpointPreserving.castSucc_cutInv_apply {n m : ℕ}
    (g : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩) (y : Fin (m + 1)) :
    ((EndpointPreserving.cutInv g).toOrderHom y).castSucc =
      g.hom.toOrderHom.rightAdjoint (EndpointPreserving.toOrderHom_zero g) y.castSucc :=
  Fin.castSucc_castPred _ (EndpointPreserving.rightAdjoint_castSucc_ne_last g y)

/-- Galois characterization of `EndpointPreserving.cutInv g`:
`x ≤ (EndpointPreserving.cutInv g).toOrderHom y ↔ g.hom.toOrderHom x.castSucc ≤ y.castSucc`. -/
@[simp]
theorem EndpointPreserving.le_cutInv_iff {n m : ℕ}
    (g : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩)
    (x : Fin (n + 1)) (y : Fin (m + 1)) :
    x ≤ (EndpointPreserving.cutInv g).toOrderHom y ↔ g.hom.toOrderHom x.castSucc ≤ y.castSucc := by
  rw [← Fin.castSucc_le_castSucc_iff, EndpointPreserving.castSucc_cutInv_apply]
  exact OrderHom.le_rightAdjoint_iff _ _

/-- On hom-sets between positive-length boundary objects `⦋n + 1⦌ ⟶ ⦋m + 1⦌`, applying the
endpoint-preserving lift of `SimplexCategory.II.map` to `(EndpointPreserving.cutInv g).op`
recovers `g`. -/
@[simp]
theorem iiOpToEndpointPreserving_map_cutInv {n m : ℕ}
    (g : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩) :
    iiOpToEndpointPreserving.map (EndpointPreserving.cutInv g).op = g := by
  refine WideSubcategory.hom_ext _ <| Hom.ext _ _ <| OrderHom.ext _ _ <|
    funext fun (x : Fin (n + 2)) ↦ ?_
  have hmap : (iiOpToEndpointPreserving.map (EndpointPreserving.cutInv g).op).hom.toOrderHom x =
      II.map' (EndpointPreserving.cutInv g).toOrderHom x :=
    II_map_unop_toOrderHom_apply (EndpointPreserving.cutInv g) x
  rw [hmap]
  refine Fin.eq_iff_forall_castSucc_lt_and_le.mpr ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · have hiff : II.map' (EndpointPreserving.cutInv g).toOrderHom x ≤ y.castSucc ↔
        g.hom.toOrderHom x ≤ y.castSucc := by
      rw [II.map'_le_castSucc_iff, EndpointPreserving.castSucc_cutInv_apply]
      exact OrderHom.le_rightAdjoint_iff _ _
    exact lt_of_not_ge fun h ↦ hy.not_ge (hiff.mp h)
  · rw [II.map'_le_castSucc_iff, EndpointPreserving.castSucc_cutInv_apply]
    exact (OrderHom.le_rightAdjoint_iff _ _).mpr hy

/-- On hom-sets between positive-length boundary objects `⦋n + 1⦌ ⟶ ⦋m + 1⦌`,
`EndpointPreserving.cutInv` is left inverse to the endpoint-preserving lift of
`SimplexCategory.II.map`. -/
@[simp]
theorem EndpointPreserving.cutInv_iiOpToEndpointPreserving_map {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    EndpointPreserving.cutInv (iiOpToEndpointPreserving.map α.op) = α := by
  let g : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩ := iiOpToEndpointPreserving.map α.op
  change EndpointPreserving.cutInv g = α
  refine Hom.ext _ _ <| OrderHom.ext _ _ <| funext fun (y : Fin (m + 1)) ↦ ?_
  have h (x : Fin (n + 1)) :
      x ≤ (EndpointPreserving.cutInv g).toOrderHom y ↔ x ≤ α.toOrderHom y := by
    have hmap : g.hom.toOrderHom x.castSucc = II.map' α.toOrderHom x.castSucc :=
      II_map_unop_toOrderHom_apply α x.castSucc
    rw [EndpointPreserving.le_cutInv_iff g x y, hmap, II.map'_le_castSucc_iff,
      Fin.castSucc_le_castSucc_iff]
  exact le_antisymm ((h _).mp le_rfl) ((h _).mpr le_rfl)

/-- `EndpointPreserving.cutInv` preserves identities on positive-length boundary objects
`⟨⦋n + 1⦌⟩`. -/
@[simp]
theorem EndpointPreserving.cutInv_id (n : ℕ) :
    EndpointPreserving.cutInv (𝟙 (⟨⦋n + 1⦌⟩ : EndpointPreserving)) = 𝟙 ⦋n⦌ := by
  have hc : iiOpToEndpointPreserving.map (𝟙 ⦋n⦌).op =
      𝟙 (⟨⦋n + 1⦌⟩ : EndpointPreserving) := by
    rw [op_id, CategoryTheory.Functor.map_id]
    -- `iiOpToEndpointPreserving.obj (op ⦋n⦌)` is definitionally `⟨⦋n + 1⦌⟩`.
    rfl
  rw [← hc]
  exact EndpointPreserving.cutInv_iiOpToEndpointPreserving_map (𝟙 ⦋n⦌)

/-- `EndpointPreserving.cutInv` reverses composition on positive-length boundary objects. -/
@[simp]
theorem EndpointPreserving.cutInv_comp {n m p : ℕ}
    (f : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩)
    (g : (⟨⦋m + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋p + 1⦌⟩) :
    EndpointPreserving.cutInv (f ≫ g) =
      EndpointPreserving.cutInv g ≫ EndpointPreserving.cutInv f := by
  have hc : iiOpToEndpointPreserving.map (EndpointPreserving.cutInv g ≫
      EndpointPreserving.cutInv f).op = f ≫ g := by
    rw [op_comp, Functor.map_comp]
    simp only [iiOpToEndpointPreserving_map_cutInv]
    -- `iiOpToEndpointPreserving.obj (op ⦋_⦌)` is definitionally `⟨⦋_ + 1⦌⟩`.
    rfl
  rw [← hc]
  exact EndpointPreserving.cutInv_iiOpToEndpointPreserving_map _

/-- `EndpointPreserving.cutInv` sends the restricted interior coface `EndpointPreserving.δ i`
(`⦋n + 1⦌ ⟶ ⦋n + 2⦌`, omitting `i.succ.castSucc`) to the codegeneracy `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌`. -/
@[simp]
theorem EndpointPreserving.cutInv_δ {n : ℕ} (i : Fin (n + 1)) :
    EndpointPreserving.cutInv (EndpointPreserving.δ i) = _root_.SimplexCategory.σ i := by
  rw [← iiOpToEndpointPreserving_map_σ]
  exact EndpointPreserving.cutInv_iiOpToEndpointPreserving_map (_root_.SimplexCategory.σ i)

/-- `EndpointPreserving.cutInv` sends the restricted codegeneracy
`EndpointPreserving.σ i : ⦋n + 2⦌ ⟶ ⦋n + 1⦌` to the coface `δ i : ⦋n⦌ ⟶ ⦋n + 1⦌`. -/
@[simp]
theorem EndpointPreserving.cutInv_σ {n : ℕ} (i : Fin (n + 2)) :
    EndpointPreserving.cutInv (EndpointPreserving.σ i) = _root_.SimplexCategory.δ i := by
  rw [← iiOpToEndpointPreserving_map_δ]
  exact EndpointPreserving.cutInv_iiOpToEndpointPreserving_map (_root_.SimplexCategory.δ i)

/-- The inverse functor `Δ_∂ ⥤ Δ₊ᵒᵖ` sending `⦋0⦌` to `op .star`, `⦋n + 1⦌` to `op (.of ⦋n⦌)`,
and each endpoint-preserving map `⦋n + 1⦌ ⟶ ⦋m + 1⦌` to its cut-inverse `⦋m⦌ ⟶ ⦋n⦌`. -/
@[expose] def endpointPreservingToAugmentedOp :
    EndpointPreserving ⥤ AugmentedSimplexCategoryᵒᵖ where
  obj x := match x.obj.len with
    | 0 => op (WithInitial.star : AugmentedSimplexCategory)
    | n + 1 => op (WithInitial.of ⦋n⦌)
  map {x y} f := match x, y with
    | ⟨⟨0⟩⟩, ⟨⟨0⟩⟩ => 𝟙 (op (WithInitial.star : AugmentedSimplexCategory))
    | ⟨⟨0⟩⟩, ⟨⟨m + 1⟩⟩ => ((EndpointPreserving.isEmpty_hom_zero_succ m).false f).elim
    | ⟨⟨n + 1⟩⟩, ⟨⟨0⟩⟩ => (WithInitial.homTo ⦋n⦌).op
    | ⟨⟨n + 1⟩⟩, ⟨⟨m + 1⟩⟩ => (EndpointPreserving.cutInv f).op
  map_id x := by
    rcases x with ⟨⟨_ | n⟩⟩
    · rfl
    · exact Quiver.Hom.unop_inj (EndpointPreserving.cutInv_id n)
  map_comp {x y z} f g := by
    rcases x with ⟨⟨_ | n⟩⟩ <;> rcases y with ⟨⟨_ | m⟩⟩ <;> rcases z with ⟨⟨_ | p⟩⟩
    · rfl
    · exact ((EndpointPreserving.isEmpty_hom_zero_succ p).false g).elim
    · exact ((EndpointPreserving.isEmpty_hom_zero_succ m).false f).elim
    · exact ((EndpointPreserving.isEmpty_hom_zero_succ m).false f).elim
    · exact Subsingleton.elim _ _
    · exact ((EndpointPreserving.isEmpty_hom_zero_succ p).false g).elim
    · exact Subsingleton.elim _ _
    · exact Quiver.Hom.unop_inj (EndpointPreserving.cutInv_comp f g)

/-- `endpointPreservingToAugmentedOp` sends `⟨⦋0⦌⟩` to `op WithInitial.star`. -/
@[simp]
theorem endpointPreservingToAugmentedOp_obj_zero :
    endpointPreservingToAugmentedOp.obj ⟨⦋0⦌⟩ =
      op (WithInitial.star : AugmentedSimplexCategory) :=
  (rfl)

/-- `endpointPreservingToAugmentedOp` sends `⟨⦋n + 1⦌⟩` to `op (WithInitial.of ⦋n⦌)`. -/
@[simp]
theorem endpointPreservingToAugmentedOp_obj_succ (n : ℕ) :
    endpointPreservingToAugmentedOp.obj ⟨⦋n + 1⦌⟩ = op (WithInitial.of ⦋n⦌) :=
  (rfl)

/-- `endpointPreservingToAugmentedOp` sends `EndpointPreserving.constToZero ⦋n + 1⦌` to the
opposite of `WithInitial.homTo ⦋n⦌`. -/
@[simp]
theorem endpointPreservingToAugmentedOp_map_constToZero (n : ℕ) :
    endpointPreservingToAugmentedOp.map (EndpointPreserving.constToZero ⦋n + 1⦌) =
      (WithInitial.homTo ⦋n⦌).op :=
  (rfl)

/-- On morphisms between positive-length boundary objects, `endpointPreservingToAugmentedOp` acts
by `EndpointPreserving.cutInv`. -/
@[simp]
theorem endpointPreservingToAugmentedOp_map_succ {n m : ℕ}
    (f : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩) :
    endpointPreservingToAugmentedOp.map f = (EndpointPreserving.cutInv f).op :=
  (rfl)

/-- `augmentedOpToEndpointPreserving` and `endpointPreservingToAugmentedOp` are strict left/right
inverses on `Δ₊ᵒᵖ`. -/
@[simp]
theorem augmentedOpToEndpointPreserving_comp_endpointPreservingToAugmentedOp :
    augmentedOpToEndpointPreserving ⋙ endpointPreservingToAugmentedOp =
      𝟭 AugmentedSimplexCategoryᵒᵖ :=
  CategoryTheory.Functor.hext (fun x ↦ by rcases x with ⟨⟨_⟩ | _⟩ <;> rfl) fun x y f ↦ by
    rcases x with ⟨nx | _⟩ <;> rcases y with ⟨ny | _⟩
    · refine heq_of_eq <| Quiver.Hom.unop_inj ?_
      -- `augmentedOpToEndpointPreserving.obj (op (.of _))` and `iiOpToEndpointPreserving.obj`
      -- are only defeq to `⟨⦋_ + 1⦌⟩`, so `rw [augmentedOpToEndpointPreserving_map_of]` fails at
      -- `implicit` transparency under `endpointPreservingToAugmentedOp.map`.
      change EndpointPreserving.cutInv (iiOpToEndpointPreserving.map (f.unop : ny ⟶ nx).op) = _
      exact EndpointPreserving.cutInv_iiOpToEndpointPreserving_map (f.unop : ny ⟶ nx)
    · exact heq_of_eq
        (Subsingleton.elim (α := _ ⟶ op (WithInitial.star : AugmentedSimplexCategory)) _ _)
    · exact (WithInitial.false_of_to_star f.unop).elim
    · exact heq_of_eq
        (Subsingleton.elim (α := _ ⟶ op (WithInitial.star : AugmentedSimplexCategory)) _ _)

/-- `endpointPreservingToAugmentedOp` and `augmentedOpToEndpointPreserving` are strict left/right
inverses on `Δ_∂`. -/
@[simp]
theorem endpointPreservingToAugmentedOp_comp_augmentedOpToEndpointPreserving :
    endpointPreservingToAugmentedOp ⋙ augmentedOpToEndpointPreserving = 𝟭 EndpointPreserving :=
  CategoryTheory.Functor.hext (fun x ↦ by rcases x with ⟨⟨_ | _⟩⟩ <;> rfl) fun x y f ↦ by
    rcases x with ⟨⟨_ | n⟩⟩ <;> rcases y with ⟨⟨_ | m⟩⟩
    · exact heq_of_eq (Subsingleton.elim (α := _ ⟶ (⟨⦋0⦌⟩ : EndpointPreserving)) _ _)
    · exact ((EndpointPreserving.isEmpty_hom_zero_succ m).false f).elim
    · exact heq_of_eq (Subsingleton.elim (α := _ ⟶ (⟨⦋0⦌⟩ : EndpointPreserving)) _ _)
    · refine heq_of_eq ?_
      simp only [Functor.comp_map, endpointPreservingToAugmentedOp_map_succ]
      exact (augmentedOpToEndpointPreserving_map_of (EndpointPreserving.cutInv f)).trans
        (iiOpToEndpointPreserving_map_cutInv f)

/-- Strict isomorphism of categories `Δ₊ᵒᵖ ≅ Δ_∂`. -/
def augmentedOpIsoEndpointPreserving :
    Cat.of AugmentedSimplexCategoryᵒᵖ ≅ Cat.of EndpointPreserving where
  hom := augmentedOpToEndpointPreserving.toCatHom
  inv := endpointPreservingToAugmentedOp.toCatHom
  hom_inv_id := Cat.ext augmentedOpToEndpointPreserving_comp_endpointPreservingToAugmentedOp
  inv_hom_id := Cat.ext endpointPreservingToAugmentedOp_comp_augmentedOpToEndpointPreserving

/-- Underlying forward functor of `augmentedOpIsoEndpointPreserving`. -/
@[simp]
theorem augmentedOpIsoEndpointPreserving_hom_toFunctor :
    augmentedOpIsoEndpointPreserving.hom.toFunctor = augmentedOpToEndpointPreserving :=
  (rfl)

/-- Underlying inverse functor of `augmentedOpIsoEndpointPreserving`. -/
@[simp]
theorem augmentedOpIsoEndpointPreserving_inv_toFunctor :
    augmentedOpIsoEndpointPreserving.inv.toFunctor = endpointPreservingToAugmentedOp :=
  (rfl)

instance : augmentedOpToEndpointPreserving.IsEquivalence :=
  haveI : augmentedOpIsoEndpointPreserving.hom.toFunctor.IsEquivalence :=
    inferInstanceAs (Cat.equivOfIso augmentedOpIsoEndpointPreserving).functor.IsEquivalence
  Functor.isEquivalence_of_iso (eqToIso augmentedOpIsoEndpointPreserving_hom_toFunctor)

/-- `iiOpToEndpointPreserving` is faithful. -/
instance : iiOpToEndpointPreserving.Faithful :=
  Functor.Faithful.of_iso
    (eqToIso inclusion_op_comp_augmentedOpToEndpointPreserving)

/-- `iiOpToEndpointPreserving` is full. -/
instance : iiOpToEndpointPreserving.Full :=
  Functor.Full.of_iso
    (eqToIso inclusion_op_comp_augmentedOpToEndpointPreserving)

/-- `endpointPreservingToAugmentedOp` sends the restricted interior coface
`EndpointPreserving.δ i : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` (omitting `i.succ.castSucc`) to the opposite
codegeneracy `(AugmentedSimplexCategory.inclusion.map (σ i)).op`. -/
theorem endpointPreservingToAugmentedOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    endpointPreservingToAugmentedOp.map (EndpointPreserving.δ i) =
      (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.σ i)).op :=
  (endpointPreservingToAugmentedOp_map_succ _).trans
    (congrArg Quiver.Hom.op (EndpointPreserving.cutInv_δ i))

/-- `endpointPreservingToAugmentedOp` sends the restricted codegeneracy
`EndpointPreserving.σ i : ⦋n + 2⦌ ⟶ ⦋n + 1⦌` to the opposite coface
`(AugmentedSimplexCategory.inclusion.map (δ i)).op`. -/
theorem endpointPreservingToAugmentedOp_map_σ {n : ℕ} (i : Fin (n + 2)) :
    endpointPreservingToAugmentedOp.map (EndpointPreserving.σ i) =
      (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.δ i)).op :=
  (endpointPreservingToAugmentedOp_map_succ _).trans
    (congrArg Quiver.Hom.op (EndpointPreserving.cutInv_σ i))

end TauCeti.SimplexCategory
