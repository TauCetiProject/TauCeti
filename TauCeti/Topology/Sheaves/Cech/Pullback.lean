/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Lattice

/-!
# Pullback maps of fixed-family Čech complexes

For a continuous map `f : X ⟶ Y` and a morphism of presheaves `α : P ⟶ f_* Q`,
`TopCat.Hom.cechComplexPullback` sends the Čech complex of `P` for a family `U` to the Čech
complex of `Q` for the inverse-image family. It uses the native tuple complex,
including repeated indices and empty intersections. No covering condition is needed.

The map commutes with actual refinement functions, with the homotopies between the maps
induced by two refinement functions, and with coefficient morphisms, and it is an isomorphism when
the coefficient morphism is (`TopCat.Hom.isIso_cechComplexPullback`).
Consequently, restriction to an open subspace can be performed before or after a
refinement. `TopologicalSpace.Opens.cechComplexRestrict` is this restriction map, with the
presheaf on the subspace obtained by evaluating on its open subsets regarded as opens of the
ambient space. These chain maps supply restriction maps before taking cover colimits.

The construction uses `TauCeti.CategoryTheory.cechComplexCompIso`, and the refinement
maps are those of the Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.CategoryTheory

universe u v w

variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]
  {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y)
  {P : Y.Presheaf A} {Q : X.Presheaf A}

namespace TopCat.Hom

/-- Inverse image preserves the finite intersections occurring in a Čech term. -/
private theorem preimageProduct (n : ℕ) (a : Fin (n + 1) → ι) :
    Nonempty ((∏ᶜ fun j ↦ (Opens.map f).obj (U (a j))) ⟶
      (Opens.map f).obj (∏ᶜ fun j ↦ U (a j))) :=
  ⟨inv (piComparison (Opens.map f) (fun j ↦ U (a j)))⟩

/-- The map of tuple Čech complexes induced by a continuous map and a morphism
`P ⟶ f_* Q`. The inverse-image family has the same index type as the original family. -/
def cechComplexPullback (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) :
    (cechComplexFunctor U).obj P ⟶
      (cechComplexFunctor (fun i ↦ (Opens.map f).obj (U i))).obj Q :=
  (cechComplexFunctor U).map α ≫
    (cechComplexCompIso (Opens.map f) U Q (preimageProduct f U)).inv

/-- The pullback map is characterized by the coefficient map and the canonical comparison
between inverse images of intersections and intersections of inverse images. -/
@[reassoc (attr := simp)]
private theorem cechComplexPullback_comp_comparison
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) :
    cechComplexPullback f U α ≫
        (cechComplexCompIso (Opens.map f) U Q (preimageProduct f U)).hom =
      (cechComplexFunctor U).map α := by
  simp [cechComplexPullback]

/-- On each tuple, pullback applies the coefficient map and identifies the inverse image of
the intersection with the intersection of the inverse images. -/
@[simp, reassoc]
theorem cechComplexPullback_f_π
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechComplexPullback f U α).f n ≫
        Pi.π (fun b : Fin (n + 1) → ι ↦ Q.obj (op (∏ᶜ fun j ↦ (Opens.map f).obj (U (b j))))) a =
      Pi.π _ a ≫ α.app (op (∏ᶜ fun j ↦ U (a j))) ≫
        Q.map (inv (piComparison (Opens.map f) (fun j ↦ U (a j)))).op := by
  let e := cechComplexCompIso (Opens.map f) U Q (preimageProduct f U)
  have ht : (cechComplexPullback f U α).f n ≫ e.hom.f n =
      ((cechComplexFunctor U).map α).f n :=
    congrArg (fun z ↦ z.f n) (cechComplexPullback_comp_comparison f U α)
  have hπ := cechComplexCompIso_hom_f_π (Opens.map f) U Q (preimageProduct f U) n a
  -- The tuple projections use native Čech term wrappers. Composing their equations as terms
  -- avoids unfolding these wrappers during rewriting.
  have hl := (Category.assoc _ _ _).trans
    (((cechComplexPullback f U α).f n) ≫= hπ.symm)
  have h := hl.trans ((Category.assoc _ _ _).symm.trans (ht =≫ Pi.π _ a))
  apply (cancel_mono (Q.map (piComparison (Opens.map f) (fun j ↦ U (a j))).op)).mp
  refine h.trans ((cechComplexFunctor_map_f_π U P α n a).trans ?_)
  have hc : Q.map (inv (piComparison (Opens.map f) (fun j ↦ U (a j)))).op ≫
      Q.map (piComparison (Opens.map f) (fun j ↦ U (a j))).op = 𝟙 _ := by
    rw [← Q.map_comp, ← op_comp, IsIso.hom_inv_id, op_id, Q.map_id]
  exact ((Category.assoc _ _ _).trans <| (Pi.π _ a ≫=
    ((Category.assoc _ _ _).trans ((α.app _ ≫= hc).trans (Category.comp_id _))))).symm

/-- Pullback along an isomorphism of coefficients is an isomorphism of Čech complexes. -/
instance isIso_cechComplexPullback (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) [IsIso α] :
    IsIso (cechComplexPullback f U α) := by
  rw [cechComplexPullback]
  infer_instance

/-- Pullback commutes with every actual refinement, not just with its induced cohomology map. -/
@[reassoc]
theorem cechComplexMap_comp_cechComplexPullback {κ : Type u} {V : κ → Opens Y}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) :
    cechComplexMap P φ ≫ cechComplexPullback f U α =
      cechComplexPullback f V α ≫ cechComplexMap Q
        (⟨φ.f, fun i ↦ (Opens.map f).map (φ.φ i)⟩ :
          FormalCoproduct.mk _ (fun i ↦ (Opens.map f).obj (U i)) ⟶
            FormalCoproduct.mk _ (fun i ↦ (Opens.map f).obj (V i))) := by
  rw [← cancel_mono (cechComplexCompIso (Opens.map f) U Q (preimageProduct f U)).hom]
  simp only [Category.assoc, cechComplexPullback_comp_comparison]
  have h := cechComplexMap_comp_cechComplexCompIso_hom (Opens.map f) U Q
    (preimageProduct f U) φ (preimageProduct f V)
  exact (cechComplexMap_naturality P α φ).symm.trans <|
    ((cechComplexPullback_comp_comparison f V α =≫ _).symm.trans <|
      (Category.assoc _ _ _).trans (cechComplexPullback f V α ≫= h.symm))

/-- Pullback carries the homotopy between the maps induced by two actual refinements
(`TauCeti.CategoryTheory.cechComplexMapHomotopy`) to the homotopy between the maps induced by the
inverse-image refinements. -/
@[reassoc]
theorem cechComplexPullback_f_comp_cechComplexMapHomotopy_hom {κ : Type u} {V : κ → Opens Y}
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) (i j : ℕ) :
    (cechComplexPullback f V α).f i ≫
        (cechComplexMapHomotopy Q
          (⟨φ.f, fun i ↦ (Opens.map f).map (φ.φ i)⟩ :
            FormalCoproduct.mk _ (fun i ↦ (Opens.map f).obj (U i)) ⟶
              FormalCoproduct.mk _ (fun i ↦ (Opens.map f).obj (V i)))
          ⟨ψ.f, fun i ↦ (Opens.map f).map (ψ.φ i)⟩).hom i j =
      (cechComplexMapHomotopy P φ ψ).hom i j ≫ (cechComplexPullback f U α).f j := by
  rw [← cancel_mono ((cechComplexCompIso (Opens.map f) U Q (preimageProduct f U)).hom.f j),
    Category.assoc, Category.assoc,
    cechComplexMapHomotopy_hom_comp_cechComplexCompIso_hom _ _ _ _ _ _ (preimageProduct f V),
    ← Category.assoc, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
    cechComplexPullback_comp_comparison, cechComplexPullback_comp_comparison]
  exact cechComplexMapHomotopy_hom_naturality P α φ ψ i j

/-- A commutative square of coefficient maps induces a commutative square of pullback maps. -/
@[reassoc]
theorem cechComplexPullback_naturality {P' : Y.Presheaf A} {Q' : X.Presheaf A}
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q)
    (α' : P' ⟶ (TopCat.Presheaf.pushforward A f).obj Q')
    (β : P ⟶ P') (γ : Q ⟶ Q')
    (h : β ≫ α' = α ≫ (TopCat.Presheaf.pushforward A f).map γ) :
    (cechComplexFunctor U).map β ≫ cechComplexPullback f U α' =
      cechComplexPullback f U α ≫
        (cechComplexFunctor (fun i ↦ (Opens.map f).obj (U i))).map γ := by
  rw [← cancel_mono (cechComplexCompIso (Opens.map f) U Q' (preimageProduct f U)).hom]
  simp only [Category.assoc, cechComplexPullback_comp_comparison,
    cechComplexFunctor_map_comp_cechComplexCompIso_hom,
    cechComplexPullback_comp_comparison_assoc]
  exact ((cechComplexFunctor U).map_comp β α').symm.trans
    ((congrArg (cechComplexFunctor U).map h).trans ((cechComplexFunctor U).map_comp _ _))

end TopCat.Hom

namespace TopologicalSpace.Opens

open TopCat.Hom

/-- Restrict the Čech complex of a presheaf to an open subspace. The presheaf on the subspace
is evaluated by regarding each of its opens as an open of the ambient space. -/
def cechComplexRestrict (W : Opens X) (U : ι → Opens X) (P : X.Presheaf A) :
    (cechComplexFunctor U).obj P ⟶
      (cechComplexFunctor (fun i ↦ (Opens.map W.inclusion').obj (U i))).obj
        (W.isOpenEmbedding.isOpenMap.functor.op ⋙ P) :=
  cechComplexPullback W.inclusion' U
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) P)

/-- Open restriction is pullback along the inclusion, with its canonical coefficient map. -/
theorem cechComplexRestrict_eq (W : Opens X) (U : ι → Opens X) (P : X.Presheaf A) :
    cechComplexRestrict W U P = cechComplexPullback W.inclusion' U
      (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) P) :=
  (rfl)

/-- A tuple coordinate of open restriction is the usual restriction along the inclusion of
the corresponding intersection in the open subspace into the ambient intersection. -/
@[simp, reassoc]
theorem cechComplexRestrict_f_π (W : Opens X) (U : ι → Opens X) (P : X.Presheaf A)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechComplexRestrict W U P).f n ≫
        Pi.π (fun b : Fin (n + 1) → ι ↦ P.obj (op
          (W.isOpenEmbedding.isOpenMap.functor.obj
            (∏ᶜ fun j ↦ (Opens.map W.inclusion').obj (U (b j)))))) a =
      Pi.π _ a ≫ P.map
        (W.isOpenEmbedding.isOpenMap.functor.map
            (inv (piComparison (Opens.map W.inclusion') (fun j ↦ U (a j)))) ≫
          W.isOpenEmbedding.isOpenMap.adjunction.counit.app (∏ᶜ fun j ↦ U (a j))).op := by
  refine (cechComplexPullback_f_π W.inclusion' U (P := P)
    (Q := W.isOpenEmbedding.isOpenMap.functor.op ⋙ P)
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) P)
    n a).trans ?_
  exact (_ ≫= (P.map_comp _ _).symm)

/-- Restricting a cover and refining it commute as cochain maps. -/
@[reassoc]
theorem cechComplexMap_comp_cechComplexRestrict (W : Opens X) (U : ι → Opens X)
    (P : X.Presheaf A) {κ : Type u} {V : κ → Opens X}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechComplexMap P φ ≫ cechComplexRestrict W U P =
      cechComplexRestrict W V P ≫
        cechComplexMap (W.isOpenEmbedding.isOpenMap.functor.op ⋙ P)
          (⟨φ.f, fun i ↦ (Opens.map W.inclusion').map (φ.φ i)⟩ :
            FormalCoproduct.mk _ (fun i ↦ (Opens.map W.inclusion').obj (U i)) ⟶
              FormalCoproduct.mk _ (fun i ↦ (Opens.map W.inclusion').obj (V i))) :=
  cechComplexMap_comp_cechComplexPullback W.inclusion' U φ _

/-- Restricting a cover commutes with the homotopy between the maps induced by two actual
refinements. -/
@[reassoc]
theorem cechComplexRestrict_f_comp_cechComplexMapHomotopy_hom (W : Opens X) (U : ι → Opens X)
    (P : X.Presheaf A) {κ : Type u} {V : κ → Opens X}
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (i j : ℕ) :
    (cechComplexRestrict W V P).f i ≫
        (cechComplexMapHomotopy (W.isOpenEmbedding.isOpenMap.functor.op ⋙ P)
          (⟨φ.f, fun i ↦ (Opens.map W.inclusion').map (φ.φ i)⟩ :
            FormalCoproduct.mk _ (fun i ↦ (Opens.map W.inclusion').obj (U i)) ⟶
              FormalCoproduct.mk _ (fun i ↦ (Opens.map W.inclusion').obj (V i)))
          ⟨ψ.f, fun i ↦ (Opens.map W.inclusion').map (ψ.φ i)⟩).hom i j =
      (cechComplexMapHomotopy P φ ψ).hom i j ≫ (cechComplexRestrict W U P).f j :=
  cechComplexPullback_f_comp_cechComplexMapHomotopy_hom W.inclusion' U φ ψ _ i j

end TopologicalSpace.Opens

namespace TopCat.Hom

variable [HasZeroObject A]

/-- Pullback is compatible with the Čech augmentation and the map on global sections. -/
@[reassoc]
theorem cechAugmentation_comp_cechComplexPullback
    (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q) :
    cechAugmentation U isTerminalTop P ≫ cechComplexPullback f U α =
      (CochainComplex.single₀ A).map (α.app (op ⊤)) ≫
        cechAugmentation (fun i ↦ (Opens.map f).obj (U i)) isTerminalTop Q := by
  rw [← cancel_mono (cechComplexCompIso (Opens.map f) U Q (preimageProduct f U)).hom]
  simp only [Category.assoc, cechComplexPullback_comp_comparison]
  have h := cechAugmentation_comp_cechComplexCompIso_hom (Opens.map f) U Q
    (preimageProduct f U) isTerminalTop isTerminalTop
  exact (cechAugmentation_naturality U isTerminalTop P α).trans <|
    (((CochainComplex.single₀ A).map (α.app (op ⊤)) ≫= h.symm).trans
      (Category.assoc _ _ _).symm)

end TopCat.Hom
