/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech complexes along a functor into a thin category

Let `G : C ⥤ D` be a functor between categories with finite products, where `D` is thin, for
instance a monotone map between posets of open subsets. For a family `U : ι → C` and a presheaf
`Q : Dᵒᵖ ⥤ A`, the Čech complex of the pulled-back presheaf `G.op ⋙ Q` for `U` has terms
`Q(G(U (a 0) × ⋯ × U (a n)))`, while the Čech complex of `Q` for the family `G ∘ U` has terms
`Q(G (U (a 0)) × ⋯ × G (U (a n)))`. There is always a map `G(U (a 0) × ⋯ × U (a n)) ⟶
G (U (a 0)) × ⋯ × G (U (a n))`; when there is also a map in the reverse direction
`G (U (a 0)) × ⋯ × G (U (a n)) ⟶ G(U (a 0) × ⋯ × U (a n))`, the two objects are isomorphic in the
thin category `D`, and the two Čech complexes are isomorphic (`cechComplexCompIso`). If moreover
`G` sends the terminal object `T` of `C` to a terminal object of `D`, this isomorphism is
compatible with the augmentations, so one augmented Čech complex is exact if and only if the other
is.

For open covers this compares the restriction of a cover to an open with a cover in a smaller
poset: for an open `Y ⊆ W`, the presheaf `F(Y ∩ -)` on the opens contained in `W` is pulled back
from the opens contained in `Y` along `V ↦ Y ∩ V`, which preserves intersections.

## Main definitions

* `TauCeti.CategoryTheory.cechComplexCompIso`: the isomorphism between the Čech complex of `Q` for
  `G ∘ U` and the Čech complex of `G.op ⋙ Q` for `U`.

## Main results

* `TauCeti.CategoryTheory.cechAugmentation_comp_cechComplexCompIso_hom`: this isomorphism is
  compatible with the augmentations.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_op_comp_iff`: the augmented Čech complex of
  `G.op ⋙ Q` for `U` is exact if and only if the one of `Q` for `G ∘ U` is.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology

universe w v v' v'' u u' u''

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w}

/-! ### The two Čech complexes are isomorphic

The degree `n` term of a Čech complex is, up to unfolding, a product indexed by
`a : Fin (n + 1) → ι` (`cechXIso`); the differential is the alternating sum of the restrictions
along the coface maps (`cechComplexFunctor_obj_d_comp_π`). The isomorphism of Čech complexes
acts on the factor indexed by `a` through `Q` applied to the comparison isomorphism
`G(U (a 0) × ⋯ × U (a n)) ≅ G (U (a 0)) × ⋯ × G (U (a n))` (`prodIso`); it commutes with the
differentials because all the morphisms of `D` with the same ends agree. -/

/-- The degree `n` term of the Čech complex is, up to unfolding, the product of the values of `P`
on the `(n + 1)`-fold products of members. -/
private def cechXIso (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ≅
      ∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  Iso.refl _

/-- `cechXIso` is the identity. -/
private lemma cechXIso_hom_π (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechXIso U P n).hom ≫ Pi.π _ a = (Pi.π _ a : ((cechComplexFunctor U).obj P).X n ⟶ _) :=
  Category.id_comp _

/-- `cechComplexFunctor_obj_d_comp_π`, stated through `cechXIso`. -/
@[reassoc]
private lemma cechComplexFunctor_obj_d_comp_cechXIso_hom_π (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (k : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ (cechXIso U P (n + 1)).hom ≫ Pi.π _ k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • ((cechXIso U P n).hom ≫ Pi.π _ (k ∘ m.succAbove) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op) :=
  -- `cechXIso` is the identity
  (_ ≫= Category.id_comp _).trans <| (cechComplexFunctor_obj_d_comp_π U P n k).trans <|
    Finset.sum_congr rfl fun _ _ ↦ congrArg _ (Category.id_comp _).symm

variable {D : Type u''} [Category.{v''} D] [HasFiniteProducts D] [Quiver.IsThin D]
  (G : C ⥤ D) (U : ι → C) (Q : Dᵒᵖ ⥤ A)
  (hG : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
    Nonempty ((∏ᶜ fun j ↦ G.obj (U (a j))) ⟶ G.obj (∏ᶜ fun j ↦ U (a j))))

/-- The comparison isomorphism `G(U (a 0) × ⋯ × U (a n)) ≅ G (U (a 0)) × ⋯ × G (U (a n))` in the
thin category `D`. -/
private def prodIso (n : ℕ) (a : Fin (n + 1) → ι) :
    G.obj (∏ᶜ fun j ↦ U (a j)) ≅ ∏ᶜ fun j ↦ G.obj (U (a j)) :=
  iso_of_both_ways (Pi.lift fun j ↦ G.map (Pi.π _ j)) (hG n a).some

/-- The degree `n` component of the isomorphism of Čech complexes. -/
private def compXIso (n : ℕ) :
    ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q).X n ≅
      ((cechComplexFunctor U).obj (G.op ⋙ Q)).X n :=
  cechXIso _ Q n ≪≫ (Pi.mapIso fun a : Fin (n + 1) → ι ↦ Q.mapIso (prodIso G U hG n a).op) ≪≫
    (cechXIso U (G.op ⋙ Q) n).symm

/-- The factors of `compXIso` are given by `prodIso`. -/
private lemma compXIso_hom_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (compXIso G U Q hG n).hom ≫ (cechXIso U (G.op ⋙ Q) n).hom ≫ Pi.π _ a =
      (cechXIso _ Q n).hom ≫ Pi.π _ a ≫ Q.map (prodIso G U hG n a).hom.op := by
  simp [compXIso]

/-- The components `compXIso` commute with the differentials. -/
private lemma compXIso_hom_comp_d (n : ℕ) :
    (compXIso G U Q hG n).hom ≫ ((cechComplexFunctor U).obj (G.op ⋙ Q)).d n (n + 1) =
      ((cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q).d n (n + 1) ≫
        (compXIso G U Q hG (n + 1)).hom := by
  rw [← cancel_mono (cechXIso U (G.op ⋙ Q) (n + 1)).hom]
  refine Pi.hom_ext _ _ fun k ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexFunctor_obj_d_comp_cechXIso_hom_π, compXIso_hom_π,
    cechComplexFunctor_obj_d_comp_cechXIso_hom_π_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    ← Category.assoc (cechXIso U (G.op ⋙ Q) n).hom, ← Category.assoc (compXIso G U Q hG n).hom,
    compXIso_hom_π]
  simp only [Category.assoc, Functor.comp_map, Functor.op_map, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun g ↦ (-1 : ℤ) ^ (m : ℕ) • (_ ≫ _ ≫ Q.map (Quiver.Hom.op g)))
    (Subsingleton.elim _ _)

/-- The Čech complex of `Q` for the family `G ∘ U` is isomorphic to the Čech complex of `G.op ⋙ Q`
for `U`, provided each product `G (U (a 0)) × ⋯ × G (U (a n))` maps to `G(U (a 0) × ⋯ × U (a n))`.
In degree `n` it acts on the factor indexed by `a` through `Q` applied to the canonical map
`G(U (a 0) × ⋯ × U (a n)) ⟶ G (U (a 0)) × ⋯ × G (U (a n))` (`cechComplexCompIso_hom_f_π`). -/
def cechComplexCompIso :
    (cechComplexFunctor (fun i ↦ G.obj (U i))).obj Q ≅ (cechComplexFunctor U).obj (G.op ⋙ Q) :=
  HomologicalComplex.Hom.isoOfComponents (compXIso G U Q hG) fun n _ h ↦ by
    obtain rfl : n + 1 = _ := h
    exact compXIso_hom_comp_d G U Q hG n

/-- The factor of `(cechComplexCompIso G U Q hG).hom.f n` indexed by `a` is `Q` applied to the
canonical map `G(U (a 0) × ⋯ × U (a n)) ⟶ G (U (a 0)) × ⋯ × G (U (a n))`. -/
@[reassoc]
theorem cechComplexCompIso_hom_f_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechComplexCompIso G U Q hG).hom.f n ≫ Pi.π _ a =
      Pi.π _ a ≫ Q.map (Pi.lift fun j ↦ G.map (Pi.π (fun j ↦ U (a j)) j)).op :=
  -- `cechXIso` is the identity
  (_ ≫= (Category.id_comp _).symm).trans <| (compXIso_hom_π G U Q hG n a).trans (Category.id_comp _)

variable [HasZeroObject A] {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))

/-- If `G` sends the terminal object `T` of `C` to a terminal object, the isomorphism of Čech
complexes `cechComplexCompIso` is compatible with the augmentations. -/
@[reassoc]
theorem cechAugmentation_comp_cechComplexCompIso_hom :
    cechAugmentation (fun i ↦ G.obj (U i)) hGT Q ≫ (cechComplexCompIso G U Q hG).hom =
      cechAugmentation U hT (G.op ⋙ Q) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [← cancel_mono (cechXIso U (G.op ⋙ Q) 0).hom]
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [HomologicalComplex.comp_f, cechComplexCompIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Category.assoc, compXIso_hom_π]
  rw [← Category.assoc (cechXIso _ Q 0).hom, cechXIso_hom_π, cechXIso_hom_π]
  -- both sides restrict along morphisms in the thin category `D` with the same ends
  exact (Category.assoc _ _ _).symm.trans <|
    (cechAugmentation_f_zero_comp_π _ hGT Q a =≫ _).trans <| (Q.map_comp _ _).symm.trans <|
      (congrArg (fun g ↦ Q.map (Quiver.Hom.op g)) (Subsingleton.elim _ _)).trans
        (cechAugmentation_f_zero_comp_π U hT (G.op ⋙ Q) a).symm

variable [CategoryWithHomology A]

include hG in
/-- **Čech complexes along a functor into a thin category.** Let `G : C ⥤ D` be a functor between
categories with finite products, with `D` thin, let `U` be a family in `C` and let `Q` be a
presheaf on `D` with values in an abelian category. Suppose that `G` sends the terminal object `T`
of `C` to a terminal object, and that each product `G (U (a 0)) × ⋯ × G (U (a n))` maps to
`G(U (a 0) × ⋯ × U (a n))`. Then the augmented Čech complex of `G.op ⋙ Q` for `U` is exact if and
only if the augmented Čech complex of `Q` for the family `G ∘ U` is. -/
theorem quasiIso_cechAugmentation_op_comp_iff :
    QuasiIso (cechAugmentation U hT (G.op ⋙ Q)) ↔
      QuasiIso (cechAugmentation (fun i ↦ G.obj (U i)) hGT Q) := by
  rw [← cechAugmentation_comp_cechComplexCompIso_hom G U Q hG hT hGT]
  exact quasiIso_iff_comp_right _ _

end TauCeti.CategoryTheory
