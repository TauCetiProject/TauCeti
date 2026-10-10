/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Thin
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech complexes of two-member covers

Let `C` be a thin category with finite products and a terminal object `T`, for instance the poset
of open subsets of a topological space, and let `P : Cᵒᵖ ⥤ A` be a presheaf with values in an
abelian category. For a family of two objects `U 0` and `U 1`, the Čech complex of `P` reduces to
the Mayer-Vietoris sequence `0 ⟶ P(T) ⟶ P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1) ⟶ 0`: its cohomology
vanishes in every degree `≥ 2`, and the augmented Čech complex is exact precisely when the
Mayer-Vietoris sequence is short exact. This is the form in which exactness in every degree of the
augmented Čech complex of a cover by two opens follows from statements in degrees `0` and `1`: the
sheaf condition for the cover, and the fact that every section over the intersection is a
difference of restrictions.

The proof restricts `P` to the members. For an object `Y`, the presheaf `P(Y × -)` has an exact
augmented Čech complex for any family with a member receiving a map from `Y`
(`quasiIso_cechAugmentation_prod_of_hom`): in a thin category the family `U` may be replaced by
`Y × U`, which refines and is refined by the single object `Y`. Restriction along the projections
then gives a short exact sequence of Čech complexes
`0 ⟶ Č(U, P) ⟶ Č(U, P(U 0 × -)) ⊞ Č(U, P(U 1 × -)) ⟶ Č(U, P(U 0 × U 1 × -)) ⟶ 0`,
split in each degree because each product of members lies in `U 0` or in `U 1`, and its long exact
cohomology sequence gives the result.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_prod_of_hom`: for `Y ⟶ U i₀`, the augmented
  Čech complex of `P(Y × -)` for the family `U` is exact.
* `TauCeti.CategoryTheory.exactAt_add_two_cechComplexFunctor_obj`: the Čech complex of any
  presheaf for a two-member family is exact in every degree `≥ 2`.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff`: the augmented Čech complex of `P`
  for a two-member family is exact if and only if `P` satisfies the sheaf condition for the family
  and `P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1)` is an epimorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Appendix A, Definition A.1,
  where a cover is called `F`-acyclic when its augmented Čech complex is exact.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]

/-- In a thin category, a presheaf takes the same value on any two parallel morphisms. -/
private lemma map_eq_map [Quiver.IsThin C] (P : Cᵒᵖ ⥤ A) {X Y : Cᵒᵖ} (f g : X ⟶ Y) :
    P.map f = P.map g :=
  congrArg P.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- In a thin category, a presheaf takes the same value on any two parallel composites. -/
private lemma map_comp_map_eq [Quiver.IsThin C] (P : Cᵒᵖ ⥤ A) {X Y Y' Z : Cᵒᵖ} (f : X ⟶ Y)
    (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z) : P.map f ≫ P.map g = P.map f' ≫ P.map g' :=
  (P.map_comp f g).symm.trans ((map_eq_map P _ _).trans (P.map_comp f' g'))

/-- If `f ≫ g = f' ≫ g'` with `f` and `g'` invertible, then `inv f ≫ f' = g ≫ inv g'`. -/
private lemma inv_comp_eq_comp_inv {X Y Y' Z : A} {f : X ⟶ Y} {f' : X ⟶ Y'} {g : Y ⟶ Z}
    {g' : Y' ⟶ Z} [IsIso f] [IsIso g'] (w : f ≫ g = f' ≫ g') : inv f ≫ f' = g ≫ inv g' := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, w]

variable [HasFiniteProducts C]

/-! ### Restriction to an object -/

section Restriction

variable [Quiver.IsThin C] [Preadditive A] [HasProducts.{w} A]

/-- The projection from the family `Y × W` to the family `W`. -/
private abbrev prodFamilyHom (Y : C) {κ : Type w} (W : κ → C) :
    FormalCoproduct.mk _ (fun i ↦ Y ⨯ W i) ⟶ FormalCoproduct.mk _ W :=
  ⟨id, fun i ↦ (prod.snd : Y ⨯ W i ⟶ W i)⟩

/-- For the presheaf `P(Y × -)`, replacing a family `W` by `Y × W` does not change the Čech
complex: each factor `P(Y × W (a 0) × ⋯ × W (a n))` is restricted along a morphism between
isomorphic objects of the thin category `C`. -/
private lemma isIso_cechComplexMap_prod (P : Cᵒᵖ ⥤ A) (Y : C) {κ : Type w} (W : κ → C) :
    IsIso (cechComplexMap ((prod.functor.obj Y).op ⋙ P) (prodFamilyHom Y W)) :=
  isIso_cechComplexMap _ _ fun _ a ↦
    (P.mapIso (iso_of_both_ways
      (prod.map (𝟙 Y) (Limits.Pi.map fun j ↦ (prod.snd : Y ⨯ W (a j) ⟶ W (a j))))
      (prod.lift prod.fst (Pi.lift fun j ↦ prod.lift prod.fst (prod.snd ≫ Pi.π _ j)))).op).isIso_hom

variable [HasZeroObject A] [CategoryWithHomology A] {ι : Type w} (U : ι → C) {T : C}
  (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

/-- **The Čech complex of a restricted presheaf.** If some member `U i₀` of the family receives a
morphism from `Y`, then the augmented Čech complex of the presheaf `P(Y × -)` for `U` is exact.
For `Y = T` this is `quasiIso_cechAugmentation_of_hom`; for an open cover of `T` and an open
`Y` contained in a member, it says that the cover restricted to `Y` is acyclic for `P`. -/
theorem quasiIso_cechAugmentation_prod_of_hom (Y : C) {i₀ : ι} (g : Y ⟶ U i₀) :
    QuasiIso (cechAugmentation U hT ((prod.functor.obj Y).op ⋙ P)) := by
  -- replacing a family `W` by `Y × W` does not change the augmented Čech complex of `P(Y × -)`
  have key {κ : Type w} (W : κ → C) :
      QuasiIso (cechAugmentation (fun i ↦ Y ⨯ W i) hT ((prod.functor.obj Y).op ⋙ P)) ↔
        QuasiIso (cechAugmentation W hT ((prod.functor.obj Y).op ⋙ P)) := by
    have := isIso_cechComplexMap_prod P Y W
    rw [← cechAugmentation_comp_cechComplexMap hT _ (prodFamilyHom Y W)]
    exact quasiIso_iff_comp_right _ _
  -- the families `Y × U` and `Y × T` map to each other, and replacing `Y × T` by `T` gives a
  -- family with `T` as a member
  rw [← key, quasiIso_cechAugmentation_congr hT _ (V := fun _ : PUnit.{w + 1} ↦ Y ⨯ T)
    ⟨fun _ ↦ PUnit.unit, fun _ ↦ prod.map (𝟙 Y) (hT.from _)⟩
    ⟨fun _ ↦ i₀, fun _ ↦ prod.lift prod.fst (prod.fst ≫ g)⟩, key]
  exact quasiIso_cechAugmentation_of_hom _ hT _ (i₀ := PUnit.unit) (𝟙 T)

end Restriction

/-! ### Two-member covers -/

section TwoMembers

variable (U : Fin 2 → C) {T : C} (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

section FactorwiseMaps

/-! In degree `n`, the terms of Čech complexes for `U` are products indexed by
`a : Fin (n + 1) → Fin 2`; `cechXMap` builds morphisms between them factorwise. -/

variable [Preadditive A] [HasProducts.{0} A]

/-- The morphism of degree `n` terms of Čech complexes acting on the factor indexed by `a` by
`φ a`. -/
private def cechXMap {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → Fin 2,
      F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j)))) :
    ((cechComplexFunctor U).obj F).X n ⟶ ((cechComplexFunctor U).obj G).X n :=
  Limits.Pi.map φ

private lemma cechXMap_π {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → Fin 2,
      F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j))))
    (a : Fin (n + 1) → Fin 2) :
    cechXMap U n φ ≫ Pi.π _ a = Pi.π _ a ≫ φ a :=
  Pi.map_π φ a

private lemma cechXMap_ext {F G : Cᵒᵖ ⥤ A} {n : ℕ}
    {φ ψ : ∀ a : Fin (n + 1) → Fin 2,
      F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j)))}
    (h : ∀ a, φ a = ψ a) : cechXMap U n φ = cechXMap U n ψ :=
  congrArg _ (funext h)

private lemma map_f_eq_cechXMap {F G : Cᵒᵖ ⥤ A} (α : F ⟶ G) (n : ℕ) :
    ((cechComplexFunctor U).map α).f n = cechXMap U n fun a ↦ α.app (op (∏ᶜ fun j ↦ U (a j))) :=
  Pi.hom_ext _ _ fun a ↦ (cechComplexFunctor_map_f_π U F α n a).trans
    (cechXMap_π U n (fun b ↦ α.app (op (∏ᶜ fun j ↦ U (b j)))) a).symm

private lemma cechXMap_comp {F G H : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → Fin 2,
      F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j))))
    (ψ : ∀ a : Fin (n + 1) → Fin 2,
      G.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ H.obj (op (∏ᶜ fun j ↦ U (a j)))) :
    cechXMap U n φ ≫ cechXMap U n ψ = cechXMap U n fun a ↦ φ a ≫ ψ a :=
  Limits.Pi.map_comp_map φ ψ

private lemma cechXMap_add {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ ψ : ∀ a : Fin (n + 1) → Fin 2,
      F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j)))) :
    cechXMap U n φ + cechXMap U n ψ = cechXMap U n fun a ↦ φ a + ψ a :=
  Pi.hom_ext _ _ fun a ↦ (Preadditive.add_comp _ _ _ _ _ _).trans <|
    (congrArg₂ (· + ·) (cechXMap_π U n φ a) (cechXMap_π U n ψ a)).trans <|
      (Preadditive.comp_add _ _ _ _ _ _).symm.trans (cechXMap_π U n (fun b ↦ φ b + ψ b) a).symm

private lemma cechXMap_neg {F G : Cᵒᵖ ⥤ A} (n : ℕ)
    (φ : ∀ a : Fin (n + 1) → Fin 2,
      F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j)))) :
    -cechXMap U n φ = cechXMap U n fun a ↦ -φ a :=
  Pi.hom_ext _ _ fun a ↦ (Preadditive.neg_comp _ _).trans <|
    (congrArg Neg.neg (cechXMap_π U n φ a)).trans <|
      (Preadditive.comp_neg _ _).symm.trans (cechXMap_π U n (fun b ↦ -φ b) a).symm

private lemma cechXMap_id (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechXMap U n (fun a ↦ 𝟙 (F.obj (op (∏ᶜ fun j ↦ U (a j))))) = 𝟙 _ :=
  Limits.Pi.map_id

private lemma cechXMap_zero (F G : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechXMap U n (fun a ↦ (0 : F.obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ G.obj (op (∏ᶜ fun j ↦ U (a j))))) =
      0 :=
  Pi.hom_ext _ _ fun a ↦ (cechXMap_π U n (fun b ↦ (0 : F.obj (op (∏ᶜ fun j ↦ U (b j))) ⟶
    G.obj (op (∏ᶜ fun j ↦ U (b j))))) a).trans <| comp_zero.trans zero_comp.symm

end FactorwiseMaps

variable [Quiver.IsThin C]

/-- The presheaf `P(Y × -)`. -/
private abbrev restr (Y : C) : Cᵒᵖ ⥤ A :=
  (prod.functor.obj Y).op ⋙ P

/-- Restriction `P ⟶ P(Y × -)` along the projections `Y × V ⟶ V`. -/
private def toRestr (Y : C) : P ⟶ restr P Y where
  app V := P.map (prod.snd : Y ⨯ V.unop ⟶ V.unop).op
  naturality _ _ _ := map_comp_map_eq P _ _ _ _

/-- Restriction `P(Y × -) ⟶ P(Y' × -)` along a morphism `Y' ⟶ Y`. -/
private abbrev restrMap {Y Y' : C} (h : Y' ⟶ Y) : restr P Y ⟶ restr P Y' :=
  Functor.whiskerRight (NatTrans.op (prod.functor.map h)) P

private lemma toRestr_comp_restrMap {Y Y' : C} (h : Y' ⟶ Y) :
    toRestr P Y ≫ restrMap P h = toRestr P Y' := by
  ext V
  exact (P.map_comp _ _).symm.trans (map_eq_map P _ _)

/-- The two restrictions `P ⟶ P(U 0 × U 1 × -)`, through `U 0` and through `U 1`, agree. -/
private lemma toRestr_comp_restrMap_app (V : C) :
    (toRestr P (U 0)).app (op V) ≫ (restrMap P (prod.fst : U 0 ⨯ U 1 ⟶ U 0)).app (op V) =
      (toRestr P (U 1)).app (op V) ≫ (restrMap P (prod.snd : U 0 ⨯ U 1 ⟶ U 1)).app (op V) :=
  (NatTrans.comp_app _ _ _).symm.trans <| (NatTrans.congr_app ((toRestr_comp_restrMap P _).trans
    (toRestr_comp_restrMap P _).symm) (op V)).trans (NatTrans.comp_app _ _ _)

/-- Over an object `V` with a morphism to `Y`, restriction along `Y × V ⟶ V` is invertible. -/
private lemma isIso_toRestr_app {Y V : C} (g : V ⟶ Y) : IsIso ((toRestr P Y).app (op V)) :=
  (P.mapIso (iso_of_both_ways (prod.snd : Y ⨯ V ⟶ V) (prod.lift g (𝟙 V))).op).isIso_hom

/-- Over an object `V` with `Y × V` mapping to `Y'`, restriction along `Y' × V ⟶ Y × V` is
invertible. -/
private lemma isIso_restrMap_app {Y Y' V : C} (h : Y' ⟶ Y) (g : Y ⨯ V ⟶ Y') :
    IsIso ((restrMap P h).app (op V)) :=
  (P.mapIso (iso_of_both_ways (prod.map h (𝟙 V)) (prod.lift g prod.snd)).op).isIso_hom

variable [Abelian A] [HasProducts.{0} A]

/-- The difference of restrictions
`Č(U, P(U 0 × -)) ⊞ Č(U, P(U 1 × -)) ⟶ Č(U, P(U 0 × U 1 × -))`. -/
private abbrev mvDiff :
    (cechComplexFunctor U).obj (restr P (U 0)) ⊞ (cechComplexFunctor U).obj (restr P (U 1)) ⟶
      (cechComplexFunctor U).obj (restr P (U 0 ⨯ U 1)) :=
  biprod.desc ((cechComplexFunctor U).map (restrMap P (prod.fst : U 0 ⨯ U 1 ⟶ U 0)))
    (-(cechComplexFunctor U).map (restrMap P (prod.snd : U 0 ⨯ U 1 ⟶ U 1)))

/-- The short complex of Čech complexes
`Č(U, P) ⟶ Č(U, P(U 0 × -)) ⊞ Č(U, P(U 1 × -)) ⟶ Č(U, P(U 0 × U 1 × -))`, given by restriction
and by the difference of restrictions. -/
private def mvShortComplex : ShortComplex (CochainComplex A ℕ) :=
  ShortComplex.mk
    (biprod.lift ((cechComplexFunctor U).map (toRestr P (U 0)))
      ((cechComplexFunctor U).map (toRestr P (U 1))))
    (mvDiff U P)
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp,
        toRestr_comp_restrMap, toRestr_comp_restrMap, add_neg_cancel])

/-! The splitting in degree `n` acts factorwise. A factor of the degree `n` term is indexed by
`a : Fin (n + 1) → Fin 2`, and the product `V` of the members `U (a j)` maps to `U (a 0)`. If
`a 0 = 0`, then `P(V) ⟶ P(U 0 × V)` and `P(U 1 × V) ⟶ P(U 0 × U 1 × V)` are isomorphisms;
if `a 0 = 1`, then so are `P(V) ⟶ P(U 1 × V)` and `P(U 0 × V) ⟶ P(U 0 × U 1 × V)`. -/

/-- The product of the members indexed by `a` maps to `U i` when `a 0 = i`. -/
private def toMember {n : ℕ} {a : Fin (n + 1) → Fin 2} {i : Fin 2} (h : a 0 = i) :
    (∏ᶜ fun j ↦ U (a j)) ⟶ U i :=
  Pi.π _ 0 ≫ eqToHom (congrArg U h)

/-- The factors of the retraction of `Č(U, P) ⟶ Č(U, P(U 0 × -)) ⊞ Č(U, P(U 1 × -))` in degree
`n` coming from the first summand. -/
private def retr₀ {n : ℕ} (a : Fin (n + 1) → Fin 2) :
    (restr P (U 0)).obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  if h : a 0 = 0 then
    haveI := isIso_toRestr_app P (toMember U h)
    inv ((toRestr P (U 0)).app (op (∏ᶜ fun j ↦ U (a j))))
  else 0

/-- The factors of the retraction coming from the second summand. -/
private def retr₁ {n : ℕ} (a : Fin (n + 1) → Fin 2) :
    (restr P (U 1)).obj (op (∏ᶜ fun j ↦ U (a j))) ⟶ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  if h : a 0 = 0 then 0
  else
    haveI := isIso_toRestr_app P (toMember U (Fin.eq_one_of_ne_zero _ h))
    inv ((toRestr P (U 1)).app (op (∏ᶜ fun j ↦ U (a j))))

/-- The factors of the section of the difference map in degree `n`, into the first summand. -/
private def sect₀ {n : ℕ} (a : Fin (n + 1) → Fin 2) :
    (restr P (U 0 ⨯ U 1)).obj (op (∏ᶜ fun j ↦ U (a j))) ⟶
      (restr P (U 0)).obj (op (∏ᶜ fun j ↦ U (a j))) :=
  if h : a 0 = 0 then 0
  else
    haveI := isIso_restrMap_app P (prod.fst : U 0 ⨯ U 1 ⟶ U 0)
      (prod.lift prod.fst (prod.snd ≫ toMember U (Fin.eq_one_of_ne_zero _ h)))
    inv ((restrMap P (prod.fst : U 0 ⨯ U 1 ⟶ U 0)).app (op (∏ᶜ fun j ↦ U (a j))))

/-- The factors of the section of the difference map in degree `n`, into the second summand. -/
private def sect₁ {n : ℕ} (a : Fin (n + 1) → Fin 2) :
    (restr P (U 0 ⨯ U 1)).obj (op (∏ᶜ fun j ↦ U (a j))) ⟶
      (restr P (U 1)).obj (op (∏ᶜ fun j ↦ U (a j))) :=
  if h : a 0 = 0 then
    haveI := isIso_restrMap_app P (prod.snd : U 0 ⨯ U 1 ⟶ U 1)
      (prod.lift (prod.snd ≫ toMember U h) prod.fst)
    (-inv ((restrMap P (prod.snd : U 0 ⨯ U 1 ⟶ U 1)).app (op (∏ᶜ fun j ↦ U (a j)))))
  else 0

/-- The retraction of `Č(U, P) ⟶ Č(U, P(U 0 × -)) ⊞ Č(U, P(U 1 × -))` in degree `n`. -/
private def mvRetr (n : ℕ) :
    ((cechComplexFunctor U).obj (restr P (U 0)) ⊞ (cechComplexFunctor U).obj (restr P (U 1))).X n ⟶
      ((cechComplexFunctor U).obj P).X n :=
  (biprod.fst : _ ⟶ (cechComplexFunctor U).obj (restr P (U 0))).f n ≫ cechXMap U n (retr₀ U P) +
    (biprod.snd : _ ⟶ (cechComplexFunctor U).obj (restr P (U 1))).f n ≫ cechXMap U n (retr₁ U P)

/-- The section of the difference map in degree `n`. -/
private def mvSect (n : ℕ) :
    ((cechComplexFunctor U).obj (restr P (U 0 ⨯ U 1))).X n ⟶
      ((cechComplexFunctor U).obj (restr P (U 0)) ⊞
        (cechComplexFunctor U).obj (restr P (U 1))).X n :=
  cechXMap U n (sect₀ U P) ≫ (biprod.inl : (cechComplexFunctor U).obj (restr P (U 0)) ⟶ _).f n +
    cechXMap U n (sect₁ U P) ≫ (biprod.inr : (cechComplexFunctor U).obj (restr P (U 1)) ⟶ _).f n

private lemma mvRetr_id (n : ℕ) :
    mvRetr U P n ≫ (biprod.lift ((cechComplexFunctor U).map (toRestr P (U 0)))
        ((cechComplexFunctor U).map (toRestr P (U 1)))).f n +
      (mvDiff U P).f n ≫ mvSect U P n = 𝟙 _ := by
  -- compare the four components of both sides with respect to the biproduct decomposition
  apply HomologicalComplex.biprodX_ext_from <;> apply HomologicalComplex.biprodX_ext_to <;>
    simp only [mvRetr, mvSect, Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      HomologicalComplex.biprod_inl_fst_f_assoc, HomologicalComplex.biprod_inl_snd_f_assoc,
      HomologicalComplex.biprod_inr_fst_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
      HomologicalComplex.biprod_inl_fst_f, HomologicalComplex.biprod_inl_snd_f,
      HomologicalComplex.biprod_inr_fst_f, HomologicalComplex.biprod_inr_snd_f,
      HomologicalComplex.biprod_lift_fst_f, HomologicalComplex.biprod_lift_snd_f,
      HomologicalComplex.biprod_inl_desc_f_assoc, HomologicalComplex.biprod_inr_desc_f_assoc,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp, zero_comp,
      comp_zero, Category.comp_id, add_zero, zero_add, map_f_eq_cechXMap,
      cechXMap_comp, cechXMap_neg, cechXMap_add]
  · refine (cechXMap_ext U fun a ↦ ?_).trans (cechXMap_id U _ n)
    by_cases h : a 0 = 0 <;> simp [retr₀, sect₀, h]
  · refine (cechXMap_ext U fun a ↦ ?_).trans (cechXMap_zero U _ _ n)
    by_cases h : a 0 = 0
    · have := isIso_toRestr_app P (toMember U h)
      have := isIso_restrMap_app P (prod.snd : U 0 ⨯ U 1 ⟶ U 1)
        (prod.lift (prod.snd ≫ toMember U h) prod.fst)
      simp [retr₀, sect₁, h, inv_comp_eq_comp_inv (toRestr_comp_restrMap_app U P _)]
    · simp [retr₀, sect₁, h]
  · refine (cechXMap_ext U fun a ↦ ?_).trans (cechXMap_zero U _ _ n)
    by_cases h : a 0 = 0
    · simp [retr₁, sect₀, h]
    · have := isIso_toRestr_app P (toMember U (Fin.eq_one_of_ne_zero _ h))
      have := isIso_restrMap_app P (prod.fst : U 0 ⨯ U 1 ⟶ U 0)
        (prod.lift prod.fst (prod.snd ≫ toMember U (Fin.eq_one_of_ne_zero _ h)))
      simp [retr₁, sect₀, h, inv_comp_eq_comp_inv (toRestr_comp_restrMap_app U P _).symm]
  · refine (cechXMap_ext U fun a ↦ ?_).trans (cechXMap_id U _ n)
    by_cases h : a 0 = 0 <;> simp [retr₁, sect₁, h]

/-- The short complex `mvShortComplex` is split in each degree. -/
private def mvSplitting (n : ℕ) :
    ((mvShortComplex U P).map (HomologicalComplex.eval A (ComplexShape.up ℕ) n)).Splitting where
  r := mvRetr U P n
  s := mvSect U P n
  f_r := by
    simp only [mvShortComplex, mvRetr, ShortComplex.map_f, ShortComplex.map_X₁, ShortComplex.map_X₂,
      HomologicalComplex.eval_obj, HomologicalComplex.eval_map, Preadditive.comp_add,
      HomologicalComplex.biprod_lift_fst_f_assoc, HomologicalComplex.biprod_lift_snd_f_assoc,
      map_f_eq_cechXMap, cechXMap_comp, cechXMap_add, ← cechXMap_id]
    exact cechXMap_ext U fun a ↦ by by_cases h : a 0 = 0 <;> simp [retr₀, retr₁, h]
  s_g := by
    simp only [mvShortComplex, mvSect, ShortComplex.map_g, ShortComplex.map_X₂, ShortComplex.map_X₃,
      HomologicalComplex.eval_obj, HomologicalComplex.eval_map, Preadditive.add_comp,
      Category.assoc, HomologicalComplex.biprod_inl_desc_f, HomologicalComplex.biprod_inr_desc_f,
      HomologicalComplex.neg_f_apply, map_f_eq_cechXMap, cechXMap_neg, cechXMap_comp, cechXMap_add,
      ← cechXMap_id]
    exact cechXMap_ext U fun a ↦ by by_cases h : a 0 = 0 <;> simp [sect₀, sect₁, h]
  -- the maps of `(mvShortComplex U P).map (eval _ _ n)` are the degree `n` components
  id := mvRetr_id U P n

private lemma mvShortComplex_shortExact : (mvShortComplex U P).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ (mvSplitting U P n).shortExact

/-- The Čech complex of `P(Y × -)` for `U` is exact in positive degrees when `Y` maps to a
member. -/
private lemma exactAt_restr {Y : C} {i₀ : Fin 2} (g : Y ⟶ U i₀) (n : ℕ) :
    ((cechComplexFunctor U).obj (restr P Y)).ExactAt (n + 1) :=
  ((quasiIso_cechAugmentation_iff U terminalIsTerminal (restr P Y)).1
    (quasiIso_cechAugmentation_prod_of_hom U terminalIsTerminal P Y g)).2 n

private lemma exactAt_mvShortComplex_X₂ (n : ℕ) : (mvShortComplex U P).X₂.ExactAt (n + 1) :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact.exactAt_X₂ (n + 1)
    (exactAt_restr U P (𝟙 (U 0)) n) (exactAt_restr U P (𝟙 (U 1)) n)

private lemma exactAt_mvShortComplex_X₃ (n : ℕ) : (mvShortComplex U P).X₃.ExactAt (n + 1) :=
  exactAt_restr U P (prod.fst : U 0 ⨯ U 1 ⟶ U 0) n

/-- **The Čech complex of a two-member family vanishes in degrees `≥ 2`.** In a thin category
with finite products, the Čech complex of any presheaf with values in an abelian category, for a
family of two objects, is exact in every degree `≥ 2`. -/
theorem exactAt_add_two_cechComplexFunctor_obj (n : ℕ) :
    ((cechComplexFunctor U).obj P).ExactAt (n + 2) :=
  (mvShortComplex_shortExact U P).exactAt_X₁ (n + 2)
    (mono_of_source_iso_zero _ (exactAt_mvShortComplex_X₂ U P (n + 1)).isZero_homology.isoZero)
    fun i hi ↦ by
      obtain rfl : i = n + 1 := by simp only [ComplexShape.up_Rel] at hi; omega
      exact epi_of_target_iso_zero _ (exactAt_mvShortComplex_X₃ U P n).isZero_homology.isoZero

/-- The value of `P(Y × -)` at `V` is the value of `P` at `Y × V`. -/
private def restrObjIso (Y V : C) : (restr P Y).obj (op V) ≅ P.obj (op (Y ⨯ V)) :=
  Iso.refl _

/-- The map from `P(Y)` to the degree `0` cohomology of `Č(U, P(Y × -))`: restriction
`P(Y) ⟶ P(Y × T)` followed by the augmentation. It is an isomorphism when `Y` maps to a member
(`isIso_homologyZeroRestr`). -/
private def homologyZeroRestr (Y : C) :
    P.obj (op Y) ⟶ ((cechComplexFunctor U).obj (restr P Y)).homology 0 :=
  P.map (prod.fst : Y ⨯ ⊤_ C ⟶ Y).op ≫ (restrObjIso P Y (⊤_ C)).inv ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      ((restr P Y).obj (op (⊤_ C)))).inv ≫
      HomologicalComplex.homologyMap (cechAugmentation U terminalIsTerminal (restr P Y)) 0

private lemma isIso_homologyZeroRestr {Y : C} {i₀ : Fin 2} (g : Y ⟶ U i₀) :
    IsIso (homologyZeroRestr U P Y) := by
  have : IsIso (HomologicalComplex.homologyMap
      (cechAugmentation U terminalIsTerminal (restr P Y)) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ 0).1
      ((quasiIso_iff _).1 (quasiIso_cechAugmentation_prod_of_hom U terminalIsTerminal P Y g) 0)
  have : IsIso (P.map (prod.fst : Y ⨯ ⊤_ C ⟶ Y).op) := (P.mapIso (iso_of_both_ways
    (prod.fst : Y ⨯ ⊤_ C ⟶ Y) (prod.lift (𝟙 Y) (terminal.from Y))).op).isIso_hom
  unfold homologyZeroRestr
  infer_instance

/-- Restriction from `Y` to `Y'` is compatible with the identifications `homologyZeroRestr`. -/
private lemma homologyZeroRestr_comp_homologyMap {Y Y' : C} (h : Y' ⟶ Y) :
    homologyZeroRestr U P Y ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map (restrMap P h)) 0 =
      P.map h.op ≫ homologyZeroRestr U P Y' := by
  simp only [homologyZeroRestr, Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp, cechAugmentation_naturality,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc, ← Category.assoc,
    ← Category.assoc (P.map h.op)]
  simp only [← Category.assoc]
  refine ((?_ : _ = _) =≫ _) =≫ _
  -- `restrObjIso` is the identity, and the remaining restrictions agree in the thin category `C`
  exact (Category.comp_id _ =≫ _).trans ((map_comp_map_eq P _ _ _ _).trans
    (Category.comp_id _).symm)

/-- The identification of `P(U 0) ⊞ P(U 1)` with the degree `0` cohomology of the middle term of
`mvShortComplex`. -/
private abbrev homologyZeroBiprod :
    P.obj (op (U 0)) ⊞ P.obj (op (U 1)) ⟶
      ((cechComplexFunctor U).obj (restr P (U 0)) ⊞
        (cechComplexFunctor U).obj (restr P (U 1))).homology 0 :=
  biprod.desc (homologyZeroRestr U P (U 0) ≫ HomologicalComplex.homologyMap biprod.inl 0)
    (homologyZeroRestr U P (U 1) ≫ HomologicalComplex.homologyMap biprod.inr 0)

private lemma isIso_homologyZeroBiprod : IsIso (homologyZeroBiprod U P) := by
  have := isIso_homologyZeroRestr U P (𝟙 (U 0))
  have := isIso_homologyZeroRestr U P (𝟙 (U 1))
  -- degree `0` cohomology commutes with the biproduct
  have : IsIso (biprod.desc (HomologicalComplex.homologyMap
      (biprod.inl : (cechComplexFunctor U).obj (restr P (U 0)) ⟶ _) 0)
      (HomologicalComplex.homologyMap
        (biprod.inr : (cechComplexFunctor U).obj (restr P (U 1)) ⟶ _) 0)) :=
    ⟨⟨biprod.lift (HomologicalComplex.homologyMap biprod.fst 0)
        (HomologicalComplex.homologyMap biprod.snd 0),
      by ext <;> simp [← HomologicalComplex.homologyMap_comp],
      by simp [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_add]⟩⟩
  rw [show homologyZeroBiprod U P = biprod.map (homologyZeroRestr U P (U 0))
      (homologyZeroRestr U P (U 1)) ≫ biprod.desc (HomologicalComplex.homologyMap biprod.inl 0)
        (HomologicalComplex.homologyMap biprod.inr 0) by ext <;> simp]
  have : IsIso (biprod.map (homologyZeroRestr U P (U 0)) (homologyZeroRestr U P (U 1))) :=
    (biprod.mapIso (asIso (homologyZeroRestr U P (U 0)))
      (asIso (homologyZeroRestr U P (U 1)))).isIso_hom
  infer_instance

/-- In degree `0` cohomology, the difference map of `mvShortComplex` is the Mayer-Vietoris map
`P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1)`. -/
private lemma homologyZeroBiprod_comp_homologyMap_mvDiff :
    homologyZeroBiprod U P ≫ HomologicalComplex.homologyMap (mvDiff U P) 0 =
      biprod.desc (P.map (prod.fst : U 0 ⨯ U 1 ⟶ U 0).op)
        (-P.map (prod.snd : U 0 ⨯ U 1 ⟶ U 1).op) ≫ homologyZeroRestr U P (U 0 ⨯ U 1) := by
  ext
  · rw [biprod.inl_desc_assoc, biprod.inl_desc_assoc, Category.assoc,
      ← HomologicalComplex.homologyMap_comp]
    exact (_ ≫= congrArg (HomologicalComplex.homologyMap · 0) (biprod.inl_desc _ _)).trans
      (homologyZeroRestr_comp_homologyMap U P _)
  · rw [biprod.inr_desc_assoc, biprod.inr_desc_assoc, Category.assoc,
      ← HomologicalComplex.homologyMap_comp, Preadditive.neg_comp,
      ← homologyZeroRestr_comp_homologyMap, ← Preadditive.comp_neg,
      ← HomologicalComplex.homologyMap_neg]
    exact _ ≫= congrArg (HomologicalComplex.homologyMap · 0) (biprod.inr_desc _ _)

/-- The difference map of `mvShortComplex` is an epimorphism in degree `0` cohomology exactly
when the Mayer-Vietoris map `P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1)` is an epimorphism. -/
private lemma epi_homologyMap_mvDiff_iff :
    Epi (HomologicalComplex.homologyMap (mvDiff U P) 0) ↔
      Epi (biprod.desc (P.map (prod.fst : U 0 ⨯ U 1 ⟶ U 0).op)
        (-P.map (prod.snd : U 0 ⨯ U 1 ⟶ U 1).op)) := by
  have := isIso_homologyZeroBiprod U P
  have := isIso_homologyZeroRestr U P (prod.fst : U 0 ⨯ U 1 ⟶ U 0)
  rw [← epi_comp_iff_of_epi (homologyZeroBiprod U P), homologyZeroBiprod_comp_homologyMap_mvDiff,
    epi_comp_iff_of_isIso]

/-- **Exactness of the Čech complex of a two-member cover.** In a thin category with finite
products and a terminal object `T`, let `P` be a presheaf with values in an abelian category and
let `U 0`, `U 1` be two objects. The augmented Čech complex `0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯`
is exact if and only if `P` satisfies the sheaf condition for the family `U i ⟶ T` and the
difference of restrictions `P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1)` is an epimorphism, that is, if and
only if the Mayer-Vietoris sequence `0 ⟶ P(T) ⟶ P(U 0) ⊞ P(U 1) ⟶ P(U 0 × U 1) ⟶ 0` is short
exact. -/
theorem quasiIso_cechAugmentation_fin_two_iff :
    QuasiIso (cechAugmentation U hT P) ↔
      (∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E)) ∧
        Epi (biprod.desc (P.map (prod.fst : U 0 ⨯ U 1 ⟶ U 0).op)
          (-P.map (prod.snd : U 0 ⨯ U 1 ⟶ U 1).op)) := by
  rw [quasiIso_cechAugmentation_iff, ← epi_homologyMap_mvDiff_iff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h n ↦ ?_⟩
  · -- the connecting map `H⁰(Č(U, P(U 0 × U 1 × -))) ⟶ H¹(Č(U, P))` vanishes
    exact ((mvShortComplex_shortExact U P).homology_exact₃ 0 1 (by simp)).epi_f
      ((h 0).isZero_homology.eq_of_tgt _ _)
  · cases n with
    | zero =>
      exact (mvShortComplex_shortExact U P).exactAt_X₁ 1
        (mono_of_source_iso_zero _ (exactAt_mvShortComplex_X₂ U P 0).isZero_homology.isoZero)
        fun i hi ↦ by
          obtain rfl : i = 0 := by simp only [ComplexShape.up_Rel] at hi; omega
          exact h
    | succ n => exact exactAt_add_two_cechComplexFunctor_obj U P n

end TwoMembers

end TauCeti.CategoryTheory
