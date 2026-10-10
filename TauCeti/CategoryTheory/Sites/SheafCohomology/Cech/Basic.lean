/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import TauCeti.AlgebraicTopology.CechNerve
public import TauCeti.CategoryTheory.Limits.FormalCoproducts.Cech
public import TauCeti.CategoryTheory.Sites.IsSheafFor

/-!
# The augmented Čech complex of a presheaf

Let `C` be a category with finite products and a terminal object `T`, let `U : ι → C` be a family
of objects and let `P : Cᵒᵖ ⥤ A` be a presheaf with values in a preadditive category with
products. Mathlib's `CategoryTheory.cechComplexFunctor U` sends `P` to its Čech complex
`Č(U, P)`, whose degree `n` term is the product, over `a : Fin (n + 1) → ι`, of
`P(U (a 0) × ⋯ × U (a n))`. This file constructs the augmentation `P(T) ⟶ Č⁰(U, P)`, as a map of
cochain complexes from `P(T)` placed in degree `0`, and characterises when it is a
quasi-isomorphism, that is, when the augmented Čech complex
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact. The augmentation is Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.ε` for the augmented Čech object
`FormalCoproduct.cech.augmentOfIsTerminal` evaluated at `P`, transported from `Aᵒᵖ` to `A`.

For an open cover `U` of a topological space `X` and a presheaf of abelian groups `F` on `X`, this
is Wedhorn's notion of an `F`-acyclic cover: the augmentation identifies `F(X)` with the degree `0`
cohomology of `Č(U, F)`, and `Č(U, F)` has no cohomology in positive degrees. A cover of an open
subset `W` fits this setting in the category `Over W`, which has finite products and the terminal
object `Over.mk (𝟙 W)` (`CategoryTheory.Over.mkIdTerminal`).

A morphism of families `U ⟶ V`, that is a morphism of formal coproducts, induces a map of Čech
complexes `Č(V, P) ⟶ Č(U, P)` compatible with the augmentations, and any two morphisms `U ⟶ V`
induce homotopic maps. For open covers this says that the map on Čech cohomology induced by a
refinement does not depend on the refinement map; in particular, acyclicity of a cover only depends
on the cover up to refinement in both directions, so that members contained in other members may
be added or removed.

## Main definitions

* `TauCeti.CategoryTheory.cechAugmentation U hT P`: the augmentation of the Čech complex of `P`
  for `U`; its degree `0` component restricts a section over `T` along each map to `T`
  (`TauCeti.CategoryTheory.cechAugmentation_f_zero_comp_π`).
* `TauCeti.CategoryTheory.cechComplexMap P φ`: the map of Čech complexes `Č(V, P) ⟶ Č(U, P)`
  induced by a morphism of families `φ : U ⟶ V`.

## Main results

* `TauCeti.CategoryTheory.quasiIsoAt_cechAugmentation_zero_iff`: the augmentation induces an
  isomorphism in degree `0` exactly when `P` satisfies the sheaf condition for the family of
  maps `U i ⟶ T`, in Mathlib's form for presheaves with values in `A`: every
  `P ⋙ coyoneda.obj E` is a sheaf for `Presieve.ofArrows U`.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff`: the augmentation is a
  quasi-isomorphism exactly when `P` satisfies that sheaf condition and the Čech complex is
  exact in every positive degree.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_hom`: if some `U i₀` receives a map from
  `T`, for instance if `U i₀ = T`, then the augmentation is a quasi-isomorphism. This comes from
  Mathlib's extra degeneracy `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` of the
  Čech object, which makes `ε` a homotopy equivalence
  (`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`).
* `TauCeti.CategoryTheory.cechComplexMapHomotopy`: any two morphisms of families `U ⟶ V`
  induce homotopic maps of Čech complexes.
* `TauCeti.CategoryTheory.cechComplexHomotopyEquiv`: families with morphisms `U ⟶ V` and
  `V ⟶ U` have homotopy equivalent Čech complexes.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_congr`: for such families, the augmented Čech
  complex of `P` for `U` is exact if and only if the one for `V` is.
* `TauCeti.CategoryTheory.isIso_cechComplexMap`: a morphism of families that is the identity on
  indices induces an isomorphism of Čech complexes when `P` inverts the induced maps of products.
* `TauCeti.CategoryTheory.cechAugmentation_naturality`: the augmentation is natural in `P`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Appendix A: Definition A.1 and
  the acyclicity of a cover having `X` as a member, stated after Remark A.2.
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4, for the independence of the map induced by a refinement from the refinement
  map.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology Simplicial

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T) (P : Cᵒᵖ ⥤ A)

variable [Preadditive A] [HasProducts.{w} A]

/-! ### The Čech complex in degrees `0` and `1`

Mathlib's `cechComplexFunctor` is a composite of several functors, so its terms agree only up to
unfolding with the products that define them. The identity isomorphisms `cechXIso₀` and
`cechXIso₁` record these identifications once, so that every later statement composes maps
between syntactically equal objects. A `0`-cochain is determined by its restrictions `restrict`
to the members `U i`, and it is killed by the differential `Č⁰(U, P) ⟶ Č¹(U, P)` exactly when
these restrictions agree on the products of pairs of members (`comp_d_eq_zero_iff`). -/

private def cechXIso₀ : ((cechComplexFunctor U).obj P).X 0 ≅
    ∏ᶜ fun a : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) := Iso.refl _

private def cechXIso₁ : ((cechComplexFunctor U).obj P).X 1 ≅
    ∏ᶜ fun k : Fin 2 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (k j))) := Iso.refl _

private def cechδ (m : Fin 2) : ((cechComplexFunctor U).obj P).X 0 ⟶
    ((cechComplexFunctor U).obj P).X 1 :=
  ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P).δ m

private lemma cechComplexFunctor_obj_d_zero_one :
    ((cechComplexFunctor U).obj P).d 0 1 = cechδ U P 0 - cechδ U P 1 :=
  (CochainComplex.of_d _ (AlternatingCofaceMapComplex.objD _) 0).trans <| by
    simp [sub_eq_add_neg]
    -- `cechδ m` unfolds to the coface map `δ m`
    rfl

private lemma cechδ_comp_π (m : Fin 2) (k : Fin 2 → ι) :
    cechδ U P m ≫ (cechXIso₁ U P).hom ≫ Pi.π _ k =
      (cechXIso₀ U P).hom ≫ Pi.π _ (fun x ↦ k (m.succAbove x)) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op :=
  -- `cechXIso₀` and `cechXIso₁` are identities, and `cechδ m` unfolds to a `Pi.lift`
  (_ ≫= Category.id_comp _).trans <| (Pi.lift_comp_π _ _).trans (Category.id_comp _).symm

private def restrict (a : Fin 1 → ι) :
    ((cechComplexFunctor U).obj P).X 0 ⟶ P.obj (op (U (a default))) :=
  (cechXIso₀ U P).hom ≫ Pi.π _ a ≫ P.map (productUniqueIso _).inv.op

private lemma restrict_eq_restrict_const (a : Fin 1 → ι) :
    restrict U P a = restrict U P (fun _ ↦ a default) :=
  eq_const_of_unique a ▸ rfl

@[reassoc]
private lemma cechXIso₀_hom_comp_π (a : Fin 1 → ι) : (cechXIso₀ U P).hom ≫ Pi.π _ a =
    restrict U P a ≫ P.map (productUniqueIso fun j ↦ U (a j)).hom.op :=
  -- `restrict a` is the left-hand side followed by `P.map (productUniqueIso _).inv.op`
  (P.mapIso (productUniqueIso _).op).comp_inv_eq.1 (Category.assoc _ _ _)

private lemma cechComplexFunctor_obj_X_zero_hom_ext {W : A}
    {y y' : W ⟶ ((cechComplexFunctor U).obj P).X 0}
    (h : ∀ i, y ≫ restrict U P (fun _ ↦ i) = y' ≫ restrict U P (fun _ ↦ i)) : y = y' :=
  (cancel_mono (cechXIso₀ U P).hom).1 <| Pi.hom_ext _ _ fun a ↦ by
    grind [cechXIso₀_hom_comp_π, restrict_eq_restrict_const]

private lemma comp_d_eq_zero_iff {W : A} (y : W ⟶ ((cechComplexFunctor U).obj P).X 0) :
    y ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 ↔ ∀ k : Fin 2 → ι,
      y ≫ restrict U P (fun _ ↦ k 1) ≫ P.map (Pi.π (fun j ↦ U (k j)) 1).op =
        y ≫ restrict U P (fun _ ↦ k 0) ≫ P.map (Pi.π (fun j ↦ U (k j)) 0).op := by
  have key (m : Fin 2) (k : Fin 2 → ι) : cechδ U P m ≫ (cechXIso₁ U P).hom ≫ Pi.π _ k =
      restrict U P (fun _ ↦ k (m.succAbove default)) ≫
        P.map (Pi.π (fun j ↦ U (k j)) (m.succAbove default)).op := by
    rw [cechδ_comp_π, cechXIso₀_hom_comp_π_assoc, ← P.map_comp, ← op_comp, productUniqueIso_hom,
      Pi.lift_comp_π, restrict_eq_restrict_const]
  rw [← cancel_mono (cechXIso₁ U P).hom, zero_comp, Pi.hom_ext_iff]
  simp [cechComplexFunctor_obj_d_zero_one, key, sub_eq_zero, Fin.one_succAbove_zero]

private def lift₀ {W : A} (x : ∀ i, W ⟶ P.obj (op (U i))) :
    W ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  (Pi.lift fun a ↦ x (a default) ≫ P.map (productUniqueIso _).hom.op) ≫ (cechXIso₀ U P).inv

@[reassoc]
private lemma lift₀_comp_restrict {W : A} (x : ∀ i, W ⟶ P.obj (op (U i))) (a : Fin 1 → ι) :
    lift₀ U P x ≫ restrict U P a = x (a default) := by
  simp [restrict, lift₀, ← P.map_comp, ← op_comp]

/-! ### The augmented Čech object with values in `Aᵒᵖ`

Applying `P` to Mathlib's augmented Čech object `FormalCoproduct.cech.augmentOfIsTerminal`
gives an augmented simplicial object in `Aᵒᵖ`, whose alternating face map complex is, after
passing back to `A`, the Čech complex of `P`. Its augmentation `AlternatingFaceMapComplex.ε`,
passed back to `A` in the same way (`singleIso`), is the augmentation of the Čech complex. -/

private abbrev cechSimplicial : SimplicialObject Aᵒᵖ :=
  ((SimplicialObject.whiskering _ _).obj ((FormalCoproduct.evalOp C A).obj P).rightOp).obj
    (FormalCoproduct.mk _ U).cech

private abbrev augmentedCech : SimplicialObject.Augmented Aᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering _ _).obj ((FormalCoproduct.evalOp C A).obj P).rightOp).obj
    ((FormalCoproduct.mk _ U).cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl _ hT))

private lemma unop_d_eq_cechComplexFunctor_obj_d (n : ℕ) :
    (AlternatingFaceMapComplex.obj (cechSimplicial U P)).unop.d n (n + 1) =
      ((cechComplexFunctor U).obj P).d n (n + 1) := by
  rw [HomologicalComplex.unop_d, AlternatingFaceMapComplex.obj_d_eq]
  -- the unopposite of each face map of `cechSimplicial` is a coface map of the Čech object
  exact Eq.symm <| (CochainComplex.of_d _ _ n).trans (AlternatingCofaceMapComplex.d_eq_unop_d _ n)

private def unopAlternatingFaceMapComplexIso :
    ((AlternatingFaceMapComplex.obj (cechSimplicial U P)).unop : CochainComplex A ℕ) ≅
      (cechComplexFunctor U).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun i _ h ↦
    h ▸ (Category.id_comp _).trans
      ((unop_d_eq_cechComplexFunctor_obj_d U P i).symm.trans (Category.comp_id _).symm)

/-! ### Maps of presheaves -/

/-- A morphism of presheaves `α : P ⟶ Q` acts on the Čech complexes factorwise: the factor of
`((cechComplexFunctor U).map α).f n` indexed by `a` is the component of `α` at
`U (a 0) × ⋯ × U (a n)`. -/
theorem cechComplexFunctor_map_f_π {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map α).f n ≫ Pi.π _ a =
      Pi.π _ a ≫ α.app (op (∏ᶜ fun j ↦ U (a j))) :=
  Pi.map_π (fun _ ↦ α.app _) a

/-! ### Maps of families

A morphism `φ` from the family `U` to a family `V : κ → C`, as a morphism of formal coproducts,
consists of a map `φ.f : ι → κ` of indices and morphisms `φ.φ i : U i ⟶ V (φ.f i)`; for open covers
it is a refinement map. It induces a map of Čech complexes `Č(V, P) ⟶ Č(U, P)`
(`cechComplexMap`). Any two morphisms `U ⟶ V` induce homotopic maps (`cechComplexMapHomotopy`),
because they induce simplicially homotopic maps of Čech nerves
(`CategoryTheory.Arrow.mapCechNerveHomotopy`). -/

section Map

variable {U} {κ : Type w} {V : κ → C}

/-- The map of Čech complexes `Č(V, P) ⟶ Č(U, P)` induced by a morphism `φ` from the family `U`
to the family `V`. In degree `n` it sends the factor `P(V (b 0) × ⋯ × V (b n))` indexed by
`b = φ.f ∘ a` to the factor `P(U (a 0) × ⋯ × U (a n))` by restriction along the product of the
`φ.φ (a j)` (`cechComplexMap_f_π`). -/
noncomputable def cechComplexMap (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechComplexFunctor V).obj P ⟶ (cechComplexFunctor U).obj P :=
  (alternatingCofaceMapComplex A).map (Functor.whiskerRight
    (NatTrans.rightOp (FormalCoproduct.cechFunctor.map φ)) ((FormalCoproduct.evalOp C A).obj P))

/-- The factor of `(cechComplexMap P φ).f n` indexed by `a` is the factor of `Č(V, P)` indexed by
`φ.f ∘ a`, restricted along the product of the morphisms `φ.φ (a j)`. -/
theorem cechComplexMap_f_π (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ)
    (a : Fin (n + 1) → ι) :
    (cechComplexMap P φ).f n ≫ Pi.π _ a =
      Pi.π _ (φ.f ∘ a) ≫ P.map (Limits.Pi.map fun j ↦ φ.φ (a j)).op :=
  Pi.lift_comp_π _ _

/-- The identity morphism of a family induces the identity of its Čech complex. -/
@[simp]
theorem cechComplexMap_id : cechComplexMap P (𝟙 (FormalCoproduct.mk _ U)) = 𝟙 _ := by
  simp only [cechComplexMap, CategoryTheory.Functor.map_id, NatTrans.rightOp_id,
    Functor.whiskerRight_id']
  exact (alternatingCofaceMapComplex A).map_id _

/-- `cechComplexMap` is contravariantly functorial in the morphism of families. -/
@[simp]
theorem cechComplexMap_comp {ι' : Type w} {W : ι' → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W) :
    cechComplexMap P (φ ≫ ψ) = cechComplexMap P ψ ≫ cechComplexMap P φ := by
  simp only [cechComplexMap, CategoryTheory.Functor.map_comp, NatTrans.rightOp_comp,
    Functor.whiskerRight_comp]
  exact (alternatingCofaceMapComplex A).map_comp _ _

/-- A morphism of families which is the identity on indices, given by morphisms
`φ i : U i ⟶ W i`, induces an isomorphism of Čech complexes `Č(W, P) ⟶ Č(U, P)` as soon as `P`
turns each induced morphism `U (a 0) × ⋯ × U (a n) ⟶ W (a 0) × ⋯ × W (a n)` into an
isomorphism. -/
theorem isIso_cechComplexMap {W : ι → C} (φ : ∀ i, U i ⟶ W i)
    (h : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsIso (P.map (Limits.Pi.map fun j ↦ φ (a j)).op)) :
    IsIso (cechComplexMap P (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)) := by
  have (n : ℕ) : IsIso ((cechComplexMap P
      (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)).f n) := by
    have hπ (a : Fin (n + 1) → ι) : (cechComplexMap P
        (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)).f n ≫ Pi.π _ a =
          Pi.π _ a ≫ P.map (Limits.Pi.map fun j ↦ φ (a j)).op :=
      cechComplexMap_f_π P _ n a
    -- in degree `n` the map is the product of the maps `P.map (Pi.map fun j ↦ φ (a j)).op`
    have e : (cechComplexMap P
        (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)).f n =
          Limits.Pi.map (fun a : Fin (n + 1) → ι ↦ P.map (Limits.Pi.map fun j ↦ φ (a j)).op) :=
      Pi.hom_ext _ _ fun a ↦ (hπ a).trans
        (Pi.map_π (fun a : Fin (n + 1) → ι ↦ P.map (Limits.Pi.map fun j ↦ φ (a j)).op) a).symm
    have := h n
    rw [e]
    exact Pi.map_isIso _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The morphism of arrows to the terminal object of `FormalCoproduct C` induced by a morphism of
formal coproducts. -/
private abbrev cechArrowHom {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) :
    Arrow.mk ((FormalCoproduct.isTerminalIncl _ terminalIsTerminal).from X) ⟶
      Arrow.mk ((FormalCoproduct.isTerminalIncl _ terminalIsTerminal).from Y) :=
  Arrow.homMk φ (𝟙 _) ((FormalCoproduct.isTerminalIncl _ terminalIsTerminal).hom_ext _ _)

/-- Under the identification of the Čech object of a formal coproduct with the Čech nerve of its
map to the terminal object, the map induced by `φ` is `Arrow.mapCechNerve`. -/
private lemma cechFunctor_map_eq {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) :
    (FormalCoproduct.cechFunctor.map φ : X.cech ⟶ Y.cech) =
      (X.cechIsoCechNerve terminalIsTerminal).hom ≫ Arrow.mapCechNerve (cechArrowHom φ) ≫
        (Y.cechIsoCechNerve terminalIsTerminal).inv :=
  ((Iso.eq_comp_inv _).2 (FormalCoproduct.cechFunctor_map_comp_cechIsoCechNerve_hom _ φ)).trans
    (Category.assoc _ _ _)

/-- `cechComplexMap` read through `unopAlternatingFaceMapComplexIso`, as the map of alternating
face map complexes of simplicial objects in `Aᵒᵖ`. -/
private lemma cechComplexMap_eq (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechComplexMap P φ = (unopAlternatingFaceMapComplexIso V P).inv ≫
      (HomologicalComplex.unopFunctor _ _).map ((alternatingFaceMapComplex Aᵒᵖ).map
        (((SimplicialObject.whiskering _ _).obj ((FormalCoproduct.evalOp C A).obj P).rightOp).map
          (FormalCoproduct.cechFunctor.map φ))).op ≫
        (unopAlternatingFaceMapComplexIso U P).hom := by
  ext n : 1
  -- the components of `unopAlternatingFaceMapComplexIso` are identities
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **Any two morphisms of families induce homotopic maps of Čech complexes.** For morphisms
`φ ψ` from the family `U` to the family `V`, for instance two refinement maps between open covers,
the maps `Č(V, P) ⟶ Č(U, P)` they induce are homotopic. -/
noncomputable def cechComplexMapHomotopy (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    Homotopy (cechComplexMap P φ) (cechComplexMap P ψ) :=
  -- the simplicial homotopy between the maps of Čech nerves, carried to the Čech objects and
  -- then to simplicial objects in `Aᵒᵖ` by `P`
  let H := (((Arrow.mapCechNerveHomotopy (cechArrowHom φ) (cechArrowHom ψ) rfl).postcomp
    ((FormalCoproduct.mk _ V).cechIsoCechNerve terminalIsTerminal).inv).precomp
      ((FormalCoproduct.mk _ U).cechIsoCechNerve terminalIsTerminal).hom).whiskerRight
        ((FormalCoproduct.evalOp C A).obj P).rightOp
  (Homotopy.ofEq (by
    rw [cechComplexMap_eq, cechFunctor_map_eq]
    exact (Category.assoc _ _ _).symm)).trans <|
      ((H.toChainHomotopy.unop.compLeft (unopAlternatingFaceMapComplexIso V P).inv).compRight
        (unopAlternatingFaceMapComplexIso U P).hom).trans <|
          Homotopy.ofEq (by
            rw [cechComplexMap_eq, cechFunctor_map_eq]
            exact Category.assoc _ _ _)

/-- **Families that map to each other have homotopy equivalent Čech complexes.** Given morphisms
of families `φ : U ⟶ V` and `ψ : V ⟶ U`, for instance two open covers each refining the other, the
induced maps `Č(V, P) ⟶ Č(U, P)` and `Č(U, P) ⟶ Č(V, P)` are mutually inverse homotopy
equivalences. -/
noncomputable def cechComplexHomotopyEquiv (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    HomotopyEquiv ((cechComplexFunctor V).obj P) ((cechComplexFunctor U).obj P) where
  hom := cechComplexMap P φ
  inv := cechComplexMap P ψ
  homotopyHomInvId := (Homotopy.ofEq (cechComplexMap_comp P ψ φ).symm).trans <|
    (cechComplexMapHomotopy P (ψ ≫ φ) (𝟙 _)).trans (Homotopy.ofEq (cechComplexMap_id P))
  homotopyInvHomId := (Homotopy.ofEq (cechComplexMap_comp P φ ψ).symm).trans <|
    (cechComplexMapHomotopy P (φ ≫ ψ) (𝟙 _)).trans (Homotopy.ofEq (cechComplexMap_id P))

/-- The forward map of `cechComplexHomotopyEquiv P φ ψ` is the map induced by `φ`. -/
@[simp]
theorem cechComplexHomotopyEquiv_hom (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    (cechComplexHomotopyEquiv P φ ψ).hom = cechComplexMap P φ := (rfl)

/-- The backward map of `cechComplexHomotopyEquiv P φ ψ` is the map induced by `ψ`. -/
@[simp]
theorem cechComplexHomotopyEquiv_inv (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    (cechComplexHomotopyEquiv P φ ψ).inv = cechComplexMap P ψ := (rfl)

end Map

variable [HasZeroObject A]

private def singleIso : (CochainComplex.single₀ A).obj (P.obj (op T)) ≅
    (((ChainComplex.single₀ Aᵒᵖ).obj (augmentedCech U hT P).right).unop : CochainComplex A ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 => HomologicalComplex.singleObjXSelf _ 0 _ ≪≫
          (((FormalCoproduct.evalOpCompInlIsoId C A).app P).app (op T)).symm ≪≫
            (HomologicalComplex.singleObjXSelf _ 0 _).unop
      | n + 1 => (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).iso
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).unop)
    (fun _ _ _ ↦ by
      simp only [HomologicalComplex.single_obj_d, HomologicalComplex.unop_d, unop_zero, zero_comp]
      exact comp_zero)

/-- The augmentation of the Čech complex of `P` for the family `U`, as a map of cochain complexes
from `P(T)` placed in degree `0`. It is Mathlib's augmentation `AlternatingFaceMapComplex.ε` of the
augmented Čech object evaluated at `P`, passed from `Aᵒᵖ` back to `A`. Its degree `0` component
`P(T) ⟶ Č⁰(U, P)` restricts a section over `T` along the maps to `T`
(`cechAugmentation_f_zero_comp_π`). As for `CategoryTheory.InjectiveResolution.ι`, exactness of the
augmented Čech complex `0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is expressed as
`QuasiIso (cechAugmentation U hT P)`; `quasiIso_cechAugmentation_iff` unpacks it into the sheaf
condition for the family `U i ⟶ T` and exactness of the Čech complex in positive degrees. -/
def cechAugmentation : (CochainComplex.single₀ A).obj (P.obj (op T)) ⟶
    (cechComplexFunctor U).obj P :=
  (singleIso U hT P).hom ≫ (HomologicalComplex.unopFunctor _ _).map
    (AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)).op ≫
      (unopAlternatingFaceMapComplexIso U P).hom

/-- The degree `0` component of the augmentation, followed by the projection of `Č⁰(U, P)` onto its
factor indexed by `a : Fin 1 → ι`, is `P` applied to the map from `∏ᶜ fun j ↦ U (a j)` to the
terminal object: the augmentation restricts a section over `T` to each member of the family, seen as
a one-fold product. -/
@[reassoc]
theorem cechAugmentation_f_zero_comp_π (a : Fin 1 → ι) : (cechAugmentation U hT P).f 0 ≫ Pi.π _ a =
    P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op := by
  -- in degree `0`, `cechAugmentation` is `ε` between the identifications made by `singleIso` and
  -- `unopAlternatingFaceMapComplexIso`, and `ε` is `P` applied to the map to the terminal object
  have h : (cechAugmentation U hT P).f 0 = ((HomologicalComplex.singleObjXSelf _ 0 _).hom ≫
      (Pi.lift fun _ ↦ 𝟙 _) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (augmentedCech U hT P).right).hom.unop) ≫
      ((AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)).f 0).unop ≫ 𝟙 _ := rfl
  -- the augmentation of `augmentedCech` is `evalOp P` applied to the map to `incl T`
  have hM : ((augmentedCech U hT P).hom.app (op ⦋0⦌)).unop = 𝟙 _ ≫
      ((FormalCoproduct.evalOp C A).obj P).map ((FormalCoproduct.isTerminalIncl _ hT).from _).op :=
    rfl
  rw [h]
  simp only [CochainComplex.single₀_obj_zero, Functor.rightOp_obj, FormalCoproduct.cech_obj,
    Functor.comp_obj, SimplicialObject.Augmented.point_obj, ChainComplex.single₀_obj_zero,
    SimplicialObject.Augmented.drop_obj, alternatingFaceMapComplex_obj_X,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, ChainComplex.single₀ObjXSelf, unop_id,
    Category.id_comp, AlternatingFaceMapComplex.ε_app_f_zero, Functor.id_obj, Category.comp_id]
  rw [hM]
  simp only [SimplicialObject.Augmented.drop_obj, FormalCoproduct.evalOp_obj_map,
    Quiver.Hom.unop_op]
  exact ((Category.comp_id _ =≫ _) =≫ _).trans <| ((_ ≫= Category.id_comp _) =≫ _).trans <|
    (Category.assoc _ _ _).trans <| (_ ≫= Pi.lift_comp_π _ _).trans <|
      (Pi.lift_comp_π_assoc _ _ _).trans <| (Category.id_comp _).trans <|
        P.congr_map (congrArg Quiver.Hom.op (hT.hom_ext _ _))

section Map

variable {U} {κ : Type w} {V : κ → C}

/-- The augmentations of the Čech complexes are compatible with the maps induced by morphisms of
families: restricting a section over `T` to the members of `V` and then to the members of `U`
restricts it to the members of `U`. -/
@[reassoc (attr := simp)]
theorem cechAugmentation_comp_cechComplexMap
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechAugmentation V hT P ≫ cechComplexMap P φ = cechAugmentation U hT P := by
  refine HomologicalComplex.from_single_hom_ext (Pi.hom_ext _ _ fun (a : Fin 1 → ι) ↦ ?_)
  -- both sides restrict along a map to the terminal object `T`
  exact (Category.assoc _ _ _).trans <| (_ ≫= cechComplexMap_f_π P φ 0 a).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechAugmentation_f_zero_comp_π V hT P _ =≫ _).trans <|
      (P.map_comp _ _).symm.trans <|
      (P.congr_map (congrArg Quiver.Hom.op (hT.hom_ext _ _))).trans
        (cechAugmentation_f_zero_comp_π U hT P a).symm

end Map

/-- The augmentation is natural in the presheaf: for `α : P ⟶ Q`, restricting a section of `P`
over `T` to the members of the family and then applying `α` is applying `α` over `T` and then
restricting. -/
@[reassoc]
theorem cechAugmentation_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    cechAugmentation U hT P ≫ (cechComplexFunctor U).map α =
      (CochainComplex.single₀ A).map (α.app (op T)) ≫ cechAugmentation U hT Q := by
  refine HomologicalComplex.from_single_hom_ext (Pi.hom_ext _ _ fun (a : Fin 1 → ι) ↦ ?_)
  -- restrict to `a`, then use naturality of `α` along the map to `T`
  exact (Category.assoc _ _ _).trans <| (_ ≫= cechComplexFunctor_map_f_π U P α 0 a).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechAugmentation_f_zero_comp_π U hT P a =≫ _).trans <|
      (α.naturality _).trans <|
      (_ ≫= cechAugmentation_f_zero_comp_π U hT Q a).symm.trans <| (Category.assoc _ _ _).symm.trans
        ((by simp : _ = ((CochainComplex.single₀ A).map (α.app (op T)) ≫
          cechAugmentation U hT Q).f 0) =≫ _)

/-! ### The augmentation in degree `0`

The degree `0` component `augmentation₀ : P(T) ⟶ Č⁰(U, P)` of the augmentation restricts along
the maps to `T`. Since any family of sections over the `U i` defines a `0`-cochain (`lift₀`),
which is killed by the Čech differential exactly when the family is compatible,
`comp_d_eq_zero_iff` shows that `augmentation₀` is a kernel of the Čech differential exactly when
`P` satisfies the sheaf condition for the family `U i ⟶ T`
(`isLimit_kernelFork_iff_isSheafFor`). -/

private def augmentation₀ : P.obj (op T) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ (cechAugmentation U hT P).f 0

@[reassoc]
private lemma augmentation₀_comp_restrict (a : Fin 1 → ι) :
    augmentation₀ U hT P ≫ restrict U P a = P.map (hT.from (U (a default))).op :=
  -- `singleObjXSelf _ 0 _` and `cechXIso₀` are identities
  (Category.assoc _ _ _).trans <| (Category.id_comp _).trans <| (_ ≫= Category.id_comp _).trans <|
    (Category.assoc _ _ _).symm.trans <| (cechAugmentation_f_zero_comp_π U hT P a =≫ _).trans <|
      (P.map_comp _ _).symm.trans <| P.congr_map (congrArg Quiver.Hom.op (hT.hom_ext _ _))

private lemma augmentation₀_comp_d :
    augmentation₀ U hT P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 :=
  (Category.assoc _ _ _).trans <| (_ ≫= (cechAugmentation U hT P).comm 0 1).trans <| by
    simp only [HomologicalComplex.single_obj_d, zero_comp]
    exact comp_zero

private lemma comp_augmentation₀_eq_iff {W : A} (t : W ⟶ P.obj (op T))
    (y : W ⟶ ((cechComplexFunctor U).obj P).X 0) : t ≫ augmentation₀ U hT P = y ↔
      ∀ i, t ≫ P.map (hT.from (U i)).op = y ≫ restrict U P fun _ ↦ i :=
  ⟨fun h i ↦ by simp [← h, augmentation₀_comp_restrict], fun h ↦
    cechComplexFunctor_obj_X_zero_hom_ext U P fun i ↦ by simp [augmentation₀_comp_restrict, h]⟩

private lemma isLimit_kernelFork_iff_isSheafFor :
    Nonempty (IsLimit (KernelFork.ofι (augmentation₀ U hT P) (augmentation₀_comp_d U hT P))) ↔
      ∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E) := by
  simp only [op_surjective.forall, Presieve.isSheafFor_arrows_iff,
    Presieve.Arrows.compatible_iff_of_isTerminal hT, Functor.comp_map, Functor.flip_obj_map,
    yoneda_map_app, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  refine ⟨fun ⟨hl⟩ W x hx ↦ ?_, fun h ↦ ⟨Fork.IsLimit.ofExistsUnique fun s ↦ ?_⟩⟩
  · simpa [comp_augmentation₀_eq_iff, lift₀_comp_restrict] using
      Fork.IsLimit.existsUnique hl (lift₀ U P x) <| by
        simpa [comp_d_eq_zero_iff, lift₀_comp_restrict_assoc] using hx
  · simpa [comp_augmentation₀_eq_iff] using h s.pt (fun i ↦ s.ι ≫ restrict U P fun _ ↦ i) <| by
      simpa using (comp_d_eq_zero_iff U P _).1 (KernelFork.condition s)

variable [CategoryWithHomology A]

private lemma quasiIsoAt_cechAugmentation_zero_iff_isLimit :
    QuasiIsoAt (cechAugmentation U hT P) 0 ↔
      Nonempty (IsLimit (KernelFork.ofι (augmentation₀ U hT P) (augmentation₀_comp_d U hT P))) := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  refine (ShortComplex.quasiIso_iff_isIso_liftCycles _ rfl rfl rfl).trans <|
    ((ShortComplex.cyclesIsKernel _).nonempty_isLimit_iff_isIso_lift
      (t := KernelFork.ofι _ _)).symm.trans ?_
  exact (IsLimit.equivIsoLimit (Fork.ext _ (Iso.hom_inv_id_assoc _ _))).nonempty_congr

/-- The augmentation identifies `P(T)` with the degree `0` cohomology of the Čech complex (that is,
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P)` is exact) if and only if `P` satisfies the sheaf condition for the
family of maps `U i ⟶ T`: for every `E`, the presheaf of types `P ⋙ coyoneda.obj E` is a sheaf for
`Presieve.ofArrows U`. The condition holds when `P` is a sheaf (`Presheaf.IsSheaf J P`) for a
topology `J` in which `Sieve.ofArrows U _` covers `T` (use `Presieve.isSheafFor_iff_generate`), and
`Presheaf.isLimit_iff_isSheafFor_presieve` expresses it as a limit condition. -/
@[stacks 03AN "The equivalence for a single covering, which is the content of the proof there."]
theorem quasiIsoAt_cechAugmentation_zero_iff : QuasiIsoAt (cechAugmentation U hT P) 0 ↔
    ∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E) :=
  (quasiIsoAt_cechAugmentation_zero_iff_isLimit U hT P).trans
    (isLimit_kernelFork_iff_isSheafFor U hT P)

/-- The augmentation is a quasi-isomorphism, that is, the augmented Čech complex
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact, if and only if `P` satisfies the sheaf condition
for the family of maps `U i ⟶ T` and the Čech complex is exact in every positive degree, that is,
the Čech cohomology of `P` for `U` vanishes in every positive degree. This unpacks acyclicity in the
sense of [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition A.1, so that it can be proved or used
degree by degree; the degree `0` part alone is `quasiIsoAt_cechAugmentation_zero_iff`. -/
theorem quasiIso_cechAugmentation_iff : QuasiIso (cechAugmentation U hT P) ↔
    (∀ E : Aᵒᵖ, (Presieve.ofArrows U fun i ↦ hT.from (U i)).IsSheafFor (P ⋙ coyoneda.obj E)) ∧
      ∀ n, ((cechComplexFunctor U).obj P).ExactAt (n + 1) := by
  rw [quasiIso_iff, ← Nat.and_forall_add_one, quasiIsoAt_cechAugmentation_zero_iff]
  simp [quasiIsoAt_iff_exactAt, CochainComplex.exactAt_succ_single_obj]

/-- If some member `U i₀` of the family receives a map `f : T ⟶ U i₀` from the terminal object,
equivalently if `U i₀ ⟶ T` is a split epimorphism, then the augmentation of the Čech complex of
every presheaf `P` for `U` is a quasi-isomorphism: the augmented Čech complex
`0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact. For an open cover of `W`, viewed in `Over W`, such
a map exists exactly when `W` is itself a member of the cover. -/
@[stacks 0G6S "exactness of the extended Čech complex"]
theorem quasiIso_cechAugmentation_of_hom {i₀ : ι} (f : T ⟶ U i₀) :
    QuasiIso (cechAugmentation U hT P) := by
  -- `f` gives an extra degeneracy of the augmented Čech object, so that its augmentation `ε` is a
  -- homotopy equivalence
  have : QuasiIso (AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)) :=
    (((FormalCoproduct.mk _ U).extraDegeneracyCech hT f).map
      ((FormalCoproduct.evalOp C A).obj P).rightOp).homotopyEquiv.quasiIso_hom
  have hε : QuasiIso ((HomologicalComplex.unopFunctor _ _).map
    (AlternatingFaceMapComplex.ε.app (augmentedCech U hT P)).op) := inferInstance
  -- the isomorphisms on either side are quasi-isomorphisms, as homotopy equivalences
  exact quasiIso_comp _ _ (hφ := (HomotopyEquiv.ofIso (singleIso U hT P)).quasiIso_hom)
    (hφ' := quasiIso_comp _ _ (hφ := hε)
      (hφ' := (HomotopyEquiv.ofIso (unopAlternatingFaceMapComplexIso U P)).quasiIso_hom))

section Map

variable {U} {κ : Type w} {V : κ → C}

/-- **Acyclicity of the Čech complex depends only on the family up to maps both ways.** If there
are morphisms of families `U ⟶ V` and `V ⟶ U`, for instance if `U` and `V` are open covers each
refining the other, then the augmented Čech complex of `P` for `U` is exact if and only if the one
for `V` is. -/
theorem quasiIso_cechAugmentation_congr (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U) :
    QuasiIso (cechAugmentation U hT P) ↔ QuasiIso (cechAugmentation V hT P) := by
  have : QuasiIso (cechComplexMap P φ) := (cechComplexHomotopyEquiv P φ ψ).quasiIso_hom
  rw [← cechAugmentation_comp_cechComplexMap hT P φ]
  exact quasiIso_iff_comp_right _ _

end Map

end TauCeti.CategoryTheory
