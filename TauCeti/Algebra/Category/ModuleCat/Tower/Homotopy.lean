/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.DerivedLimit
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Homotopy

/-!
# Homotopy-coherent maps of countable towers

A family of cochain maps between the levels of two strict towers need not commute with
transitions. Specified homotopies of the adjacent transition squares assemble to a homotopy
of the square of product difference maps, and hence give a map of the native homotopy limits.
In relative coordinates the correction at level `n` uses the homotopy evaluated on the
`n + 1` component. The construction retains this homotopy data when composing maps.

The towers are complexes in the category of module towers, so the resulting map has exactly
the carriers of `ModuleTower.homotopyLimitFunctor`. No replacement fibre complex is introduced.
We use the native mapping-cocone map and its characteristic equations, following Joël Riou's
`CochainComplex.mappingCone.mapOfHomotopy` construction.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5.
* The Stacks Project, More on Algebra, Tags 091D and 07KX.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite CochainComplex HomologicalComplex

universe v u

variable {R : Type u} [Ring R]
  {K L M : CochainComplex (ModuleTower.{v} R) ℤ}

local notation "ev" => fun n : ℕ ↦
  Functor.mapHomologicalComplex (Functor.obj (evaluation ℕᵒᵖ (ModuleCat R)) (op n))
    (ComplexShape.up ℤ)

local notation "tr" => fun n : ℕ ↦ NatTrans.mapHomologicalComplex
  (CategoryTheory.Functor.map (evaluation ℕᵒᵖ (ModuleCat R))
    (Quiver.Hom.op (homOfLE (Nat.le_succ n))))
  (ComplexShape.up ℤ)

/-- The map of product complexes induced by a family of level maps; compatibility with
transitions is not required. -/
def productComplexMapOfFamily (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L) :
    (productComplexFunctor R).obj K ⟶ (productComplexFunctor R).obj L where
  f i := ConcreteCategory.ofHom (C := ModuleCat R) (LinearMap.piMap
    (φ := fun n ↦ (K.X i).obj (op n)) (ψ := fun n ↦ (L.X i).obj (op n))
    fun n ↦ ((f n).f i).hom)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    -- Fix the native product carrier before rewriting its differential componentwise.
    change (K.X i).Product at x
    change productMap (L.d i j) (fun n ↦ (f n).f i (x n)) n =
      (f n).f j (productMap (K.d i j) x n)
    rw [productMap_apply, productMap_apply]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using!
      congrArg (fun g ↦ g.hom (x n)) ((f n).comm i j)

@[simp↓]
lemma productComplexMapOfFamily_f_apply
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L) (i : ℤ)
    (x : ((productComplexFunctor R).obj K).X i) (n : ℕ) :
    (productComplexMapOfFamily f).f i x n = (f n).f i (x n) :=
  (rfl)

/-- The product map of levelwise composites is the composite of the product maps. -/
@[simp]
lemma productComplexMapOfFamily_comp
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (g : ∀ n, (ev n).obj L ⟶ (ev n).obj M) :
    productComplexMapOfFamily (fun n ↦ f n ≫ g n) =
      productComplexMapOfFamily f ≫ productComplexMapOfFamily g := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext n
  rfl

/-- The product map of identity level maps is the identity. -/
@[simp]
lemma productComplexMapOfFamily_id :
    productComplexMapOfFamily (fun n ↦ 𝟙 ((ev n).obj K)) =
      𝟙 ((productComplexFunctor R).obj K) := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext n
  rfl

/-- For a strict map of complexes of towers, the family construction is the product functor. -/
@[simp]
lemma productComplexMapOfFamily_map (f : K ⟶ L) :
    productComplexMapOfFamily (fun n ↦ (ev n).map f) = (productComplexFunctor R).map f := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext n
  exact (productMap_apply (f.f i) x n).symm

/-- Adjacent-square homotopies assemble to a homotopy between the two product-difference
composites. Its `n`th component uses the input at `n + 1`. -/
def productComplexSquareHomotopy
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L)) :
    Homotopy (productComplexMapOfFamily f ≫ (complexShift R).app L)
      ((complexShift R).app K ≫ productComplexMapOfFamily f) where
  hom p q := ConcreteCategory.ofHom (C := ModuleCat R) (LinearMap.pi
    (φ := fun n ↦ (L.X q).obj (op n)) fun n ↦
    ((h n).hom p q).hom.comp (LinearMap.proj (n + 1)))
  zero p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    -- The homotopy lives on the actual dependent product, whose zero map is pointwise.
    change (h n).hom p q (x (n + 1)) = 0
    rw [(h n).zero p q hpq]
    rfl
  comm p := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    have he := (h n).comm p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at he
    have e := congrArg (fun g ↦ g.hom (x (n + 1))) he
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_add, LinearMap.add_apply] at e
    -- Name the native scalar actions on the evaluated carriers before adding coordinates.
    let F (i : ℤ) (n : ℕ) : (K.X i).obj (op n) →ₗ[R] (L.X i).obj (op n) :=
      ((f n).f i).hom
    let H (i j : ℤ) (n : ℕ) : (K.X i).obj (op (n + 1)) →ₗ[R] (L.X j).obj (op n) :=
      ((h n).hom i j).hom
    change (K.X p).Product at x
    simp only [HomologicalComplex.comp_f, complexShift_app_f]
    change (L.X p).shift (fun n ↦ F p n (x n)) n =
      H (p + 1) p n (productMap (K.d p (p + 1)) x (n + 1)) +
        productMap (L.d (p - 1) p) (fun n ↦ H p (p - 1) n (x (n + 1))) n +
        F p n ((K.X p).shift x n)
    rw [shift_apply, shift_apply, productMap_apply, productMap_apply]
    simp only [map_sub]
    have e' : F p n ((K.X p).transition n (x (n + 1))) =
        H (p + 1) p n (((K.d p (p + 1)).app (op (n + 1))).hom (x (n + 1))) +
          ((L.d (p - 1) p).app (op n)).hom (H p (p - 1) n (x (n + 1))) +
          (L.X p).transition n (F p (n + 1) (x (n + 1))) := by
      simpa only [F, H, transition_def] using! e
    rw [e']
    abel

@[simp↓]
lemma productComplexSquareHomotopy_hom_apply
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (p q : ℤ) (x : ((productComplexFunctor R).obj K).X p) (n : ℕ) :
    (productComplexSquareHomotopy f h).hom p q x n = (h n).hom p q (x (n + 1)) :=
  (rfl)

/-- A levelwise cochain map with specified homotopies of its transition squares induces a
map between the native homotopy limits. -/
def homotopyLimitMapOfHomotopies
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L)) :
    (homotopyLimitFunctor R).obj K ⟶ (homotopyLimitFunctor R).obj L :=
  mappingCocone.mapOfHomotopy (productComplexSquareHomotopy f h).symm

/-- The native cocone presentation of the corrected map, allowing the generic second-homotopy
API for cocones to be applied to the assembled product square. -/
lemma homotopyLimitMapOfHomotopies_def
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L)) :
    homotopyLimitMapOfHomotopies f h =
      mappingCocone.mapOfHomotopy (productComplexSquareHomotopy f h).symm :=
  (rfl)

/-- The homotopy-limit map commutes with its projection onto the product complex. -/
@[reassoc (attr := simp)]
lemma homotopyLimitMapOfHomotopies_comp_fst
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L)) :
    homotopyLimitMapOfHomotopies f h ≫ homotopyLimitFst L =
      homotopyLimitFst K ≫ productComplexMapOfFamily f := by
  rw [homotopyLimitMapOfHomotopies, homotopyLimitFst_def, homotopyLimitFst_def]
  exact mappingCocone.mapOfHomotopy_fst _

/-- In relative coordinates, the second component contains the specified adjacent-square
homotopy evaluated on the next level of the first component. -/
@[simp↓]
lemma relativeCoordinates_homotopyLimitMapOfHomotopies
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (p q : ℤ) (hpq : p + -1 = q) (x : ((homotopyLimitFunctor R).obj K).X p) :
    mappingCocone.relativeCoordinates ((complexShift R).app L) p q hpq
        ((homotopyLimitMapOfHomotopies f h).f p x) =
      (fun n ↦ (f n).f p
          ((mappingCocone.relativeCoordinates ((complexShift R).app K) p q hpq x).1 n),
        fun n ↦ (f n).f q
            ((mappingCocone.relativeCoordinates ((complexShift R).app K) p q hpq x).2 n) +
          (h n).hom p q
            ((mappingCocone.relativeCoordinates ((complexShift R).app K) p q hpq x).1
              (n + 1))) := by
  exact mappingCocone.relativeCoordinates_mapOfHomotopy (productComplexSquareHomotopy f h)
    p q hpq x

/-- Composition retains the transported sum of the given adjacent-square homotopies. -/
@[reassoc]
lemma homotopyLimitMapOfHomotopies_comp
    (f : ∀ n, (ev n).obj K ⟶ (ev n).obj L)
    (h : ∀ n, Homotopy ((tr n).app K ≫ f n) (f (n + 1) ≫ (tr n).app L))
    (g : ∀ n, (ev n).obj L ⟶ (ev n).obj M)
    (k : ∀ n, Homotopy ((tr n).app L ≫ g n) (g (n + 1) ≫ (tr n).app M)) :
    homotopyLimitMapOfHomotopies (fun n ↦ f n ≫ g n) (fun n ↦ (h n).compSquare (k n)) =
      homotopyLimitMapOfHomotopies f h ≫ homotopyLimitMapOfHomotopies g k := by
  have he : (productComplexSquareHomotopy (fun n ↦ f n ≫ g n)
      (fun n ↦ (h n).compSquare (k n))).symm =
      (productComplexSquareHomotopy f h).symm.compSquare
        (productComplexSquareHomotopy g k).symm := by
    apply Homotopy.ext
    funext p q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    simp only [Homotopy.symm_hom, productComplexSquareHomotopy,
      productComplexMapOfFamily, Homotopy.compSquare_hom]
    -- Display the componentwise product maps after fixing the native complex carriers.
    change -(((g n).f q).hom (((h n).hom p q).hom (x (n + 1))) +
        ((k n).hom p q).hom (((f (n + 1)).f p).hom (x (n + 1)))) =
      ((g n).f q).hom (-(((h n).hom p q).hom (x (n + 1)))) +
        -(((k n).hom p q).hom (((f (n + 1)).f p).hom (x (n + 1))))
    simp only [map_neg, neg_add]
  -- The generic composition law lives on the native cocone presentation.
  simpa only [homotopyLimitMapOfHomotopies] using!
    (congrArg mappingCocone.mapOfHomotopy he).trans
      (mappingCocone.mapOfHomotopy_comp
        (productComplexSquareHomotopy f h).symm (productComplexSquareHomotopy g k).symm)

/-- For a strict map, use its naturality homotopies to recover the ordinary homotopy-limit map. -/
@[simp]
lemma homotopyLimitMapOfHomotopies_map (f : K ⟶ L) :
    homotopyLimitMapOfHomotopies (fun n ↦ (ev n).map f)
        (fun n ↦ Homotopy.ofEq ((tr n).naturality f).symm) =
      (homotopyLimitFunctor R).map f := by
  have comm : (complexShift R).app K ≫ productComplexMapOfFamily (fun n ↦ (ev n).map f) =
      productComplexMapOfFamily (fun n ↦ (ev n).map f) ≫ (complexShift R).app L := by
    rw [productComplexMapOfFamily_map]
    exact ((complexShift R).naturality f).symm
  have h : (productComplexSquareHomotopy (fun n ↦ (ev n).map f)
      (fun n ↦ Homotopy.ofEq ((tr n).naturality f).symm)).symm =
      Homotopy.ofEq comm := by
    apply Homotopy.ext
    funext p q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext n
    -- The chosen strict square homotopies have zero components.
    change -(0 : (L.X q).Product) n = 0
    simp
  rw [homotopyLimitMapOfHomotopies, h, mappingCocone.mapOfHomotopy_ofEq,
    homotopyLimitFunctor_map]
  simp only [productComplexMapOfFamily_map]
  rfl

end TauCeti.ModuleTower
