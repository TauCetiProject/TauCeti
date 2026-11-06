/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.HomotopyEquiv
import TauCeti.Data.Fin.Tuple.Sort
import TauCeti.Data.Finset.Inversions

/-!
# Refinements of ordered Čech complexes

A morphism of indexed families in a thin category induces a map of ordered Čech complexes,
without any monotonicity assumption on its index function. Extend an ordered cochain
alternatingly to all tuples, apply the tuple refinement map, and restrict to increasing tuples.
Consequently, a collapsed tuple contributes zero, and an injective tuple contributes with the
sign of its increasing rearrangement. This works over integral coefficients, without division.

The tuple/ordered comparison intertwines these maps up to homotopy. Any two refinement functions
induce homotopic ordered maps; composition holds up to homotopy, and hence strictly on cohomology.
The cohomology comparison commutes with refinements. These statements apply to families of opens
and presheaves on arbitrary spaces; neither a covering hypothesis nor finiteness is needed.

## References

* The Stacks Project, Cohomology of Sheaves, §§20.23 and 20.25 (ordered Čech complexes and
  refinement homotopies). The construction uses the alternating extension and homotopy equivalence
  in `TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.HomotopyEquiv`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι κ : Type w} [LinearOrder ι] [LinearOrder κ] {U : ι → C} {V : κ → C}
  (P : Cᵒᵖ ⥤ A)

/-- The map of ordered Čech complexes induced by an actual refinement. The index function need
not preserve the orders: alternating extension supplies the reordering sign and kills repetitions.
-/
def strictMonoCechComplexMap (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (strictMonoCechComplexFunctor V).obj P ⟶ (strictMonoCechComplexFunctor U).obj P :=
  (fromStrictMonoCechComplex V).app P ≫ cechComplexMap P φ ≫ (toStrictMonoCechComplex U).app P

/-- Ordered refinement is alternating extension, tuple refinement, then ordered restriction. -/
lemma strictMonoCechComplexMap_def (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    strictMonoCechComplexMap P φ =
      (fromStrictMonoCechComplex V).app P ≫ cechComplexMap P φ ≫
        (toStrictMonoCechComplex U).app P :=
  (rfl)

private lemma strictMonoCechComplexMap_f_π_eq
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    (strictMonoCechComplexMap P φ).f n ≫ strictMonoCechComplexπ U P a =
      (((fromStrictMonoCechComplex V).app P).f n ≫
        Pi.π _ (φ.f ∘ a.1)) ≫
          P.map (Limits.Pi.map fun j ↦ φ.φ (a.1 j)).op := by
  -- Keep the tuple products explicitly typed: simplifying their opaque formal-coproduct
  -- presentation before composing the projection identities obstructs rewriting.
  rw [strictMonoCechComplexMap_def]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  exact (congrArg (fun f ↦ ((fromStrictMonoCechComplex V).app P).f n ≫
    (cechComplexMap P φ).f n ≫ f) (toStrictMonoCechComplex_app_f_π U P n a)).trans
      ((congrArg (fun f ↦ ((fromStrictMonoCechComplex V).app P).f n ≫ f)
        (cechComplexMap_f_π P φ n a.1)).trans (Category.assoc _ _ _).symm)

/-- On an increasing tuple whose image has no repetitions, refinement sorts the image tuple,
multiplies by its inversion sign, and restricts the resulting section. -/
@[reassoc]
theorem strictMonoCechComplexMap_f_π
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) (ha : Function.Injective (φ.f ∘ a.1)) :
    (strictMonoCechComplexMap P φ).f n ≫ strictMonoCechComplexπ U P a =
      (-1 : ℤ) ^ (Finset.univ.inversions (φ.f ∘ a.1)).card •
        (strictMonoCechComplexπ V P
          ⟨(φ.f ∘ a.1) ∘ Tuple.sort (φ.f ∘ a.1), Tuple.strictMono_comp_sort ha⟩ ≫
          P.map (Pi.lift fun j ↦ Pi.π (fun j ↦ V ((φ.f ∘ a.1) j))
            (Tuple.sort (φ.f ∘ a.1) j)).op ≫
          P.map (Limits.Pi.map fun j ↦ φ.φ (a.1 j)).op) := by
  exact (strictMonoCechComplexMap_f_π_eq P φ n a).trans
    ((congrArg (fun f ↦ f ≫ P.map (Limits.Pi.map fun j ↦ φ.φ (a.1 j)).op)
      (fromStrictMonoCechComplex_app_f_π V P n ha)).trans
        ((Preadditive.zsmul_comp _ _ _).trans (congrArg _ (Category.assoc _ _ _))))

/-- A tuple collapsed by the refinement contributes zero to the ordered refinement map. -/
@[simp, reassoc]
theorem strictMonoCechComplexMap_f_π_of_not_injective
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) (ha : ¬Function.Injective (φ.f ∘ a.1)) :
    (strictMonoCechComplexMap P φ).f n ≫ strictMonoCechComplexπ U P a = 0 := by
  exact (strictMonoCechComplexMap_f_π_eq P φ n a).trans
    ((congrArg (fun f ↦ f ≫ P.map (Limits.Pi.map fun j ↦ φ.φ (a.1 j)).op)
      (fromStrictMonoCechComplex_app_f_π_of_not_injective V P n ha)).trans zero_comp)

/-- Ordered refinement is natural in the coefficient presheaf. -/
@[reassoc]
theorem strictMonoCechComplexMap_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (strictMonoCechComplexFunctor V).map α ≫ strictMonoCechComplexMap Q φ =
      strictMonoCechComplexMap P φ ≫ (strictMonoCechComplexFunctor U).map α := by
  simp only [strictMonoCechComplexMap_def, Category.assoc]
  rw [(fromStrictMonoCechComplex V).naturality_assoc α, cechComplexMap_naturality_assoc,
    (toStrictMonoCechComplex U).naturality]

/-- The identity refinement acts as the identity, already on ordered cochains. -/
@[simp]
theorem strictMonoCechComplexMap_id :
    strictMonoCechComplexMap P (𝟙 (FormalCoproduct.mk _ U)) = 𝟙 _ := by
  simp [strictMonoCechComplexMap_def, ← NatTrans.comp_app]

/-- Restriction from tuple to ordered cochains intertwines refinement up to homotopy. -/
def toStrictMonoCechComplexMapHomotopy
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    Homotopy ((toStrictMonoCechComplex V).app P ≫ strictMonoCechComplexMap P φ)
      (cechComplexMap P φ ≫ (toStrictMonoCechComplex U).app P) := by
  simpa only [strictMonoCechComplexMap_def, Category.assoc,
    strictMonoCechComplexHomotopyEquiv_hom, strictMonoCechComplexHomotopyEquiv_inv] using
    ((strictMonoCechComplexHomotopyEquiv V P).homotopyHomInvId.compRightId
      (cechComplexMap P φ ≫ (toStrictMonoCechComplex U).app P))

/-- Alternating extension from ordered to tuple cochains intertwines refinement up to homotopy.
-/
def fromStrictMonoCechComplexMapHomotopy
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    Homotopy (strictMonoCechComplexMap P φ ≫ (fromStrictMonoCechComplex U).app P)
      ((fromStrictMonoCechComplex V).app P ≫ cechComplexMap P φ) := by
  simpa only [strictMonoCechComplexMap_def, Category.assoc,
    strictMonoCechComplexHomotopyEquiv_hom, strictMonoCechComplexHomotopyEquiv_inv] using
    ((strictMonoCechComplexHomotopyEquiv U P).homotopyHomInvId.compLeftId
      ((fromStrictMonoCechComplex V).app P ≫ cechComplexMap P φ))

/-- Any two actual refinement functions induce homotopic ordered refinement maps. -/
def strictMonoCechComplexMapHomotopy
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    Homotopy (strictMonoCechComplexMap P φ) (strictMonoCechComplexMap P ψ) :=
  (cechComplexMapHomotopy P φ ψ).compRight ((toStrictMonoCechComplex U).app P) |>.compLeft
    ((fromStrictMonoCechComplex V).app P)

/-- The ordered refinement homotopy is the tuple refinement homotopy, sandwiched between
alternating extension and ordered restriction. In particular its sign is inherited unchanged.
-/
@[simp]
lemma strictMonoCechComplexMapHomotopy_hom
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (i j : ℕ) :
    (strictMonoCechComplexMapHomotopy P φ ψ).hom i j =
      ((fromStrictMonoCechComplex V).app P).f i ≫
        (cechComplexMapHomotopy P φ ψ).hom i j ≫ ((toStrictMonoCechComplex U).app P).f j :=
  (rfl)

/-- Successive ordered refinements agree with their composite up to homotopy. -/
def strictMonoCechComplexMapCompHomotopy {τ : Type w} [LinearOrder τ] {W : τ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W) :
    Homotopy (strictMonoCechComplexMap P ψ ≫ strictMonoCechComplexMap P φ)
      (strictMonoCechComplexMap P (φ ≫ ψ)) := by
  simpa only [strictMonoCechComplexMap_def, cechComplexMap_comp, Category.assoc] using
    ((toStrictMonoCechComplexMapHomotopy P φ).compLeft
      ((fromStrictMonoCechComplex W).app P ≫ cechComplexMap P ψ))

section Homology

variable [CategoryWithHomology A] (n : ℕ)

/-- The map on ordered Čech cohomology induced by an actual refinement, natural in coefficients.
-/
def strictMonoCechComplexHomologyMap
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    strictMonoCechComplexFunctor V ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      strictMonoCechComplexFunctor U ⋙ HomologicalComplex.homologyFunctor A _ n where
  app P := (HomologicalComplex.homologyFunctor A _ n).map (strictMonoCechComplexMap P φ)
  naturality P Q α := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp,
      strictMonoCechComplexMap_naturality]

@[simp]
lemma strictMonoCechComplexHomologyMap_app
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (strictMonoCechComplexHomologyMap n φ).app P =
      HomologicalComplex.homologyMap (strictMonoCechComplexMap P φ) n :=
  (rfl)

/-- The map on ordered Čech cohomology is independent of the refinement function. -/
theorem strictMonoCechComplexHomologyMap_eq
    (φ ψ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    strictMonoCechComplexHomologyMap (A := A) n φ = strictMonoCechComplexHomologyMap n ψ := by
  ext P
  exact (strictMonoCechComplexMapHomotopy P φ ψ).homologyMap_eq n

@[simp]
lemma strictMonoCechComplexHomologyMap_id :
    strictMonoCechComplexHomologyMap (A := A) n (𝟙 (FormalCoproduct.mk _ U)) = 𝟙 _ := by
  ext P
  exact ((HomologicalComplex.homologyFunctor A _ n).congr_map
    (strictMonoCechComplexMap_id P)).trans ((HomologicalComplex.homologyFunctor A _ n).map_id _)

/-- Refinement acts contravariantly on ordered Čech cohomology. -/
@[simp]
theorem strictMonoCechComplexHomologyMap_comp {τ : Type w} [LinearOrder τ] {W : τ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V)
    (ψ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W) :
    strictMonoCechComplexHomologyMap (A := A) n (φ ≫ ψ) =
      strictMonoCechComplexHomologyMap n ψ ≫ strictMonoCechComplexHomologyMap n φ := by
  ext P
  exact ((strictMonoCechComplexMapCompHomotopy P φ ψ).homologyMap_eq n).symm.trans
    (HomologicalComplex.homologyMap_comp _ _ n)

/-- The tuple-to-ordered cohomology isomorphisms commute with every raw refinement. -/
@[reassoc]
theorem homologyMap_toStrictMonoCechComplex_comp
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    HomologicalComplex.homologyMap ((toStrictMonoCechComplex V).app P) n ≫
        HomologicalComplex.homologyMap (strictMonoCechComplexMap P φ) n =
      HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫
        HomologicalComplex.homologyMap ((toStrictMonoCechComplex U).app P) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    (toStrictMonoCechComplexMapHomotopy P φ).homologyMap_eq n

end Homology

end TauCeti.CategoryTheory
