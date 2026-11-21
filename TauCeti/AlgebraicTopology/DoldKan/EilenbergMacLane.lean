/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.AlgebraicTopology.DoldKan.HomotopyGroups

/-!
# Simplicial Eilenberg–MacLane modules

The Dold–Kan image of the complex with a module `A` in degree `n` and zero elsewhere
is a functorial simplicial Eilenberg–MacLane module. Its normalized Moore complex is
canonically `A[n]`. At the zero vertex every `πₖ` with `k ≠ n` is a singleton; in
particular the module is connected when `n` is positive. For positive `n`, the group
`πₙ` is identified with `A`, naturally in coefficient maps. No identification of `π₀`
with `A` is given here for the degree-zero model.

The coefficient identification uses the native Dold–Kan counit, followed by the
canonical homology identification for a single complex. Thus it fixes a specific
identification, rather than just asserting the existence of an abstract isomorphism.
All statements here concern combinatorial homotopy groups of the underlying Kan
complex; no comparison with topological homotopy groups is asserted.

## Main definitions

* `TauCeti.doldKanEilenbergMacLane`: the coefficient functor `A ↦ Γ(A[n])`.
* `TauCeti.DoldKanEilenbergMacLane.simplicialSet`: its underlying Kan complex.
* `TauCeti.DoldKanEilenbergMacLane.normalizationIso`: the natural counit `NΓ(A[n]) ≅ A[n]`.
* `TauCeti.DoldKanEilenbergMacLane.piAddEquiv`: the coefficient-normalized identification
  `πₙ₊₁(Γ(A[n+1]), 0) ≃+ A`.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter III, §2.
* J. P. May, *Simplicial Objects in Algebraic Topology*, §17, for the Moore-complex
  homotopy comparison used here.
-/

public noncomputable section

open CategoryTheory SimplicialObject HomologicalComplex
open scoped Simplicial

universe u v

namespace TauCeti

/-- The simplicial Eilenberg–MacLane module functor, obtained by denormalizing
the chain complex concentrated in degree `n`. -/
abbrev doldKanEilenbergMacLane (R : Type u) [Ring R] (n : ℕ) :
    ModuleCat.{v} R ⥤ SimplicialObject (ModuleCat.{v} R) :=
  single (ModuleCat R) (ComplexShape.down ℕ) n ⋙ Idempotents.DoldKan.Γ

namespace DoldKanEilenbergMacLane

variable {R : Type u} [Ring R]

/-- The underlying simplicial set of the Eilenberg–MacLane module `Γ(A[n])`. -/
abbrev simplicialSet (A : ModuleCat.{v} R) (n : ℕ) : SSet.{v} :=
  (doldKanEilenbergMacLane R n).obj A ⋙ forget (ModuleCat R)

/-- The zero vertex of the simplicial Eilenberg–MacLane module. -/
abbrev basepoint (A : ModuleCat.{v} R) (n : ℕ) : (simplicialSet A n) _⦋0⦌ :=
  (0 : ((doldKanEilenbergMacLane R n).obj A) _⦋0⦌)

/-- A coefficient map induces the corresponding map of simplicial Eilenberg–MacLane sets. -/
def map {A B : ModuleCat.{v} R} (f : A ⟶ B) (n : ℕ) :
    simplicialSet A n ⟶ simplicialSet B n :=
  Functor.whiskerRight ((doldKanEilenbergMacLane R n).map f) (forget (ModuleCat R))

/-- The induced map is the whiskered coefficient map of `Γ(A[n])`. -/
lemma map_def {A B : ModuleCat.{v} R} (f : A ⟶ B) (n : ℕ) :
    map f n = Functor.whiskerRight ((doldKanEilenbergMacLane R n).map f) (forget (ModuleCat R)) :=
  (rfl)

/-- The induced map acts on simplices by the coefficient map of `Γ(A[n])`.
Not `@[simp]`: `simp` rewrites the carrier type of its left-hand side by `Functor.comp_obj`,
so the `simpNF` linter rejects it. -/
lemma map_app_apply {A B : ModuleCat.{v} R} (f : A ⟶ B) (n : ℕ) (X : SimplexCategoryᵒᵖ)
    (x : (simplicialSet A n).obj X) :
    (map f n).app X x = ((doldKanEilenbergMacLane R n).map f).app X x :=
  (rfl)

/-- The induced map preserves the zero vertex. -/
lemma map_basepoint {A B : ModuleCat.{v} R} (f : A ⟶ B) (n : ℕ) :
    (map f n).app _ (basepoint A n) = basepoint B n :=
  map_zero (((doldKanEilenbergMacLane R n).map f).app _).hom

/-- Identity coefficient maps induce identity simplicial maps. -/
@[simp]
lemma map_id (A : ModuleCat.{v} R) (n : ℕ) : map (𝟙 A) n = 𝟙 (simplicialSet A n) := by
  simp [map, simplicialSet]

/-- Composition of coefficient maps induces composition of simplicial maps. -/
@[simp]
lemma map_comp {A B C : ModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  simp [map, simplicialSet]

/-- The normalized Moore complex of `Γ(A[n])` is naturally the single complex `A[n]`,
through Mathlib's abelian Dold–Kan counit. -/
def normalizationIso (n : ℕ) :
    doldKanEilenbergMacLane.{u, v} R n ⋙ AlgebraicTopology.normalizedMooreComplex (ModuleCat R) ≅
      single (ModuleCat R) (ComplexShape.down ℕ) n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ Abelian.DoldKan.equivalence.counitIso ≪≫ Functor.rightUnitor _

/-- The normalization isomorphism at a coefficient module is the native Dold–Kan counit. -/
@[simp]
lemma normalizationIso_app (A : ModuleCat.{v} R) (n : ℕ) :
    (normalizationIso (R := R) n).app A =
      Abelian.DoldKan.equivalence.counitIso.app
        ((single (ModuleCat R) (ComplexShape.down ℕ) n).obj A) := by
  apply Iso.ext
  simp [normalizationIso, Functor.isoWhiskerLeft, Functor.associator, Functor.rightUnitor]
  rfl

/-- The forward normalization map at a coefficient module is the native Dold–Kan counit. -/
@[simp]
lemma normalizationIso_hom_app (A : ModuleCat.{v} R) (n : ℕ) :
    (normalizationIso (R := R) n).hom.app A =
      Abelian.DoldKan.equivalence.counitIso.hom.app
        ((single (ModuleCat R) (ComplexShape.down ℕ) n).obj A) := by
  rw [← Iso.app_hom, normalizationIso_app, Iso.app_hom]

/-- The inverse normalization map at a coefficient module is the inverse native Dold–Kan
counit. -/
@[simp]
lemma normalizationIso_inv_app (A : ModuleCat.{v} R) (n : ℕ) :
    (normalizationIso (R := R) n).inv.app A =
      Abelian.DoldKan.equivalence.counitIso.inv.app
        ((single (ModuleCat R) (ComplexShape.down ℕ) n).obj A) := by
  rw [← Iso.app_inv, normalizationIso_app, Iso.app_inv]

/-- In the distinguished positive degree the homotopy group is the coefficient module,
using the Moore comparison and the Dold–Kan counit, with no choice of sign. -/
def piAddEquiv (A : ModuleCat.{v} R) (n : ℕ) :
    Additive (SSet.KanComplex.π (n + 1) (simplicialSet A (n + 1))
      (basepoint A (n + 1))) ≃+ A :=
  (ChainComplex.doldKanPiAddEquivHomology
    ((single (ModuleCat R) (ComplexShape.down ℕ) (n + 1)).obj A) n).trans
      (singleObjHomologySelfIso (ComplexShape.down ℕ) (n + 1) A).toLinearEquiv.toAddEquiv

/-- Compute the coefficient of a homotopy class by the Moore comparison, the normalization
counit and the canonical identification of single-complex homology. -/
lemma piAddEquiv_apply (A : ModuleCat.{v} R) (n : ℕ)
    (x : Additive (SSet.KanComplex.π (n + 1) (simplicialSet A (n + 1))
      (basepoint A (n + 1)))) :
    piAddEquiv A n x = (singleObjHomologySelfIso (ComplexShape.down ℕ) (n + 1) A).hom
      (homologyMap ((normalizationIso (R := R) (n + 1)).hom.app A) (n + 1)
        (piAddEquivNormalizedMooreComplexHomology
          ((doldKanEilenbergMacLane R (n + 1)).obj A) n x)) := by
  rw [normalizationIso_hom_app, piAddEquiv, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    ChainComplex.doldKanPiAddEquivHomology_apply]
  -- `erw`: the two sides elaborate `ComplexShape.down ℕ` with different `Add ℕ` instances
  erw [Iso.toLinearEquiv_apply]

/-- On a pointed simplex represented by a normalized cycle, the coefficient is obtained by
applying the counit to that cycle and reading its value in `A[n+1]`. This pins the
representative normalization as well as the abstract homotopy-group identification. -/
lemma piAddEquiv_mk (A : ModuleCat.{v} R) (n : ℕ)
    (p : SSet.PtSimplex (simplicialSet A (n + 1)) (n + 1) (basepoint A (n + 1)))
    (c : ((AlgebraicTopology.normalizedMooreComplex (ModuleCat R)).obj
      ((doldKanEilenbergMacLane R (n + 1)).obj A)).cycles (n + 1))
    (hc : (AlgebraicTopology.inclusionOfMooreComplexMap
        ((doldKanEilenbergMacLane R (n + 1)).obj A)).f (n + 1)
      (((AlgebraicTopology.normalizedMooreComplex (ModuleCat R)).obj
        ((doldKanEilenbergMacLane R (n + 1)).obj A)).iCycles (n + 1) c) =
          SSet.yonedaEquiv p.map) :
    piAddEquiv A n (.ofMul (SSet.KanComplex.π.mk p)) =
      (singleObjCyclesSelfIso (ComplexShape.down ℕ) (n + 1) A).hom
        (cyclesMap ((normalizationIso (R := R) (n + 1)).hom.app A) (n + 1) c) := by
  rw [piAddEquiv, AddEquiv.trans_apply, ChainComplex.doldKanPiAddEquivHomology_mk _ n p c hc,
    LinearEquiv.coe_toAddEquiv]
  -- `erw`: the two sides elaborate `ComplexShape.down ℕ` with different `Add ℕ` instances
  erw [Iso.toLinearEquiv_apply]
  exact ConcreteCategory.congr_hom
    (homologyπ_singleObjHomologySelfIso_hom (ComplexShape.down ℕ) (n + 1) A) _

/-- The coefficient identification of the distinguished homotopy group is natural. -/
lemma piAddEquiv_map {A B : ModuleCat.{v} R} (f : A ⟶ B) (n : ℕ)
    (x : SSet.KanComplex.π (n + 1) (simplicialSet A (n + 1)) (basepoint A (n + 1))) :
    piAddEquiv B n (.ofMul (SSet.KanComplex.π.map (map f (n + 1)) (map_basepoint f _) x)) =
      f (piAddEquiv A n (.ofMul x)) := by
  simp only [map_def, Functor.comp_map, piAddEquiv, AddEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv]
  -- `erw`: the class lives over `(single ⋙ Γ).obj A ⋙ forget _`, which is
  -- `Γ.obj (single.obj A) ⋙ forget _` only after unfolding `Functor.comp`
  erw [ChainComplex.doldKanPiAddEquivHomology_map]
  exact ConcreteCategory.congr_hom
    (singleObjHomologySelfIso_hom_naturality (ComplexShape.down ℕ) (n + 1) f)
    (ChainComplex.doldKanPiAddEquivHomology _ n (.ofMul x))

/-- Every homotopy set outside the distinguished degree is a singleton. In particular, the
simplicial Eilenberg–MacLane module of positive degree is connected. -/
theorem subsingleton_pi (A : ModuleCat.{v} R) (n k : ℕ) (h : k ≠ n) :
    Subsingleton (SSet.KanComplex.π k (simplicialSet A n) (basepoint A n)) := by
  have := ModuleCat.subsingleton_of_isZero
    (isZero_single_obj_homology (ComplexShape.down ℕ) n A k h)
  cases k with
  | zero =>
    exact (ChainComplex.doldKanPiZeroEquivHomology
      ((single (ModuleCat R) (ComplexShape.down ℕ) n).obj A)).subsingleton
  | succ k =>
    exact (Additive.ofMul.trans (ChainComplex.doldKanPiAddEquivHomology
      ((single (ModuleCat R) (ComplexShape.down ℕ) n).obj A) k).toEquiv).subsingleton

end DoldKanEilenbergMacLane

end TauCeti
