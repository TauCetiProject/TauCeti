/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import TauCeti.CategoryTheory.GradedObject.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Tor.Basic

/-!
# `Tor` in low degrees: `Tor₀` is the tensor product

Let `F` be a right exact additive functor between abelian categories. The comparison
`F.fromLeftDerivedZero : F.leftDerived 0 ⟶ F` is then an isomorphism
(`CategoryTheory.Functor.leftDerivedZeroIsoSelf`), computed on a projective resolution `P` of `X`
by `CategoryTheory.ProjectiveResolution.homologyπ_isoLeftDerivedObj_inv_fromLeftDerivedZero_app`
(in `TauCeti.CategoryTheory.Abelian.LeftDerived`): a cycle of `F(P)` in degree `0` is sent to its
image under `F(P.π.f 0) : F(P.X 0) ⟶ F(X)`.

In a monoidal abelian category, for an object `X` such that `X ⊗ -` is right exact, this gives
the isomorphism `CategoryTheory.torZeroIso X Y : Tor₀(X, Y) ≅ X ⊗ Y` and its computation on a
projective resolution of `Y` (`CategoryTheory.homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom`).
For graded objects indexed by an additive monoid with antidiagonals, such as `ℕ` (where the
coproducts involved exist automatically), the sums `⨁_{i + j = n} Tor₀(Xᵢ, Yⱼ)` and
`⨁_{i + j = n} Xᵢ ⊗ Yⱼ` are identified summandwise when each `Xᵢ ⊗ -` is right exact
(`CategoryTheory.GradedObject.mapBifunctorMapObjTorZeroIso`).

## Main definitions and results

* `CategoryTheory.torZeroIso`: `Tor₀(X, Y) ≅ X ⊗ Y`, computed by
  `CategoryTheory.homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom`.
* `CategoryTheory.GradedObject.mapBifunctorMapObjTorZeroIso`: the graded version, characterized by
  `CategoryTheory.GradedObject.ι_mapBifunctorMapObjTorZeroIso_hom`.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [HasProjectiveResolutions C]

/-- **`Tor₀` is the tensor product**: `Tor₀(X, Y) ≅ X ⊗ Y` when `X ⊗ -` is right exact, `Tor` being
derived in the second variable. -/
def torZeroIso (X Y : C) [PreservesFiniteColimits ((tensoringLeft C).obj X)] :
    ((Tor C 0).obj X).obj Y ≅ X ⊗ Y :=
  ((tensoringLeft C).obj X).leftDerivedZeroIsoSelf.app Y

/-- The isomorphism `CategoryTheory.torZeroIso` is the comparison
`((tensoringLeft C).obj X).fromLeftDerivedZero`. -/
lemma torZeroIso_hom (X Y : C) [PreservesFiniteColimits ((tensoringLeft C).obj X)] :
    (torZeroIso X Y).hom = ((tensoringLeft C).obj X).fromLeftDerivedZero.app Y :=
  (rfl)

/-- **`Tor₀(X, Y) ≅ X ⊗ Y` on a projective resolution.** For a projective resolution `P` of `Y`,
a cycle of `X ⊗ P` in degree `0`, identified with a class of `Tor₀(X, Y)`, is sent by
`CategoryTheory.torZeroIso` to its image under `X ◁ P.π.f 0 : X ⊗ P.X 0 ⟶ X ⊗ Y`. -/
@[reassoc]
lemma homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom (X : C)
    [PreservesFiniteColimits ((tensoringLeft C).obj X)] {Y : C} (P : ProjectiveResolution Y) :
    ((((tensoringLeft C).obj X).mapHomologicalComplex _).obj P.complex).homologyπ 0 ≫
        (P.isoLeftDerivedObj ((tensoringLeft C).obj X) 0).inv ≫ (torZeroIso X Y).hom =
      ((((tensoringLeft C).obj X).mapHomologicalComplex _).obj P.complex).iCycles 0 ≫
        X ◁ P.π.f 0 := by
  rw [torZeroIso_hom, P.homologyπ_isoLeftDerivedObj_inv_fromLeftDerivedZero_app]
  -- `(tensoringLeft C).obj X` sends `f` to `X ◁ f` by definition
  rfl

namespace GradedObject

attribute [local instance] Abelian.hasFiniteBiproducts

variable {I : Type*} [AddMonoid I] [Finset.HasAntidiagonal I] (X Y : GradedObject I C)
  [HasMap (((mapBifunctor (Tor C 0) I I).obj X).obj Y) (fun x ↦ x.1 + x.2)] [X.HasTensor Y]
  [∀ i, PreservesFiniteColimits ((tensoringLeft C).obj (X i))] (n : I)

/-- **`⨁_{i + j = n} Tor₀(Xᵢ, Yⱼ) ≅ ⨁_{i + j = n} Xᵢ ⊗ Yⱼ`**, summandwise by
`CategoryTheory.torZeroIso`. -/
def mapBifunctorMapObjTorZeroIso :
    mapBifunctorMapObj (Tor C 0) (fun x ↦ x.1 + x.2) X Y n ≅ Monoidal.tensorObj X Y n :=
  mapBifunctorMapObjIsoBiproduct (Tor C 0) X Y n ≪≫
    biproduct.mapIso (fun x ↦ torZeroIso (X x.val.1) (Y x.val.2)) ≪≫
    (Monoidal.tensorObjIsoBiproduct X Y n).symm

/-- On the summand `Tor₀(Xᵢ, Yⱼ)`, the isomorphism
`CategoryTheory.GradedObject.mapBifunctorMapObjTorZeroIso` is `CategoryTheory.torZeroIso`,
followed by the inclusion of the summand `Xᵢ ⊗ Yⱼ`. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjTorZeroIso_hom (i j : I) (h : i + j = n) :
    ιMapBifunctorMapObj (Tor C 0) (fun x ↦ x.1 + x.2) X Y i j n h ≫
        (mapBifunctorMapObjTorZeroIso X Y n).hom =
      (torZeroIso (X i) (Y j)).hom ≫ Monoidal.ιTensorObj X Y i j n h := by
  simp [mapBifunctorMapObjTorZeroIso]

end GradedObject

end CategoryTheory
