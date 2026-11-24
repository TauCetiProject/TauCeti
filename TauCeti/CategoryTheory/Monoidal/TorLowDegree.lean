/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Data.Finset.NatAntidiagonal
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.GradedObject.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Tor

/-!
# `Tor` in low degrees: `Tor₀` is the tensor product

Let `F` be a right exact additive functor between abelian categories and `P` a projective
resolution of `X`. The comparison `F.fromLeftDerivedZero : F.leftDerived 0 ⟶ F`, an isomorphism
for right exact `F` (`CategoryTheory.Functor.leftDerivedZeroIsoSelf`), is computed on `P`: a cycle
of `F(P)` in degree `0`, through the identification of `H₀(F(P))` with `(F.leftDerived 0).obj X`,
is sent to its image under `F(P.π.f 0) : F(P.X 0) ⟶ F(X)`
(`CategoryTheory.ProjectiveResolution.homologyπ_isoLeftDerivedObj_inv_fromLeftDerivedZero_app`).

In a monoidal abelian category, for an object `X` such that `X ⊗ -` is right exact, this gives
the isomorphism `CategoryTheory.torZeroIso X Y : Tor₀(X, Y) ≅ X ⊗ Y` and its computation on a
projective resolution of `Y` (`CategoryTheory.homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom`).
For graded objects indexed by `ℕ`, the sums `⨁_{i + j = n} Tor₀(Xᵢ, Yⱼ)` and
`⨁_{i + j = n} Xᵢ ⊗ Yⱼ` are identified summandwise when each `Xᵢ ⊗ -` is right exact
(`CategoryTheory.GradedObject.mapBifunctorMapObjTorZeroIso`).

When `Y` has projective dimension at most one, `Torₙ(X, Y)` vanishes for `n ≥ 2`
(`CategoryTheory.isZero_Tor_add_two_of_hasProjectiveDimensionLE_one`), as computed on the
projective presentation `0 ⟶ ker π ⟶ P ⟶ Y ⟶ 0` of `Y`, whose kernel is then projective. Only
`Y` is assumed to have projective dimension at most one.

## Main definitions and results

* `CategoryTheory.ProjectiveResolution.homologyπ_isoLeftDerivedObj_inv_fromLeftDerivedZero_app`:
  the comparison `F.leftDerived 0 ⟶ F` on a projective resolution.
* `CategoryTheory.torZeroIso`: `Tor₀(X, Y) ≅ X ⊗ Y`, computed by
  `CategoryTheory.homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom`.
* `CategoryTheory.GradedObject.mapBifunctorMapObjTorZeroIso`: the graded version, characterized by
  `CategoryTheory.GradedObject.ι_mapBifunctorMapObjTorZeroIso_hom`.
* `CategoryTheory.isZero_Tor_add_two_of_hasProjectiveDimensionLE_one`: the vanishing of `Torₙ` for
  `n ≥ 2` against an object of projective dimension at most one.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits MonoidalCategory

section LeftDerived

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasProjectiveResolutions C]
  [Abelian D]

/-- **The comparison `F.leftDerived 0 ⟶ F` on a projective resolution.** For a projective
resolution `P` of `X`, a cycle of `F(P)` in degree `0`, identified with a class of
`(F.leftDerived 0).obj X` through `P.isoLeftDerivedObj F 0`, is sent by `F.fromLeftDerivedZero` to
its image under `F.map (P.π.f 0)`. -/
@[reassoc]
lemma ProjectiveResolution.homologyπ_isoLeftDerivedObj_inv_fromLeftDerivedZero_app {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj P.complex).homologyπ 0 ≫ (P.isoLeftDerivedObj F 0).inv ≫
        F.fromLeftDerivedZero.app X =
      ((F.mapHomologicalComplex _).obj P.complex).iCycles 0 ≫ F.map (P.π.f 0) := by
  rw [P.fromLeftDerivedZero_eq F, Iso.inv_hom_id_assoc, HomologicalComplex.isoHomologyι_hom,
    HomologicalComplex.homology_π_ι_assoc, pOpcycles_comp_fromLeftDerivedZero']

end LeftDerived

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

/-- **`Tor` against an object of projective dimension at most one** vanishes in degrees `≥ 2`. -/
lemma isZero_Tor_add_two_of_hasProjectiveDimensionLE_one (X Y : C) [EnoughProjectives C]
    [HasProjectiveDimensionLE Y 1] (n : ℕ) : IsZero (((Tor C (n + 2)).obj X).obj Y) :=
  -- the kernel of the projective cover `P ⟶ Y` has projective dimension `< 1`, as `P` is projective
  -- and `Y` has projective dimension `< 2`
  have : HasProjectiveDimensionLT (Projective.kernelShortComplex Y).X₁ 1 :=
    (Projective.kernelShortComplex_shortExact Y).hasProjectiveDimensionLT_X₁ 1
      inferInstance ‹_›
  (Projective.kernelShortComplex_shortExact Y).isZero_Tor_add_two X n

namespace GradedObject

attribute [local instance] Abelian.hasFiniteBiproducts

variable (X Y : GradedObject ℕ C) [∀ i, PreservesFiniteColimits ((tensoringLeft C).obj (X i))]
  (n : ℕ)

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
lemma ι_mapBifunctorMapObjTorZeroIso_hom (i j : ℕ) (h : i + j = n) :
    ιMapBifunctorMapObj (Tor C 0) (fun x ↦ x.1 + x.2) X Y i j n h ≫
        (mapBifunctorMapObjTorZeroIso X Y n).hom =
      (torZeroIso (X i) (Y j)).hom ≫ Monoidal.ιTensorObj X Y i j n h := by
  simp [mapBifunctorMapObjTorZeroIso]

end GradedObject

end CategoryTheory
