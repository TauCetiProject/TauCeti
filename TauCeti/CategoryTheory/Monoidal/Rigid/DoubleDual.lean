/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.CategoryTheory.Monoidal.Rigid.Closed

/-!
# The double-dual map in a closed braided monoidal category

Let `C` be a braided monoidal category and `Y` an object for which both `Y` and its internal dual
`Yᵛ := (Y ⟶[C] 𝟙_ C)` are closed. The *double-dual map*

```text
Y ⟶ (Yᵛ ⟶[C] 𝟙_ C)
```

is the transpose of the braided evaluation `Yᵛ ⊗ Y ⟶ Y ⊗ Yᵛ ⟶ 𝟙_ C`. For modules over a
commutative ring it is the evaluation map `m ↦ (φ ↦ φ m)` into the double dual, `Module.Dual.eval`
in Mathlib; for sheaves of modules it is the map `𝓔 ⟶ 𝓗om(𝓗om(𝓔, 𝒪), 𝒪)`.

The map is natural in `Y`, and it is an isomorphism whenever `Y` has a left or a right dual. So in
a closed symmetric monoidal category such as `QCoh(X)` or modules over a commutative ring, every
dualizable object is canonically isomorphic to its double dual, with the duals computed by
internal homs into the unit. The `IsIso` instances are found by instance search, so
`asIso (doubleDualMap Y)` is available for any object with a `HasLeftDual` or `HasRightDual`
instance, for example a finite projective module.

## Main declarations

* `TauCeti.doubleDualMap`: the canonical map `Y ⟶ ((Y ⟶[C] 𝟙_ C) ⟶[C] 𝟙_ C)`, characterized by
  `TauCeti.whiskerLeft_doubleDualMap_comp_ev`;
* `TauCeti.doubleDualMap_naturality`: its naturality in `Y`;
* `TauCeti.doubleDualMap_comp_pre_ihomUnitIso_inv_app`: its form for a chosen left dual `D`, the
  transpose of the braided pairing `D ⊗ Y ⟶ 𝟙_ C`;
* `TauCeti.isIso_doubleDualMap_of_exactPairing`, `TauCeti.isIso_doubleDualMap` and
  `TauCeti.isIso_doubleDualMap_of_hasRightDual`: it is an isomorphism for an object with a left or
  a right dual.

## References

* [A. Dold and D. Puppe, *Duality, trace, and transfer*][doldpuppe1980], §1
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

section Map

variable (Y : C) [Closed Y] [Closed (Y ⟶[C] 𝟙_ C)]

/-- The canonical map `Y ⟶ ((Y ⟶[C] 𝟙_ C) ⟶[C] 𝟙_ C)` from an object to its double dual: the
transpose of the evaluation `(Y ⟶[C] 𝟙_ C) ⊗ Y ⟶ Y ⊗ (Y ⟶[C] 𝟙_ C) ⟶ 𝟙_ C`, braided so that the
dual acts on the left. -/
def doubleDualMap : Y ⟶ ((Y ⟶[C] 𝟙_ C) ⟶[C] 𝟙_ C) :=
  curry ((β_ (Y ⟶[C] 𝟙_ C) Y).hom ≫ (ihom.ev Y).app (𝟙_ C))

/-- Evaluation characterizes the double-dual map: evaluating the double dual of `y` at `φ` is
evaluating `φ` at `y`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_doubleDualMap_comp_ev :
    (Y ⟶[C] 𝟙_ C) ◁ doubleDualMap Y ≫ (ihom.ev (Y ⟶[C] 𝟙_ C)).app (𝟙_ C) =
      (β_ (Y ⟶[C] 𝟙_ C) Y).hom ≫ (ihom.ev Y).app (𝟙_ C) :=
  whiskerLeft_curry_ihom_ev_app _ _ _

/-- Uncurrying the double-dual map gives the braided evaluation. -/
@[simp]
theorem uncurry_doubleDualMap :
    uncurry (doubleDualMap Y) = (β_ (Y ⟶[C] 𝟙_ C) Y).hom ≫ (ihom.ev Y).app (𝟙_ C) :=
  uncurry_curry _

end Map

/-- The double-dual map is natural: for `f : Y ⟶ Y'`, following `f` by the double-dual map of
`Y'` is the double-dual map of `Y` followed by the double transpose of `f`, obtained by
precomposing twice. -/
theorem doubleDualMap_naturality {Y Y' : C} [Closed Y] [Closed (Y ⟶[C] 𝟙_ C)] [Closed Y']
    [Closed (Y' ⟶[C] 𝟙_ C)] (f : Y ⟶ Y') :
    f ≫ doubleDualMap Y' =
      doubleDualMap Y ≫ (pre ((pre f).app (𝟙_ C))).app (𝟙_ C) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_doubleDualMap, uncurry_doubleDualMap,
    braiding_naturality_right_assoc, braiding_naturality_left_assoc, id_tensor_pre_app_comp_ev]

section IsIso

variable {Y : C} [Closed Y] [Closed (Y ⟶[C] 𝟙_ C)]

/-- For a left dual `D` of `Y`, identifying `(Y ⟶[C] 𝟙_ C)` with `D` through
`TauCeti.ihomUnitIso` turns the double-dual map into the transpose of the braided pairing
`D ⊗ Y ⟶ Y ⊗ D ⟶ 𝟙_ C`. -/
theorem doubleDualMap_comp_pre_ihomUnitIso_inv_app (D : C) [ExactPairing D Y] [Closed D] :
    doubleDualMap Y ≫ (pre (ihomUnitIso D Y).inv).app (𝟙_ C) =
      curry ((β_ D Y).hom ≫ ε_ D Y) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_doubleDualMap, uncurry_curry, braiding_naturality_left_assoc,
    whiskerLeft_ihomUnitIso_inv_comp_ev]

/-- The double-dual map of an object with a left dual `D` is an isomorphism: `Y` is a left dual
of `(Y ⟶[C] 𝟙_ C)`, and the double-dual map is the inverse of the comparison
`TauCeti.ihomUnitIso` for that pairing. -/
theorem isIso_doubleDualMap_of_exactPairing (D : C) [ExactPairing D Y] :
    IsIso (doubleDualMap Y) := by
  -- `(Y ⟶[C] 𝟙_ C)` is a left dual of `Y` with the internal-hom evaluation; swap it.
  let := exactPairingIhomUnit D Y
  let := exactPairing_swap (Y ⟶[C] 𝟙_ C) Y
  have h : doubleDualMap Y = (ihomUnitIso Y (Y ⟶[C] 𝟙_ C)).inv := by
    rw [ihomUnitIso_inv, doubleDualMap]
    congr 1
    -- By definition of `exactPairing_swap`, the evaluation of the swapped pairing is the
    -- braiding followed by the evaluation of `exactPairingIhomUnit D Y`, which is the
    -- internal-hom evaluation.
    exact congrArg ((β_ (Y ⟶[C] 𝟙_ C) Y).hom ≫ ·) (exactPairingIhomUnit_evaluation D Y).symm
  rw [h]
  infer_instance

/-- The double-dual map of an object with a left dual is an isomorphism. -/
instance isIso_doubleDualMap [HasLeftDual Y] : IsIso (doubleDualMap Y) :=
  isIso_doubleDualMap_of_exactPairing (ᘁY)

/-- The double-dual map of an object with a right dual is an isomorphism. -/
instance isIso_doubleDualMap_of_hasRightDual [HasRightDual Y] : IsIso (doubleDualMap Y) :=
  letI : HasLeftDual Y := hasLeftDualOfHasRightDual
  isIso_doubleDualMap

end IsIso

end TauCeti
