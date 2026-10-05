/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.AlgebraicGeometry.VectorBundle.Quasicoherent

/-!
# Duals of finite locally free sheaves

A finite locally free sheaf `E` on a scheme `X` is dualizable, with left dual its internal Hom
`𝓗om(E, 𝒪_X)` into the structure sheaf. The evaluation `E ⊗ 𝓗om(E, 𝒪_X) ⟶ 𝒪_X` is the evaluation
of the internal Hom, and the coevaluation is the preimage of the identity of `E` under the
dual-tensor comparison `𝓗om(E, 𝒪_X) ⊗ E ⟶ 𝓗om(E, E)`, which is invertible because `E` is finite
locally free (`AlgebraicGeometry.Scheme.Modules.isIso_dualTensorIhom_of_isLocallyFree`).

Consequently the symmetric monoidal category `FiniteLocallyFreeSheaf X` is rigid, and a
quasicoherent sheaf whose underlying module is finite locally free has the left dual
`𝓗om(E, 𝒪_X)` in the symmetric monoidal category `QuasicoherentSheaf X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.dual`: the dual `𝓗om(E, 𝒪_X)` of a finite
  locally free sheaf;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.exactPairingDual`: the exact pairing between
  `E` and its dual;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rigidCategory`: finite locally free sheaves
  form a rigid category;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.nonempty_hasLeftDual_of_isFiniteLocallyFree`: a
  finite locally free quasicoherent sheaf is dualizable in `QuasicoherentSheaf X`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace FiniteLocallyFreeSheaf

/-- The dual `𝓗om(E, 𝒪_X)` of a finite locally free sheaf `E`: the internal Hom from `E` into the
structure sheaf, which is again finite locally free.

This is an abbreviation so that instance search sees its underlying internal Hom, and hence the
exact pairing of that sheaf with `E`. -/
abbrev dual (E : FiniteLocallyFreeSheaf X) : FiniteLocallyFreeSheaf X :=
  ⟨(ihom E.obj).obj (𝟙_ X.Modules),
    _root_.SheafOfModules.isFiniteLocallyFree_ihom_unit (R := X.sheaf) E.obj⟩

/-- The underlying sheaf of the dual of `E` is the internal Hom from `E` into `𝒪_X`. -/
@[simp]
theorem dual_obj (E : FiniteLocallyFreeSheaf X) :
    (dual E).obj = (ihom E.obj).obj (𝟙_ X.Modules) :=
  (rfl)

/-- A finite locally free sheaf `E` has left dual `𝓗om(E, 𝒪_X)`. The evaluation is the evaluation
of the internal Hom, and the coevaluation is the preimage of the identity of `E` under the
invertible dual-tensor comparison. -/
instance exactPairingDual (E : FiniteLocallyFreeSheaf X) : ExactPairing (dual E) E :=
  letI : ExactPairing (dual E).obj E.obj := exactPairingOfIsIsoDualTensorIhom (Y := E.obj)
  ObjectProperty.exactPairingFullSubcategory _ _

/-- Finite locally free sheaves form a rigid category: the left and right duals of `E` are both
`𝓗om(E, 𝒪_X)`, the right duality obtained from the left one through the symmetry. -/
instance rigidCategory : RigidCategory (FiniteLocallyFreeSheaf X) :=
  letI : LeftRigidCategory (FiniteLocallyFreeSheaf X) := { leftDual E := ⟨dual E⟩ }
  BraidedCategory.rigidCategoryOfLeftRigidCategory

/-- The chosen left dual of a finite locally free sheaf is its dual `𝓗om(E, 𝒪_X)`. -/
@[simp]
theorem leftDual_eq_dual (E : FiniteLocallyFreeSheaf X) : (ᘁE) = dual E :=
  (rfl)

/-- The chosen right dual of a finite locally free sheaf is its dual `𝓗om(E, 𝒪_X)`. -/
@[simp]
theorem rightDual_eq_dual (E : FiniteLocallyFreeSheaf X) : (Eᘁ) = dual E :=
  (rfl)

/-- The evaluation `E ⊗ ᘁE ⟶ 𝒪_X` of the rigid structure is the evaluation of the internal Hom
`𝓗om(E, 𝒪_X)`. -/
theorem evaluation_leftDual_hom (E : FiniteLocallyFreeSheaf X) :
    (ε_ (ᘁE) E).hom = (ihom.ev E.obj).app (𝟙_ X.Modules) := by
  -- The chosen left dual is `dual E` by definition, but `ᘁE` cannot be rewritten under the
  -- dependent exact-pairing instance.
  change (ε_ (dual E) E).hom = _
  rw [ObjectProperty.exactPairingFullSubcategory_evaluation_hom]
  exact exactPairingOfIsIsoDualTensorIhom_evaluation

/-- The coevaluation `𝒪_X ⟶ ᘁE ⊗ E` of the rigid structure is the preimage of the identity of `E`
under the dual-tensor comparison `𝓗om(E, 𝒪_X) ⊗ E ⟶ 𝓗om(E, E)`. -/
theorem coevaluation_leftDual_hom (E : FiniteLocallyFreeSheaf X) :
    (η_ (ᘁE) E).hom = MonoidalClosed.id E.obj ≫ inv ((dualTensorIhom E.obj).app E.obj) := by
  -- As for the evaluation, the chosen left dual is `dual E` by definition.
  change (η_ (dual E) E).hom = _
  rw [ObjectProperty.exactPairingFullSubcategory_coevaluation_hom]
  exact exactPairingOfIsIsoDualTensorIhom_coevaluation

end FiniteLocallyFreeSheaf

namespace QuasicoherentSheaf

/-- A quasicoherent sheaf whose underlying module is finite locally free has a left dual in the
symmetric monoidal category `QuasicoherentSheaf X`, namely `𝓗om(E, 𝒪_X)` with the exact pairing of
`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.exactPairingDual`. -/
theorem nonempty_hasLeftDual_of_isFiniteLocallyFree (E : QuasicoherentSheaf X)
    (hE : Scheme.Modules.isFiniteLocallyFree X E.obj) : Nonempty (HasLeftDual E) :=
  let F : FiniteLocallyFreeSheaf X := ⟨E.obj, hE⟩
  -- `QuasicoherentSheaf X` is a full subcategory of `X.Modules`, so the pairing is restricted
  -- from the underlying pairing in `X.Modules` of the finite locally free sheaf `F`.
  letI : ExactPairing (FiniteLocallyFreeSheaf.dual F).obj F.obj :=
    exactPairingOfIsIsoDualTensorIhom (Y := F.obj)
  ⟨{ leftDual := (FiniteLocallyFreeSheaf.toQuasicoherent X).obj (FiniteLocallyFreeSheaf.dual F)
     exact := @ObjectProperty.exactPairingFullSubcategory X.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent X) _ E this }⟩

end QuasicoherentSheaf

end

end AlgebraicGeometry

end TauCeti
