/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Dualizable
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Dual
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Duality for sheaves of modules on a scheme

The self-duality of a finite free sheaf of modules specializes to the symmetric monoidal category
`X.Modules` on a scheme. This is the local model for duality of finite locally free sheaves.
Gluing these local dualities, the dual-tensor comparison `𝓗om(M, 𝒪_X) ⊗ N ⟶ 𝓗om(M, N)` of a
locally free `𝒪_X`-module of finite type is an isomorphism, so `𝓗om(M, 𝒪_X)` is a left dual of `M`
by `TauCeti.exactPairingOfIsIsoDualTensorIhom`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exactPairingFree`: a finite free `𝒪_X`-module is
  self-dual;
* `AlgebraicGeometry.Scheme.Modules.isIso_dualTensorIhom_of_isLocallyFree`: the dual-tensor
  comparison of a locally free `𝒪_X`-module of finite type is an isomorphism;
* `AlgebraicGeometry.Scheme.Modules.dualHomUnitEquiv`: for such a module `M`, linear functionals
  `𝓗om(M, 𝒪_X) ⟶ 𝒪_X` on the dual are global sections `𝒪_X ⟶ M`, a section corresponding to
  evaluation at it.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The monoidal structure of `X.Modules`, stated for the unfolded type
`SheafOfModules X.ringCatSheaf`, which typeclass search does not see through the definition of
`Scheme.Modules`. -/
local instance monoidalCategorySheafOfModules : MonoidalCategory
    (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X

/-- The free `𝒪_X`-module on a finite type is self-dual. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.exactPairingFree
    (I : Type u) [Finite I] :
    ExactPairing
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) :=
  @TauCeti.SheafOfModules.exactPairingFree _ _ _ _ _ _ X.sheaf I _

/-- The dual-tensor comparison `𝓗om(M, 𝒪_X) ⊗ N ⟶ 𝓗om(M, N)` of a locally free `𝒪_X`-module of
finite type is an isomorphism. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isIso_dualTensorIhom_of_isLocallyFree
    {X : Scheme.{u}} (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] :
    IsIso (dualTensorIhom M) :=
  _root_.SheafOfModules.isIso_dualTensorIhom_of_isLocallyFree (R := X.sheaf) M

section DualHomUnitEquiv

open MonoidalClosed

variable {X} (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType]

/-- Linear functionals on the dual of a locally free `𝒪_X`-module `M` of finite type are global
sections of `M`: `(𝓗om(M, 𝒪_X) ⟶ 𝒪_X) ≃ (𝒪_X ⟶ M)`. A global section `s` corresponds to
evaluation of functionals at `s` (`Scheme.Modules.dualHomUnitEquiv_symm_apply`). This is
`TauCeti.ExactPairing.homUnitEquiv` for the exact pairing of `𝓗om(M, 𝒪_X)` with `M`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.dualHomUnitEquiv :
    ((ihom M).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules) ≃ (𝟙_ X.Modules ⟶ M) :=
  letI : ExactPairing ((ihom M).obj (𝟙_ X.Modules)) M := exactPairingOfIsIsoDualTensorIhom
  ExactPairing.homUnitEquiv ((ihom M).obj (𝟙_ X.Modules)) M

/-- The global section of a functional `φ` on the dual of `M` applies `φ` after the
coevaluation `𝒪_X ⟶ 𝓗om(M, 𝒪_X) ⊗ M`, the preimage of the identity of `M` under the dual-tensor
comparison. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.dualHomUnitEquiv_apply
    (φ : (ihom M).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules) :
    Scheme.Modules.dualHomUnitEquiv M φ =
      (MonoidalClosed.id M ≫ inv ((dualTensorIhom M).app M)) ≫ φ ▷ M ≫ (λ_ M).hom := by
  let : ExactPairing ((ihom M).obj (𝟙_ X.Modules)) M := exactPairingOfIsIsoDualTensorIhom
  rw [Scheme.Modules.dualHomUnitEquiv, ExactPairing.homUnitEquiv_apply,
    exactPairingOfIsIsoDualTensorIhom_coevaluation]

/-- The functional on the dual of `M` of a global section `s` is evaluation at `s`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.dualHomUnitEquiv_symm_apply
    (s : 𝟙_ X.Modules ⟶ M) :
    (Scheme.Modules.dualHomUnitEquiv M).symm s =
      (λ_ _).inv ≫ s ▷ (ihom M).obj (𝟙_ X.Modules) ≫ (ihom.ev M).app (𝟙_ X.Modules) := by
  let : ExactPairing ((ihom M).obj (𝟙_ X.Modules)) M := exactPairingOfIsIsoDualTensorIhom
  rw [Scheme.Modules.dualHomUnitEquiv, ExactPairing.homUnitEquiv_symm_apply,
    exactPairingOfIsIsoDualTensorIhom_evaluation]

variable {M} {N : X.Modules} [N.IsLocallyFree] [N.IsFiniteType]

/-- Evaluation at a section is natural: evaluating at the image `s ≫ b` of a section under
`b : M ⟶ N` is evaluating at `s` after precomposition with `b`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.dualHomUnitEquiv_symm_comp
    (s : 𝟙_ X.Modules ⟶ M) (b : M ⟶ N) :
    (Scheme.Modules.dualHomUnitEquiv N).symm (s ≫ b) =
      (pre b).app (𝟙_ X.Modules) ≫ (Scheme.Modules.dualHomUnitEquiv M).symm s := by
  rw [Scheme.Modules.dualHomUnitEquiv_symm_apply, Scheme.Modules.dualHomUnitEquiv_symm_apply,
    comp_whiskerRight, Category.assoc, ← id_tensor_pre_app_comp_ev, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

/-- The section of a functional precomposed with the dual of `b : M ⟶ N` is the image under `b`
of the section of the functional. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.dualHomUnitEquiv_pre_comp
    (φ : (ihom M).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules) (b : M ⟶ N) :
    Scheme.Modules.dualHomUnitEquiv N ((pre b).app (𝟙_ X.Modules) ≫ φ) =
      Scheme.Modules.dualHomUnitEquiv M φ ≫ b := by
  rw [← Equiv.eq_symm_apply, Scheme.Modules.dualHomUnitEquiv_symm_comp, Equiv.symm_apply_apply]

end DualHomUnitEquiv

end


end AlgebraicGeometry

end TauCeti
