/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.CategoryTheory.Monoidal.Rigid.DoubleDual
import TauCeti.CategoryTheory.Monoidal.Closed.Basic

/-!
# Reflexive sheaves of modules on a scheme

Let `X` be a scheme. The *dual* of an `𝒪_X`-module `M` is the internal Hom `M^∨ = 𝓗om(M, 𝒪_X)`,
and the evaluation map `M ⟶ M^∨∨` into the double dual sends a section `m` to evaluation at `m`
(`TauCeti.doubleDualMap`, the transpose of the braided evaluation `M^∨ ⊗ M ⟶ 𝒪_X`). The module
`M` is *reflexive* when this map is an isomorphism (`Scheme.Modules.IsReflexive`; Stacks, Definition
31.13.1 (0AVU), stated there for an integral scheme and coherent `M`; the same evaluation-map
definition is made here for every `𝒪_X`-module).

Reflexivity is invariant under isomorphism (`Scheme.Modules.IsReflexive.of_iso`). Locally free
modules of finite type are reflexive (`Scheme.Modules.IsReflexive.locallyFree`): `M^∨` is a left
dual of `M`, and the double-dual map of a dualizable object is an isomorphism. In particular the
structure sheaf is reflexive. The dual of a reflexive module is reflexive
(`Scheme.Modules.IsReflexive.dual`): in a symmetric monoidal category the double-dual map of `M^∨`
is a section of the dual of the double-dual map of `M`.

## Main declarations

* `Scheme.Modules.IsReflexive M`: the evaluation map `M ⟶ M^∨∨` is an isomorphism, with the
  isomorphism `Scheme.Modules.IsReflexive.doubleDualIso`;
* `Scheme.Modules.IsReflexive.of_iso`: reflexivity transports along isomorphisms;
* `Scheme.Modules.IsReflexive.locallyFree`: locally free modules of finite type are reflexive;
* `Scheme.Modules.IsReflexive.dual`: the dual of a reflexive module is reflexive.

## References

* [Stacks Project, Definition 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module `M` is **reflexive** when the evaluation map `M ⟶ M^∨∨` into its double dual
`𝓗om(𝓗om(M, 𝒪_X), 𝒪_X)` is an isomorphism (Stacks, Definition 0AVU). -/
@[stacks 0AVU]
class _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive (M : X.Modules) : Prop where
  isIso_doubleDualMap : IsIso (doubleDualMap M)

attribute [instance] _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive.isIso_doubleDualMap

/-- The isomorphism `M ≅ M^∨∨` of a reflexive module with its double dual, given by evaluation. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive.doubleDualIso (M : X.Modules)
    [M.IsReflexive] :
    M ≅ ((ihom ((ihom M).obj (𝟙_ X.Modules))).obj (𝟙_ X.Modules)) :=
  asIso (doubleDualMap M)

/-- Reflexivity is invariant under isomorphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive.of_iso {M N : X.Modules} (e : M ≅ N)
    [M.IsReflexive] : N.IsReflexive := by
  have : IsIso (pre e.hom) := pre_isIso e
  have : IsIso ((pre e.hom).app (𝟙_ X.Modules)) := NatIso.isIso_app_of_isIso _ _
  have : IsIso (pre ((pre e.hom).app (𝟙_ X.Modules))) :=
    pre_isIso (asIso ((pre e.hom).app (𝟙_ X.Modules)))
  have : IsIso ((pre ((pre e.hom).app (𝟙_ X.Modules))).app (𝟙_ X.Modules)) :=
    NatIso.isIso_app_of_isIso _ _
  have h : doubleDualMap N =
      e.inv ≫ doubleDualMap M ≫ (pre ((pre e.hom).app (𝟙_ X.Modules))).app (𝟙_ X.Modules) := by
    rw [← doubleDualMap_naturality, Iso.inv_hom_id_assoc]
  exact ⟨h ▸ inferInstance⟩

/-- A locally free `𝒪_X`-module of finite type is reflexive: its dual `𝓗om(M, 𝒪_X)` is a left
dual of `M`, and the double-dual map of a dualizable object is an isomorphism. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive.locallyFree (M : X.Modules)
    [M.IsLocallyFree] [M.IsFiniteType] : M.IsReflexive :=
  letI : ExactPairing ((ihom M).obj (𝟙_ X.Modules)) M := exactPairingOfIsIsoDualTensorIhom
  ⟨isIso_doubleDualMap_of_exactPairing ((ihom M).obj (𝟙_ X.Modules))⟩

/-- The structure sheaf is reflexive. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive.unit :
    (𝟙_ X.Modules).IsReflexive :=
  ⟨inferInstance⟩

/-- The dual `𝓗om(M, 𝒪_X)` of a reflexive module is reflexive: its double-dual map is a section of
the dual of the double-dual map of `M`, which is an isomorphism. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.IsReflexive.dual (M : X.Modules)
    [M.IsReflexive] : ((ihom M).obj (𝟙_ X.Modules)).IsReflexive := by
  have : IsIso (pre (doubleDualMap M)) := pre_isIso (asIso (doubleDualMap M))
  have : IsIso ((pre (doubleDualMap M)).app (𝟙_ X.Modules)) := NatIso.isIso_app_of_isIso _ _
  have h := doubleDualMap_comp_pre_doubleDualMap M
  have : doubleDualMap ((ihom M).obj (𝟙_ X.Modules)) =
      inv ((pre (doubleDualMap M)).app (𝟙_ X.Modules)) := by
    rw [← cancel_mono ((pre (doubleDualMap M)).app (𝟙_ X.Modules)), h, IsIso.inv_hom_id]
  exact ⟨this ▸ inferInstance⟩

end

end AlgebraicGeometry

end TauCeti
