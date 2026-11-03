/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Module structures on scheme-module stalks

The stalk of an `𝒪_X`-module carries the action of the original commutative local ring
`𝒪_{X,x}`. This exposes Mathlib's presheaf stalk action through the scheme-module presentation.

For a point `x` of an open `U`, the stalk `M_x` is also a `Γ(X, U)`-module through the germ map
`Γ(X, U) ⟶ 𝒪_{X,x}` (`AlgebraicGeometry.Scheme.Modules.moduleSectionStalk`), and the germ map
`Γ(M, U) → M_x` is `Γ(X, U)`-linear (`AlgebraicGeometry.Scheme.Modules.germₗ`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (x : X)

/-- The stalk of a scheme module is a module over the scheme's commutative local ring. -/
instance stalkModule : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  let Q : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) := M.val
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) Q.presheaf x))

/-- The module germ of a scalar multiple is the local-ring germ acting on the module germ. -/
theorem germ_smul (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(M, U)) :
    M.presheaf.germ U x hx (r • m) =
      X.presheaf.germ U x hx r • M.presheaf.germ U x hx m :=
  let Q : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) := M.val
  _root_.PresheafOfModules.germ_smul (R := X.presheaf) Q x U hx r m

section Section

variable {U : X.Opens} (x : U)

/-- For a point `x` of an open `U`, the stalk `M_x` is a `Γ(X, U)`-module through the germ map
`Γ(X, U) ⟶ 𝒪_{X,x}`, which is Mathlib's algebra structure
`TopCat.Presheaf.algebra_section_stalk`. -/
instance moduleSectionStalk : Module Γ(X, U) (M.presheaf.stalk x) :=
  Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk x))

/-- The `Γ(X, U)`-module structure on `M_x` factors through the local ring `𝒪_{X,x}`. -/
instance isScalarTower_sectionStalk :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  IsScalarTower.of_compHom _ _ _

/-- A function `r` on `U` acts on the stalk `M_x` through its germ at `x`. -/
lemma section_smul_stalk_def (r : Γ(X, U)) (m : M.presheaf.stalk x) :
    r • m = X.presheaf.germ U x x.2 r • m :=
  (rfl)

/-- The germ map `Γ(M, U) → M_x` at a point `x` of `U`, as a `Γ(X, U)`-linear map. This is the
linear form of `PresheafOfModules.germSemilinear`, which is semilinear along
`Γ(X, U) ⟶ 𝒪_{X,x}`; localization of modules is phrased for linear maps. -/
def germₗ : Γ(M, U) →ₗ[Γ(X, U)] M.presheaf.stalk x where
  toFun := M.presheaf.germ U x x.2
  map_add' := map_add _
  map_smul' r m := M.germ_smul x U x.2 r m

@[simp]
lemma germₗ_apply (m : Γ(M, U)) : M.germₗ x m = M.presheaf.germ U x x.2 m :=
  (rfl)

end Section

end AlgebraicGeometry.Scheme.Modules
