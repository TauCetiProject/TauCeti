/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Sites.Point.ConstantSheaf
public import TauCeti.AlgebraicGeometry.Sites.EtaleSepClosed

/-!
# Finite lisse étale sheaves on a separably closed field

Let `Ω` be a separably closed field and `Λ` a ring. Étale sheaves of `Λ`-modules on `Spec Ω` are
the same as `Λ`-modules, through the constant sheaf functor and the global sections functor
(`AlgebraicGeometry.Scheme.isEquivalence_constantSheaf`). This file shows that this equivalence
restricts to the finite coefficients: a sheaf is finite lisse exactly when its global sections
are a finitely generated `Λ`-module, so the finite lisse étale sheaves of `Λ`-modules on `Spec Ω`
form a category equivalent to the finitely generated `Λ`-modules.

A finite lisse sheaf has finitely generated stalks, and the stalk at the geometric point
`𝟙 (Spec Ω)` is the global sections; conversely every sheaf on `Spec Ω` is the constant sheaf on
its global sections, which is finite lisse when they are finitely generated.

## Main results

* `CategoryTheory.Sheaf.isFiniteLisse_iff_finite_Γ`: on `Spec Ω`, a sheaf of `Λ`-modules is finite
  lisse exactly when its global sections are a finitely generated `Λ`-module.
* `CategoryTheory.Sheaf.isFiniteLisse_constantSheaf_iff`: on any scheme with a geometric point,
  the constant sheaf on a `Λ`-module `M` is finite lisse exactly when `M` is finitely generated.
* `CategoryTheory.Sheaf.finiteLisseSepClosedEquivalence`: the finite lisse étale sheaves of
  `Λ`-modules on `Spec Ω` are equivalent to `FGModuleCat Λ`, through the constant sheaf functor.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2, for sheaves on the étale
  site of a field as discrete Galois modules; here the Galois group is trivial.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TauCeti.AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] {Λ : Type u} [Ring Λ]

/-- On a scheme with a geometric point, the constant étale sheaf on a `Λ`-module `M` is finite
lisse exactly when `M` is finitely generated: its stalk at the point is `M`. -/
theorem isFiniteLisse_constantSheaf_iff {S : Scheme.{u}} (s : Spec (.of Ω) ⟶ S)
    (M : ModuleCat.{u} Λ) :
    ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M).IsFiniteLisse ↔
      Module.Finite Λ M :=
  ⟨fun h ↦ have := h.finite_etaleStalk s
    .equiv ((pointSmallEtale s).sheafFiberConstantSheafIso M).toLinearEquiv,
    fun _ ↦ isFiniteLisse_constantSheaf M⟩

/-- On a separably closed field, an étale sheaf of `Λ`-modules is finite lisse exactly when its
global sections are a finitely generated `Λ`-module. -/
theorem isFiniteLisse_iff_finite_Γ
    (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)) :
    F.IsFiniteLisse ↔ Module.Finite Λ ((Sheaf.Γ _ (ModuleCat.{u} Λ)).obj F) := by
  let adj := constantSheafΓAdj (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)
  -- `F` is the constant sheaf on its global sections.
  have e : (constantSheaf _ (ModuleCat.{u} Λ)).obj ((Sheaf.Γ _ (ModuleCat.{u} Λ)).obj F) ≅ F :=
    asIso (adj.counit.app F)
  rw [← isFiniteLisse_constantSheaf_iff Ω (𝟙 _)]
  exact ⟨fun h ↦ IsFiniteLisse.of_iso e.symm h, fun h ↦ IsFiniteLisse.of_iso e h⟩

variable (Λ) in
/-- On a separably closed field, the finite lisse étale sheaves of `Λ`-modules form a category
equivalent to the finitely generated `Λ`-modules, through the constant sheaf functor. -/
noncomputable def finiteLisseSepClosedEquivalence :
    FGModuleCat.{u} Λ ≌ ObjectProperty.FullSubcategory
      fun F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ) ↦ F.IsFiniteLisse :=
  haveI : ObjectProperty.IsClosedUnderIsomorphisms
      fun F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ) ↦ F.IsFiniteLisse :=
    ⟨fun e h ↦ IsFiniteLisse.of_iso e h⟩
  (constantSheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)).asEquivalence
    |>.congrFullSubcategory <| funext fun M ↦ propext (isFiniteLisse_constantSheaf_iff Ω (𝟙 _) M)

end CategoryTheory.Sheaf
