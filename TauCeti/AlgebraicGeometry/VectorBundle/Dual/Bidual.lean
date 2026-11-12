/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.DoubleDual

/-!
# Functorial duality and biduality of finite locally free sheaves

Internal Hom into the structure sheaf gives a contravariant endofunctor on finite locally free
sheaves. Its action on morphisms is precomposition, not an arbitrary choice of categorical dual.
The canonical map to the double dual is a natural isomorphism. It is the existing
`TauCeti.doubleDualMap`, whose evaluation equation pairs a local functional with the original
section. Thus dualization loses no information about the sheaf or its morphisms: together with the
triangle identity relating the bidual isomorphisms of `E` and of `E^∨`, biduality makes
dualization an anti-autoequivalence `dualEquiv` of finite locally free sheaves.

The functor and natural isomorphism follow the finite-projective module formalization in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal` as their template.

The construction lifts Mathlib's `MonoidalClosed.internalHom`, evaluated at the structure sheaf,
using `ObjectProperty.lift`. Biduality uses `TauCeti.doubleDualMap`; invertibility follows from the
exact pairing with the internal-Hom dual.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

-- Expose the functor so that morphism equations and the dependent components of biduality
-- have endpoints expressed by the existing `dual`, without transport along object equalities.
/-- Internal-Hom dualization of finite locally free sheaves, acting on morphisms by
precomposition. -/
@[expose]
def dualFunctor : (FiniteLocallyFreeSheaf X)ᵒᵖ ⥤ FiniteLocallyFreeSheaf X :=
  ObjectProperty.lift _
    ((Scheme.Modules.isFiniteLocallyFree X).ι.op ⋙ internalHom ⋙
      (CategoryTheory.evaluation X.Modules X.Modules).obj (𝟙_ X.Modules))
    fun E ↦ (dual E.unop).property

/-- The object assigned by dualization is the internal-Hom dual. -/
@[simp]
theorem dualFunctor_obj (E : (FiniteLocallyFreeSheaf X)ᵒᵖ) :
    dualFunctor.obj E = dual E.unop :=
  (rfl)

/-- Dualization acts on the underlying module morphism by precomposition. -/
@[simp]
theorem dualFunctor_map_hom {E F : (FiniteLocallyFreeSheaf X)ᵒᵖ} (f : E ⟶ F) :
    (dualFunctor.map f).hom = (pre f.unop.hom).app (𝟙_ X.Modules) :=
  (rfl)

/-- A finite locally free sheaf is canonically isomorphic to its internal-Hom double dual.
The forward map is the transpose of evaluation, with the functional on the left. -/
def evalIso (E : FiniteLocallyFreeSheaf X) : E ≅ dual (dual E) :=
  letI : ExactPairing (dual E).obj E.obj := exactPairingOfIsIsoDualTensorIhom (Y := E.obj)
  have : IsIso (doubleDualMap E.obj) := isIso_doubleDualMap_of_exactPairing (dual E).obj
  ObjectProperty.isoMk _ (asIso (doubleDualMap E.obj))

/-- The bidual isomorphism uses the canonical double-dual map of the underlying sheaf. -/
@[simp]
theorem evalIso_hom_hom (E : FiniteLocallyFreeSheaf X) :
    (evalIso E).hom.hom = doubleDualMap E.obj :=
  (rfl)

/-- Double-dual evaluation is natural in maps of finite locally free sheaves. -/
@[reassoc]
theorem evalIso_naturality {E F : FiniteLocallyFreeSheaf X} (f : E ⟶ F) :
    f ≫ (evalIso F).hom = (evalIso E).hom ≫
      dualFunctor.map (X := .op (dual E)) (Y := .op (dual F)) (dualFunctor.map f.op).op := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, evalIso_hom_hom]
  exact doubleDualMap_naturality f.hom

/-- The identity functor on finite locally free sheaves is naturally isomorphic to
internal-Hom dualization applied twice. -/
def evalNatIso : 𝟭 (FiniteLocallyFreeSheaf X) ≅ dualFunctor.rightOp ⋙ dualFunctor :=
  NatIso.ofComponents evalIso fun f ↦ evalIso_naturality f

/-- The forward component of the bidual natural isomorphism is canonical evaluation. -/
@[simp]
theorem evalNatIso_hom_app (E : FiniteLocallyFreeSheaf X) :
    evalNatIso.hom.app E = (evalIso E).hom :=
  (rfl)

/-- The inverse component of the bidual natural isomorphism is inverse evaluation. -/
@[simp]
theorem evalNatIso_inv_app (E : FiniteLocallyFreeSheaf X) :
    evalNatIso.inv.app E = (evalIso E).inv :=
  (rfl)

/-- **Triangle identity of biduality.** The bidual isomorphism of `E^∨` followed by the dual of
the bidual isomorphism of `E` is the identity of `E^∨`. -/
@[simp, reassoc]
theorem evalIso_hom_dual_comp_dualFunctor_map (E : FiniteLocallyFreeSheaf X) :
    (evalIso (dual E)).hom ≫
        dualFunctor.map (X := .op (dual (dual E))) (Y := .op E) (evalIso E).hom.op =
      𝟙 (dual E) := by
  apply ObjectProperty.hom_ext
  exact doubleDualMap_comp_pre_doubleDualMap E.obj

/-- Internal-Hom dualization is an anti-autoequivalence of finite locally free sheaves. Its
functor sends `E` to `E^∨` in the opposite category, its inverse is `dualFunctor`, its unit is
the bidual isomorphism `evalNatIso` and its counit is the opposite of the bidual isomorphism. -/
-- Exposed so that the functor, inverse, unit and counit lemmas below typecheck by unfolding.
@[expose]
def dualEquiv : FiniteLocallyFreeSheaf X ≌ (FiniteLocallyFreeSheaf X)ᵒᵖ where
  functor := dualFunctor.rightOp
  inverse := dualFunctor
  unitIso := evalNatIso
  counitIso := NatIso.ofComponents (fun E ↦ (evalIso E.unop).op)
    fun f ↦ Quiver.Hom.unop_inj (evalIso_naturality f.unop).symm
  functor_unitIso_comp E := by
    rw [evalNatIso_hom_app]
    exact Quiver.Hom.unop_inj (evalIso_hom_dual_comp_dualFunctor_map E)

/-- The functor of `dualEquiv` is dualization into the opposite category. -/
@[simp]
theorem dualEquiv_functor : (dualEquiv (X := X)).functor = dualFunctor.rightOp :=
  (rfl)

/-- The inverse of `dualEquiv` is dualization out of the opposite category. -/
@[simp]
theorem dualEquiv_inverse : (dualEquiv (X := X)).inverse = dualFunctor :=
  (rfl)

/-- The unit of `dualEquiv` is the bidual isomorphism. -/
@[simp]
theorem dualEquiv_unitIso : (dualEquiv (X := X)).unitIso = evalNatIso :=
  (rfl)

/-- The counit of `dualEquiv` at `E` is the opposite of the bidual isomorphism of `E`. -/
@[simp]
theorem dualEquiv_counitIso_app (E : (FiniteLocallyFreeSheaf X)ᵒᵖ) :
    (dualEquiv (X := X)).counitIso.app E = (evalIso E.unop).op :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
