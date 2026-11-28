/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.HomFromProjective.Functor
public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.DerivedCategory.Grothendieck
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable
public import TauCeti.Algebra.Category.ModuleCat.Generator
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The regular module generates the unbounded derived category

The regular module placed in degree zero has a coproduct-preserving additive Hom functor,
and its integer shifts detect zero objects of the unbounded derived category. More generally,
additive Hom from the regular module placed in degree `n` is the underlying abelian group
of `n`-th cohomology, naturally in the target complex.

We use the small-Hom derived category supplied by
`CategoryTheory.IsGrothendieckAbelian.hasDerivedCategory`: for `R : Type u`, both ordinary
and derived morphisms lie in `Type u`. No commutativity, finiteness or boundedness is required.
The shift convention is cohomological: shifting `R[0]` by `-n` places it in degree `n`.

This is the module case of compact generation in Stacks, Theorem 36.15.3 (Tag 09IS).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Functor ZeroObject DerivedCategory

universe u

namespace TauCeti

variable (R : Type u) [Ring R]

/-- Additive Hom from the regular module in degree `n` is the underlying abelian group of
`n`-th cohomology. -/
def derivedModuleCatPreadditiveCoyonedaRingIso (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R))) ≅
      homologyFunctor (ModuleCat.{u} R) n ⋙ forget₂ (ModuleCat R) AddCommGrpCat :=
  preadditiveCoyonedaSingleIso (ModuleCat.of R R) n ≪≫
    isoWhiskerLeft _ (moduleCatPreadditiveCoyonedaRingIso R)

/-- The cohomology class corresponding to a derived morphism from the regular module is
obtained by evaluating its cohomology map at `1`. -/
@[simp]
lemma derivedModuleCatPreadditiveCoyonedaRingIso_hom_app_apply (n : ℤ)
    (E : DerivedCategory (ModuleCat.{u} R))
    (f : (singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) :
    DFunLike.coe (F := ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
      (homologyFunctor (ModuleCat R) n).obj E)
      ((derivedModuleCatPreadditiveCoyonedaRingIso R n).hom.app E).hom f =
      (((singleFunctorCompHomologyFunctorIso (ModuleCat R) n).inv.app (ModuleCat.of R R)) ≫
        (homologyFunctor (ModuleCat R) n).map f).hom (1 : R) := by
  simp only [derivedModuleCatPreadditiveCoyonedaRingIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app]
  -- Fix the underlying Hom types explicitly: the bundled functor objects otherwise prevent
  -- rewriting the evaluation lemma at implicit transparency.
  let g : ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E :=
    DFunLike.coe (F := ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
      (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E))
      ((preadditiveCoyonedaSingleIso (ModuleCat.of R R) n).hom.app E).hom f
  change DFunLike.coe (F := (ModuleCat.of R R ⟶ (homologyFunctor (ModuleCat R) n).obj E) →+
    (homologyFunctor (ModuleCat R) n).obj E)
    ((moduleCatPreadditiveCoyonedaRingIso R).hom.app _).hom g = _
  rw [ModuleCat.preadditiveCoyonedaRingIso_hom_app_apply]
  exact congrArg (fun g : ModuleCat.of R R ⟶ _ ↦ g.hom (1 : R))
    (preadditiveCoyonedaSingleIso_hom_app_apply (ModuleCat.of R R) n E f)

/-- Every small coproduct is preserved by additive Hom from the regular module placed in
any one degree, in particular in degree zero. -/
instance preservesColimitsOfShape_preadditiveCoyoneda_ring (n : ℤ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj
        (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)))) :=
  preservesColimitsOfShape_of_natIso (derivedModuleCatPreadditiveCoyonedaRingIso R n).symm

end TauCeti

namespace DerivedCategory

/-- The integer shifts of the regular module in degree zero detect zero objects of the
unbounded derived category. -/
lemma isZero_of_forall_shift_ring_hom_eq_zero {R : Type u} [Ring R]
    (E : DerivedCategory (ModuleCat.{u} R))
    (h : ∀ (k : ℤ) (f : ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))⟦k⟧ ⟶ E),
      f = 0) : IsZero E :=
  E.isZero_of_forall_shift_projective_hom_eq_zero (ModuleCat.of R R)
    (ModuleCat.isSeparator_of_isGenerator _) h

end DerivedCategory
