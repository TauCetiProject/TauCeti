/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.HomFromProjective.Functor
public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.DerivedCategory.Grothendieck
public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
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

open CategoryTheory Limits Opposite Functor ZeroObject

universe u

namespace DerivedCategory

variable (R : Type u) [Ring R]

/-- Additive Hom from the regular module in degree `n` is the underlying abelian group of
`n`-th cohomology. -/
def preadditiveCoyonedaRingIso (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R))) ≅
      homologyFunctor (ModuleCat.{u} R) n ⋙ forget₂ (ModuleCat R) AddCommGrpCat :=
  preadditiveCoyonedaSingleIso (ModuleCat.of R R) n ≪≫
    isoWhiskerLeft _ (ModuleCat.preadditiveCoyonedaRingIso R)

/-- The cohomology class corresponding to a derived morphism from the regular module is
obtained by evaluating its cohomology map at `1`. -/
@[simp]
lemma preadditiveCoyonedaRingIso_hom_app_apply (n : ℤ)
    (E : DerivedCategory (ModuleCat.{u} R))
    (f : (singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) :
    DFunLike.coe (F := ((singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) →+
      (homologyFunctor (ModuleCat R) n).obj E)
      ((preadditiveCoyonedaRingIso R n).hom.app E).hom f =
      (((singleFunctorCompHomologyFunctorIso (ModuleCat R) n).inv.app (ModuleCat.of R R)) ≫
        (homologyFunctor (ModuleCat R) n).map f).hom (1 : R) := by
  calc
    _ = ((preadditiveCoyonedaSingleIso (ModuleCat.of R R) n).hom.app E f).hom (1 : R) :=
      ModuleCat.preadditiveCoyonedaRingIso_hom_app_apply _ _
    _ = _ := congrArg (fun g : ModuleCat.of R R ⟶ _ ↦ g.hom (1 : R))
      (preadditiveCoyonedaSingleIso_hom_app_apply (ModuleCat.of R R) n E f)

/-- Every small coproduct is preserved by additive Hom from the regular module placed in
any one degree, in particular in degree zero. -/
instance preservesColimitsOfShape_preadditiveCoyoneda_ring (n : ℤ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj
        (op ((singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)))) :=
  preservesColimitsOfShape_of_natIso (preadditiveCoyonedaRingIso R n).symm

/-- The integer shifts of the regular module in degree zero detect zero objects of the
unbounded derived category. -/
lemma isZero_of_forall_shift_ring_hom_eq_zero (E : DerivedCategory (ModuleCat.{u} R))
    (h : ∀ (k : ℤ) (f : ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))⟦k⟧ ⟶ E),
      f = 0) : IsZero E := by
  have hH (n : ℤ) : IsZero ((homologyFunctor (ModuleCat R) n).obj E) := by
    let e := (preadditiveCoyonedaRingIso R n).app E
    have hz (f : (singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R) ⟶ E) : f = 0 := by
      let s := ((singleFunctors (ModuleCat R)).shiftIso (-n) n 0 (by omega)).app
        (ModuleCat.of R R)
      have hs := h (-n) (s.hom ≫ f)
      exact (cancel_epi s.hom).1 (by simpa using hs)
    have hm (x : (homologyFunctor (ModuleCat R) n).obj E) : x = 0 := by
      obtain ⟨f, hf⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 x
      rw [← hf, hz f]
      exact map_zero (AddCommGrpCat.Hom.hom e.hom)
    let : Subsingleton ((homologyFunctor (ModuleCat R) n).obj E) :=
      ⟨fun x y ↦ (hm x).trans (hm y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  have hi : IsIso (0 : E ⟶ 0) := (isIso_iff (ModuleCat R) _).2 fun n ↦ by
    exact (hH n).isIso
      ((homologyFunctor (ModuleCat R) n).map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : E ⟶ 0))

end DerivedCategory
