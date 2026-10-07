/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Equivalence

/-!
# Descending invariants of finite representations to the group-algebra Grothendieck group

For a finite monoid `G` and a commutative Noetherian coefficient ring `k`, a function on
`FDRep k G` which is additive on short exact sequences induces a unique homomorphism from
`G₀(k[G])` to its target abelian group. The input is stated entirely in representation language;
the output lives in the same group-algebra Grothendieck group as restriction, induction and
permutation classes. This lets additive invariants of representations, such as dimension or
Euler characteristics, be evaluated on virtual module classes without choosing a module model.

`TauCeti.liftFDRepK0` is the induced homomorphism, `TauCeti.liftFDRepK0_of` computes its value on
an actual representation, and `TauCeti.liftFDRepK0_unique` is its uniqueness property. No separate
isomorphism-invariance hypothesis is necessary: short-exact additivity already implies it, as
proved by `TauCeti.ExactK0.AdditiveInvariant.map_iso`.

The construction uses the exact equivalence `TauCeti.fdRepEquivalence` and the universal property
`TauCeti.ExactK0.lift` of exact Grothendieck groups.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [CommRing k] [IsNoetherianRing k] [Monoid G] [Finite G]
  {A : Type*} [AddCommGroup A]

/-- A short-exact-additive function on finite representations descends to the exact
Grothendieck group of the group algebra. -/
noncomputable def liftFDRepK0 (f : FDRep k G → A)
    (hf : ∀ ⦃S : ShortComplex (FDRep k G)⦄, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) :
    ExactK0 (finiteModulesExactStructure k[G]) →+ A :=
  (ExactK0.lift (E := ExactStructure.abelian (FDRep k G))
    { obj := f
      map_conflation := fun {S} hS ↦ hf ((ExactStructure.abelian_conflation S).mp hS) }).comp
    (ExactK0.mapEquiv (fdRepEquivalence k G)
      (isConflationExact_fdRepEquivalence_functor k G)
      (isConflationExact_fdRepEquivalence_inverse k G)).symm.toAddMonoidHom

/-- The descended invariant takes its original value on the class of a finite representation's
group-algebra module. -/
@[simp]
theorem liftFDRepK0_of (f : FDRep k G → A)
    (hf : ∀ ⦃S : ShortComplex (FDRep k G)⦄, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃)
    (V : FDRep k G) :
    letI : Module.Finite k[G] (_root_.Representation.asModule V.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    liftFDRepK0 f hf (ExactK0.of (FGModuleCat.of k[G]
      (_root_.Representation.asModule V.ρ))) = f V := by
  let : Module.Finite k[G] (_root_.Representation.asModule V.ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  have hV : (ExactK0.of (FGModuleCat.of k[G] (_root_.Representation.asModule V.ρ)) :
      ExactK0 (finiteModulesExactStructure k[G])) =
      ExactK0.mapEquiv (fdRepEquivalence k G)
        (isConflationExact_fdRepEquivalence_functor k G)
        (isConflationExact_fdRepEquivalence_inverse k G) (ExactK0.of V) := by
    rw [ExactK0.mapEquiv_of]
    exact ExactK0.of_congr (ObjectProperty.isoMk _
      (eqToIso (fdRepEquivalence_functor_obj_obj k G V).symm))
  rw [hV, liftFDRepK0, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, ExactK0.lift_of]

/-- An additive homomorphism out of the group-algebra Grothendieck group is the descended
invariant if it agrees with that invariant on every finite representation. -/
theorem liftFDRepK0_unique (f : FDRep k G → A)
    (hf : ∀ ⦃S : ShortComplex (FDRep k G)⦄, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃)
    (F : ExactK0 (finiteModulesExactStructure k[G]) →+ A)
    (hF : ∀ V : FDRep k G,
      letI : Module.Finite k[G] (_root_.Representation.asModule V.ρ) :=
        Module.Finite.of_restrictScalars_finite k k[G] _
      F (ExactK0.of (FGModuleCat.of k[G] (_root_.Representation.asModule V.ρ))) = f V) :
    F = liftFDRepK0 f hf := by
  let e := ExactK0.mapEquiv (fdRepEquivalence k G)
    (isConflationExact_fdRepEquivalence_functor k G)
    (isConflationExact_fdRepEquivalence_inverse k G)
  suffices h : F.comp e.toAddMonoidHom = (liftFDRepK0 f hf).comp e.toAddMonoidHom by
    apply DFunLike.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact DFunLike.congr_fun h y
  apply ExactK0.hom_ext
  intro V
  let : Module.Finite k[G] (_root_.Representation.asModule V.ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  have hV : e (ExactK0.of V) =
      (ExactK0.of (FGModuleCat.of k[G] (_root_.Representation.asModule V.ρ)) :
        ExactK0 (finiteModulesExactStructure k[G])) := by
    rw [ExactK0.mapEquiv_of]
    exact ExactK0.of_congr (ObjectProperty.isoMk _
      (eqToIso (fdRepEquivalence_functor_obj_obj k G V)))
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hV, liftFDRepK0_of]
  exact hF V

end TauCeti
