/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.Algebra.Category.FGModuleCat.Pivotal
public import TauCeti.CategoryTheory.Action.Pivotal

/-!
# The standard spherical structure on finite-dimensional representations

For a field `k` and a group `G`, the category `FDRep k G` of finite-dimensional representations is
symmetric and rigid, so it carries the canonical spherical structure of a symmetric rigid
category (`TauCeti.symmetricSphericalCategory`). This is the standard spherical structure on
`FDRep k G`, and this file identifies it with the classical data of linear algebra:

* its pivotal isomorphism `V ≅ Vᘁᘁ` is, on underlying vector spaces, the evaluation map
  `Module.Dual.eval k V` into the double dual;
* the categorical trace of an equivariant endomorphism `f` is the linear trace of `f`, read as the
  scalar endomorphism of the trivial representation `k`;
* the quantum dimension of a representation is the dimension of its underlying vector space.

All three are transported from `FGModuleCat k` along the forgetful functor, using that traces in
categories of actions are computed on underlying objects (`Action.drinfeldIso_hom_hom` and
`Action.trace_hom`).

## Main results

* `FDRep.drinfeldIso_hom_hom_hom_hom`: the pivotal isomorphism, which is the Drinfeld
  isomorphism, is the double-dual evaluation map;
* `FDRep.trace_eq_smul`: the categorical trace is the linear trace;
* `FDRep.quantumDim_eq_smul`: the quantum dimension is the dimension.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory Module TauCeti

namespace FDRep

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The Drinfeld isomorphism `V ≅ Vᘁᘁ` of a finite-dimensional representation, which is the
canonical pivotal isomorphism `pivotalIsoApp V` by `TauCeti.pivotalIsoApp_eq_drinfeldIso`, is on
underlying vector spaces the evaluation map into the double dual. -/
theorem drinfeldIso_hom_hom_hom_hom (V : FDRep k G) :
    (drinfeldIso V).hom.hom.hom.hom = Dual.eval k V := by
  rw [Action.drinfeldIso_hom_hom]
  exact FGModuleCat.drinfeldIso_hom_hom_hom V.V

/-- The categorical trace of an equivariant endomorphism of a finite-dimensional representation
is its linear trace, acting on the trivial representation by scalar multiplication. -/
@[simp]
theorem trace_eq_smul {V : FDRep k G} (f : V ⟶ V) :
    trace f = LinearMap.trace k V f.hom.hom.hom • 𝟙 (𝟙_ (FDRep k G)) := by
  ext : 1
  rw [Action.trace_hom, FGModuleCat.trace_eq_smul, Action.smul_hom, Action.id_hom]
  -- The unit object of `FDRep k G` has the unit object of `FGModuleCat k` as underlying object.
  rfl

/-- The quantum dimension of a finite-dimensional representation is the dimension of its
underlying vector space, acting on the trivial representation by scalar multiplication. -/
@[simp]
theorem quantumDim_eq_smul (V : FDRep k G) :
    quantumDim V = (finrank k V : k) • 𝟙 (𝟙_ (FDRep k G)) := by
  rw [← trace_id, trace_eq_smul, Action.id_hom, FGModuleCat.hom_hom_id, LinearMap.trace_id]

end FDRep
